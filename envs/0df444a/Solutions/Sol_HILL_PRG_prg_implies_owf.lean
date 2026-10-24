-- Prove2me | solution 1 for HILL.PRG.prg_implies_owf
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Victorized
-- created : 2026-10-24T05:00:18.295994+00:00
-- url     : https://prove2.me/submissions/bf576cab-683e-4edf-be85-9a0eddfd44bb
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_HILL_PRG_InversionCheck
import Theorems.Thm_HILL_PRG_inverter_check_advantage_bound
import Theorems.Thm_HILL_PRG_inversion_checker_polytime

open HILL.PRG
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace WentaoHILLReverse

private lemma mem_cube {n : ℕ} {x : Bits} : x ∈ cube n ↔ x.length = n := by
  constructor
  · intro hx
    obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp hx
    simp
  · intro hx
    apply Finset.mem_image.mpr
    refine ⟨fun i : Fin n => x[i.val]'(by omega), Finset.mem_univ _, ?_⟩
    apply List.ext_getElem
    · simpa using hx.symm
    · intro i hi hj
      simp

private lemma unary_prefix (n : ℕ) (w : Bits) :
    ((encAdvice n 0 w).takeWhile id).length = n := by
  unfold encAdvice enc
  simp only [List.replicate_zero, List.nil_append]
  rw [List.takeWhile_append_of_pos (by intro b hb; simpa using List.eq_of_mem_replicate hb)]
  simp

private lemma encoded_payload (n : ℕ) (w : Bits) :
    (encAdvice n 0 w).drop (n + 2) = w := by
  simp [encAdvice, enc, List.drop_append]

private lemma checker_correct (G : FunEns) (M I : Bits → Bits)
    (hM : ∀ n x, x ∈ cube (G.t n) → M (encAdvice n 0 x) = G.f 0 n x)
    (n : ℕ) (y r : Bits) (hy : y ∈ cube (G.ℓ n)) :
    (inversionChecker (fun w => List.replicate (G.t w.length) true)
      (fun w => List.replicate (G.ℓ w.length) true) M I
      (encAdvice n 0 (y ++ r)) = [true] ↔
      let out := I (enc n (y ++ r));
      out ∈ cube (G.t n) ∧ G.f 0 n out = y) := by
  simp only [inversionChecker, unary_prefix, encoded_payload, List.length_replicate]
  have hytake : (y ++ r).take (G.ℓ n) = y := by
    rw [← mem_cube.mp hy]
    simp
  rw [hytake]
  let out := I (enc n (y ++ r))
  change ((if out.length = G.t n ∧ M (encAdvice n 0 out) = y then [true] else []) =
    [true] ↔ out ∈ cube (G.t n) ∧ G.f 0 n out = y)
  by_cases hx : out ∈ cube (G.t n)
  · have hlen := mem_cube.mp hx
    have hm := hM n out hx
    simp [hlen, hm, hx]
  · have hlen : out.length ≠ G.t n := by simpa only [mem_cube] using hx
    simp [hlen, hx]

private lemma negligible_of_eventual_le_two {u v : ℕ → ℝ}
    (hv : Negligible v) (hbound : ∀ n, 1 ≤ n → u n ≤ 2 * v n) : Negligible u := by
  intro k
  obtain ⟨N, hN⟩ := hv (k + 1)
  refine ⟨max N 2, ?_⟩
  intro n hn
  have hnN : N ≤ n := le_trans (le_max_left _ _) hn
  have hn2 : 2 ≤ n := le_trans (le_max_right _ _) hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have htwo : (2 : ℝ) / n ≤ 1 := (div_le_one hnR).mpr (by exact_mod_cast hn2)
  calc
    u n ≤ 2 * v n := hbound n (by omega)
    _ < 2 * (1 / (n : ℝ) ^ (k + 1)) :=
      mul_lt_mul_of_pos_left (hN n hnN) (by norm_num)
    _ = (2 / (n : ℝ)) * (1 / (n : ℝ) ^ k) := by
      rw [pow_succ]
      field_simp
    _ ≤ 1 * (1 / (n : ℝ) ^ k) :=
      mul_le_mul_of_nonneg_right htwo (by positivity)
    _ = 1 / (n : ℝ) ^ k := one_mul _

end WentaoHILLReverse

open WentaoHILLReverse

theorem solution :
    (∃ G : FunEns, IsPRG G (fun _ => 0)) →
      ∃ F : FunEns, IsOWF F := by
  rintro ⟨G, hGtime, hstretch, hind⟩
  refine ⟨G, hGtime, ?_⟩
  intro A
  obtain ⟨ht, hl, ha, M, hM, heval⟩ := hGtime
  let B : Adv := {
    run := inversionChecker (fun w => List.replicate (G.t w.length) true)
      (fun w => List.replicate (G.ℓ w.length) true) M A.run
    polyTime := inversion_checker_polytime _ _ _ _ ht.2 hl.2 hM A.polyTime
    coins := A.coins
    coinsPoly := A.coinsPoly }
  have hcheck : ∀ n y r, y ∈ cube (G.ℓ n) → r ∈ cube (A.coins n) →
      (B.run (encAdvice n 0 (y ++ r)) = [true] ↔
        let out := A.run (enc n (y ++ r));
        out ∈ cube (G.t n) ∧ G.f 0 n out = y) := by
    intro n y r hy _hr
    exact checker_correct G M A.run (fun n x hx => (heval n x hx).1) n y r hy
  apply negligible_of_eventual_le_two (hind B)
  intro n hn
  exact inverter_check_advantage_bound G A B
    (fun n x hx => (heval n x hx).2) rfl hcheck n (hstretch n hn)
