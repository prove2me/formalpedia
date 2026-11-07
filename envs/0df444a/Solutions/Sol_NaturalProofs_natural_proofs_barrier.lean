-- Prove2me | solution 1 for NaturalProofs.natural_proofs_barrier
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:51:09.568762+00:00
-- url     : https://prove2.me/submissions/2cfb8272-fe1f-487e-9281-884ffbf9d09a

module
public import Definitions.Def_NaturalProofs_GGM
public import Definitions.Def_NaturalProofs_Main
public import Theorems.Thm_NaturalProofs_distC_eval
public import Theorems.Thm_NaturalProofs_distC_size
public import Theorems.Thm_NaturalProofs_level_hybrid
public import Theorems.Thm_NaturalProofs_prfC_eval
public import Theorems.Thm_NaturalProofs_prfC_size
public import Theorems.Thm_NaturalProofs_prob_eq_card_filter


set_option autoImplicit true
@[expose] public section
public section
open NaturalProofs
open Finset
namespace NaturalProofs
theorem _root_.solution (G : (k : ℕ) → (Fin k → Bool) → Fin (2 * k) → Bool)
    (hG : GenInPPoly G) (ε : ℝ) (hε : 0 < ε)
    (hH : ∀ k₀ : ℕ, ∃ k ≥ k₀, HardnessAtLeast G k (2 ^ ((k : ℝ) ^ ε))) :
    ¬ ∃ C : Property, IsNatural C ∧ UsefulAgainstPPoly C := by
  rintro ⟨C, ⟨C', hsub, ⟨a, n₁, hcons⟩, ⟨b, n₂, hlarge⟩⟩, huse⟩
  obtain ⟨cG, hgc⟩ := hG
  choose gc hgcs hgce using hgc
  -- Parameters: `m` with `m ε ≥ 2`, a hard seed length `k`, and `n` the largest number with
  -- `n ^ m ≤ k`, so that `n ^ m ≤ k ≤ (2 n) ^ m`.
  --
  set m := ⌈2 / ε⌉₊ with hm_def
  have hm2 : (2 : ℝ) ≤ m * ε := by
    have := Nat.le_ceil (2 / ε)
    rw [div_le_iff₀ hε] at this
    linarith
  have hm1 : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · rw [h] at hm2
      simp at hm2
      linarith
    · exact h
  set d := 2 + m + m * cG with hd
  obtain ⟨N, hN⟩ := huse (d + 1)
  set K := a + d + b + 4 with hK
  obtain ⟨D2, hD2⟩ : ∃ D2 : ℕ, 2 ^ d = D2 := ⟨_, rfl⟩
  set L := n₁ + n₂ + N + (2 * cG + 6) + D2 + K + 1 with hL
  obtain ⟨k, hkL, hH⟩ := hH (L ^ m)
  set n := Nat.findGreatest (fun n => n ^ m ≤ k) k with hn_def
  have hLk : L ≤ k := (Nat.le_self_pow (by omega) L).trans hkL
  have hLn : L ≤ n := Nat.le_findGreatest hLk hkL
  have hnm : n ^ m ≤ k := Nat.findGreatest_spec (P := fun n => n ^ m ≤ k) hLk hkL
  have hkn : k ≤ (2 * n) ^ m := by
    have h1 : k < (n + 1) ^ m := by
      by_cases h : n + 1 ≤ k
      · exact Nat.lt_of_not_le
          (Nat.findGreatest_is_greatest (P := fun n => n ^ m ≤ k) (Nat.lt_succ_self n) h)
      · have : n + 1 ≤ (n + 1) ^ m := Nat.le_self_pow (Nat.one_le_iff_ne_zero.mp hm1) _
        omega
    have h2 : (n + 1) ^ m ≤ (2 * n) ^ m := Nat.pow_le_pow_left (by omega) m
    omega
  have hnpos : 0 < n := by omega
  have hk : 0 < k := by omega
  set B := k ^ cG + cG with hB_def
  have hB : ∀ j, (gc k j).size ≤ B := hgcs k
  -- The functions `prf G k n s` have circuits of size `n ^ (d + 1)`.
  --
  have hQ : n * (2 * k * B + 4 * k) ≤ n ^ (d + 1) := by
    set w := 2 * n with hw_def
    have hw : 2 * cG + 6 ≤ w := by omega
    have hP : 1 ≤ w ^ (m * cG) := Nat.one_le_pow _ _ (by omega)
    have hB' : B ≤ w ^ (m * cG) + cG := by
      rw [hB_def, pow_mul]
      exact Nat.add_le_add_right (Nat.pow_le_pow_left hkn cG) _
    have hnw : n ≤ w := by omega
    have h2d : 2 ^ d ≤ n := by
      rw [hD2]
      omega
    calc n * (2 * k * B + 4 * k) ≤ w * (2 * w ^ m * (w ^ (m * cG) + cG) + 4 * w ^ m) :=
          Nat.mul_le_mul hnw (Nat.add_le_add
            (Nat.mul_le_mul (Nat.mul_le_mul_left 2 hkn) hB') (Nat.mul_le_mul_left 4 hkn))
      _ = w * w ^ m * (2 * w ^ (m * cG) + 2 * cG + 4) := by ring
      _ ≤ w * w ^ m * (w ^ (m * cG) * (2 * cG + 6)) := by
          gcongr
          nlinarith
      _ ≤ w * w ^ m * (w ^ (m * cG) * w) := by gcongr
      _ = 2 ^ d * n ^ d := by
          rw [hd, hw_def, mul_pow]
          ring
      _ ≤ n * n ^ d := Nat.mul_le_mul_right _ h2d
      _ = n ^ (d + 1) := by ring
  have hprf : ∀ s, prf G k n s ∉ C' n := by
    intro s hs
    have h1 := hN n (by omega) (prf G k n s) (hsub n hs) (prfC gc hk n s)
      (prfC_eval G gc hgce hk n s)
    have h2 := prfC_size gc hB hk n s
    omega
  -- The test `D` from constructivity.
  --
  obtain ⟨D, hDsize, hD⟩ := hcons n (by omega)
  let T : BoolFn n → Bool := fun f => D.eval f
  have hTprf : ∀ s, T (prf G k n s) = false := by
    intro s
    cases h : D.eval (prf G k n s)
    · exact h
    · exact absurd ((hD _).mp h) (hprf s)
  have hT0 : prob (fun s => T (prf G k n s)) = 0 := by
    simp [prob, hTprf, ind]
  have hT1 : (1 : ℝ) / 2 ^ (b * n) ≤ prob T := by
    classical
    rw [prob_eq_card_filter]
    have hfilt : univ.filter (fun f => T f = true) = univ.filter (fun f => f ∈ C' n) := by
      ext f
      simp [T, hD f]
    rw [hfilt]
    have hl := hlarge n (by omega)
    have hcard : Fintype.card (BoolFn n) = 2 ^ (2 ^ n) := by simp
    rw [hcard, div_le_div_iff₀ (by positivity) (by positivity), one_mul]
    have : 2 ^ (2 ^ n) ≤ (univ.filter (fun f : BoolFn n => f ∈ C' n)).card * 2 ^ (b * n) := by
      convert hl
    exact_mod_cast this
  -- The hybrid argument.
  --
  obtain ⟨i, hi, e, c, hlev⟩ := level_hybrid G hk n hnpos T
  set Dc := distC gc hk i e c D
  have hu : prob (fun u : Bits k => T (hybF G (i + 1) (expand (Function.update c e (G k u))))) =
      prob (fun u : Fin k → Bool => Dc.eval (G k u)) := by
    congr 1
    funext u
    rw [distC_eval G gc hgce]
  have hy : prob (fun y : Fin (2 * k) → Bool => T (hybF G (i + 1) (expand (Function.update c e y)))) =
      prob (fun y : Fin (2 * k) → Bool => Dc.eval y) := by
    congr 1
    funext y
    rw [distC_eval G gc hgce]
  rw [hu, hy, hT0, zero_sub, abs_neg, abs_of_nonneg (by simp only [prob, ind]; positivity)]
    at hlev
  -- Size of the distinguisher.
  --
  have hsize : Dc.size ≤ 2 ^ (K * n) := by
    have h0 := distC_size gc hB hk i e c D
    have x1 : n + n * (d + 1) ≤ (a + d + 2) * n :=
      calc n + n * (d + 1) = (d + 2) * n := by ring
        _ ≤ (a + d + 2) * n := Nat.mul_le_mul_right n (by omega)
    have x2 : a * n ≤ (a + d + 2) * n := Nat.mul_le_mul_right n (by omega)
    have x3 : (a + d + 2) * n + 1 ≤ K * n :=
      calc (a + d + 2) * n + 1 ≤ (a + d + 2) * n + n := by omega
        _ = (a + d + 3) * n := by ring
        _ ≤ K * n := Nat.mul_le_mul_right n (by omega)
    have e1 : 2 ^ n * n ^ (d + 1) ≤ 2 ^ ((a + d + 2) * n) :=
      calc 2 ^ n * n ^ (d + 1) ≤ 2 ^ n * (2 ^ n) ^ (d + 1) :=
            Nat.mul_le_mul_left _ (Nat.pow_le_pow_left Nat.lt_two_pow_self.le (d + 1))
        _ = 2 ^ (n + n * (d + 1)) := by rw [← pow_mul, ← pow_add]
        _ ≤ 2 ^ ((a + d + 2) * n) := Nat.pow_le_pow_right (by norm_num) x1
    have e2 : 2 ^ (a * n) ≤ 2 ^ ((a + d + 2) * n) := Nat.pow_le_pow_right (by norm_num) x2
    have e3 : 2 ^ ((a + d + 2) * n) * 2 ≤ 2 ^ (K * n) := by
      rw [← pow_succ]
      exact Nat.pow_le_pow_right (by norm_num) x3
    have e4 : 2 ^ n * (n * (2 * k * B + 4 * k)) ≤ 2 ^ n * n ^ (d + 1) :=
      Nat.mul_le_mul_left _ hQ
    calc Dc.size ≤ 2 ^ n * (n * (2 * k * B + 4 * k)) + D.size := h0
      _ ≤ 2 ^ n * n ^ (d + 1) + 2 ^ (a * n) := Nat.add_le_add e4 hDsize
      _ ≤ 2 ^ ((a + d + 2) * n) + 2 ^ ((a + d + 2) * n) := Nat.add_le_add e1 e2
      _ = 2 ^ ((a + d + 2) * n) * 2 := by ring
      _ ≤ 2 ^ (K * n) := e3
  -- Advantage of the distinguisher.
  --
  have hadv : (1 : ℝ) / 2 ^ (K * n) ≤
      |prob (fun u : Fin k → Bool => Dc.eval (G k u)) - prob (fun y => Dc.eval y)| := by
    have hden : (n : ℝ) * 2 ^ i ≤ 2 ^ (2 * n) := by
      have h1 : (n : ℝ) ≤ 2 ^ n := by exact_mod_cast Nat.lt_two_pow_self.le
      have h2 : (2 : ℝ) ^ i ≤ 2 ^ n := pow_le_pow_right₀ (by norm_num) hi.le
      calc (n : ℝ) * 2 ^ i ≤ 2 ^ n * 2 ^ n := by gcongr
        _ = 2 ^ (2 * n) := by ring
    have hpos : (0 : ℝ) < n * 2 ^ i := by positivity
    have hTb : 1 ≤ prob T * 2 ^ (b * n) := by
      rw [div_le_iff₀ (by positivity)] at hT1
      exact hT1
    calc (1 : ℝ) / 2 ^ (K * n) ≤ 1 / (2 ^ (b * n) * 2 ^ (2 * n)) := by
          apply one_div_le_one_div_of_le (by positivity)
          rw [← pow_add]
          have hbK : b * n + 2 * n ≤ K * n :=
            calc b * n + 2 * n = (b + 2) * n := by ring
              _ ≤ K * n := Nat.mul_le_mul_right n (by omega)
          exact pow_le_pow_right₀ (by norm_num) hbK
      _ ≤ prob T / (n * 2 ^ i) := by
          rw [div_le_div_iff₀ (by positivity) hpos, one_mul]
          calc (n : ℝ) * 2 ^ i ≤ 2 ^ (2 * n) := hden
            _ = 1 * 2 ^ (2 * n) := (one_mul _).symm
            _ ≤ (prob T * 2 ^ (b * n)) * 2 ^ (2 * n) :=
                mul_le_mul_of_nonneg_right hTb (by positivity)
            _ = prob T * (2 ^ (b * n) * 2 ^ (2 * n)) := by ring
      _ ≤ _ := hlev
  -- Hardness.
  --
  have hard := hH (2 ^ (K * n)) Dc (by positivity) hsize (by
    have := hadv
    simp only [prob_eq_card_filter, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin,
      Nat.cast_pow, Nat.cast_ofNat] at this
    simpa using this)
  have hexp : (k : ℝ) ^ ε ≤ ((K * n : ℕ) : ℝ) := by
    have hard' : (2 : ℝ) ^ ((k : ℝ) ^ ε) ≤ (2 : ℝ) ^ (((K * n : ℕ)) : ℝ) := by
      rw [Real.rpow_natCast]
      exact_mod_cast hard
    exact (Real.rpow_le_rpow_left_iff (by norm_num : (1 : ℝ) < 2)).mp hard'
  have hkε : (n : ℝ) ^ 2 ≤ (k : ℝ) ^ ε := by
    calc (n : ℝ) ^ 2 = (n : ℝ) ^ (2 : ℝ) := by norm_cast
      _ ≤ (n : ℝ) ^ ((m : ℝ) * ε) :=
          Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hnpos) hm2
      _ = ((n : ℝ) ^ m) ^ ε := by rw [Real.rpow_mul (by positivity), Real.rpow_natCast]
      _ ≤ (k : ℝ) ^ ε :=
          Real.rpow_le_rpow (by positivity) (by exact_mod_cast hnm) hε.le
  have hfin : (n : ℝ) * n ≤ K * n := by
    have := hkε.trans hexp
    push_cast at this
    nlinarith
  have hnK : (n : ℝ) ≤ K := le_of_mul_le_mul_right hfin (by exact_mod_cast hnpos)
  have : n ≤ K := by exact_mod_cast hnK
  omega
end NaturalProofs
