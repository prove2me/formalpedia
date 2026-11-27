-- Prove2me | solution 1 for LinearChoresCLS.encoded_scaled_price_ratios
-- status  : ACCEPTED   (disprove)
-- author  : @Shuze Chen
-- created : 2026-11-27T00:45:29.055797+00:00
-- url     : https://prove2.me/submissions/786ee7ad-eaae-4f15-9d85-b94ed1451833

import Mathlib
import Definitions.Def_LinearChoresCLS_PriceFamily
import Definitions.Def_LinearChoresCLS_ChoresSearch

set_option autoImplicit false

namespace DisproofScaled
open CookPvsNP

section tm
variable {Γ : Type} (M : TM Γ)

theorem step_tape_len (c : Cfg Γ M.Q) :
    (M.step c).left.length + (M.step c).right.length ≤ c.left.length + c.right.length + 1 := by
  unfold TM.step
  split
  · exact Nat.le_add_right _ _
  · obtain ⟨q', s', h⟩ := M.δ c.state c.head
    cases h with
    | right =>
        simp only [List.length_cons, List.length_tail]
        cases c.right with
        | nil => simp
        | cons b r => simp; omega
    | left =>
        cases c.left with
        | nil => simp
        | cons a x' => simp; omega

theorem run_tape_len (n : ℕ) (c : Cfg Γ M.Q) :
    (M.run n c).left.length + (M.run n c).right.length ≤ n + c.left.length + c.right.length := by
  induction n generalizing c with
  | zero => simp [TM.run]
  | succ n ih =>
      have hrun : M.run (Nat.succ n) c = M.step (M.run n c) := by
        show M.step^[Nat.succ n] c = M.step (M.step^[n] c)
        exact Function.iterate_succ_apply' M.step n c
      rw [hrun]
      have hstep := step_tape_len M (M.run n c)
      have ih' := ih c
      omega

theorem output_length_le (n : ℕ) (w : List Γ) :
    (M.output (M.run n (M.init w))).length ≤ n + w.length + 1 := by
  have hdrop : ∀ c : Cfg Γ M.Q, ((c.head :: c.right).reverse.dropWhile Option.isNone).length
      ≤ 1 + c.right.length := by
    intro c
    have h := List.length_dropWhile_le Option.isNone (c.head :: c.right).reverse
    have h' : (c.head :: c.right).reverse.length = c.right.length + 1 := by
      simp only [List.length_reverse, List.length_cons]
    omega
  have hout : ∀ c : Cfg Γ M.Q, (M.output c).length ≤ 1 + c.right.length := by
    intro c
    have h2 := hdrop c
    simpa [TM.output, add_comm] using h2
  have hinit : (M.init w).left.length + (M.init w).right.length ≤ w.length := by
    simp [TM.init]
  have hrun := run_tape_len M n (M.init w)
  have hc := hout (M.run n (M.init w))
  omega

end tm

theorem polytime_len_le {A B : Type} {f : List A → List B} (hf : PolyTimeComputable f) :
    ∃ k : ℕ, ∀ x, (f x).length ≤ x.length ^ k + k + x.length + 1 := by
  obtain ⟨Γ, _, ι₁, ι₂, M, k, hM⟩ := hf
  refine ⟨k, fun x => ?_⟩
  have h := (hM x).2
  have hl := output_length_le M (x.length ^ k + k) (x.map ι₁)
  rw [h] at hl
  simpa using hl

end DisproofScaled

namespace DisproofScaled
open Filter Topology

theorem exp_beats_poly (k c : ℕ) : ∃ N : ℕ, (2 * N + c) ^ k + k + 2 * N + c < 2 ^ N := by
  set A : ℕ := (c + k + 3) ^ (k + 1)
  have hT := tendsto_pow_const_div_const_pow_of_one_lt (k + 1) (by norm_num : (1 : ℝ) < 2)
  have hA : (0 : ℝ) < 1 / ((A : ℝ) + 1) := by positivity
  obtain ⟨N, hN1, hN⟩ := ((eventually_ge_atTop 1).and (hT.eventually (gt_mem_nhds hA))).exists
  refine ⟨N, ?_⟩
  -- polynomial bound
  have hP : (2 * N + c) ^ k + k + 2 * N + c ≤ A * N ^ (k + 1) := by
    have h1 : 2 * N + c + k + 1 ≤ (c + k + 3) * N := by nlinarith
    have h2 : (2 * N + c) ^ k + k + 2 * N + c ≤ (2 * N + c + k + 1) ^ (k + 1) := by
      have e1 : (2 * N + c) ^ k ≤ (2 * N + c + k + 1) ^ k := Nat.pow_le_pow_left (by omega) k
      have e2 : (2 * N + c + k + 1) ^ (k + 1) = (2 * N + c + k + 1) ^ k * (2 * N + c + k + 1) := by
        rw [pow_succ]
      have e3 : 1 ≤ (2 * N + c + k + 1) ^ k := Nat.one_le_pow _ _ (by omega)
      rw [e2]; nlinarith
    calc (2 * N + c) ^ k + k + 2 * N + c ≤ (2 * N + c + k + 1) ^ (k + 1) := h2
      _ ≤ ((c + k + 3) * N) ^ (k + 1) := Nat.pow_le_pow_left h1 _
      _ = A * N ^ (k + 1) := by rw [mul_pow]
  have hreal : (A : ℝ) * (N : ℝ) ^ (k + 1) < (2 : ℝ) ^ N := by
    have h2pos : (0 : ℝ) < 2 ^ N := by positivity
    have := hN
    rw [div_lt_div_iff₀ h2pos (by positivity)] at this
    have hNk : (0 : ℝ) ≤ (N : ℝ) ^ (k + 1) := by positivity
    nlinarith
  have : A * N ^ (k + 1) < 2 ^ N := by exact_mod_cast hreal
  omega

end DisproofScaled

namespace DisproofScaled
open NetworkEquilibriumCLS.LinearNash LinearChoresCLS

theorem len_encNat (n : ℕ) : (encNat n).length = 2 * Nat.size n + 1 := by
  simp [encNat, Nat.size_eq_bits_len]; omega

theorem disproof : ¬ (∃ h : List (Option (Bool ⊕ Bool)) → List Bool, PolyTime h ∧
      ∀ {n a m : ℕ} (L : ℕ) (b : Fin (n+1) → Fin m),
        (∀ j, (b j).val = j.val) →
        ∀ (p : Fin m → ℚ) (z : Fin a → Fin m → ℚ), 0 < p (b 0) →
        encVector (fun i : Fin n =>
          (1 / ((1/2 : ℚ)^L)) * (p (b i.succ) / p (b 0) - 1)) =
        h (pairCode (encNat n ++ encNat L) (encCE p z))) := by
  rintro ⟨h, hpoly, hspec⟩
  obtain ⟨k, hk⟩ := polytime_len_le hpoly
  set p : Fin 2 → ℚ := ![1, 2]
  set z : Fin 0 → Fin 2 → ℚ := fun i => i.elim0
  set C0 := (encCE p z).length
  obtain ⟨N, hN⟩ := exp_beats_poly k (C0 + 7)
  set L := 2 ^ N
  have hs := hspec (n := 1) (a := 0) (m := 2) L id (fun j => rfl) p z (by simp [p])
  -- the left-hand side is long
  have hval : (fun i : Fin 1 => (1 / ((1/2 : ℚ)^L)) * (p (id i.succ) / p (id 0) - 1)) =
      fun _ => (2 : ℚ) ^ L := by
    funext i; fin_cases i; simp [p]; norm_num
  rw [hval] at hs
  have hlhs : L + 1 ≤ (encVector (fun _ : Fin 1 => (2 : ℚ) ^ L)).length := by
    have : ((2 : ℚ) ^ L).num = ((2 : ℤ) ^ L) := by
      rw [show ((2 : ℚ) ^ L) = (((2 : ℤ) ^ L : ℤ) : ℚ) by push_cast; rfl, Rat.num_intCast]
    simp only [encVector, encList, List.ofFn_succ, List.ofFn_zero, List.flatMap_cons,
      List.flatMap_nil, List.append_nil, encRat, encInt, this, List.length_append, List.length_cons,
      len_encNat]
    have : Nat.size (((2 : ℤ) ^ L).natAbs) = L + 1 := by
      rw [Int.natAbs_pow]; simp [Nat.size_pow]
    omega
  -- the input is short
  have hin : (pairCode (encNat 1 ++ encNat L) (encCE p z)).length = 2 * Nat.size L + 5 + C0 := by
    simp [pairCode, len_encNat]; omega
  have hsizeL : Nat.size L = N + 1 := by simp [L, Nat.size_pow]
  have hk' := hk (pairCode (encNat 1 ++ encNat L) (encCE p z))
  rw [← hs, hin, hsizeL] at hk'
  have := hlhs.trans hk'
  have e : 2 * (N + 1) + 5 + C0 = 2 * N + (C0 + 7) := by ring
  rw [e] at this
  omega

end DisproofScaled

open NetworkEquilibriumCLS.LinearNash LinearChoresCLS

theorem solution : ¬ (∃ h : List (Option (Bool ⊕ Bool)) → List Bool, PolyTime h ∧
      ∀ {n a m : ℕ} (L : ℕ) (b : Fin (n+1) → Fin m),
        (∀ j, (b j).val = j.val) →
        ∀ (p : Fin m → ℚ) (z : Fin a → Fin m → ℚ), 0 < p (b 0) →
        encVector (fun i : Fin n =>
          (1 / ((1/2 : ℚ)^L)) * (p (b i.succ) / p (b 0) - 1)) =
        h (pairCode (encNat n ++ encNat L) (encCE p z))) :=
  DisproofScaled.disproof
