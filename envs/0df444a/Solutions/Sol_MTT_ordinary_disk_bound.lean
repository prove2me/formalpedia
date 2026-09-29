-- Prove2me | solution 1 for MTT.ordinary_disk_bound
-- status  : ACCEPTED   (prove)
-- author  : @allychan327
-- created : 2026-09-06T03:39:47.235034+00:00
-- url     : https://prove2.me/submissions/d47bf546-e352-45dc-8eee-d41739abc085

import Mathlib
import Definitions.Def_MTT_Measures

set_option autoImplicit false
noncomputable section
open Finset MTT

namespace MTTMass

variable {p : ℕ} [Fact p.Prime]

/-- A finitely generated `ℤ`-submodule of `Qbar` has uniformly bounded image in `ℂ_[p]`. -/
theorem fg_norm_bound (ιp : Qbar →+* ℂ_[p]) (S : Set Qbar)
    (hS : (Submodule.span ℤ S).FG) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x ∈ S, ‖ιp x‖ ≤ B := by
  obtain ⟨T, hT⟩ := hS
  refine ⟨∑ t ∈ T, ‖ιp t‖, Finset.sum_nonneg fun t _ => norm_nonneg _, ?_⟩
  have key : ∀ x ∈ Submodule.span ℤ (↑T : Set Qbar), ‖ιp x‖ ≤ ∑ t ∈ T, ‖ιp t‖ := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
        exact Finset.single_le_sum (f := fun t => ‖ιp t‖)
          (fun t _ => norm_nonneg _) (by simpa using hy)
    | zero => simpa using Finset.sum_nonneg fun t _ => norm_nonneg _
    | add y z _ _ hy hz =>
        refine le_trans ?_ (max_le hy hz)
        simpa using IsUltrametricDist.norm_add_le_max (ιp y) (ιp z)
    | smul c y _ hy =>
        have hc : ιp (c • y) = (c : ℂ_[p]) * ιp y := by rw [zsmul_eq_mul, map_mul, map_intCast]
        rw [hc, norm_mul]
        calc ‖(c : ℂ_[p])‖ * ‖ιp y‖ ≤ 1 * ‖ιp y‖ :=
              mul_le_mul_of_nonneg_right
                (IsUltrametricDist.norm_intCast_le_one _ c) (norm_nonneg _)
          _ = ‖ιp y‖ := one_mul _
          _ ≤ _ := hy
  intro x hx
  exact key x (hT ▸ Submodule.subset_span hx)

/-- In degree zero the algebraic symbol is a single normalized value. -/
theorem algebraicSymbol_zero {k : ℕ} {ι : Qbar →+* ℂ} {f : UpperHalfPlane → ℂ}
    (P : Periods k ι f) (s : Bool) (a m : ℚ) :
    algebraicSymbol P s 0 a m = P.value s 0 (-a / m) := by
  simp [algebraicSymbol]

end MTTMass

open MTTMass in
theorem solution {p N k : ℕ} [Fact p.Prime] (hN : 0 < N) (hk : 2 ≤ k)
    (ι : Qbar →+* ℂ) (ιp : Qbar →+* ℂ_[p]) (f : Eigenform N k ι)
    (P : Periods k ι f.form) (α : ℂ_[p]) (hα : IsOrdinaryRoot f ιp α) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (s : Bool) (n : ℕ), 0 < n → ∀ (a : ℤ),
      ‖diskMoment f ιp P α s 0 n a‖ ≤ C := by
  classical
  obtain ⟨B, hB0, hB⟩ := fg_norm_bound ιp _ P.lattice_fg
  set E : ℝ := ‖ιp (f.epsilon (p : ZMod N))‖ with hE
  have hE0 : 0 ≤ E := norm_nonneg _
  refine ⟨B + E * B, by positivity, ?_⟩
  intro s n _ a
  have hk2 : 0 ≤ k - 2 := Nat.zero_le _
  have hval1 : ‖ιp (P.value s 0 (-(a : ℚ) / (p : ℚ) ^ n))‖ ≤ B := hB _ ⟨s, 0, _, hk2, rfl⟩
  have hval2 : ‖ιp (P.value s 0 (-(a : ℚ) / (p : ℚ) ^ (n - 1)))‖ ≤ B := hB _ ⟨s, 0, _, hk2, rfl⟩
  have hd : diskMoment f ιp P α s 0 n a
      = (α ^ n)⁻¹ * ιp (P.value s 0 (-(a : ℚ) / (p : ℚ) ^ n))
        - ιp (f.epsilon (p : ZMod N)) * (p : ℂ_[p]) ^ (k - 2) / α ^ (n + 1) *
            ιp (P.value s 0 (-(a : ℚ) / (p : ℚ) ^ (n - 1))) := by
    simp only [diskMoment, algebraicSymbol_zero]
  rw [hd]
  set q : ℝ := ‖(p : ℂ_[p])‖ with hq
  have hq0 : 0 ≤ q := norm_nonneg _
  have hq1 : q ≤ 1 := IsUltrametricDist.norm_natCast_le_one _ p
  have hαn : ‖(α ^ n)⁻¹‖ = 1 := by rw [norm_inv, norm_pow, hα.1, one_pow, inv_one]
  have hαn1 : ‖α ^ (n + 1)‖ = 1 := by rw [norm_pow, hα.1, one_pow]
  have t1 : ‖(α ^ n)⁻¹ * ιp (P.value s 0 (-(a : ℚ) / (p : ℚ) ^ n))‖ ≤ B := by
    rw [norm_mul, hαn, one_mul]; exact hval1
  have t2 : ‖ιp (f.epsilon (p : ZMod N)) * (p : ℂ_[p]) ^ (k - 2) / α ^ (n + 1) *
      ιp (P.value s 0 (-(a : ℚ) / (p : ℚ) ^ (n - 1)))‖ ≤ E * B := by
    rw [norm_mul, norm_div, norm_mul, hαn1, div_one, norm_pow, ← hE]
    calc E * q ^ (k - 2) * ‖ιp (P.value s 0 (-(a : ℚ) / (p : ℚ) ^ (n - 1)))‖
        ≤ E * 1 * B := by
          refine mul_le_mul (mul_le_mul_of_nonneg_left (pow_le_one₀ hq0 hq1) hE0) hval2
            (norm_nonneg _) (by positivity)
      _ = E * B := by ring
  calc ‖(α ^ n)⁻¹ * ιp (P.value s 0 (-(a : ℚ) / (p : ℚ) ^ n))
        - ιp (f.epsilon (p : ZMod N)) * (p : ℂ_[p]) ^ (k - 2) / α ^ (n + 1) *
            ιp (P.value s 0 (-(a : ℚ) / (p : ℚ) ^ (n - 1)))‖
      ≤ _ + _ := norm_sub_le _ _
    _ ≤ B + E * B := add_le_add t1 t2
