-- Prove2me | solution 1 for Matrix.l2_opNorm_le_sqrt_of_row_col_sums
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T00:51:58.874575+00:00
-- url     : https://prove2.me/submissions/ac965edd-a2ef-4fe7-9c80-d194fef3d0d1

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_SchurCore
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_SchurTest
public import Theorems.Thm_Lean4LPD_l2_opNorm_le_schur


set_option autoImplicit true
@[expose] public section
public section
open scoped Matrix Matrix.Norms.L2Operator
open Matrix
variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n] {C : ℝ}
namespace Matrix
theorem _root_.solution (R : Matrix m n ℝ) (hR : ∀ i j, 0 ≤ R i j) {a b : ℝ}
    (hrow : ∀ i, ∑ j, R i j ≤ a) (hcol : ∀ j, ∑ i, R i j ≤ b) :
    ‖R‖ ≤ Real.sqrt (a * b) := by
  -- If either index type is empty then `R` vanishes and the bound is trivial; otherwise a
  -- single row and a single column witness `0 ≤ a` and `0 ≤ b`.
  rcases isEmpty_or_nonempty m with hm | hm
  · simp [Subsingleton.elim R 0]
  rcases isEmpty_or_nonempty n with hn | hn
  · simp [Subsingleton.elim R 0]
  obtain ⟨i₀⟩ := hm
  obtain ⟨j₀⟩ := hn
  have ha : 0 ≤ a := (Finset.sum_nonneg fun j _ ↦ hR i₀ j).trans (hrow i₀)
  have hb : 0 ≤ b := (Finset.sum_nonneg fun i _ ↦ hR i j₀).trans (hcol j₀)
  apply Lean4LPD.l2_opNorm_le_schur R ha hb
  · simpa only [Real.norm_eq_abs, abs_of_nonneg (hR _ _)] using hrow
  · simpa only [Real.norm_eq_abs, abs_of_nonneg (hR _ _)] using hcol
end Matrix
