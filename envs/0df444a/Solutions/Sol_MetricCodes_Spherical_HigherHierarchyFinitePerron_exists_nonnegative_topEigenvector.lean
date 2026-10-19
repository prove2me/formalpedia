-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchyFinitePerron.exists_nonnegative_topEigenvector
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:42.304385+00:00
-- url     : https://prove2.me/submissions/48d29ec6-9f4a-4919-a644-d5d4bc2ec537

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchyFinitePerron_rayleigh_le_top
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchyFinitePerron_operator_isSymmetric
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchyFinitePerron_exists_topEigenvector
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchyFinitePerron_coordinateAbs_ne_zero
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchyFinitePerron_rayleigh_eq_of_eigenvector
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchyFinitePerron_rayleigh_le_coordinateAbs

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unnecessarySimpa false
set_option autoImplicit false
open MetricCodes
open MetricCodes.Spherical
noncomputable section
set_option autoImplicit false
open Metric
open scoped BigOperators InnerProductSpace Matrix
open MetricCodes.Spherical.HigherHierarchyFinitePerron
variable {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
namespace MetricCodes.Spherical.HigherHierarchyFinitePerron
theorem _root_.solution (A : Matrix I I ℝ)
    (hsymm : Aᵀ = A) (hnonneg : ∀ i j : I, 0 ≤ A i j) :
    ∃ x : Space I, x ≠ 0 ∧
      operator A x = topEigenvalue A • x ∧ ∀ i : I, 0 ≤ x i := by
  obtain ⟨x, hx, heig⟩ := exists_topEigenvector A hsymm
  let y : Space I := coordinateAbs x
  have hy : y ≠ 0 := coordinateAbs_ne_zero hx
  have hbelow := rayleigh_le_coordinateAbs A hnonneg x
  have habove := rayleigh_le_top A y hy
  have hxray := rayleigh_eq_of_eigenvector A x hx (topEigenvalue A) heig
  rw [hxray] at hbelow
  have hyray : rayleigh A y = topEigenvalue A :=
    le_antisymm habove hbelow
  have hself : IsSelfAdjoint (continuousOperator A) :=
    (operator_isSymmetric A hsymm).isSelfAdjoint
  have hmax :
      IsMaxOn (continuousOperator A).reApplyInnerSelf
        (sphere (0 : Space I) ‖y‖) y := by
    intro z hz
    have hnorm : ‖z‖ = ‖y‖ := by simpa using hz
    have hznonzero : z ≠ 0 := by
      intro hzzero
      rw [hzzero, norm_zero] at hnorm
      exact hy (norm_eq_zero.mp hnorm.symm)
    have hray := rayleigh_le_top A z hznonzero
    rw [← hyray] at hray
    change
      (continuousOperator A).reApplyInnerSelf z / ‖z‖ ^ 2 ≤
        (continuousOperator A).reApplyInnerSelf y / ‖y‖ ^ 2 at hray
    rw [hnorm] at hray
    exact (div_le_div_iff_of_pos_right
      (sq_pos_of_pos (norm_pos_iff.mpr hy))).mp hray
  have heigy := hself.hasEigenvector_of_isMaxOn hy hmax
  refine ⟨y, hy, ?_, fun i => abs_nonneg (x i)⟩
  have happly := heigy.apply_eq_smul
  simpa [topEigenvalue, rayleigh, continuousOperator] using happly
end MetricCodes.Spherical.HigherHierarchyFinitePerron
