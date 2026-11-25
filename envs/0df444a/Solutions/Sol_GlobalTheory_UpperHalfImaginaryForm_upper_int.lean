-- Prove2me | solution 1 for GlobalTheory.UpperHalfImaginaryForm.upper_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:29:29.170155+00:00
-- url     : https://prove2.me/submissions/c0e63b73-c31c-48ce-9e53-fb4d95f933a3

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsTranslateJetNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusSplitting_CoeffEqZeroOfOrthonormal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsImEqLattice
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_DifferentiableFderivApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ImFormApply
import Theorems.Thm_GlobalTheory_UpperHalfImaginaryForm_imForm_apply
import Theorems.Thm_GlobalTheory_UpperHalfImaginaryForm_upper_basis
import Theorems.Thm_GlobalTheory_ThetaGauss_transl_apply
import Theorems.Thm_GlobalTheory_constDerivEval_X
import Theorems.Thm_GlobalTheory_lineDerivList_nil
import Theorems.Thm_GlobalTheory_lineDerivList_zero
import Theorems.Thm_GlobalTheory_orthogonalQuotientForm_mk
import Theorems.Thm_GlobalTheory_pderivEval_X
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.ThetaGauss.transl_apply
attribute [local simp] GlobalTheory.constDerivEval_X
attribute [local simp] GlobalTheory.lineDerivList_nil
attribute [local simp] GlobalTheory.lineDerivList_zero
attribute [local simp] GlobalTheory.orthogonalQuotientForm_mk
attribute [local simp] GlobalTheory.pderivEval_X



set_option autoImplicit false
open GlobalTheory GlobalTheory.UpperHalfImaginaryForm
open ReciprocityTheory.ChartRestriction.G.I2
noncomputable section
variable {ι : Type} [Fintype ι]
variable {n : ℕ}
namespace GlobalTheory.UpperHalfImaginaryForm
theorem _root_.solution (b : Module.Basis (Fin n) ℝ (EuclideanSpace ℂ ι))
    (hint : ∀ x y : EuclideanSpace ℂ ι, x ∈ lat b → y ∈ lat b → ∃ k : ℤ, (Hf x y).im = k)
    {x y : EuclideanSpace ℂ ι} (hx : x ∈ lat b) (hy : y ∈ lat b) :
    ∃ k : ℤ, upper b x y = k := by
  have base : ∀ i j, ∃ k : ℤ, upper b (b i) (b j) = k := by
    intro i j
    rw [upper_basis]
    split_ifs
    · rw [imForm_apply]
      exact hint _ _ (Submodule.subset_span ⟨i, rfl⟩) (Submodule.subset_span ⟨j, rfl⟩)
    · exact ⟨0, by simp⟩
  have hrow : ∀ i, ∃ k : ℤ, upper b (b i) y = k := by
    intro i
    induction hy using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨j, rfl⟩ := hz
      exact base i j
    | zero => exact ⟨0, by simp⟩
    | add z w _ _ hz hw =>
      obtain ⟨k₁, h₁⟩ := hz
      obtain ⟨k₂, h₂⟩ := hw
      exact ⟨k₁ + k₂, by simp [map_add, h₁, h₂]⟩
    | smul n z _ hz =>
      obtain ⟨k₁, h₁⟩ := hz
      exact ⟨n * k₁, by simp [map_zsmul, h₁, zsmul_eq_mul]⟩
  induction hx using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨i, rfl⟩ := hz
    exact hrow i
  | zero => exact ⟨0, by simp⟩
  | add z w _ _ hz hw =>
    obtain ⟨k₁, h₁⟩ := hz
    obtain ⟨k₂, h₂⟩ := hw
    exact ⟨k₁ + k₂, by simp [map_add, LinearMap.add_apply, h₁, h₂]⟩
  | smul n z _ hz =>
    obtain ⟨k₁, h₁⟩ := hz
    exact ⟨n * k₁, by simp [map_zsmul, LinearMap.smul_apply, h₁, zsmul_eq_mul]⟩
end GlobalTheory.UpperHalfImaginaryForm
