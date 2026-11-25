-- Prove2me | solution 1 for GlobalTheory.UpperHalfImaginaryForm.exists_coc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:06:28.998953+00:00
-- url     : https://prove2.me/submissions/9ad468fe-dbb8-4bb1-be59-4a112d12206c

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsTranslateJetNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusSplitting_CoeffEqZeroOfOrthonormal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsImEqLattice
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_DifferentiableFderivApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ImFormApply
import Theorems.Thm_GlobalTheory_UpperHalfImaginaryForm_imForm_apply
import Theorems.Thm_GlobalTheory_UpperHalfImaginaryForm_upper_sub
import Theorems.Thm_GlobalTheory_UpperHalfImaginaryForm_upper_int
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
theorem _root_.solution {ι : Type} [Fintype ι]
    (b : Module.Basis (Fin (2 * Fintype.card ι)) ℝ (EuclideanSpace ℂ ι))
    (hint : ∀ x y : EuclideanSpace ℂ ι, x ∈ lat b → y ∈ lat b → ∃ k : ℤ, (Hf x y).im = k)
    (hperf : ∀ φ : lat b →+ ℤ, ∃ x ∈ lat b, ∀ y : lat b,
      (φ y : ℝ) = (Hf x (y : EuclideanSpace ℂ ι)).im) :
    ∃ Y : GT ι, Y.b = b ∧ FPw.Coc Y 1 := by
  refine ⟨⟨b, hint, hperf, fun x => Complex.exp (((Real.pi * upper b x x : ℝ) : ℂ) * Complex.I),
    fun x _ => Complex.norm_exp_ofReal_mul_I _⟩, rfl, ?_⟩
  intro γ hγ γ' hγ'
  obtain ⟨k, hk⟩ := upper_int b hint hγ hγ'
  have him : (Hf γ γ').im = upper b γ γ' - upper b γ' γ := by
    rw [← imForm_apply]
    exact upper_sub b γ γ'
  have hadd : upper b (γ + γ') (γ + γ') =
      upper b γ γ + upper b γ γ' + upper b γ' γ + upper b γ' γ' := by
    simp only [map_add, LinearMap.add_apply]
    ring
  dsimp only
  rw [← Complex.exp_add, ← Complex.exp_add, Complex.exp_eq_exp_iff_exists_int]
  refine ⟨k, ?_⟩
  rw [hadd, him, hk]
  push_cast
  ring
end GlobalTheory.UpperHalfImaginaryForm
