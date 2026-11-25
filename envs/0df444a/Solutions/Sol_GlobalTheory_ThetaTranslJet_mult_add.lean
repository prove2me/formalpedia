-- Prove2me | solution 1 for GlobalTheory.ThetaTranslJet.mult_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:38:38.898837+00:00
-- url     : https://prove2.me/submissions/d9b46b4e-ffad-4e1f-8981-8b71b772056f

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsTranslateJetNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusSplitting_CoeffEqZeroOfOrthonormal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsImEqLattice
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_DifferentiableFderivApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ImFormApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ThetaFunctionIsogenyRestriction
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
open Matrix ReciprocityTheory.ChartRestriction.G.I2
open scoped ComplexOrder
open GlobalTheory GlobalTheory.ThetaTranslJet
variable {g : ℕ} {Hm : Matrix (Fin g) (Fin g) ℂ}
namespace GlobalTheory.ThetaTranslJet
theorem _root_.solution {Λ : AddSubgroup (Fin g → ℂ)} {χ θ : (Fin g → ℂ) → ℂ} {z₀ : Fin g → ℂ}
    (h0 : θ z₀ ≠ 0)
    (hθ : ∀ a ∈ Λ, ∀ z, θ (z + a) = χ a * Complex.exp (Real.pi * (star a ⬝ᵥ Hm.mulVec z) +
      Real.pi / 2 * (star a ⬝ᵥ Hm.mulVec a)) * θ z) {a b : Fin g → ℂ} (ha : a ∈ Λ) (hb : b ∈ Λ) :
    χ (a + b) = χ a * χ b *
      Complex.exp (Real.pi / 2 * (star a ⬝ᵥ Hm.mulVec b - star b ⬝ᵥ Hm.mulVec a)) := by
  have e1 := hθ _ (Λ.add_mem ha hb) z₀
  rw [show z₀ + (a + b) = z₀ + b + a by abel, hθ a ha, hθ b hb, ← mul_assoc] at e1
  have e2 := mul_right_cancel₀ h0 e1
  refine mul_right_cancel₀ (Complex.exp_ne_zero _) (e2.symm.trans ?_)
  rw [mul_mul_mul_comm, mul_assoc (χ a * χ b), ← Complex.exp_add, ← Complex.exp_add]
  congr 2
  simp only [star_add, mulVec_add, add_dotProduct, dotProduct_add]
  ring
end GlobalTheory.ThetaTranslJet
