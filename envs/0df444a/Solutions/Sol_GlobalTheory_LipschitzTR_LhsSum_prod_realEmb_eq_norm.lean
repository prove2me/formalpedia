-- Prove2me | solution 1 for GlobalTheory.LipschitzTR.LhsSum.prod_realEmb_eq_norm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T18:45:09.229842+00:00
-- url     : https://prove2.me/submissions/4621e6d7-64f7-4942-9d1d-f448bf71a779

import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RembApply
import Definitions.Def_Formalism_LatticeTheta_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SummableLipschitzLatticeNormPowSummand

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField nonZeroDivisors MeasureTheory GlobalTheory.LipschitzTR GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent
open scoped FourierTransform RealInnerProductSpace
noncomputable section
open GlobalTheory GlobalTheory.LipschitzTR GlobalTheory.LipschitzTR.LhsSum
variable {F : Type} [Field F] [NumberField F]
namespace GlobalTheory.LipschitzTR.LhsSum
theorem _root_.solution [IsTotallyReal F] (x : F) :
    (∏ τ : F →+* ℝ, τ x) = ((Algebra.norm ℚ x : ℚ) : ℝ) := by
  apply Complex.ofReal_injective
  push_cast
  have h := Algebra.norm_eq_prod_embeddings ℚ ℂ x
  rw [show ((Algebra.norm ℚ x : ℚ) : ℂ) = algebraMap ℚ ℂ (Algebra.norm ℚ x) from rfl, h]
  have hb : Function.Bijective (fun τ : F →+* ℝ => Complex.ofRealHom.comp τ) := by
    refine ⟨fun τ τ' h => ?_, fun φ => ?_⟩
    · ext x
      exact Complex.ofReal_injective (RingHom.congr_fun h x)
    · exact ⟨(IsTotallyReal.complexEmbedding_isReal φ).embedding, RingHom.ext fun x =>
        (IsTotallyReal.complexEmbedding_isReal φ).coe_embedding_apply x⟩
  refine Fintype.prod_bijective (fun τ : F →+* ℝ => RingHom.equivRatAlgHom F ℂ (Complex.ofRealHom.comp τ))
    ((RingHom.equivRatAlgHom F ℂ).bijective.comp hb) _ _ (fun τ => ?_)
  rfl
end GlobalTheory.LipschitzTR.LhsSum
