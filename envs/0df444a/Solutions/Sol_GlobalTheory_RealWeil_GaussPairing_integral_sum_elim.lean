-- Prove2me | solution 1 for GlobalTheory.RealWeil.GaussPairing.integral_sum_elim
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T19:52:51.162522+00:00
-- url     : https://prove2.me/submissions/3c3d46e0-b39b-4e31-8c01-ec3558e30f66

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousFourierGau
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HalfAddSelf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IntegralComplexGaussianPosDefHermitianPartStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MeasurePreservingOfNormSqEqSumComplexCoords
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GaussianPairingUnitaryGroupTwoThree

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Complex Matrix GlobalTheory.RealWeil
open scoped RealInnerProductSpace ContDiff Real ComplexOrder
open GlobalTheory GlobalTheory.RealWeil GlobalTheory.RealWeil.GaussPairing
namespace GlobalTheory.RealWeil.GaussPairing
theorem _root_.solution {ι : Type} [Fintype ι] (F : (ι ⊕ ι → ℂ) → ℂ) (hF : Integrable F) :
    ∫ z : ι → ℂ, ∫ w : ι → ℂ, F (Sum.elim z w) = ∫ x, F x := by
  have hmp := volume_measurePreserving_sumPiEquivProdPi_symm (fun _ : ι ⊕ ι => ℂ)
  have hF' : Integrable (fun p => F ((MeasurableEquiv.sumPiEquivProdPi fun _ : ι ⊕ ι => ℂ).symm p))
      ((volume : Measure (ι → ℂ)).prod volume) :=
    (hmp.integrable_comp_emb (MeasurableEquiv.measurableEmbedding _)).2 hF
  rw [← hmp.integral_comp' F, Measure.volume_eq_prod, integral_prod _ hF']
  rfl
end GlobalTheory.RealWeil.GaussPairing
