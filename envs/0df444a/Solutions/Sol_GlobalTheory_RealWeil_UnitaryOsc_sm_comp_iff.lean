-- Prove2me | solution 1 for GlobalTheory.RealWeil.UnitaryOsc.sm_comp_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:14:44.437959+00:00
-- url     : https://prove2.me/submissions/cdfc8de5-6ebb-4992-9348-4490a8d146fe

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousFourierGau
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsOscillatorActionOfGaussianPairingsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CartanInvolutionConjOfPosDef
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GaussianPairingUnitaryGroupTwoThreeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HermitianCongrInvolution
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ProjEqSelfOfAnnihilated
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsOscillatorActionUnitaryGroupHermitian

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Complex Matrix GlobalTheory.RealWeil
open scoped RealInnerProductSpace ContDiff Real ComplexOrder
open GlobalTheory GlobalTheory.RealWeil GlobalTheory.RealWeil.UnitaryOsc
variable {V V' : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup V'] [NormedSpace ℝ V']
  {B : Type} [NormedAddCommGroup B] [NormedSpace ℂ B]
namespace GlobalTheory.RealWeil.UnitaryOsc
theorem _root_.solution (E : V ≃L[ℝ] V') (ρ : V' → B →L[ℂ] B) (f : B) : Sm (fun v => ρ (E v)) f ↔ Sm ρ f :=
  E.contDiff_comp_iff (f := fun v => ρ v f)
end GlobalTheory.RealWeil.UnitaryOsc
