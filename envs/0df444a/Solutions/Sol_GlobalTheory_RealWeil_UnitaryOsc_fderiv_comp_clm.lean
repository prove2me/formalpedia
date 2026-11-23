-- Prove2me | solution 1 for GlobalTheory.RealWeil.UnitaryOsc.fderiv_comp_clm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:15:02.275147+00:00
-- url     : https://prove2.me/submissions/124641a4-957c-4be2-9ea5-19d9978600eb

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
theorem _root_.solution {ρ : V' → B →L[ℂ] B} {f : B} (hf : Sm ρ f) (E : V →L[ℝ] V') (z : V) :
    fderiv ℝ (fun v => ρ (E v) f) 0 z = fderiv ℝ (fun v => ρ v f) 0 (E z) := by
  have h1 : DifferentiableAt ℝ (fun v => ρ v f) (E 0) := (ContDiff.differentiable hf (by simp)).differentiableAt
  have h2 := fderiv_comp (0 : V) h1 E.differentiableAt
  rw [E.fderiv, map_zero] at h2
  exact congrArg (fun T : V →L[ℝ] B => T z) h2
end GlobalTheory.RealWeil.UnitaryOsc
