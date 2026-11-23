-- Prove2me | solution 1 for GlobalTheory.RealWeil.UnitaryOsc.isHeis_comp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:14:25.304593+00:00
-- url     : https://prove2.me/submissions/d01cd4e2-d424-4851-90cd-e76ab4633d2e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousFourierGau
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsOscillatorActionOfGaussianPairingsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CartanInvolutionConjOfPosDef
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GaussianPairingUnitaryGroupTwoThreeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HermitianCongrInvolution
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ProjEqSelfOfAnnihilated
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsOscillatorActionUnitaryGroupHermitian
import Theorems.Thm_GlobalTheory_RealWeil_IsHeis_continuous


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
theorem _root_.solution {om : V' → V' → ℝ} {om' : V → V → ℝ} {ρ : V' → B →L[ℂ] B} (h : IsHeis om ρ) (E : V →L[ℝ] V')
    (hE : ∀ x y, om (E x) (E y) = om' x y) : IsHeis om' fun v => ρ (E v) :=
  ⟨fun f => by simp only [map_zero, h.1], fun u v f => by simp only [h.2.1, hE, map_add], fun u f => h.2.2.1 _ f,
    fun f => (h.2.2.2 f).comp E.continuous⟩
end GlobalTheory.RealWeil.UnitaryOsc
