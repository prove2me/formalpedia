-- Prove2me | solution 1 for GlobalTheory.RealWeil.UnitaryOsc.isOsc_comp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:20:34.436976+00:00
-- url     : https://prove2.me/submissions/e7005a3a-2bc9-4549-a782-7eb6c5392652

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousFourierGau
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsOscillatorActionOfGaussianPairingsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CartanInvolutionConjOfPosDef
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GaussianPairingUnitaryGroupTwoThreeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HermitianCongrInvolution
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ProjEqSelfOfAnnihilated
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsOscillatorActionUnitaryGroupHermitian
import Theorems.Thm_GlobalTheory_RealWeil_UnitaryOsc_sm_comp_iff

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
theorem _root_.solution (E : V ≃L[ℝ] V') {ρ : V' → B →L[ℂ] B} {G G' : Type} [Group G] [Group G'] (φ : G →* G')
    {k : G → V' → V'} {k' : G' → V → V} (hk : ∀ g v, E (k' (φ g) v) = k g (E v)) {Ω : G' → B → B}
    (h : IsOsc (fun v => ρ (E v)) k' Ω) : IsOsc ρ k fun g => Ω (φ g) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  simp only [sm_comp_iff] at h1 h2 h3 h4 h5 h6 h7 h8
  refine ⟨fun g => h1 _, fun g => h2 _, fun g => h3 _, fun f hf => ?_, fun g g' f hf => ?_, fun g v f hf => ?_,
    fun g A hA => h7 _ A fun v => hA _, fun H _ _ _ Φ hΦ g => h8 H Φ (fun v => hΦ _) _⟩
  · simp only [map_one, h4 f hf]
  · simp only [map_mul, h5 _ _ f hf]
  · have := h6 (φ g) (E.symm v) f hf
    simpa only [hk, E.apply_symm_apply] using this
end GlobalTheory.RealWeil.UnitaryOsc
