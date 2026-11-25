-- Prove2me | solution 1 for GlobalTheory.Mass.LineGlue.nondeg_of_pd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T07:48:33.592501+00:00
-- url     : https://prove2.me/submissions/0ee8725b-0714-4190-a595-dd80177f1332

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianLatticeDiscriminantOrderNeZeroUnimodula
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_LatticeQuotientGensAndIntermediateCount
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_WittExtensionTotallyDefiniteHermitian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CardHermitianLatticesGluedAlongLine

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical
open GlobalTheory GlobalTheory.Mass GlobalTheory.Mass.LineGlue
namespace GlobalTheory.Mass.LineGlue
theorem _root_.solution {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
    (h : V →ₗ⋆[K] V →ₗ[K] K) (hpd : PD h) : h.Nondegenerate := by
  have ha : ∀ x, h x x = 0 → x = 0 := by
    intro x hx
    by_contra h0
    obtain ⟨τ⟩ : Nonempty (K →+* ℂ) := inferInstance
    have := hpd τ x h0
    simp [hx] at this
  exact ⟨fun x hx => ha x (hx x), fun x hx => ha x (hx x)⟩
end GlobalTheory.Mass.LineGlue
