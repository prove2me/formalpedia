-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.KModExists.kHighest_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:40:51.698628+00:00
-- url     : https://prove2.me/submissions/878dc768-cb1d-4fd5-ad52-158ee51e72a0

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_EigenspaceCyclicDensity_LowKMultOneP
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_CompactFiniteAdelesAwayPBoundedDenominators

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open scoped InnerProductSpace
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.KModExists
open Formalism.REAL (GlRel IsUnitary KHighest IsWeight)
open PI.UpqRep (IsKFin IsKTypeOf IsKStableOn)
open CompanionTheory.D.DSIC
namespace GlobalTheory.CompanionTheory.KModExists
theorem _root_.solution {n : ℕ} (ε : Fin n → Bool) {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
    [Module ℂ W] (ι : V →ₗ[ℂ] W) (hι : Function.Injective ι) (E' : Fin n → Fin n → Module.End ℂ V)
    (E : Fin n → Fin n → Module.End ℂ W) (h : ∀ a b v, ι (E' a b v) = E a b (ι v)) (μ : Fin n → ℝ) (v : V) :
    KHighest ε E' μ v ↔ KHighest ε E μ (ι v) := by
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun a => ?_, fun a b hab he => ?_⟩
    · rw [← h, h1 a, map_smul]
    · rw [← h, h2 a b hab he, map_zero]
  · rintro ⟨h1, h2⟩
    refine ⟨fun a => hι ?_, fun a b hab he => hι ?_⟩
    · rw [h, h1 a, map_smul]
    · rw [h, h2 a b hab he, map_zero]
end GlobalTheory.CompanionTheory.KModExists
