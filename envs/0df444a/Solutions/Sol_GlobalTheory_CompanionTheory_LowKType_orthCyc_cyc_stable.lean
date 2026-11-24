-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.LowKType.orthCyc_cyc_stable
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:49:43.191814+00:00
-- url     : https://prove2.me/submissions/4ec33e1f-4d2d-445f-83d9-22f9f08d80e6

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_EigenspaceCyclicDensity_LowKMultOneP
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_OrthCycCycStable
import Theorems.Thm_CompanionTheory_D_DSIC_lift_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] CompanionTheory.D.DSIC.lift_apply



set_option autoImplicit false
open scoped InnerProductSpace
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.LowKType
open CompanionTheory.D.LK CompanionTheory.D.DSIC Formalism.REAL
namespace GlobalTheory.CompanionTheory.LowKType
theorem _root_.solution {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (E : Fin n → Fin n → Module.End ℂ V) (v : V) (a b : Fin n) {x : V} (hx : x ∈ Cyc E v) :
    E a b x ∈ Cyc E v := by
  obtain ⟨t, rfl⟩ := hx
  refine ⟨FreeAlgebra.ι ℂ (a, b) * t, ?_⟩
  simp [ev]
end GlobalTheory.CompanionTheory.LowKType
