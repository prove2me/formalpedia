-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.CasselmanOsborne.deg_Fop
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:23:02.66115+00:00
-- url     : https://prove2.me/submissions/25123b9d-60d7-4fa8-b32a-a9946cb3634c

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_DiscreteSeriesCharacters_CapelliDeterminantBlockProduct
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_ZetaDegZero
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
open Finset
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.CasselmanOsborne
open Formalism.REAL (GlRel qdet qminor Tm)
open CompanionTheory.D.DSIC
variable {n : ℕ} {ε : Fin n → Bool} {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
namespace GlobalTheory.CompanionTheory.CasselmanOsborne
theorem _root_.solution (hG : GFacts) {j : ℕ} (E : Fin n → Fin n → Module.End ℂ V) (c d : Fin n) {x : Ch ε V}
    (hx : Deg j x) : Deg j (Fop ε E c d x) := by
  obtain ⟨g, hg, -, hc, -⟩ := hG n ε
  intro A hA
  simp only [Fop, LinearMap.add_apply, Pi.add_apply, lift_apply, hx A hA, map_zero, zero_add, hg]
  refine Finset.sum_eq_zero fun B _ => ?_
  by_cases h0 : g c d A B = 0
  · simp [h0]
  · rw [hx B (by rw [← (hc c d A B h0).1]; exact hA), smul_zero]
end GlobalTheory.CompanionTheory.CasselmanOsborne
