-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.DSICFRel.sum_pt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:26:23.734254+00:00
-- url     : https://prove2.me/submissions/c8db3f11-230b-4d28-b671-e09c1591013e

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_DiscreteSeriesCharacters_CapelliDeterminantBlockProduct
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_CarImpFrel
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
open Finset CompanionTheory.D.DSIC
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.DSICFRel
variable {n : ℕ}
namespace GlobalTheory.CompanionTheory.DSICFRel
theorem _root_.solution (ε : Fin n → Bool) (x y : Fin n) (hx : ε x = true) (hy : ε y = false)
    (f : Fin n × Fin n → ℂ) : ∑ k : NC ε, dl k.1.1 x * dl k.1.2 y * f k.1 = f (x, y) := by
  rw [Finset.sum_eq_single (⟨(x, y), hx, hy⟩ : NC ε)]
  · simp [dl]
  · rintro ⟨⟨u, v⟩, h⟩ _ hne
    by_cases h1 : u = x
    · by_cases h2 : v = y
      · subst h1 h2; exact absurd rfl hne
      · simp [dl, h2]
    · simp [dl, h1]
  · simp
end GlobalTheory.CompanionTheory.DSICFRel
