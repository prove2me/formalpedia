-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.LKDens.rho_surj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:57:42.784463+00:00
-- url     : https://prove2.me/submissions/1a639b98-c322-45b3-8a26-d7a89889902b

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_EigenspaceCyclicDensity_LowKMultOneP
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_EigenspaceCyclicDensity_CreationOperators_RhoSurj
import Theorems.Thm_GlobalTheory_CompanionTheory_LKDens_burnside
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
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.LKDens
open CompanionTheory.D.LK
open CompanionTheory.D.DSIC (KStab)
variable {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
namespace GlobalTheory.CompanionTheory.LKDens
theorem _root_.solution (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ V) (L : Submodule ℂ V) (hL : KStab ε E L)
    [FiniteDimensional ℂ L] {v : V} (hv : v ≠ 0) (hvL : v ∈ L)
    (hirr : ∀ L' ≤ L, KStab ε E L' → L' = ⊥ ∨ L' = L) : Function.Surjective (rho ε E L hL) := by
  refine burnside (rho ε E L hL) ⟨⟨v, hvL⟩, 0, fun h => hv (congrArg Subtype.val h)⟩ ?_
  intro W hW
  have hst : KStab ε E (W.map L.subtype) := by
    rintro a b hab _ ⟨w, hw, rfl⟩
    refine ⟨rho ε E L hL (FreeAlgebra.ι ℂ (a, b)) w, hW _ w hw, ?_⟩
    simp [rho, hab]
  rcases hirr _ (Submodule.map_subtype_le L W) hst with h | h
  · left
    apply Submodule.map_injective_of_injective L.injective_subtype
    simpa using h
  · right
    apply Submodule.map_injective_of_injective L.injective_subtype
    simpa using h
end GlobalTheory.CompanionTheory.LKDens
