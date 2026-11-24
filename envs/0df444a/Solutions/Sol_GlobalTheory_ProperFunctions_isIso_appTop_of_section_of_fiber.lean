-- Prove2me | solution 1 for GlobalTheory.ProperFunctions.isIso_appTop_of_section_of_fiber
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T20:45:38.733825+00:00
-- url     : https://prove2.me/submissions/ab22e7b0-79dc-427e-b823-3a67f8215965

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIsoAppTopOfIsPullbackOfSurjective
import Theorems.Thm_GlobalTheory_ProperFunctions_eq_zero_of_forall_affineOpens
import Theorems.Thm_GlobalTheory_ProperFunctions_mem_map_of_compatible

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits AlgebraicGeometry TensorProduct Opposite
universe u
open GlobalTheory
open GlobalTheory.ProperFunctions
variable {X S : Scheme.{u}}
namespace GlobalTheory.ProperFunctions
theorem _root_.solution (p : X ⟶ S) [IsAffine S] [IsLocallyNoetherian S] [Flat p]
    (hq : ∀ s : S, Function.Surjective (p.fiberToSpecResidueField s).appTop)
    {e : S ⟶ X} (he : e ≫ p = 𝟙 S) : IsIso p.appTop := by
  have h1 : p.appTop ≫ e.appTop = 𝟙 _ := by
    rw [← Scheme.Hom.comp_appTop, he, Scheme.Hom.id_appTop]
  have h2 : Function.Injective e.appTop := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    refine eq_zero_of_forall_affineOpens x fun U ↦ ?_
    have := mem_map_of_compatible hq he ⊥
      (fun U ↦ X.presheaf.map (homOfLE (le_top : U.1 ≤ ⊤)).op x) ?_ ?_ U
    · simpa using this
    · intro U V hVU
      rw [← CommRingCat.comp_apply, ← Functor.map_comp, Ideal.map_bot, Ideal.mem_bot, sub_eq_zero]
      rfl
    · intro U W hW
      rw [Ideal.map_bot, Ideal.mem_bot, ← CommRingCat.comp_apply, Scheme.Hom.map_appLE,
        Scheme.Hom.appLE, CommRingCat.comp_apply]
      erw [hx]
      exact map_zero _
  have : Mono e.appTop := ConcreteCategory.mono_of_injective _ h2
  exact ⟨e.appTop, h1, by rw [← cancel_mono e.appTop, Category.assoc, h1]; simp⟩
end GlobalTheory.ProperFunctions
