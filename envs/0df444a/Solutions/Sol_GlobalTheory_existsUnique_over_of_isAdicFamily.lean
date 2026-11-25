-- Prove2me | solution 1 for GlobalTheory.existsUnique_over_of_isAdicFamily
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T01:32:39.475799+00:00
-- url     : https://prove2.me/submissions/f88d72e8-5dd1-461c-b05f-277ef71f2cbd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsUniqueFactorCompletedStalkOfMap
import Theorems.Thm_GlobalTheory_hom_ext_of_isHausdorff
import Theorems.Thm_GlobalTheory_existsUnique_of_isAdicFamily

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry IsLocalRing
universe u
open GlobalTheory
variable {R : Type u} [CommRing R] (I : Ideal R)
variable {I}
variable [IsLocalRing R]
namespace GlobalTheory
theorem _root_.solution [IsAdicComplete I R] {X S : Scheme.{u}}
    (s : Spec (.of R) ⟶ S) (p : X ⟶ S)
    {f : ∀ n : ℕ, Spec (.of (R ⧸ I ^ (n + 1))) ⟶ X} (hf : IsAdicFamily I f)
    (hs : ∀ n, f n ≫ p = adicLevelι I (n + 1) ≫ s) :
    ∃! g : Spec (.of R) ⟶ X, g ≫ p = s ∧ ∀ n, adicLevelι I (n + 1) ≫ g = f n := by
  obtain ⟨g, hg, hu⟩ := existsUnique_of_isAdicFamily hf
  refine ⟨g, ⟨hom_ext_of_isHausdorff I fun n => ?_, hg⟩, fun g' hg' => hu g' hg'.2⟩
  rw [← Category.assoc, hg, hs]
end GlobalTheory
