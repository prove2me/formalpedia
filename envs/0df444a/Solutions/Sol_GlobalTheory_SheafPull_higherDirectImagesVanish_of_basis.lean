-- Prove2me | solution 1 for GlobalTheory.SheafPull.higherDirectImagesVanish_of_basis
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T05:03:25.816818+00:00
-- url     : https://prove2.me/submissions/a4137321-05cd-4ecd-a99c-60851cf51a85

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_FreeYonedaHomEquivFreeToPullbackComp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_PushComparisonBijectiveOfIsClosedEmbedding

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Abelian Opposite Limits TopologicalSpace
universe w w' w'' u
noncomputable section
open GlobalTheory
open GlobalTheory.SheafPull
open SheafLES Flasque
variable {X Y : TopCat.{u}}
variable [HasExt.{w} (AbSheaf X)] [HasExt.{w'} (AbSheaf Y)]
variable (f : Y ⟶ X)
omit [HasExt.{w} (AbSheaf X)]
namespace GlobalTheory.SheafPull
theorem _root_.solution (G : AbSheaf Y)
    (h : ∀ (V : Opens X), ∀ x ∈ V, ∃ W ≤ V, x ∈ W ∧
      ∀ n, 0 < n → Subsingleton (Sheaf.H'.{w'} G n ((Opens.map f).obj W))) :
    HigherDirectImagesVanish.{w'} f G := fun n hn V _ x hx ↦ by
  obtain ⟨W, hWV, hx, hW⟩ := h V x hx
  exact ⟨W, homOfLE hWV, hx, @Subsingleton.elim _ (hW n hn) _ _⟩
end GlobalTheory.SheafPull
