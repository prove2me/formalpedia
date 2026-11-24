-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HeckeBern.augmentation_of_hecke_operator
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:37:05.6876+00:00
-- url     : https://prove2.me/submissions/5adf92e2-c261-4d66-8642-e2d5d4863013

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_InhabitedFinite
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_HeckeOperatorsSpanAndFaithful
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_HeckeAlgebraStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_HeckeBern_eps_single
import Theorems.Thm_GlobalTheory_CompanionTheory_HeckeBern_T_dd
import Theorems.Thm_CompanionTheory_D_gk_admitted_word_cons
import Theorems.Thm_CompanionTheory_D_gk_admitted_word_nil
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] CompanionTheory.D.gk.admitted.word_cons
attribute [local simp] CompanionTheory.D.gk.admitted.word_nil



set_option autoImplicit false
open CompanionTheory.Rg.Fl
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HeckeBern
variable {G : Type} [Group G] {K : Subgroup G}
variable (T : G → Hk K) (hp : IsHeckePair K)
variable (h1 : ∀ (g : G) (S : Finset (G ⧸ K)), (↑S : Set (G ⧸ K)) = MulAction.orbit K (g : G ⧸ K) →
    (T g : Module.End ℂ ((G ⧸ K) →₀ ℂ)) (Finsupp.single ((1 : G) : G ⧸ K) 1) =
      ∑ y ∈ S, Finsupp.single y (1 : ℂ))
  (h3 : ∀ h : Hk K, (h : Module.End ℂ ((G ⧸ K) →₀ ℂ)) (Finsupp.single ((1 : G) : G ⧸ K) 1) = 0 → h = 0)
include h1
namespace GlobalTheory.CompanionTheory.HeckeBern
theorem _root_.solution (g : G) : eps K ((T g).1 (dd K)) = q hp g := by
  rw [T_dd T hp h1, map_sum]
  simp [eps_single, q]
end GlobalTheory.CompanionTheory.HeckeBern
