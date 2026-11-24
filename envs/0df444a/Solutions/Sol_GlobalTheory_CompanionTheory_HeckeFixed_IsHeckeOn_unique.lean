-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HeckeFixed.IsHeckeOn.unique
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T13:12:12.666799+00:00
-- url     : https://prove2.me/submissions/22a11e01-f220-4bac-83ab-a0dda25ccf17

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SmoothPartStable
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_TwistedFactors_LocalBaseChange_TwistedIndependenceLemma_TwistedIndependence
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_HeckeCharacterExistsUnique
import Theorems.Thm_GlobalTheory_CompanionTheory_HeckeFixed_eK_apply_of_mem
import Theorems.Thm_GlobalTheory_CompanionTheory_HeckeFixed_eK_apply_act
import Theorems.Thm_GlobalTheory_SmGL_IsSubquotient_trans


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep
attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HeckeFixed
variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
variable [TopologicalSpace G]
variable [IsTopologicalGroup G]
variable {π : Representation ℂ G V} (hπ : IsSmooth π) {K : Subgroup G}
  (hKc : IsCompact (K : Set G))
include hπ hKc
namespace GlobalTheory.CompanionTheory.HeckeFixed
namespace IsHeckeOn
theorem _root_.solution {g : G} {T T' : Module.End ℂ (fixed π K)}
    (hT : IsHeckeOn π K g T) (hT' : IsHeckeOn π K g T') : T = T' := by
  refine LinearMap.ext fun v => Subtype.ext ?_
  rw [← sub_eq_zero, ← Module.forall_dual_apply_eq_zero_iff ℂ]
  intro f
  have hinv : ∀ x ∈ K, (f ∘ₗ (fixed π K).subtype ∘ₗ eK π hπ hKc) ∘ₗ π x =
      f ∘ₗ (fixed π K).subtype ∘ₗ eK π hπ hKc := by
    intro x hx
    ext y
    simp only [LinearMap.comp_apply, eK_apply_act hπ hKc hx]
  have h := (hT v _ hinv).symm.trans (hT' v _ hinv)
  simp only [LinearMap.comp_apply, Submodule.subtype_apply,
    eK_apply_of_mem hπ hKc (T v).2, eK_apply_of_mem hπ hKc (T' v).2] at h
  rw [map_sub, h, sub_self]
end IsHeckeOn
end GlobalTheory.CompanionTheory.HeckeFixed
