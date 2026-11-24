-- Prove2me | solution 1 for GlobalTheory.Published.subsingleton_Hn_of_action_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:55:20.800797+00:00
-- url     : https://prove2.me/submissions/eeaa18f7-4e56-4e70-aac5-05728e82f9c9

import Mathlib
import Definitions.Def_ReciprocityTheory_Hypotheses_GalCoh
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_GaloisCohomology__CohDimTwoLocalOfLocalFiniteness_b2c2e165733ad400
import Theorems.Thm_GlobalTheory_Published_subsingleton_Hn_succ_iff
import Theorems.Thm_GlobalTheory_Published_dn_eq_of_action_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Representation ReciprocityTheory.Gal Formalism.ConjugateSelfDual
open GlobalTheory GlobalTheory.Published
variable {Γ : Type*} [Group Γ] [TopologicalSpace Γ] {M : Type*} [AddCommGroup M]
  [TopologicalSpace M] [IsTopologicalAddGroup M]
namespace GlobalTheory.Published
theorem _root_.solution {R R' : Type*} [CommRing R] [CommRing R'] [Module R M]
    [Module R' M] [ContinuousConstSMul R M] [ContinuousConstSMul R' M]
    (rho : Representation R Γ M) (rho' : Representation R' Γ M)
    (h : ∀ g m, rho g m = rho' g m) (n : ℕ) (hn : 0 < n) (hs : Subsingleton (Hn rho' n)) :
    Subsingleton (Hn rho n) := by
  obtain ⟨n, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  rw [subsingleton_Hn_succ_iff] at hs ⊢
  intro f hf hd
  obtain ⟨c, hc, e⟩ := hs f hf (by rw [← dn_eq_of_action_eq rho rho' h]; exact hd)
  exact ⟨c, hc, by rw [dn_eq_of_action_eq rho rho' h]; exact e⟩
end GlobalTheory.Published
