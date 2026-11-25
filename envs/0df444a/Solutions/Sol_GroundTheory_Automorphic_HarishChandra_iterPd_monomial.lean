-- Prove2me | solution 1 for GroundTheory.Automorphic.HarishChandra.iterPd_monomial
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:00:16.354207+00:00
-- url     : https://prove2.me/submissions/d6506b5f-0a64-4001-9aa6-254e5eb6affe

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_MemCenterOfCommuteE
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_RepBase
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_RhoOneEqZeroOfRhoZeroEqZero
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_iterPd_nil
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_iterPd_cons
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_toFinsupp_map_swap_cons
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_U_induction
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_word_append
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_word_cons
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_word_nil
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.HarishChandra.word_append
attribute [local simp] GroundTheory.Automorphic.HarishChandra.word_cons
attribute [local simp] GroundTheory.Automorphic.HarishChandra.word_nil


attribute [local simp] GroundTheory.Automorphic.HarishChandra.iterPd_nil
attribute [local simp] GroundTheory.Automorphic.HarishChandra.iterPd_cons

set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic GroundTheory.Automorphic.HarishChandra
attribute [local instance 100] LieRing.ofAssociativeRing
open MvPolynomial
variable {n : ℕ}
namespace GroundTheory.Automorphic.HarishChandra
theorem _root_.solution (w : List (Fin n × Fin n)) (s : Fin n × Fin n →₀ ℕ) (c : ℂ) :
    ∃ κ : ℂ, iterPd w (monomial s c) =
        monomial (s - Multiset.toFinsupp ((w.map Prod.swap : List _) : Multiset _)) (c * κ) ∧
      (κ ≠ 0 ↔ Multiset.toFinsupp ((w.map Prod.swap : List _) : Multiset _) ≤ s) := by
  induction w with
  | nil => exact ⟨1, by simp, by simp⟩
  | cons a w ih =>
    obtain ⟨κ, h1, h2⟩ := ih
    rw [toFinsupp_map_swap_cons]
    generalize Multiset.toFinsupp ((w.map Prod.swap : List _) : Multiset (Fin n × Fin n)) = T
      at h1 h2 ⊢
    refine ⟨κ * ((s - T) (a.2, a.1) : ℕ), ?_, ?_⟩
    · rw [iterPd_cons, h1, pderiv_monomial, tsub_tsub, add_comm T, mul_assoc]
    · rw [mul_ne_zero_iff, h2, Nat.cast_ne_zero, Finsupp.tsub_apply]
      constructor
      · rintro ⟨hT, hb⟩ x
        rw [Finsupp.add_apply, Finsupp.single_apply]
        have := hT x
        split_ifs with hx
        · subst hx; omega
        · omega
      · intro h
        have hx : ∀ x, T x ≤ s x := fun x => le_trans (by simp) (h x)
        refine ⟨hx, ?_⟩
        have := h (a.2, a.1)
        rw [Finsupp.add_apply, Finsupp.single_eq_same] at this
        omega
end GroundTheory.Automorphic.HarishChandra
