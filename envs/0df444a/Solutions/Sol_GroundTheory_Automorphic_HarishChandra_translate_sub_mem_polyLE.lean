-- Prove2me | solution 1 for GroundTheory.Automorphic.HarishChandra.translate_sub_mem_polyLE
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T07:03:20.627498+00:00
-- url     : https://prove2.me/submissions/3eb38547-094d-4bd6-a13d-0fdc376c9709

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_Projection
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_Capelli
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_LeadingTerm
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_mem_polyLE
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_polyLE_mono
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_translate_X
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_translate_C
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_mul_X_mem_polyLE
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_mul_C_mem_polyLE
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_U_induction
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_canon_zero
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_diagExp_apply
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_expand_zero
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_hcEmb_X
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_hcProj0_apply
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_iterPd_cons
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_iterPd_nil
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_pbw_apply
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
attribute [local simp] GroundTheory.Automorphic.HarishChandra.canon_zero
attribute [local simp] GroundTheory.Automorphic.HarishChandra.diagExp_apply
attribute [local simp] GroundTheory.Automorphic.HarishChandra.expand_zero
attribute [local simp] GroundTheory.Automorphic.HarishChandra.hcEmb_X
attribute [local simp] GroundTheory.Automorphic.HarishChandra.hcProj0_apply
attribute [local simp] GroundTheory.Automorphic.HarishChandra.iterPd_cons
attribute [local simp] GroundTheory.Automorphic.HarishChandra.iterPd_nil
attribute [local simp] GroundTheory.Automorphic.HarishChandra.pbw_apply
attribute [local simp] GroundTheory.Automorphic.HarishChandra.word_append
attribute [local simp] GroundTheory.Automorphic.HarishChandra.word_cons
attribute [local simp] GroundTheory.Automorphic.HarishChandra.word_nil



set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic GroundTheory.Automorphic.HarishChandra
attribute [local instance 100] LieRing.ofAssociativeRing
open MvPolynomial
variable {n : ℕ}
namespace GroundTheory.Automorphic.HarishChandra
theorem _root_.solution (c : Fin n → ℂ) :
    ∀ (d : ℕ) (p : MvPolynomial (Fin n) ℂ), p ∈ polyLE n d → translate c p - p ∈ polyLE n (d - 1) := by
  intro d
  induction d with
  | zero =>
    intro p hp
    rw [mem_polyLE, Nat.le_zero, totalDegree_eq_zero_iff_eq_C] at hp
    rw [hp, translate_C, sub_self]
    exact Submodule.zero_mem _
  | succ d ih =>
    intro p hp
    rw [p.as_sum, map_sum, ← Finset.sum_sub_distrib]
    refine Submodule.sum_mem _ fun s hs => ?_
    have hsd : (s.sum fun _ e => e) ≤ d + 1 := by
      have := mem_polyLE.1 hp
      rw [totalDegree] at this
      exact (Finset.le_sup hs).trans this
    by_cases hs0 : s = 0
    · rw [hs0, monomial_zero', translate_C, sub_self]
      exact Submodule.zero_mem _
    obtain ⟨i, hi⟩ := Finsupp.ne_iff.1 hs0
    set s' := s - Finsupp.single i 1
    have hss : s = s' + Finsupp.single i 1 := by
      rw [tsub_add_cancel_of_le]
      intro j
      by_cases hj : j = i
      · subst hj; simp [Nat.one_le_iff_ne_zero.2 hi]
      · simp [Ne.symm hj]
    have hs'd : (s'.sum fun _ e => e) ≤ d := by
      have : (s.sum fun _ e => e) = (s'.sum fun _ e => e) + 1 := by
        rw [hss, Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl),
          Finsupp.sum_single_index rfl]
      omega
    have hmono : monomial s (coeff s p) = monomial (s' + Finsupp.single i 1) (coeff s p) := by
      rw [← hss]
    rw [hmono, monomial_add_single, pow_one, map_mul, translate_X]
    set m' := monomial s' (coeff s p)
    have hm' : m' ∈ polyLE n d := mem_polyLE.2 ((totalDegree_monomial_le _ _).trans hs'd)
    have hT : translate c m' - m' ∈ polyLE n (d - 1) := ih m' hm'
    have hT' : translate c m' ∈ polyLE n d := by
      have := Submodule.add_mem _ (polyLE_mono (Nat.sub_le d 1) hT) hm'
      rwa [sub_add_cancel] at this
    have : translate c m' * (X i + C (c i)) - m' * X i =
        (translate c m' - m') * X i + translate c m' * C (c i) := by ring
    rw [this, Nat.add_sub_cancel]
    refine Submodule.add_mem _ ?_ (mul_C_mem_polyLE hT' _)
    rcases Nat.eq_zero_or_pos d with hd | hd
    · subst hd
      have hs'0 : s' = 0 := by
        ext j
        have : (s'.sum fun _ e => e) = 0 := Nat.le_zero.1 hs'd
        rw [Finsupp.sum, Finset.sum_eq_zero_iff] at this
        by_contra hj
        exact hj (this j (Finsupp.mem_support_iff.2 hj))
      simp only [m', hs'0, monomial_zero', translate_C, sub_self, zero_mul]
      exact Submodule.zero_mem _
    · have := mul_X_mem_polyLE hT i
      rwa [Nat.sub_add_cancel hd] at this
end GroundTheory.Automorphic.HarishChandra
