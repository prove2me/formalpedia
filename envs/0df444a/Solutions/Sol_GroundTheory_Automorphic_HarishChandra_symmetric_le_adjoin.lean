-- Prove2me | solution 1 for GroundTheory.Automorphic.HarishChandra.symmetric_le_adjoin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:02:13.27584+00:00
-- url     : https://prove2.me/submissions/611afa23-eb42-4e4e-b354-4d39c7eb5d98

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_Symmetric
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_mem_adjoin_psum_of_isSymmetric
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_TopClose_pow
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_TopClose_prod
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_isHomogeneous_psum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic GroundTheory.Automorphic.HarishChandra
open MvPolynomial Finset
variable {n : ℕ}
namespace GroundTheory.Automorphic.HarishChandra
theorem _root_.solution (q : Fin n → MvPolynomial (Fin n) ℂ) (hq : ∀ k, (q k).IsSymmetric)
    (hdeg : ∀ k, (q k - psum (Fin n) ℂ ((k : ℕ) + 1)).totalDegree < (k : ℕ) + 1) (d : ℕ) :
    ∀ p : MvPolynomial (Fin n) ℂ, p.IsSymmetric → p.totalDegree ≤ d →
      p ∈ Algebra.adjoin ℂ (Set.range q) := by
  set B := Algebra.adjoin ℂ (Set.range q)
  have hBsym : ∀ r ∈ B, r.IsSymmetric := by
    have : B ≤ symmetricSubalgebra (Fin n) ℂ :=
      Algebra.adjoin_le (by rintro _ ⟨k, rfl⟩; exact hq k)
    exact fun r hr => this hr
  have hclose : ∀ i : Fin n, TopClose ((i : ℕ) + 1) (psumFin i) (q i) := by
    intro i
    have h1 : (psumFin i).totalDegree ≤ (i : ℕ) + 1 :=
      (isHomogeneous_psum _).totalDegree_le
    refine ⟨h1, ?_, Or.inr ?_⟩
    · have : q i = psumFin i + (q i - psumFin i) := by ring
      rw [this]
      exact (totalDegree_add _ _).trans (max_le h1 (hdeg i).le)
    · rw [← neg_sub, totalDegree_neg]; exact hdeg i
  induction d with
  | zero =>
    intro p _ hp
    rw [totalDegree_eq_zero_iff_eq_C.1 (show p.totalDegree = 0 by omega)]
    exact B.algebraMap_mem _
  | succ d ih =>
    intro p hp hpd
    obtain ⟨F, rfl⟩ : ∃ F, aeval psumFin F = p := by
      have := mem_adjoin_psum_of_isSymmetric hp
      rw [Algebra.adjoin_range_eq_range_aeval] at this
      exact this
    set P : (Fin n →₀ ℕ) → MvPolynomial (Fin n) ℂ := fun c => c.prod fun i k => psumFin i ^ k
    set Q : (Fin n →₀ ℕ) → MvPolynomial (Fin n) ℂ := fun c => c.prod fun i k => q i ^ k
    have hPhom : ∀ c, (P c).IsHomogeneous (psumWt c) := by
      intro c
      simp only [P, Finsupp.prod, psumWt]
      refine IsHomogeneous.prod _ _ _ fun i _ => ?_
      rw [mul_comm]
      exact (isHomogeneous_psum _).pow _
    have hPQ : ∀ c, TopClose (psumWt c) (P c) (Q c) := by
      intro c
      simp only [P, Q, Finsupp.prod, psumWt]
      exact TopClose.prod _ _ _ _ fun i _ => (hclose i).pow (c i)
    have hF : aeval psumFin F = ∑ c ∈ F.support, coeff c F • P c := by
      conv_lhs => rw [F.as_sum]
      rw [map_sum]
      refine sum_congr rfl fun c _ => ?_
      rw [aeval_monomial, Algebra.smul_def]
    set S := F.support.filter fun c => psumWt c = d + 1
    set r := ∑ c ∈ S, coeff c F • Q c
    have hr : r ∈ B := by
      refine B.sum_mem fun c _ => B.smul_mem ?_ _
      simp only [Q, Finsupp.prod]
      exact B.prod_mem fun i _ => B.pow_mem (Algebra.subset_adjoin ⟨i, rfl⟩) _
    have htop : homogeneousComponent (d + 1) (aeval psumFin F) = ∑ c ∈ S, coeff c F • P c := by
      rw [hF, map_sum, sum_filter]
      refine sum_congr rfl fun c _ => ?_
      rw [map_smul, homogeneousComponent_of_mem (hPhom c)]
      by_cases h : psumWt c = d + 1
      · rw [if_pos h.symm, if_pos h]
      · rw [if_neg (Ne.symm h), if_neg h, smul_zero]
    have hlow : (aeval psumFin F - homogeneousComponent (d + 1) (aeval psumFin F)).totalDegree ≤ d := by
      set p := aeval psumFin F
      rw [totalDegree, Finset.sup_le_iff]
      intro m hm
      rw [mem_support_iff, coeff_sub, coeff_homogeneousComponent] at hm
      have hm' : m ∈ p.support := by
        rw [mem_support_iff]; intro h0; rw [h0] at hm; simp at hm
      have h1 := le_totalDegree hm'
      by_cases hd : m.degree = d + 1
      · rw [if_pos hd, sub_self] at hm; exact absurd rfl hm
      · have : (m.sum fun _ e => e) = m.degree := by
          rfl
        rw [this] at h1 ⊢
        omega
    have hdiff : (∑ c ∈ S, coeff c F • P c - r).totalDegree ≤ d := by
      rw [← sum_sub_distrib]
      refine totalDegree_finsetSum_le fun c hc => ?_
      rw [← smul_sub]
      refine (totalDegree_smul_le _ _).trans ?_
      have hwc : psumWt c = d + 1 := (mem_filter.1 hc).2
      rcases (hPQ c).2.2 with h | h
      · rw [h, sub_self, totalDegree_zero]; exact Nat.zero_le _
      · rw [hwc] at h; omega
    have hkey : (aeval psumFin F - r).totalDegree ≤ d := by
      have : aeval psumFin F - r = (aeval psumFin F - homogeneousComponent (d + 1) (aeval psumFin F))
          + (∑ c ∈ S, coeff c F • P c - r) := by rw [htop]; ring
      rw [this]
      exact (totalDegree_add _ _).trans (max_le hlow hdiff)
    have hsym : (aeval psumFin F - r).IsSymmetric :=
      (symmetricSubalgebra (Fin n) ℂ).sub_mem hp (hBsym r hr)
    have := B.add_mem (ih _ hsym hkey) hr
    rwa [sub_add_cancel] at this
end GroundTheory.Automorphic.HarishChandra
