-- Prove2me | solution 1 for KernelRank.exists_representation_of_sum_expPoly
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T02:36:18.01022+00:00
-- url     : https://prove2.me/submissions/4048b271-011a-4d73-8582-fc396bc12e6a

import Definitions.Def_KernelRankLean_RealExpPoly
import Definitions.Def_KernelRankLean_Defs
import Definitions.Def_KernelRankLean_Representation
import Theorems.Thm_KernelRank_re_expPoly_conjPoly
import Theorems.Thm_KernelRank_sum_eq_sum_upperHalf
import Theorems.Thm_KernelRank_expPoly_C_mul
import Theorems.Thm_KernelRank_expPoly_add
import Theorems.Thm_KernelRank_expPoly_zero
attribute [local simp] KernelRank.expPoly_zero



set_option autoImplicit true
open Complex Polynomial
open KernelRank
namespace KernelRank
theorem _root_.solution (φ : ℝ → ℝ) (S : Finset ℂ) (Q : ℂ → ℂ[X])
    (h : ∀ t, 0 ≤ t → (φ t : ℂ) = ∑ μ ∈ S, expPoly (Q μ) μ t) :
    ∃ cs : List Component, IsRepresentation cs ∧ ∀ t, 0 ≤ t → φ t = profile cs t := by
  classical
  let Q' : ℂ → ℂ[X] := fun μ => if μ ∈ S then Q μ else 0
  let V : Finset ℂ := S ∪ S.image (starRingEnd ℂ)
  have hV : ∀ μ ∈ V, starRingEnd ℂ μ ∈ V := by
    intro μ hμ
    simp only [V, Finset.mem_union, Finset.mem_image] at hμ ⊢
    rcases hμ with hμ | ⟨ν, hν, rfl⟩
    · exact Or.inr ⟨μ, hμ, rfl⟩
    · exact Or.inl (by simpa using hν)
  -- The merged polynomial of the rate `μ` and its conjugate.
  let R : ℂ → ℂ[X] := fun μ =>
    C (pairWeight μ : ℂ) * (Q' μ + conjPoly (Q' (starRingEnd ℂ μ)))
  let U := (V.filter fun μ => 0 ≤ μ.im).filter fun μ => R μ ≠ 0
  refine ⟨U.toList.map fun μ => ⟨μ, R μ⟩, ⟨?_, ?_⟩, ?_⟩
  · intro c hc
    simp only [List.mem_map, Finset.mem_toList] at hc
    obtain ⟨μ, hμ, rfl⟩ := hc
    simp only [U, Finset.mem_filter] at hμ
    refine ⟨hμ.2, hμ.1.2, fun him k => ?_⟩
    have hc : starRingEnd ℂ μ = μ := Complex.conj_eq_iff_im.mpr him
    simp [R, hc, conjPoly, coeff_map]
  · simpa [Function.comp_def] using Finset.nodup_toList U
  · intro t ht
    have hprof : profile (U.toList.map fun μ => ⟨μ, R μ⟩) t = ∑ μ ∈ U, (expPoly (R μ) μ t).re := by
      simp only [profile, List.map_map, Finset.sum_map_toList]
      rfl
    have hφ : φ t = ∑ μ ∈ V, (expPoly (Q' μ) μ t).re := by
      have h' := congrArg Complex.re (h t ht)
      rw [Complex.ofReal_re, Complex.re_sum] at h'
      calc φ t = ∑ μ ∈ S, (expPoly (Q' μ) μ t).re := by
            rw [h']
            exact Finset.sum_congr rfl fun μ hμ => by simp [Q', hμ]
        _ = ∑ μ ∈ V, (expPoly (Q' μ) μ t).re :=
            Finset.sum_subset Finset.subset_union_left fun μ _ hμ => by simp [Q', hμ]
    have hdrop : ∑ μ ∈ U, (expPoly (R μ) μ t).re =
        ∑ μ ∈ V.filter (fun μ => 0 ≤ μ.im), (expPoly (R μ) μ t).re := by
      refine Finset.sum_filter_of_ne fun μ _ hne => ?_
      intro h0
      apply hne
      simp [h0]
    rw [hprof, hdrop, hφ, sum_eq_sum_upperHalf V hV]
    refine Finset.sum_congr rfl fun μ _ => ?_
    have hc := re_expPoly_conjPoly (Q' (starRingEnd ℂ μ)) (starRingEnd ℂ μ) t
    rw [Complex.conj_conj] at hc
    simp only [R, expPoly_C_mul, expPoly_add, Complex.re_ofReal_mul, Complex.add_re, hc]
end KernelRank
