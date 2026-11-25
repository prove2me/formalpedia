-- Prove2me | solution 1 for GlobalTheory.Inertia.posIndex_diagonal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:43:25.547231+00:00
-- url     : https://prove2.me/submissions/f59b0a09-7339-4732-9455-60271c96ab56

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_ExistsOrthogonalBasisDotProductApplyEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_PosIndexMapEqCardOfCongrDiagonal
import Theorems.Thm_GlobalTheory_Inertia_isGreatest_posIndex
import Theorems.Thm_GlobalTheory_Inertia_posIndex_neg
import Theorems.Thm_GlobalTheory_Inertia_negIndex_neg
import Theorems.Thm_GlobalTheory_Inertia_re_dotProduct_diagonal_mulVec_star
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Inertia.posIndex_neg
attribute [local simp] GlobalTheory.Inertia.negIndex_neg

set_option autoImplicit false
open GlobalTheory GlobalTheory.Inertia
open Module Matrix ReciprocityTheory.ChartRestriction.G
open scoped ComplexConjugate
variable {n m : Type*} [Fintype n] [Fintype m]
variable [DecidableEq n]
namespace GlobalTheory.Inertia
theorem _root_.solution (d : n → ℂ) :
    posIndex (diagonal d) = (Finset.univ.filter fun k => 0 < (d k).re).card := by
  refine (isGreatest_posIndex _).unique
    ⟨⟨Pi.spanSubset ℂ {k | 0 < (d k).re}, ?_, fun x hx hx0 => ?_⟩, ?_⟩
  · rw [Pi.dim_spanSubset, Set.ncard_eq_toFinset_card']
    simp
  · rw [re_dotProduct_diagonal_mulVec_star]
    have hx' := Pi.mem_spanSubset_iff.1 hx
    obtain ⟨k, hk⟩ := Function.ne_iff.1 hx0
    refine Finset.sum_pos' (fun j _ => ?_) ⟨k, Finset.mem_univ _, ?_⟩
    · by_cases hj : 0 < (d j).re
      · exact mul_nonneg hj.le (Complex.normSq_nonneg _)
      · simp [hx' j hj]
    · have hk' : 0 < (d k).re := by
        by_contra h
        exact hk (hx' k h)
      exact mul_pos hk' (Complex.normSq_pos.2 hk)
  · rintro _ ⟨W, rfl, hW⟩
    set S := Finset.univ.filter fun k => 0 < (d k).re with hS
    let f : W →ₗ[ℂ] (S → ℂ) := (LinearMap.funLeft ℂ ℂ (Subtype.val : S → n)).comp W.subtype
    have hf : Function.Injective f := by
      rw [injective_iff_map_eq_zero]
      intro x hx
      refine Subtype.ext ?_
      by_contra hx0
      refine (hW x x.2 hx0).not_ge ?_
      rw [re_dotProduct_diagonal_mulVec_star]
      refine Finset.sum_nonpos fun k _ => ?_
      by_cases hk : 0 < (d k).re
      · have : (x : n → ℂ) k = 0 := congrFun hx ⟨k, by simpa [hS] using hk⟩
        simp [this]
      · exact mul_nonpos_of_nonpos_of_nonneg (not_lt.1 hk) (Complex.normSq_nonneg _)
    simpa using LinearMap.finrank_le_finrank_of_injective hf
end GlobalTheory.Inertia
