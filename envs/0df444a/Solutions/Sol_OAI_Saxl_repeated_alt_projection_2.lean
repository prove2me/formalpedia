-- Prove2me | solution 2 for OAI.Saxl.repeated_alt_projection
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T02:19:03.245018+00:00
-- url     : https://prove2.me/submissions/21b5d8fa-4766-42a7-b5a1-fd1d126fb651

-- Generated from openai/math@1581d4c lean/OAI/RepresentationTheory/Saxl/RepeatedProjection.lean:L213-L233
-- (upload_full_project.md Phase 4): solution for node OAI.Saxl.repeated_alt_projection. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_Saxl
import Definitions.Def_OAI_RepresentationTheory_Saxl_Basic
import Definitions.Def_OAI_RepresentationTheory_Saxl_Polytabloid
import Definitions.Def_OAI_RepresentationTheory_Saxl_SpechtSubmodule
import Definitions.Def_OAI_RepresentationTheory_Saxl_SpechtDuality
import Definitions.Def_OAI_RepresentationTheory_Saxl_TableauTransport
import Definitions.Def_OAI_RepresentationTheory_Saxl_StaircaseTensor
import Definitions.Def_OAI_RepresentationTheory_Saxl_HighProjection
import Definitions.Def_OAI_RepresentationTheory_Saxl_CoordinateSector
import Definitions.Def_OAI_RepresentationTheory_Saxl_PositionSplit
import Definitions.Def_OAI_RepresentationTheory_Saxl_BandFactorization
import Definitions.Def_OAI_RepresentationTheory_Saxl_PathAlternation
import Definitions.Def_OAI_RepresentationTheory_Saxl_BandMatrices
import Definitions.Def_OAI_RepresentationTheory_Saxl_PathContraction
import Definitions.Def_OAI_RepresentationTheory_Saxl_ColumnContraction
import Definitions.Def_OAI_RepresentationTheory_Saxl_BandPairing
import Definitions.Def_OAI_RepresentationTheory_Saxl_CyclicSector
import Definitions.Def_OAI_RepresentationTheory_Saxl_BandSupport
import Definitions.Def_OAI_RepresentationTheory_Saxl_ShapeRigidity
import Definitions.Def_OAI_RepresentationTheory_Saxl_SpechtClassification
import Definitions.Def_OAI_RepresentationTheory_Saxl_SupportSeparation
import Definitions.Def_OAI_RepresentationTheory_Saxl_PositionTensor
import Definitions.Def_OAI_RepresentationTheory_Saxl_BandOrbit
import Definitions.Def_OAI_RepresentationTheory_Saxl_BandGlue
import Definitions.Def_OAI_RepresentationTheory_Saxl_SignEquivalence
import Definitions.Def_OAI_RepresentationTheory_Saxl_PieriRestriction
import Definitions.Def_OAI_RepresentationTheory_Saxl_StripExtension
import Definitions.Def_OAI_RepresentationTheory_Saxl_SizedStrips
import Definitions.Def_OAI_RepresentationTheory_Saxl_HorizontalRemoval
import Definitions.Def_OAI_RepresentationTheory_Saxl_YoungRule
import Definitions.Def_OAI_RepresentationTheory_Saxl_CyclicTensor
import Definitions.Def_OAI_RepresentationTheory_Saxl_RepeatedProjection
import Theorems.Thm_OAI_Saxl_paired_term_projection

-- ---- from OAI.RepresentationTheory.Saxl.RepeatedProjection ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section

open scoped TensorProduct

universe uX

namespace Saxl

/- The strict square-moment equality used in the dominance projection.
The labels may be real; the application uses actual nonnegative integer letters. -/
end Saxl

namespace Saxl
/- Coordinate projection; equivariance is asserted only for preserved predicates. -/

lemma wordTensor_single {n d e : ℕ} (a : Fin n → Fin d) (b : Fin n → Fin e) :
    wordTensor n d e (Pi.single a 1 ⊗ₜ[ℂ] Pi.single b 1) = Pi.single (mergeWords a b) 1 := by
  classical
  ext c
  rw [wordTensor_tmul]
  by_cases h : c = mergeWords a b
  · subst c; simp
  · have hh : splitLeft c ≠ a ∨ splitRight c ≠ b := by
      by_contra hn
      push Not at hn
      exact h (by rw [← merge_split c, hn.1, hn.2])
    rcases hh with hl | hr
    · simp [Pi.single_apply, h, hl]
    · simp [Pi.single_apply, h, hr]

lemma altWord_inverse_sum {n d : ℕ} (H : Subgroup (Equiv.Perm (Fin n)))
    (a : Fin n → Fin d) :
    letI := Fintype.ofFinite H
    altWord H a = ∑ g : H, signC (g : Equiv.Perm (Fin n)) • Pi.single (a ∘ (g : Equiv.Perm (Fin n))) 1 := by
  classical
  let := Fintype.ofFinite H
  unfold altWord
  simp_rw [wordRep_single]
  apply Eq.trans ?_ (Equiv.sum_comp (Equiv.inv H) _)
  apply Finset.sum_congr rfl
  intro g hg
  congr 1
  exact (signC_inv g.val).symm

theorem repeated_alt_projection {n d e : ℕ} (H : Subgroup (Equiv.Perm (Fin n)))
    (a : Fin n → Fin d) (t : Fin n → Fin e) (ω : H)
    (ht : ∀ g : H, ∀ i, t (g.val i) = t i)
    (ha : Function.Injective (fun i => (t i, a i)))
    (hω : ∀ i, (a i).val + (a (ω.val i)).val = (t i).val) :
    orbitProjection t (pairSumMap n d e (wordTensor n d d
      (altWord H a ⊗ₜ[ℂ] altWord H a))) =
      ((Nat.card H : ℂ) * signC ω.val) • Pi.single t 1 := by
  classical
  let := Fintype.ofFinite H
  rw [altWord_inverse_sum, TensorProduct.sum_tmul]
  simp only [TensorProduct.tmul_sum, map_sum, TensorProduct.smul_tmul_smul, map_smul,
    wordTensor_single, paired_term_projection H a t ω ht ha hω]
  simp only [smul_ite, smul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  have hs (g : H) : signC g.val * signC (ω*g).val = signC ω.val := by
    simp only [Subgroup.coe_mul, map_mul]
    calc
      signC g.val * (signC ω.val * signC g.val) = signC ω.val * (signC g.val * signC g.val) := by ring
      _ = signC ω.val := by rw [signC_mul_self, mul_one]
  simp only [hs, Finset.sum_const, Finset.card_univ]
  rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, Fintype.card_eq_nat_card]

end Saxl

end

end OAI

-- ---- platform node ----
open OAI OAI.Saxl
open scoped TensorProduct


theorem solution : type_of% @_root_.OAI.Saxl.repeated_alt_projection := @_root_.OAI.Saxl.repeated_alt_projection
