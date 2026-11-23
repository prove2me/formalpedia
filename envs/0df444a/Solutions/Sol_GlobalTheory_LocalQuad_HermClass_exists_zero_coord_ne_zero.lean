-- Prove2me | solution 1 for GlobalTheory.LocalQuad.HermClass.exists_zero_coord_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:16:47.730636+00:00
-- url     : https://prove2.me/submissions/c62f9e63-a581-488c-a6b9-bc1739db4a72

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_AdelicLattices__AlgebraMapNormOfBasisOneSqrt_07cf76d090f2548e
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_ExistsOrthogonalBasisDotProductApplyEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_PosIndexMapEqCardOfCongrDiagonal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_ExistsGlIsometryCompEqOfNondegenerate
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsZeroCoordNeZero
import Theorems.Thm_GlobalTheory_Inertia_negIndex_neg
import Theorems.Thm_GlobalTheory_Inertia_posIndex_neg
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Inertia.negIndex_neg
attribute [local simp] GlobalTheory.Inertia.posIndex_neg



set_option autoImplicit false
open NumberField IsDedekindDomain
open scoped Matrix WithZero ComplexConjugate
open ReciprocityTheory.ChartRestriction.G.FD
open GlobalTheory GlobalTheory.LocalQuad
open GlobalTheory.LocalQuad.HermClass
namespace GlobalTheory.LocalQuad.HermClass
theorem _root_.solution {F : Type*} [Field F] [CharZero F] {ι : Type*} [Fintype ι]
    {a : ι → F} (ha : ∀ i, a i ≠ 0) {z : ι → F} (hz : z ≠ 0) (h : ∑ i, a i * z i ^ 2 = 0)
    (i : ι) : ∃ w : ι → F, w i ≠ 0 ∧ ∑ k, a k * w k ^ 2 = 0 := by
  classical
  by_cases hi : z i = 0
  swap
  · exact ⟨z, hi, h⟩
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hz
  have hj : z j ≠ 0 := hj
  have hij : i ≠ j := by
    rintro rfl
    exact hj hi
  have haj := ha j
  set t : F := -(a i + a j) / (2 * a j * z j) with ht
  refine ⟨fun k => (if k = i then 1 else 0) + (if k = j then 1 else 0) + t * z k, ?_, ?_⟩
  · simp [hij, hi]
  · have : ∀ k, a k * ((if k = i then 1 else 0) + (if k = j then 1 else 0) + t * z k) ^ 2 =
        (if k = i then a i else 0) + (if k = j then a j + 2 * t * a j * z j else 0) +
          t ^ 2 * (a k * z k ^ 2) := by
      intro k
      by_cases h1 : k = i
      · subst h1
        simp [hij, hi]
      · by_cases h2 : k = j
        · subst h2
          simp only [h1, if_false, if_true]
          ring
        · simp only [h1, h2, if_false]
          ring
    simp only [this, Finset.sum_add_distrib, ← Finset.mul_sum, h, Finset.sum_ite_eq',
      Finset.mem_univ, if_true]
    rw [ht]
    field_simp
    ring
end GlobalTheory.LocalQuad.HermClass
