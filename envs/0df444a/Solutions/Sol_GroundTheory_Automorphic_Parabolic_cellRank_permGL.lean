-- Prove2me | solution 1 for GroundTheory.Automorphic.Parabolic.cellRank_permGL
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:50:58.306569+00:00
-- url     : https://prove2.me/submissions/90eb239e-3769-4372-bdd9-cd55bdf36a82

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_FiniteBruhat
import Definitions.Def_GroundTheory_AutomorphicForms_InductionParabolicGroups
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaCells
import Theorems.Thm_GroundTheory_Automorphic_GLnLocal_quotientEquivLattice_mk
import Theorems.Thm_GroundTheory_Automorphic_permGL_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.GLnLocal.quotientEquivLattice_mk



set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Parabolic
open Matrix Iwasawa Topology Set DoubleCoset
variable {F : Type*} [Field F] {n : ℕ}
variable {β γ : Fin n → ℕ}
namespace GroundTheory.Automorphic.Parabolic
theorem _root_.solution (w : Equiv.Perm (Fin n)) (a b : ℕ) :
    cellRank β γ (permGL F w) a b = (Finset.univ.filter fun j => γ j ≤ b ∧ a ≤ β (w j)).card := by
  classical
  unfold cellRank
  set X := ((permGL F w : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).submatrix
    (fun i : {i : Fin n // a ≤ β i} => (i : Fin n)) (fun j : {j : Fin n // γ j ≤ b} => (j : Fin n))
    with hX
  rw [Matrix.rank_eq_finrank_span_cols]
  let v : {j : Fin n // γ j ≤ b ∧ a ≤ β (w j)} → ({i : Fin n // a ≤ β i} → F) :=
    fun t => Pi.single ⟨w t, t.2.2⟩ 1
  have hv : LinearIndependent F v := by
    have := (Pi.basisFun F {i : Fin n // a ≤ β i}).linearIndependent.comp
      (fun t : {j : Fin n // γ j ≤ b ∧ a ≤ β (w j)} => (⟨w t, t.2.2⟩ : {i : Fin n // a ≤ β i}))
      (fun s t hst => Subtype.ext (w.injective (congrArg Subtype.val hst)))
    convert this using 1
    funext t
    simp [v, Pi.basisFun_apply]
  have hspan : Submodule.span F (Set.range Xᵀ) = Submodule.span F (Set.range v) := by
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨j, rfl⟩
      by_cases h : a ≤ β (w j)
      · apply Submodule.subset_span
        refine ⟨⟨j, j.2, h⟩, ?_⟩
        funext i
        simp only [hX, v, transpose_apply, submatrix_apply, permGL_apply, Pi.single_apply,
          Subtype.ext_iff]
      · have h0 : Xᵀ j = 0 := by
          funext i
          simp only [hX, transpose_apply, submatrix_apply, permGL_apply, Pi.zero_apply]
          rw [if_neg]
          intro hi
          exact h (hi ▸ i.2)
        rw [h0]
        exact zero_mem _
    · rw [Submodule.span_le]
      rintro _ ⟨t, rfl⟩
      apply Submodule.subset_span
      refine ⟨⟨t, t.2.1⟩, ?_⟩
      funext i
      simp only [hX, v, transpose_apply, submatrix_apply, permGL_apply, Pi.single_apply,
        Subtype.ext_iff]
  rw [show Set.range X.col = Set.range Xᵀ from rfl, hspan, finrank_span_eq_card hv,
    Fintype.card_subtype]
end GroundTheory.Automorphic.Parabolic
