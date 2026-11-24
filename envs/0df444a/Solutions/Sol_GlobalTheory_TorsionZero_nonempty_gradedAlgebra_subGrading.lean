-- Prove2me | solution 1 for GlobalTheory.TorsionZero.nonempty_gradedAlgebra_subGrading
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:32:59.542113+00:00
-- url     : https://prove2.me/submissions/df3de171-3396-496e-bdf7-3dc4e712daa3

import Mathlib
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_PolynomialHeights_HeightAddRingKrullDimQuotientMvPolynomialField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaFamilyOrigin_NonemptyGradedAlgebraSubGrading
import Theorems.Thm_GlobalTheory_TorsionZero_mem_subGrading

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.TorsionZero
open MvPolynomial
variable {K R : Type} [Field K] [CommRing R] [Algebra K R]
namespace GlobalTheory.TorsionZero
theorem _root_.solution (𝒜 : ℕ → Submodule K R) [GradedAlgebra 𝒜] {N : ℕ}
    (hN : 1 ≤ N) (S : Set R) (hS : ∀ y ∈ S, ∃ e, y ∈ 𝒜 (N * e)) :
    Nonempty (GradedAlgebra (subGrading 𝒜 N (Algebra.adjoin K S))) := by
  classical
  set T := Algebra.adjoin K S with hT
  haveI gm : SetLike.GradedMonoid (subGrading 𝒜 N T) :=
    { one_mem := by
        rw [mem_subGrading]
        simpa using SetLike.one_mem_graded 𝒜
      mul_mem := fun i j a b ha hb => by
        rw [mem_subGrading] at ha hb ⊢
        simpa [mul_add] using SetLike.mul_mem_graded ha hb }
  have hind : iSupIndep (subGrading 𝒜 N T) := by
    have h0 : iSupIndep 𝒜 := (DirectSum.Decomposition.isInternal 𝒜).submodule_iSupIndep
    have h1 : iSupIndep (fun e => 𝒜 (N * e)) :=
      h0.comp (f := fun e => N * e) fun a b h => Nat.eq_of_mul_eq_mul_left hN h
    intro e
    rw [Submodule.disjoint_def]
    intro y hy hy'
    refine Subtype.ext ((Submodule.disjoint_def.1 (h1 e)) _ hy ?_)
    have : (⨆ j, ⨆ (_ : j ≠ e), subGrading 𝒜 N T j) ≤
        (⨆ j, ⨆ (_ : j ≠ e), 𝒜 (N * j)).comap T.val.toLinearMap :=
      iSup₂_le fun j hj => Submodule.comap_mono (le_iSup₂ (f := fun j (_ : j ≠ e) => 𝒜 (N * j)) j hj)
    exact this hy'
  have htop : ⨆ e, subGrading 𝒜 N T e = ⊤ := by
    rw [eq_top_iff]
    rintro ⟨y, hy⟩ -
    induction hy using Algebra.adjoin_induction with
    | mem y hy =>
      obtain ⟨e, he⟩ := hS y hy
      exact Submodule.mem_iSup_of_mem e he
    | algebraMap r =>
      refine Submodule.mem_iSup_of_mem 0 ?_
      rw [mem_subGrading]
      simpa using SetLike.algebraMap_mem_graded 𝒜 r
    | add a b ha hb h1 h2 => exact add_mem h1 h2
    | mul a b ha hb h1 h2 =>
      change (⟨a, ha⟩ : T) * ⟨b, hb⟩ ∈ _
      generalize (⟨a, ha⟩ : T) = u at h1
      generalize (⟨b, hb⟩ : T) = v at h2
      induction h1 using Submodule.iSup_induction' with
      | mem i u hu =>
        induction h2 using Submodule.iSup_induction' with
        | mem j v hv => exact Submodule.mem_iSup_of_mem (i + j) (SetLike.mul_mem_graded hu hv)
        | zero => simp
        | add v w _ _ hv hw => rw [mul_add]; exact add_mem hv hw
      | zero => simp
      | add v w _ _ hv hw => rw [add_mul]; exact add_mem hv hw
  exact ⟨{ gm, ((DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top _).2
    ⟨hind, htop⟩).chooseDecomposition with }⟩
end GlobalTheory.TorsionZero
