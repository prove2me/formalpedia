-- Prove2me | solution 1 for GlobalTheory.HermWitt.exists_isometry_of_orthogonal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T17:29:29.549799+00:00
-- url     : https://prove2.me/submissions/a98e0239-388e-4a16-855e-6543e764fd15

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_ExistsOrthogonalBasisDotProductApplyEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_ExistsGlIsometryCompEqOfNondegenerate
import Theorems.Thm_GlobalTheory_HermWitt_exists_isometry_apply_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.HermWitt
open Module Matrix GlobalTheory.HermDiag
variable {E : Type*} [Field E] {c : E →+* E} {V : Type*} [AddCommGroup V] [Module E V]
namespace GlobalTheory.HermWitt
theorem _root_.solution (h2 : (2 : E) ≠ 0) {B : V →ₗ[E] V →ₛₗ[c] E}
    (hB : ∀ x y, c (B x y) = B y x) {ι : Type*} [Finite ι] {x y : ι → V}
    (hx : ∀ i j, i ≠ j → B (x i) (x j) = 0) (hy : ∀ i j, i ≠ j → B (y i) (y j) = 0)
    (hxy : ∀ i, B (x i) (x i) = B (y i) (y i)) (hne : ∀ i, B (x i) (x i) ≠ 0) :
    ∃ γ : V ≃ₗ[E] V, (∀ z w, B (γ z) (γ w) = B z w) ∧ ∀ i, γ (x i) = y i := by
  classical
  have := Fintype.ofFinite ι
  have key : ∀ s : Finset ι,
      ∃ γ : V ≃ₗ[E] V, (∀ z w, B (γ z) (γ w) = B z w) ∧ ∀ i ∈ s, γ (x i) = y i := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact ⟨LinearEquiv.refl E V, fun _ _ => rfl, by simp⟩
    | insert i s hi ih =>
      obtain ⟨γ, hγ, e⟩ := ih
      obtain ⟨δ, hδ, e', f⟩ := exists_isometry_apply_eq h2 hB (x := γ (x i)) (y := y i)
        (by rw [hγ, hxy]) (by rw [hγ]; exact hne i)
      refine ⟨γ.trans δ, fun z w => ?_, fun j hj => ?_⟩
      · rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply, hδ, hγ]
      · rw [LinearEquiv.trans_apply]
        rcases Finset.mem_insert.1 hj with rfl | hj
        · exact e'
        · have hji : j ≠ i := fun h => hi (h ▸ hj)
          rw [f _ (by rw [hγ]; exact hx j i hji) (by rw [e j hj]; exact hy j i hji), e j hj]
  obtain ⟨γ, hγ, e⟩ := key Finset.univ
  exact ⟨γ, hγ, fun i => e i (Finset.mem_univ i)⟩
end GlobalTheory.HermWitt
