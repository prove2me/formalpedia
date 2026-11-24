-- Prove2me | solution 1 for GlobalTheory.exists_mul_eq_smul_one_of_mulVec_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:44:53.14856+00:00
-- url     : https://prove2.me/submissions/45a3f79d-5fd1-45a4-a22f-fc36069d6a24

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsMulEqSmulOneOfMulVecInjective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {R K : Type} [CommRing R] [Field K]
    (g : R →+* K) {m l : Type} [Fintype m] [Fintype l] [DecidableEq l] (M : Matrix m l R)
    (hM : ∀ x : l → K, (M.map g).mulVec x = 0 → x = 0) :
    ∃ (r : R) (T : Matrix l m R), g r ≠ 0 ∧ T * M = r • (1 : Matrix l l R) := by
  classical
  obtain ⟨κ, a, ha, hspan, hli⟩ := exists_linearIndependent' K (fun i : m => (M.map g) i)
  have : Fintype κ := Fintype.ofInjective a ha
  have h1 : Fintype.card κ ≤ Fintype.card l := by
    have := hli.fintype_card_le_finrank
    simpa using this
  have h2 : Fintype.card l ≤ Fintype.card κ := by
    have hinj : Function.Injective (Matrix.mulVecLin ((M.map g).submatrix a id)) := by
      rw [injective_iff_map_eq_zero]
      intro x hx
      apply hM
      funext i
      have hi : (M.map g) i ∈ Submodule.span K (Set.range ((fun i : m => (M.map g) i) ∘ a)) := by
        rw [hspan]; exact Submodule.subset_span ⟨i, rfl⟩
      have key : ∀ y ∈ Submodule.span K (Set.range ((fun i : m => (M.map g) i) ∘ a)),
          y ⬝ᵥ x = 0 := by
        intro y hy
        induction hy using Submodule.span_induction with
        | mem y hy =>
          obtain ⟨k, rfl⟩ := hy
          exact congrFun hx k
        | zero => simp
        | add y z _ _ hy hz => rw [add_dotProduct, hy, hz, add_zero]
        | smul c y _ hy => rw [smul_dotProduct, hy, smul_zero]
      exact key _ hi
    have := LinearMap.finrank_le_finrank_of_injective hinj
    simpa using this
  let e : l ≃ κ := Fintype.equivOfCardEq (le_antisymm h2 h1)
  let N : Matrix l l R := M.submatrix (a ∘ e) id
  have hN : IsUnit (N.map g) := by
    rw [← Matrix.linearIndependent_rows_iff_isUnit]
    exact hli.comp e e.injective
  refine ⟨N.det, N.adjugate * (1 : Matrix m m R).submatrix (a ∘ e) id, ?_, ?_⟩
  · rw [Matrix.isUnit_iff_isUnit_det] at hN
    have : g N.det = (N.map g).det := by rw [RingHom.map_det]; rfl
    rw [this]; exact hN.ne_zero
  · rw [Matrix.mul_assoc]
    have : (1 : Matrix m m R).submatrix (a ∘ e) id * M = N := by
      ext i j
      simp [N, Matrix.mul_apply, Matrix.one_apply]
    rw [this, Matrix.adjugate_mul]
end GlobalTheory
