-- Prove2me | solution 1 for MinimaxSLP.ObjExtremal.Qval_homogeneous_superadditive
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T15:30:47.981839+00:00
-- url     : https://prove2.me/submissions/e17225bc-8fee-40d8-917f-450e183a3bf2

import Mathlib
import Definitions.Def_MomentDRO_Conf_Setting
import Definitions.Def_MinimaxSLP_ObjExtremal_Model
set_option autoImplicit false
open MeasureTheory Matrix Filter Topology
open scoped Pointwise

theorem solution {n r d : ℕ}
    (W : Matrix (Fin r) (Fin d) ℝ) (T : Matrix (Fin r) (Fin n) ℝ) (h : Fin r → ℝ)
    (hA3 : ∀ q : Fin d → ℝ, ∃ π : Fin r → ℝ, Wᵀ *ᵥ π ≤ q)
    (x : Fin n → ℝ) (hrec : (MinimaxSLP.ObjSDP.recourseSet W T h x).Nonempty) :
    (∀ t : ℝ, 0 < t → ∀ q : Fin d → ℝ, MinimaxSLP.ObjSDP.Qval W T h (t • q) x = t * MinimaxSLP.ObjSDP.Qval W T h q x) ∧
    ∀ a c : Fin d → ℝ, MinimaxSLP.ObjSDP.Qval W T h a x + MinimaxSLP.ObjSDP.Qval W T h c x ≤ MinimaxSLP.ObjSDP.Qval W T h (a + c) x := by
  have hbdd : ∀ q : Fin d → ℝ,
      BddBelow ((fun w => q ⬝ᵥ w) '' MinimaxSLP.ObjSDP.recourseSet W T h x) := by
    intro q
    obtain ⟨π, hπ⟩ := hA3 q
    refine ⟨(h - T *ᵥ x) ⬝ᵥ π, ?_⟩
    rintro _ ⟨w, ⟨hw1, hw2⟩, rfl⟩
    have e1 : (h - T *ᵥ x) ⬝ᵥ π = (Wᵀ *ᵥ π) ⬝ᵥ w := by
      rw [← hw1, dotProduct_comm, Matrix.dotProduct_mulVec, Matrix.mulVec_transpose]
    rw [e1]
    exact dotProduct_le_dotProduct_of_nonneg_right hπ hw2
  constructor
  · intro t ht q
    unfold MinimaxSLP.ObjSDP.Qval
    have hset : (fun w => (t • q) ⬝ᵥ w) '' MinimaxSLP.ObjSDP.recourseSet W T h x =
        t • ((fun w => q ⬝ᵥ w) '' MinimaxSLP.ObjSDP.recourseSet W T h x) := by
      ext y
      constructor
      · rintro ⟨w, hw, rfl⟩
        exact ⟨q ⬝ᵥ w, ⟨w, hw, rfl⟩, by simp [smul_dotProduct]⟩
      · rintro ⟨_, ⟨w, hw, rfl⟩, rfl⟩
        exact ⟨w, hw, by simp [smul_dotProduct]⟩
    rw [hset, Real.sInf_smul_of_nonneg ht.le, smul_eq_mul]
  · intro a c
    unfold MinimaxSLP.ObjSDP.Qval
    apply le_csInf (hrec.image _)
    rintro _ ⟨w, hw, rfl⟩
    have h1 := csInf_le (hbdd a) ⟨w, hw, rfl⟩
    have h2 := csInf_le (hbdd c) ⟨w, hw, rfl⟩
    simp only [add_dotProduct]
    linarith
