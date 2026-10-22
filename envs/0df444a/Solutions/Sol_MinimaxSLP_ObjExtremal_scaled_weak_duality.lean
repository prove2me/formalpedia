-- Prove2me | solution 1 for MinimaxSLP.ObjExtremal.scaled_weak_duality
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T15:18:57.114298+00:00
-- url     : https://prove2.me/submissions/0a556026-8f97-4486-9e45-1e1c3464f790

import Mathlib
import Definitions.Def_MomentDRO_Conf_Setting
import Definitions.Def_MinimaxSLP_ObjExtremal_Model
set_option autoImplicit false
open MeasureTheory Matrix Filter Topology

theorem solution {n r d : ℕ}
    (W : Matrix (Fin r) (Fin d) ℝ) (T : Matrix (Fin r) (Fin n) ℝ) (h : Fin r → ℝ)
    (hA3 : ∀ q : Fin d → ℝ, ∃ π : Fin r → ℝ, Wᵀ *ᵥ π ≤ q)
    (x : Fin n → ℝ) (hrec : (MinimaxSLP.ObjSDP.recourseSet W T h x).Nonempty)
    (a : ℝ) (ha : 0 ≤ a) (v : Fin d → ℝ) (π : Fin r → ℝ) (hπ : Wᵀ *ᵥ π ≤ a • v) :
    (h - T *ᵥ x) ⬝ᵥ π ≤ a * MinimaxSLP.ObjSDP.Qval W T h v x := by
  have key : ∀ w ∈ MinimaxSLP.ObjSDP.recourseSet W T h x,
      (h - T *ᵥ x) ⬝ᵥ π ≤ a * (v ⬝ᵥ w) := by
    intro w hw
    obtain ⟨hw1, hw2⟩ := hw
    have e1 : (h - T *ᵥ x) ⬝ᵥ π = (Wᵀ *ᵥ π) ⬝ᵥ w := by
      rw [← hw1, dotProduct_comm, Matrix.dotProduct_mulVec, Matrix.mulVec_transpose]
    rw [e1]
    calc (Wᵀ *ᵥ π) ⬝ᵥ w ≤ (a • v) ⬝ᵥ w := dotProduct_le_dotProduct_of_nonneg_right hπ hw2
      _ = a * (v ⬝ᵥ w) := by rw [smul_dotProduct, smul_eq_mul]
  unfold MinimaxSLP.ObjSDP.Qval
  rcases ha.eq_or_lt with h0 | hpos
  · obtain ⟨w, hw⟩ := hrec
    have := key w hw
    rw [← h0] at this ⊢
    simpa using this
  · have hne : ((fun w => v ⬝ᵥ w) '' MinimaxSLP.ObjSDP.recourseSet W T h x).Nonempty :=
      hrec.image _
    have : ((h - T *ᵥ x) ⬝ᵥ π) / a ≤ sInf ((fun w => v ⬝ᵥ w) '' MinimaxSLP.ObjSDP.recourseSet W T h x) := by
      apply le_csInf hne
      rintro _ ⟨w, hw, rfl⟩
      rw [div_le_iff₀ hpos]
      have := key w hw
      linarith
    rw [div_le_iff₀ hpos] at this
    linarith
