-- Prove2me | solution 1 for MinimaxSLP.RhsSDP.dual_Y_posSemidef
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T22:59:14.453914+00:00
-- url     : https://prove2.me/submissions/ec3ef019-0cec-4e6b-8a5a-f39617311e5f

import Mathlib
import Definitions.Def_MomentDRO_Conf_Setting
import Definitions.Def_WorstCaseVaR_KnownMoments_Basic
import Definitions.Def_MinimaxSLP_RhsSDP_Model

open MeasureTheory Matrix

lemma Qval_ge_aux {r d n : ℕ} (W : Matrix (Fin r) (Fin d) ℝ) (T : Matrix (Fin r) (Fin n) ℝ)
    (q : Fin d → ℝ) (hA2 : ∀ z : Fin r → ℝ, ∃ w : Fin d → ℝ, 0 ≤ w ∧ W *ᵥ w = z)
    (x : Fin n → ℝ) (h π : Fin r → ℝ) (hπ : Wᵀ *ᵥ π ≤ q) :
    (h - T *ᵥ x) ⬝ᵥ π ≤ MinimaxSLP.RhsSDP.Qval W T q h x := by
  obtain ⟨w, hw0, hw⟩ := hA2 (h - T *ᵥ x)
  have hbd : BddAbove ((fun π => (h - T *ᵥ x) ⬝ᵥ π) '' {π : Fin r → ℝ | Wᵀ *ᵥ π ≤ q}) := by
    refine ⟨w ⬝ᵥ q, ?_⟩
    rintro v ⟨ρ, hρ, rfl⟩
    have e : (h - T *ᵥ x) ⬝ᵥ ρ = w ⬝ᵥ (Wᵀ *ᵥ ρ) := by
      rw [← hw, mulVec_transpose, dotProduct_comm, dotProduct_mulVec, dotProduct_comm]
    show (h - T *ᵥ x) ⬝ᵥ ρ ≤ w ⬝ᵥ q
    rw [e]
    exact dotProduct_le_dotProduct_of_nonneg_left hρ hw0
  exact le_csSup hbd ⟨π, hπ, rfl⟩

theorem solution {r d n K : ℕ} [NeZero K]
    (W : Matrix (Fin r) (Fin d) ℝ) (T : Matrix (Fin r) (Fin n) ℝ) (q : Fin d → ℝ)
    (α β : Fin K → ℝ)
    (hα : ∀ k, 0 ≤ α k)
    (hA2 : ∀ z : Fin r → ℝ, ∃ w : Fin d → ℝ, 0 ≤ w ∧ W *ᵥ w = z)
    (hA3 : ∃ π : Fin r → ℝ, Wᵀ *ᵥ π ≤ q)
    (x : Fin n → ℝ) (s : Matrix (Fin r) (Fin r) ℝ × (Fin r → ℝ) × ℝ)
    (hs : s ∈ MinimaxSLP.RhsSDP.dualFeasible12 W T q α β x) :
    s.1.PosSemidef := by
  obtain ⟨hY, hcon⟩ := hs
  obtain ⟨π0, hπ0⟩ := hA3
  rw [posSemidef_iff_dotProduct_mulVec]
  refine ⟨?_, fun v => ?_⟩
  · show s.1ᴴ = s.1
    rw [conjTranspose_eq_transpose_of_trivial]; exact hY
  simp only [star_trivial]
  by_contra hneg
  push Not at hneg
  set a := v ⬝ᵥ (s.1 *ᵥ v) with ha
  let k0 : Fin K := 0
  have key : ∀ t : ℝ, α k0 * (t * (v ⬝ᵥ π0) - (T *ᵥ x) ⬝ᵥ π0) + β k0 ≤
      t ^ 2 * a + t * (s.2.1 ⬝ᵥ v) + s.2.2 := by
    intro t
    have h1 := hcon (t • v)
    have h2 : α k0 * MinimaxSLP.RhsSDP.Qval W T q (t • v) x + β k0 ≤
        MinimaxSLP.ObjSDP.disutility α β (MinimaxSLP.RhsSDP.Qval W T q (t • v) x) := by
      unfold MinimaxSLP.ObjSDP.disutility
      exact Finset.le_sup' (fun k => α k * MinimaxSLP.RhsSDP.Qval W T q (t • v) x + β k)
        (Finset.mem_univ k0)
    have h3 := Qval_ge_aux W T q hA2 x (t • v) π0 hπ0
    have h4 : α k0 * ((t • v - T *ᵥ x) ⬝ᵥ π0) ≤ α k0 * MinimaxSLP.RhsSDP.Qval W T q (t • v) x :=
      mul_le_mul_of_nonneg_left h3 (hα k0)
    simp only [sub_dotProduct, smul_dotProduct, dotProduct_smul, mulVec_smul, smul_eq_mul]
      at h1 h4
    rw [ha]
    nlinarith
  set C := s.2.2 + α k0 * ((T *ᵥ x) ⬝ᵥ π0) - β k0 with hC
  have key2 : ∀ t : ℝ, 0 ≤ t ^ 2 * a + C := by
    intro t
    rw [hC]
    linear_combination (key t + key (-t)) / 2
  have hpos : 0 < (|C| + 1) / (-a) := div_pos (by positivity) (by linarith)
  have := key2 (Real.sqrt ((|C| + 1) / (-a)))
  rw [Real.sq_sqrt hpos.le] at this
  have e : (|C| + 1) / (-a) * a = -(|C| + 1) := by
    have ha0 : a ≠ 0 := hneg.ne
    field_simp
  rw [e] at this
  have := le_abs_self C
  linarith
