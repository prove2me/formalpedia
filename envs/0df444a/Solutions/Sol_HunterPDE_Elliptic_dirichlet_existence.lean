-- Prove2me | solution 1 for HunterPDE.Elliptic.dirichlet_existence
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-20T13:27:11.804289+00:00
-- url     : https://prove2.me/submissions/2811c03d-d80b-4eee-a711-0cbb05e717e7

import Definitions.Def_HunterPDE_Elliptic_H10
import Theorems.Thm_HunterPDE_Elliptic_poincare
import Theorems.Thm_HunterPDE_Elliptic_lax_milgram
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

open MeasureTheory HunterPDE.Elliptic
set_option autoImplicit false

theorem solution {n : ℕ} (Ω : Set (EuclideanSpace ℝ (Fin n))) (hΩ : IsOpen Ω)
    (hΩd : BoundedInSomeDirection Ω) (f : StrongDual ℝ (H10 n Ω)) :
    ∃! u : H10 n Ω, ∀ φ : H10 n Ω, ∫ x in Ω, inner ℝ (grad u x) (grad φ x) = f φ := by
  let : CompleteSpace (H10 n Ω) :=
    (Submodule.isClosed_topologicalClosure _).completeSpace_coe
  let P := (WithLp.fstL 2 ℝ ℝ (EuclideanSpace ℝ (Fin n))).compLpL 2 (volume.restrict Ω)
  let Q := (WithLp.sndL 2 ℝ ℝ (EuclideanSpace ℝ (Fin n))).compLpL 2 (volume.restrict Ω)
  let G := Q.comp (H10 n Ω).subtypeL
  have energyP (u : H10 n Ω) : ∫ x in Ω, val u x ^ 2 = ‖P (u : JetL2 n Ω)‖ ^ 2 := by
    calc
      _ = ∫ x in Ω, inner ℝ (P (u : JetL2 n Ω) x) (P (u : JetL2 n Ω) x) := by
        apply integral_congr_ae
        filter_upwards [(WithLp.fstL 2 ℝ ℝ (EuclideanSpace ℝ (Fin n))).coeFn_compLpL (u : JetL2 n Ω)] with x hx
        simp [P, hx, val, Real.norm_eq_abs, sq_abs]
      _ = _ := by rw [← L2.inner_def, real_inner_self_eq_norm_sq]
  have pairing (u v : H10 n Ω) :
      ∫ x in Ω, inner ℝ (grad u x) (grad v x) = inner ℝ (G u) (G v) := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [(WithLp.sndL 2 ℝ ℝ (EuclideanSpace ℝ (Fin n))).coeFn_compLpL (u : JetL2 n Ω),
      (WithLp.sndL 2 ℝ ℝ (EuclideanSpace ℝ (Fin n))).coeFn_compLpL (v : JetL2 n Ω)] with x hu hv
    simp [G, Q, grad, hu, hv]
  have splitting (u : H10 n Ω) : ‖u‖ ^ 2 = ‖P (u : JetL2 n Ω)‖ ^ 2 + ‖G u‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq]
    change inner ℝ (u : JetL2 n Ω) (u : JetL2 n Ω) = _
    rw [L2.inner_def, L2.inner_def, L2.inner_def, ← integral_add (L2.integrable_inner _ _) (L2.integrable_inner _ _)]
    apply integral_congr_ae
    filter_upwards [(WithLp.fstL 2 ℝ ℝ (EuclideanSpace ℝ (Fin n))).coeFn_compLpL (u : JetL2 n Ω),
      (WithLp.sndL 2 ℝ ℝ (EuclideanSpace ℝ (Fin n))).coeFn_compLpL (u : JetL2 n Ω)] with x hp hq
    simp [WithLp.prod_norm_sq_eq_of_L2, G, P, Q, hp, hq, Real.norm_eq_abs, sq_abs]
  let a : H10 n Ω →ₗ[ℝ] H10 n Ω →ₗ[ℝ] ℝ :=
    ((innerₛₗ ℝ).compl₂ G.toLinearMap).comp G.toLinearMap
  have ha (u v : H10 n Ω) : a u v = inner ℝ (G u) (G v) := rfl
  obtain ⟨C, hC⟩ := HunterPDE.Elliptic.poincare Ω hΩ hΩd
  have bound (u : H10 n Ω) : ‖u‖ ^ 2 ≤ (max C 0 + 1) * ‖G u‖ ^ 2 := by
    have h := hC u
    rw [energyP] at h
    have eqg : (∫ x in Ω, ‖grad u x‖ ^ 2) = ‖G u‖ ^ 2 := by
      simpa only [real_inner_self_eq_norm_sq] using pairing u u
    rw [eqg] at h
    have hc := mul_le_mul_of_nonneg_right (le_max_left C 0) (sq_nonneg ‖G u‖)
    rw [splitting]
    nlinarith
  have hpos : 0 < max C 0 + 1 := by positivity
  have hcoerc (u : H10 n Ω) : (max C 0 + 1)⁻¹ * ‖u‖ ^ 2 ≤ a u u := by
    rw [ha, real_inner_self_eq_norm_sq, ← div_eq_inv_mul]
    exact (div_le_iff₀ hpos).2 (by simpa [mul_comm] using bound u)
  have hbounded (u v : H10 n Ω) : |a u v| ≤ 1 * ‖u‖ * ‖v‖ := by
    have normG (w : H10 n Ω) : ‖G w‖ ≤ ‖w‖ := by
      have := splitting w
      nlinarith [sq_nonneg ‖P (w : JetL2 n Ω)‖, norm_nonneg (G w), norm_nonneg w]
    rw [ha, one_mul]
    exact (abs_real_inner_le_norm _ _).trans (mul_le_mul (normG u) (normG v) (norm_nonneg _) (norm_nonneg _))
  obtain ⟨u, hu, huniq⟩ := HunterPDE.Elliptic.lax_milgram a (max C 0 + 1)⁻¹ 1
    (inv_pos.mpr hpos) zero_lt_one hcoerc hbounded f
  refine ⟨u, fun v => ?_, fun w hw => ?_⟩
  · rw [pairing, ← ha]
    exact (hu v).symm
  · apply huniq w
    intro v
    rw [ha, ← pairing]
    exact (hw v).symm
