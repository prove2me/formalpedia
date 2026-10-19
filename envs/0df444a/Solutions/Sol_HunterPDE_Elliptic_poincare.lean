-- Prove2me | solution 1 for HunterPDE.Elliptic.poincare
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-18T21:16:14.037239+00:00
-- url     : https://prove2.me/submissions/d5ec7c88-00a0-4485-a166-b062f7de2823

import Definitions.Def_HunterPDE_Elliptic_H10
import Theorems.Thm_HunterPDE_Elliptic_span_testJets
import Theorems.Thm_HunterPDE_Elliptic_smooth_slab_poincare

open MeasureTheory HunterPDE.Elliptic
set_option autoImplicit false

theorem solution {n : ℕ} (Ω : Set (EuclideanSpace ℝ (Fin n))) (hΩ : IsOpen Ω)
    (hΩd : BoundedInSomeDirection Ω) :
    ∃ C : ℝ, ∀ u : H10 n Ω,
      ∫ x in Ω, val u x ^ 2 ≤ C * ∫ x in Ω, ‖grad u x‖ ^ 2 := by
  obtain ⟨e, he, a, b, hab⟩ := hΩd
  let P := (WithLp.fstL 2 ℝ ℝ (EuclideanSpace ℝ (Fin n))).compLpL 2 (volume.restrict Ω)
  let Q := (WithLp.sndL 2 ℝ ℝ (EuclideanSpace ℝ (Fin n))).compLpL 2 (volume.restrict Ω)
  have energyP (F : JetL2 n Ω) :
      ∫ x in Ω, (WithLp.ofLp (F x)).1 ^ 2 = ‖P F‖ ^ 2 := by
    calc
      _ = ∫ x in Ω, inner ℝ (P F x) (P F x) := by
        apply integral_congr_ae
        filter_upwards [(WithLp.fstL 2 ℝ ℝ (EuclideanSpace ℝ (Fin n))).coeFn_compLpL F] with x hx
        simp [P, hx, real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs]
      _ = inner ℝ (P F) (P F) := (L2.inner_def _ _).symm
      _ = ‖P F‖ ^ 2 := real_inner_self_eq_norm_sq _
  have energyQ (F : JetL2 n Ω) :
      ∫ x in Ω, ‖(WithLp.ofLp (F x)).2‖ ^ 2 = ‖Q F‖ ^ 2 := by
    calc
      _ = ∫ x in Ω, inner ℝ (Q F x) (Q F x) := by
        apply integral_congr_ae
        filter_upwards [(WithLp.sndL 2 ℝ ℝ (EuclideanSpace ℝ (Fin n))).coeFn_compLpL F] with x hx
        simp [Q, hx, real_inner_self_eq_norm_sq]
      _ = inner ℝ (Q F) (Q F) := (L2.inner_def _ _).symm
      _ = ‖Q F‖ ^ 2 := real_inner_self_eq_norm_sq _
  let S : Set (JetL2 n Ω) := {F | ‖P F‖ ^ 2 ≤ (b-a)^2 * ‖Q F‖ ^ 2}
  have hclosed : IsClosed S :=
    isClosed_le (P.continuous.norm.pow 2) (continuous_const.mul (Q.continuous.norm.pow 2))
  have htest : testJets n Ω ⊆ S := by
    rintro F ⟨φ, hφ, hc, hs, hF⟩
    change ‖P F‖ ^ 2 ≤ (b-a)^2 * ‖Q F‖ ^ 2
    rw [← energyP, ← energyQ]
    have hp := HunterPDE.Elliptic.smooth_slab_poincare Ω hΩ e he a b hab φ hφ hc hs
    convert hp using 1
    · apply integral_congr_ae
      filter_upwards [hF] with x hx
      simp [hx]
    · congr 1
      apply integral_congr_ae
      filter_upwards [hF] with x hx
      simp [hx]
  refine ⟨(b-a)^2, fun u => ?_⟩
  have hu := u.property
  change (u : JetL2 n Ω) ∈ closure (↑(Submodule.span ℝ (testJets n Ω)) : Set (JetL2 n Ω)) at hu
  rw [HunterPDE.Elliptic.span_testJets Ω] at hu
  have h := closure_minimal htest hclosed hu
  change ‖P (u : JetL2 n Ω)‖ ^ 2 ≤ (b-a)^2 * ‖Q (u : JetL2 n Ω)‖ ^ 2 at h
  simpa only [← energyP, ← energyQ, val, grad] using h
