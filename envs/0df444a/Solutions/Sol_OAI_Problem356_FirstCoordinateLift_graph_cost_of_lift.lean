-- Prove2me | solution 1 for OAI.Problem356.FirstCoordinateLift.graph_cost_of_lift
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T21:36:18.467147+00:00
-- url     : https://prove2.me/submissions/fcf869e0-5d2e-46e1-8909-f097d1d53ddb

import Mathlib
import Definitions.Def_CoulombCounterexample
import Definitions.Def_OAI_Analysis_CoulombTransport_AxisHessian
import Definitions.Def_OAI_Analysis_CoulombTransport_BranchCoupling
import Definitions.Def_OAI_Analysis_CoulombTransport_CoulombEstimates
import Definitions.Def_OAI_Analysis_CoulombTransport_BranchSeparation
import Definitions.Def_OAI_Analysis_CoulombTransport_GraphBridge
import Definitions.Def_OAI_Analysis_CoulombTransport_DualCertificate
import Definitions.Def_OAI_Analysis_CoulombTransport_OptimalLocalization
import Definitions.Def_OAI_Analysis_CoulombTransport_Calibration
import Definitions.Def_OAI_Analysis_CoulombTransport_CertificateAttainment
import Definitions.Def_OAI_Analysis_CoulombTransport_SplitMeasure
import Definitions.Def_OAI_Analysis_CoulombTransport_PartitionLabel
import Definitions.Def_OAI_Analysis_CoulombTransport_CenterCertificate
import Definitions.Def_OAI_Analysis_CoulombTransport_CommonBranches

open OAI OAI.Problem356
open MeasureTheory
open scoped ENNReal
open CoulombEstimates
theorem ap_inv_diff {eta a b c : ℝ} (heta : 0 < eta) (ha : eta ≤ a) (hb : eta ≤ b)
    (hab : |a - b| ≤ c) : |a⁻¹ - b⁻¹| ≤ c / eta ^ 2 := by
  have ha0 : 0 < a := lt_of_lt_of_le heta ha
  have hb0 : 0 < b := lt_of_lt_of_le heta hb
  have hc : 0 ≤ c := le_trans (abs_nonneg _) hab
  have e : a⁻¹ - b⁻¹ = (b - a) / (a * b) := by field_simp
  rw [e, abs_div, abs_of_pos (mul_pos ha0 hb0), abs_sub_comm]
  calc |a - b| / (a * b) ≤ c / (a * b) := by gcongr
    _ ≤ c / eta ^ 2 := by
      apply div_le_div_of_nonneg_left hc (by positivity)
      rw [sq]; exact mul_le_mul ha hb heta.le ha0.le

theorem ap_dist_diff {E : Type*} [PseudoMetricSpace E] {x y x' y' : E} {delta : ℝ}
    (hx : dist x x' ≤ delta) (hy : dist y y' ≤ delta) :
    |dist x y - dist x' y'| ≤ 2 * delta := by
  have := dist_dist_dist_le x y x' y'
  rw [Real.dist_eq] at this
  linarith

theorem ap_abs_realCost {E : Type*} [PseudoMetricSpace E]
    {x y z x' y' z' : E} {eta delta : ℝ}
    (heta : 0 < eta)
    (hxy : eta ≤ dist x y) (hxz : eta ≤ dist x z) (hyz : eta ≤ dist y z)
    (hxy' : eta ≤ dist x' y') (hxz' : eta ≤ dist x' z') (hyz' : eta ≤ dist y' z')
    (hx : dist x x' ≤ delta) (hy : dist y y' ≤ delta) (hz : dist z z' ≤ delta) :
    |realCost x y z - realCost x' y' z'| ≤ (6 * delta) / eta ^ 2 := by
  unfold realCost
  have h1 := ap_inv_diff heta hxy hxy' (ap_dist_diff hx hy)
  have h2 := ap_inv_diff heta hxz hxz' (ap_dist_diff hx hz)
  have h3 := ap_inv_diff heta hyz hyz' (ap_dist_diff hy hz)
  have e : (dist x y)⁻¹ + (dist x z)⁻¹ + (dist y z)⁻¹ - ((dist x' y')⁻¹ + (dist x' z')⁻¹ + (dist y' z')⁻¹)
    = ((dist x y)⁻¹ - (dist x' y')⁻¹) + ((dist x z)⁻¹ - (dist x' z')⁻¹) + ((dist y z)⁻¹ - (dist y' z')⁻¹) := by ring
  rw [e]
  calc _ ≤ |(dist x y)⁻¹ - (dist x' y')⁻¹| + |(dist x z)⁻¹ - (dist x' z')⁻¹| + |(dist y z)⁻¹ - (dist y' z')⁻¹| :=
        abs_add_three _ _ _
    _ ≤ 2 * delta / eta ^ 2 + 2 * delta / eta ^ 2 + 2 * delta / eta ^ 2 := by gcongr
    _ = 6 * delta / eta ^ 2 := by ring

theorem ap_invDistance {x y : E3} (h : 0 < dist x y) :
    invDistance x y = ENNReal.ofReal (dist x y)⁻¹ := by
  unfold invDistance
  rw [← dist_eq_norm, ENNReal.ofReal_inv_of_pos h]

theorem ap_coulomb_eq {x y z : E3} (h1 : 0 < dist x y) (h2 : 0 < dist x z) (h3 : 0 < dist y z) :
    coulombCost (x, (y, z)) = ENNReal.ofReal (realCost x y z) := by
  unfold coulombCost realCost tripleFst tripleSnd tripleThd
  simp only
  rw [ap_invDistance h1, ap_invDistance h2, ap_invDistance h3,
    ENNReal.ofReal_add (by positivity) (by positivity),
    ENNReal.ofReal_add (by positivity) (by positivity)]

open OAI OAI.Problem356 CoulombEstimates in
theorem ap_cost_le {x y z x' y' z' : E3} {eta delta : ℝ}
    (heta : 0 < eta)
    (hxy : eta ≤ dist x y) (hxz : eta ≤ dist x z) (hyz : eta ≤ dist y z)
    (hxy' : eta ≤ dist x' y') (hxz' : eta ≤ dist x' z') (hyz' : eta ≤ dist y' z')
    (hx : dist x x' ≤ delta) (hy : dist y y' ≤ delta) (hz : dist z z' ≤ delta) :
    coulombCost (x, (y, z)) ≤ coulombCost (x', (y', z')) +
      ENNReal.ofReal ((6 * delta) / eta ^ 2) := by
  have hd := ap_abs_realCost heta hxy hxz hyz hxy' hxz' hyz' hx hy hz
  rw [ap_coulomb_eq (by linarith) (by linarith) (by linarith),
    ap_coulomb_eq (by linarith) (by linarith) (by linarith)]
  have hnn : 0 ≤ realCost x' y' z' := by unfold realCost; positivity
  have hc : 0 ≤ 6 * delta / eta ^ 2 := le_trans (abs_nonneg _) hd
  rw [← ENNReal.ofReal_add hnn hc]
  apply ENNReal.ofReal_le_ofReal
  have := (abs_le.mp hd).2
  linarith

open OAI OAI.Problem356 in
theorem ap_cost_cont : Continuous coulombCost := by
  have hc : ∀ (f g : Triple → E3), Continuous f → Continuous g →
      Continuous (fun t => (ENNReal.ofReal ‖f t - g t‖)⁻¹) := fun f g hf hg =>
    continuous_inv.comp (ENNReal.continuous_ofReal.comp (hf.sub hg).norm)
  unfold coulombCost invDistance tripleFst tripleSnd tripleThd
  exact ((hc _ _ continuous_fst (continuous_fst.comp continuous_snd)).add
    (hc _ _ continuous_fst (continuous_snd.comp continuous_snd))).add
    (hc _ _ (continuous_fst.comp continuous_snd) (continuous_snd.comp continuous_snd))

theorem solution {μ : Measure E3} [IsProbabilityMeasure μ]
    {π : Measure Triple} (hπ : IsThreeCoupling μ π)
    {Q : E3 → Triple} (hQ : Measurable Q) (hmap : Measure.map Q μ = π)
    {η δ : ℝ} (hη : 0 < η) (hδ : δ ≤ η / 2)
    (hsep : ∀ᵐ t ∂π, Separated η t)
    (hclose : ∀ᵐ x ∂μ, dist x (Q x).1 ≤ δ) :
    Preserves μ (tripleSnd ∘ Q) ∧ Preserves μ (tripleThd ∘ Q) ∧
      graphCost μ (tripleSnd ∘ Q) (tripleThd ∘ Q) < ⊤ ∧
      graphCost μ (tripleSnd ∘ Q) (tripleThd ∘ Q) ≤
        (∫⁻ t, coulombCost t ∂π) + ENNReal.ofReal (24 * δ / η ^ 2) := by
  have hm2 : Measurable (tripleSnd ∘ Q) := by
    unfold tripleSnd; exact (measurable_fst.comp measurable_snd).comp hQ
  have hm3 : Measurable (tripleThd ∘ Q) := by
    unfold tripleThd; exact (measurable_snd.comp measurable_snd).comp hQ
  have hs2 : Measurable tripleSnd := by unfold tripleSnd; exact measurable_fst.comp measurable_snd
  have hs3 : Measurable tripleThd := by unfold tripleThd; exact measurable_snd.comp measurable_snd
  have hP2 : Preserves μ (tripleSnd ∘ Q) := by
    refine ⟨hm2, ?_⟩
    rw [← Measure.map_map hs2 hQ, hmap]; exact hπ.2.2.1
  have hP3 : Preserves μ (tripleThd ∘ Q) := by
    refine ⟨hm3, ?_⟩
    rw [← Measure.map_map hs3 hQ, hmap]; exact hπ.2.2.2
  have hsepQ : ∀ᵐ x ∂μ, Separated η (Q x) := by
    rw [← hmap] at hsep
    exact ae_of_ae_map hQ.aemeasurable hsep
  have hη2 : 0 < η / 2 := by linarith
  -- pointwise estimate
  have hpt : ∀ᵐ x ∂μ, coulombCost (x, ((tripleSnd ∘ Q) x, (tripleThd ∘ Q) x)) ≤
      coulombCost (Q x) + ENNReal.ofReal (24 * δ / η ^ 2) ∧
      coulombCost (x, ((tripleSnd ∘ Q) x, (tripleThd ∘ Q) x)) ≤
      ENNReal.ofReal (6 / η) := by
    filter_upwards [hsepQ, hclose] with x hx hcx
    obtain ⟨h1, h2, h3⟩ := hx
    have hδ0 : 0 ≤ δ := le_trans dist_nonneg hcx
    have d1 : η / 2 ≤ dist x (Q x).2.1 := by
      have := dist_triangle (Q x).1 x (Q x).2.1
      rw [dist_comm] at hcx; linarith
    have d2 : η / 2 ≤ dist x (Q x).2.2 := by
      have := dist_triangle (Q x).1 x (Q x).2.2
      rw [dist_comm] at hcx; linarith
    have d3 : η / 2 ≤ dist (Q x).2.1 (Q x).2.2 := by linarith
    simp only [Function.comp, tripleSnd, tripleThd]
    constructor
    · have := ap_cost_le (y := (Q x).2.1) (z := (Q x).2.2) (y' := (Q x).2.1) (z' := (Q x).2.2)
        hη2 d1 d2 d3 (by linarith) (by linarith) (by linarith) hcx
        (by simp [hδ0]) (by simp [hδ0])
      have e : 6 * δ / (η / 2) ^ 2 = 24 * δ / η ^ 2 := by field_simp; ring
      rw [e] at this
      simpa using this
    · rw [ap_coulomb_eq (by linarith) (by linarith) (by linarith)]
      apply ENNReal.ofReal_le_ofReal
      unfold realCost
      have i1 : (dist x (Q x).2.1)⁻¹ ≤ (η / 2)⁻¹ := inv_anti₀ hη2 d1
      have i2 : (dist x (Q x).2.2)⁻¹ ≤ (η / 2)⁻¹ := inv_anti₀ hη2 d2
      have i3 : (dist (Q x).2.1 (Q x).2.2)⁻¹ ≤ (η / 2)⁻¹ := inv_anti₀ hη2 d3
      have e : (η / 2)⁻¹ = 2 / η := by field_simp
      rw [e] at i1 i2 i3
      have : 2 / η + 2 / η + 2 / η = 6 / η := by ring
      linarith
  refine ⟨hP2, hP3, ?_, ?_⟩
  · unfold graphCost
    calc _ ≤ ∫⁻ _, ENNReal.ofReal (6 / η) ∂μ := lintegral_mono_ae (hpt.mono fun x hx => hx.2)
      _ < ⊤ := by simp
  · unfold graphCost
    calc _ ≤ ∫⁻ x, (coulombCost (Q x) + ENNReal.ofReal (24 * δ / η ^ 2)) ∂μ :=
          lintegral_mono_ae (hpt.mono fun x hx => hx.1)
      _ = (∫⁻ x, coulombCost (Q x) ∂μ) + ENNReal.ofReal (24 * δ / η ^ 2) := by
          rw [lintegral_add_right _ measurable_const]; simp
      _ = _ := by
          rw [← hmap, lintegral_map ap_cost_cont.measurable hQ]

