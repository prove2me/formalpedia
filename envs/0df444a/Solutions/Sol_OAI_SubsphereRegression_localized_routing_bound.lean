-- Prove2me | solution 1 for OAI.SubsphereRegression.localized_routing_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T08:16:53.296851+00:00
-- url     : https://prove2.me/submissions/1263b740-fa30-4d6d-a57c-f655fafc1e31

-- Generated from openai/math@1581d4c lean/OAI/Probability/Subsphere/Regression/Blocks.lean:L309-L337
-- (upload_full_project.md Phase 4): solution for node OAI.SubsphereRegression.localized_routing_bound. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_SubsphereCurrent
import Definitions.Def_OAI_Probability_Subsphere_Models
import Definitions.Def_OAI_Probability_Subsphere_Regression_Geometry
import Definitions.Def_OAI_Probability_Subsphere_Regression_Gram
import Definitions.Def_OAI_Probability_Subsphere_Regression_Gaussian
import Definitions.Def_OAI_Probability_Subsphere_Regression_Projection
import Definitions.Def_OAI_Probability_Subsphere_Regression_Model
import Definitions.Def_OAI_Probability_Subsphere_Regression_Spheres
import Definitions.Def_OAI_Probability_Subsphere_Regression_Blocks
import Theorems.Thm_OAI_SubsphereRegression_normalized_routing_bound

-- ---- from OAI.Probability.Subsphere.Regression.Blocks ----
namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace
universe u
namespace SubsphereRegression
open scoped Topology
open InnerProductSpace
open scoped Pointwise
namespace Learner
end Learner

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [FiniteDimensional ℝ E] in
lemma localNormalize_univ {ν : Measure E} {a : ℕ} {C : ℝ≥0∞}
    (hν : PolynomialMass ν a C) (hC : C ≠ 0) (hCt : C ≠ ∞) (z : E) {r : ℝ} (hr : 0 < r) :
    localNormalize ν a C z r univ ≤ 1 := by
  have hc0 : C * ENNReal.ofReal (r^a) ≠ 0 := mul_ne_zero hC (by positivity)
  have hct : C * ENNReal.ofReal (r^a) ≠ ∞ := ENNReal.mul_ne_top hCt ENNReal.ofReal_ne_top
  simp only [localNormalize, Measure.smul_apply, smul_eq_mul, Measure.map_apply (by fun_prop : Measurable (fun x : E => r⁻¹ • (x-z))) MeasurableSet.univ,
    Set.preimage_univ, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
  exact (mul_le_mul' le_rfl (hν z r hr)).trans_eq (ENNReal.inv_mul_cancel hc0 hct)

omit [FiniteDimensional ℝ E] in
lemma localNormalize_finite {ν : Measure E} {a : ℕ} {C : ℝ≥0∞}
    (hν : PolynomialMass ν a C) (hC : C ≠ 0) (hCt : C ≠ ∞) (z : E) {r : ℝ} (hr : 0 < r) :
    IsFiniteMeasure (localNormalize ν a C z r) :=
  ⟨(localNormalize_univ hν hC hCt z hr).trans_lt (by simp)⟩

omit [FiniteDimensional ℝ E] in
lemma localNormalize_support (ν : Measure E) (a : ℕ) (C : ℝ≥0∞) (z : E) {r : ℝ} (hr : 0 < r) :
    (localNormalize ν a C z r).support ⊆ Metric.closedBall 0 1 := by
  apply Measure.support_subset_of_isClosed Metric.isClosed_closedBall
  rw [mem_ae_iff, localNormalize, Measure.smul_apply, Measure.map_apply (by fun_prop)
    Metric.isClosed_closedBall.measurableSet.compl,
    Measure.restrict_apply ((by fun_prop : Measurable (fun x : E => r⁻¹ • (x-z)))
      Metric.isClosed_closedBall.measurableSet.compl)]
  have he : (fun x : E => r⁻¹ • (x-z)) ⁻¹' (Metric.closedBall 0 1)ᶜ ∩ Metric.closedBall z r = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro x ⟨hx,hb⟩
    apply hx
    rw [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr)]
    exact (inv_mul_le_iff₀ hr).2 (by simpa [dist_eq_norm] using hb)
  rw [he, measure_empty, smul_zero]

omit [FiniteDimensional ℝ E] in
lemma localNormalize_local {ν : Measure E} {a : ℕ} {C : ℝ≥0∞}
    (hν : PolynomialMass ν a C) (hC : C ≠ 0) (hCt : C ≠ ∞) (z : E) {r : ℝ} (hr : 0 < r) :
    HasLocalMassBound (localNormalize ν a C z r) (a : ℝ) := by
  have hc0 : C * ENNReal.ofReal (r^a) ≠ 0 := mul_ne_zero hC (by positivity)
  have hct : C * ENNReal.ofReal (r^a) ≠ ∞ := ENNReal.mul_ne_top hCt ENNReal.ofReal_ne_top
  intro t _ ρ hρ
  rw [localNormalize, Measure.smul_apply, smul_eq_mul,
    Measure.map_apply (by fun_prop) Metric.isClosed_closedBall.measurableSet]
  have hsub : (fun x : E => r⁻¹ • (x-z)) ⁻¹' Metric.closedBall t ρ ⊆
      Metric.closedBall (z + r • t) (r*ρ) := by
    intro x hx
    have he : x - (z+r • t) = r • (r⁻¹ • (x-z) - t) := by
      rw [smul_sub, smul_smul, mul_inv_cancel₀ hr.ne', one_smul]
      abel
    rw [Metric.mem_closedBall, dist_eq_norm, he, norm_smul, Real.norm_eq_abs, abs_of_pos hr]
    exact mul_le_mul_of_nonneg_left (by simpa only [Set.mem_preimage, Metric.mem_closedBall, dist_eq_norm] using hx) hr.le
  calc
    _ ≤ (C * ENNReal.ofReal (r^a))⁻¹ * ν (Metric.closedBall (z+r • t) (r*ρ)) :=
      mul_le_mul' le_rfl ((Measure.restrict_le_self _).trans (measure_mono hsub))
    _ ≤ (C * ENNReal.ofReal (r^a))⁻¹ * (C * ENNReal.ofReal ((r*ρ)^a)) :=
      mul_le_mul' le_rfl (hν _ _ (mul_pos hr hρ))
    _ = ENNReal.ofReal (ρ^(a : ℝ)) := by
      rw [mul_pow, ENNReal.ofReal_mul (pow_nonneg hr.le a), ← mul_assoc C,
        ← mul_assoc, ENNReal.inv_mul_cancel hc0 hct, one_mul, Real.rpow_natCast]

omit [FiniteDimensional ℝ E] in
lemma localNormalize_reconstruct (ν : Measure E) (a : ℕ) {C : ℝ≥0∞}
    (hC : C ≠ 0) (hCt : C ≠ ∞) (z : E) {r : ℝ} (hr : 0 < r) :
    (C * ENNReal.ofReal (r^a)) • (localNormalize ν a C z r).map (fun t => z+r • t) =
      ν.restrict (Metric.closedBall z r) := by
  have hc0 : C * ENNReal.ofReal (r^a) ≠ 0 := mul_ne_zero hC (by positivity)
  have hct : C * ENNReal.ofReal (r^a) ≠ ∞ := ENNReal.mul_ne_top hCt ENNReal.ofReal_ne_top
  rw [localNormalize, Measure.map_smul, smul_smul,
    ENNReal.mul_inv_cancel hc0 hct,
    one_smul, Measure.map_map (by fun_prop) (by fun_prop)]
  have he : (fun t : E => z+r • t) ∘ (fun x => r⁻¹ • (x-z)) = id := by
    ext x
    simp [smul_smul, hr.ne']
  rw [he, Measure.map_id]

lemma projectionLaw_smul (ν : Measure E) [SFinite ν] (m : ℕ) (c : ℝ≥0∞) :
    projectionLaw (c • ν) m = c • projectionLaw ν m := by
  rw [projectionLaw, Measure.prod_smul_right, Measure.map_smul _ _ _]
  rfl

lemma projectionLaw_affine (ν : Measure E) [SFinite ν] (m : ℕ) (z : E) (r : ℝ) :
    projectionLaw (ν.map (fun t => z + r • t)) m =
      (projectionLaw ν m).map (fun x => (x.1, fun j => ⟪z,x.1 j⟫ + r * x.2 j)) := by
  unfold projectionLaw
  rw [← Measure.map_id (μ := Measure.pi (fun _ : Fin m => stdGaussian E)),
    Measure.map_prod_map _ _ measurable_id (by fun_prop), Measure.map_map (by fun_prop) (by fun_prop),
    Measure.map_id, Measure.map_map (by fun_prop) (by fun_prop)]
  congr 1
  ext x <;> simp [inner_add_left, real_inner_smul_left]

lemma localized_routing_bound {J : Type*} [Fintype J] [MeasurableSpace J]
    [MeasurableSingletonClass J] (ν : J → Measure E) [∀ j, IsFiniteMeasure (ν j)]
    {a m n : ℕ} {C : ℝ≥0∞} (hν : ∀ j, PolynomialMass (ν j) a C)
    (hC : C ≠ 0) (hCt : C ≠ ∞)
    (hd : 1 ≤ Module.finrank ℝ E) (ha : a ≤ Module.finrank ℝ E)
    (hm : m ≤ Module.finrank ℝ E) (hn : 1 ≤ n) (hmargin : n+m ≤ a)
    (φ : ((Fin m → E) × (Fin m → ℝ)) → J) (hφ : Measurable φ)
    (z : E) {r : ℝ} (hr : 0 < r) :
    (∑ j, projectionLaw ((ν j).restrict (Metric.closedBall z r)) m {x | φ x = j}) ≤
      (32768 : ℝ≥0∞)^Module.finrank ℝ E * (Fintype.card J : ℝ≥0∞)^(1/((n : ℝ)+1)) *
        C * ENNReal.ofReal (r^a) := by
  let τ (j : J) := localNormalize (ν j) a C z r
  let F : ((Fin m → E) × (Fin m → ℝ)) → ((Fin m → E) × (Fin m → ℝ)) :=
    fun x => (x.1, fun i => ⟪z,x.1 i⟫ + r * x.2 i)
  have hF : Measurable F := by fun_prop
  let (j : J) : IsFiniteMeasure (τ j) := localNormalize_finite (hν j) hC hCt z hr
  have hb := normalized_routing_bound τ
    (fun j => localNormalize_local (hν j) hC hCt z hr)
    (fun j => localNormalize_univ (hν j) hC hCt z hr)
    (fun j => localNormalize_support (ν j) a C z hr) hd ha hm hn hmargin (φ ∘ F) (hφ.comp hF)
  have he (j : J) : projectionLaw ((ν j).restrict (Metric.closedBall z r)) m {x | φ x = j} =
      (C * ENNReal.ofReal (r^a)) * projectionLaw (τ j) m {x | φ (F x) = j} := by
    rw [← localNormalize_reconstruct (ν j) a hC hCt z hr, projectionLaw_smul,
      projectionLaw_affine, Measure.smul_apply, smul_eq_mul, Measure.map_apply hF
      (measurableSet_eq_fun hφ measurable_const)]
    rfl
  simp_rw [he]
  rw [← Finset.mul_sum]
  exact (mul_le_mul' le_rfl hb).trans_eq (by ring)

end SubsphereRegression

end

end OAI

-- ---- platform node ----
open OAI OAI.SubsphereRegression
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace
open scoped Topology
open InnerProductSpace
open scoped Pointwise


theorem solution : type_of% @_root_.OAI.SubsphereRegression.localized_routing_bound := @_root_.OAI.SubsphereRegression.localized_routing_bound
