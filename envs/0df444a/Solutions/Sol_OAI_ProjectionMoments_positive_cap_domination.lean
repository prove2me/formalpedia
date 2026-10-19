-- Prove2me | solution 1 for OAI.ProjectionMoments.positive_cap_domination
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T20:14:18.328986+00:00
-- url     : https://prove2.me/submissions/99db9d01-09dd-416b-a9e1-2723965fbefe

-- Generated from openai/math@1581d4c lean/OAI/Probability/ProjectionMoments/CapDomination.lean:L11-L70
-- (upload_full_project.md Phase 4): solution for node OAI.ProjectionMoments.positive_cap_domination. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Model
import Definitions.Def_OAI_Probability_GaussianRegression_Nets__ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Gram__ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_ReplicaMoments__ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Smoothing__ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Projection__ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Support__ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Blocks__ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Sphere__ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Stream__ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Caps__ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Execution__ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Rotational__ProjectionMoments
import Definitions.Def_OAI_Probability_ProjectionMoments_Graph
import Definitions.Def_OAI_Probability_ProjectionMoments_Frames
import Definitions.Def_OAI_Probability_ProjectionMoments_SphereDensity
import Definitions.Def_OAI_Probability_ProjectionMoments_FrameMoments
import Definitions.Def_OAI_Probability_ProjectionMoments_RieszPotential
import Definitions.Def_OAI_Probability_ProjectionMoments_Polar
import Definitions.Def_OAI_Probability_ProjectionMoments_BallMoments
import Definitions.Def_OAI_Probability_ProjectionMoments_CapTests
import Definitions.Def_OAI_Probability_ProjectionMoments_CapDuality
import Definitions.Def_OAI_Probability_ProjectionMoments_WeightedCover
import Theorems.Thm_OAI_ProjectionMoments_Weighted_measure_domination
import Theorems.Thm_OAI_ProjectionMoments_cap_dual_estimate
import Theorems.Thm_OAI_ProjectionMoments_exists_capDictionary
import Theorems.Thm_OAI_ProjectionMoments_sphere_cap_lower

-- ---- from OAI.Probability.ProjectionMoments.Caps ----
namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter InnerProductSpace
open scoped ENNReal NNReal RealInnerProductSpace Topology
namespace ProjectionMoments

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

end

universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma cap_mass_pos [Nontrivial E] {c : E} (hc : ‖c‖ = 1) {r : ℝ} (hr : 0 < r) (hr2 : r ≤ 2) :
    NoiselessRegression.ambientSphereLaw (Metric.closedBall c r) ≠ 0 := by
  intro h
  have hh := sphere_cap_lower hc hr hr2
  rw [h,mul_zero] at hh
  exact (ENNReal.ofReal_pos.mpr (pow_pos hr _)).not_ge hh

lemma capMeasure_probability [Nontrivial E] {c : E} (hc : ‖c‖ = 1) {r : ℝ}
    (hr : 0 < r) (hr2 : r ≤ 2) : IsProbabilityMeasure (capMeasure c r) := by
  constructor
  simp only [capMeasure, Measure.smul_apply, Measure.restrict_apply_univ, smul_eq_mul]
  exact ENNReal.inv_mul_cancel (cap_mass_pos hc hr hr2) (measure_ne_top _ _)

end ProjectionMoments

end

end OAI

-- ---- from OAI.Probability.ProjectionMoments.CapDuality ----
-- Lean 4.33 compatibility: Measurable.of_eval is the renamed measurable_pi_lambda
-- (Mathlib/MeasureTheory/MeasurableSpace/Constructions.lean at d13f23b records the alias).
section Lean433MeasurableOfEval
end Lean433MeasurableOfEval

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter InnerProductSpace Matrix
open MeasureTheory
open scoped ENNReal NNReal
open MeasureTheory ProbabilityTheory Set Filter InnerProductSpace
open scoped ENNReal NNReal RealInnerProductSpace Topology
namespace ProjectionMoments

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [BorelSpace E] in
lemma capReference_le_one [BorelSpace E] {k : ℕ} {K : (Fin k → E) × Label k → ℝ≥0∞}
    (hK1 : ∀ z, K z ≤ 1) (c : E) (r : ℝ) : capReference K c r ≤ 1 := by
  calc
    _ ≤ ∫⁻ X, ∫⁻ z : Label k, (1:ℝ≥0∞) ∂unitBallLaw k ∂Measure.pi (fun _ : Fin k => stdGaussian E) :=
      lintegral_mono (fun X => lintegral_mono (fun z => hK1 _))
    _ = 1 := by simp

omit [BorelSpace E] in
lemma capKernelValue_le_one [BorelSpace E] {k : ℕ} {K : (Fin k → E) × Label k → ℝ≥0∞}
    (hK1 : ∀ z, K z ≤ 1) (s : E) : capKernelValue K s ≤ 1 := by
  calc
    _ ≤ ∫⁻ X : Fin k → E, (1:ℝ≥0∞) ∂Measure.pi (fun _ => stdGaussian E) :=
      lintegral_mono (fun X => hK1 _)
    _ = 1 := by simp

end

end ProjectionMoments

end

end OAI

-- ---- from OAI.Probability.ProjectionMoments.WeightedCover ----
namespace OAI

noncomputable section

open scoped Topology BigOperators Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology BigOperators
namespace ProjectionMoments
namespace Weighted

section
variable {ι : Type*}

end

variable {Ω ι : Type*} [MeasurableSpace Ω]

theorem measure_domination_nonneg [Countable ι] (μ : Measure Ω) [IsFiniteMeasure μ]
    (P : ι → Measure Ω) [∀ i, IsProbabilityMeasure (P i)] {b : ι → ℝ}
    (hb : ∀ i, 1 ≤ b i) (hproper : ∀ R : ℝ, {i | b i ≤ R}.Finite)
    {K : ℝ} (hK : 0 ≤ K)
    (hdual : ∀ h : Ω → ℝ≥0∞, Measurable h →
      (∃ H : ℝ≥0, ∀ x, h x ≤ H) →
      (∀ i, ∫⁻ x, h x ∂P i ≤ ENNReal.ofReal (b i)) →
      ∫⁻ x, h x ∂μ ≤ ENNReal.ofReal K) :
    ∃ a : ι → ℝ, (∀ i, 0 ≤ a i) ∧ Summable (fun i => a i*b i) ∧
      (∑' i, a i*b i) ≤ K ∧ μ ≤ Measure.sum (fun i => ENNReal.ofReal (a i) • P i) := by
  rcases eq_or_lt_of_le hK with hK0 | hKpos
  · subst K
    have hm := hdual (fun _ => 1) measurable_const ⟨1,fun _ => le_rfl⟩
      (fun i => by simp only [lintegral_const,measure_univ,mul_one]; exact ENNReal.one_le_ofReal.mpr (hb i))
    simp only [lintegral_const,one_mul,ENNReal.ofReal_zero,nonpos_iff_eq_zero] at hm
    have hμ : μ = 0 := Measure.measure_univ_eq_zero.mp hm
    refine ⟨fun _ => 0,fun _ => le_rfl,?_,?_,?_⟩ <;> simp [hμ]
  · exact measure_domination μ P hb hproper hKpos hdual

end Weighted
end ProjectionMoments

end

end OAI

-- ---- from OAI.Probability.ProjectionMoments.CapDomination ----
namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter InnerProductSpace
open scoped ENNReal NNReal RealInnerProductSpace Topology
namespace ProjectionMoments

theorem positive_cap_domination :
    ∃ C : ℝ, 0 < C ∧ ∀ d : ℕ, 32 ≤ d →
      let k := d/16
      let α : ℝ := ((d:ℝ)-1)/2
      ∀ (c : EuclideanSpace ℝ (Fin d)), ‖c‖ = 1 →
      ∀ r : ℝ, 0 < r → r ≤ 2 →
      ∀ K : (Fin k → EuclideanSpace ℝ (Fin d)) × Label k → ℝ≥0∞,
      Measurable K → (∀ z, K z ≤ 1) →
      ∃ D : CapDictionary c r α, ∃ a : D.I → ℝ,
        (∀ i, 0 ≤ a i) ∧ Summable (fun i => a i*(r/D.radius i)^α) ∧
        (∑' i, a i*(r/D.radius i)^α) ≤ Real.exp (C*d)*(capReference K c r).toReal^(1-1/(k:ℝ)) ∧
        (capMeasure c r).withDensity (capKernelValue K) ≤
          Measure.sum (fun i => ENNReal.ofReal (a i) • capMeasure (D.center i) (D.radius i)) ∧
        (Measure.sum (fun i => ENNReal.ofReal (a i) • capMeasure (D.center i) (D.radius i))) Set.univ < ∞ := by
  obtain ⟨C,hC,hdual⟩ := cap_dual_estimate
  refine ⟨C,hC,?_⟩
  intro d hd k α c hc r hr hr2 K hK hK1
  let : NeZero d := ⟨by omega⟩
  have hdR : (32:ℝ) ≤ d := by exact_mod_cast hd
  have hα : 1 ≤ α := by dsimp [α]; linarith
  obtain ⟨D⟩ := exists_capDictionary hc hr hα
  let := D.countable
  let : IsProbabilityMeasure (capMeasure c r) := capMeasure_probability hc hr hr2
  let P : D.I → Measure (EuclideanSpace ℝ (Fin d)) := fun i => capMeasure (D.center i) (D.radius i)
  let (i : D.I) : IsProbabilityMeasure (P i) :=
    capMeasure_probability (D.center_norm i) (D.radius_pos i) ((D.radius_le i).trans hr2)
  let b : D.I → ℝ := fun i => (r/D.radius i)^α
  have hb : ∀ i, 1 ≤ b i := fun i => Real.one_le_rpow
    ((one_le_div (D.radius_pos i)).mpr (D.radius_le i)) (zero_le_one.trans hα)
  let μ := (capMeasure c r).withDensity (capKernelValue K)
  let : IsFiniteMeasure μ := isFiniteMeasure_withDensity (ne_of_lt
    ((lintegral_mono (capKernelValue_le_one hK1)).trans_lt (by simp)))
  let B := Real.exp (C*d)*(capReference K c r).toReal^(1-1/(k:ℝ))
  have hkR : (1:ℝ) < k := by
    have hk : 2 ≤ k := by dsimp [k]; omega
    exact_mod_cast (show 1 < k by omega)
  have hθ : 0 ≤ 1-1/(k:ℝ) := by
    have hpq := Real.HolderConjugate.conjExponent hkR
    rw [one_div,hpq.one_sub_inv]
    exact inv_nonneg.mpr hpq.symm.pos.le
  have hqtop : capReference K c r ≠ ∞ := ne_of_lt ((capReference_le_one hK1 c r).trans_lt (by simp))
  have hB : ENNReal.ofReal B = ENNReal.ofReal (Real.exp (C*d))* (capReference K c r)^(1-1/(k:ℝ)) := by
    rw [ENNReal.ofReal_mul (Real.exp_pos _).le, ← ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg hθ,
      ENNReal.ofReal_toReal hqtop]
  have htest : ∀ h : EuclideanSpace ℝ (Fin d) → ℝ≥0∞, Measurable h →
      (∃ H : ℝ≥0, ∀ x, h x ≤ H) →
      (∀ i, ∫⁻ x, h x ∂P i ≤ ENNReal.ofReal (b i)) → ∫⁻ x, h x ∂μ ≤ ENNReal.ofReal B := by
    intro h hh _ hhD
    rw [hB,lintegral_withDensity_eq_lintegral_mul _ (measurable_capKernelValue hK) hh]
    simp only [Pi.mul_apply]
    simpa only [mul_comm] using hdual d hd c hc r hr hr2 D K hK hK1 h hh hhD
  obtain ⟨a,ha,has,hcost,hdom⟩ := Weighted.measure_domination_nonneg μ P hb D.proper
    (show 0 ≤ B by positivity) htest
  refine ⟨D,a,ha,has,hcost,hdom,?_⟩
  rw [Measure.sum_apply _ MeasurableSet.univ]
  simp only [Measure.smul_apply,measure_univ,smul_eq_mul,mul_one]
  have has' : Summable a := Summable.of_nonneg_of_le ha
    (fun i => by simpa using mul_le_mul_of_nonneg_left (hb i) (ha i)) has
  rw [← ENNReal.ofReal_tsum_of_nonneg ha has']
  exact ENNReal.ofReal_lt_top

end ProjectionMoments

end

end OAI

-- ---- platform node ----
open OAI OAI.ProjectionMoments
open MeasureTheory ProbabilityTheory Set Filter InnerProductSpace
open scoped ENNReal NNReal RealInnerProductSpace Topology


theorem solution : type_of% @_root_.OAI.ProjectionMoments.positive_cap_domination := @_root_.OAI.ProjectionMoments.positive_cap_domination
