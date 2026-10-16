-- Prove2me | solution 1 for OAI.NoiselessRegression.main
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T10:49:46.291848+00:00
-- url     : https://prove2.me/submissions/90022e51-0192-4855-a27c-eb45e282bec5

-- Generated from openai/math@1581d4c lean/OAI/Probability/GaussianRegression/Main.lean:L91-L92
-- (upload_full_project.md Phase 4): solution for the platform mission target OAI.NoiselessRegression.main.
-- The source declaration is kept inside its namespace next to the proof-only helpers it needs;
-- `theorem solution` restates the platform stub (Theorems.Thm_OAI_NoiselessRegression_main) verbatim and is proved by it.
import Mathlib
import Definitions.Def_NoiselessRegression
import Definitions.Def_OAI_Probability_ProjectionMoments_Model
import Definitions.Def_OAI_Probability_GaussianRegression_Nets
import Definitions.Def_OAI_Probability_GaussianRegression_Gram
import Definitions.Def_OAI_Probability_GaussianRegression_ReplicaMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Smoothing
import Definitions.Def_OAI_Probability_GaussianRegression_Projection
import Definitions.Def_OAI_Probability_GaussianRegression_Support
import Definitions.Def_OAI_Probability_GaussianRegression_Blocks
import Definitions.Def_OAI_Probability_GaussianRegression_Sphere
import Definitions.Def_OAI_Probability_GaussianRegression_Stream
import Definitions.Def_OAI_Probability_GaussianRegression_Caps
import Definitions.Def_OAI_Probability_GaussianRegression_Execution
import Definitions.Def_OAI_Probability_GaussianRegression_Rotational
import Theorems.Thm_OAI_NoiselessRegression_Learner_linear_success_bound
import Theorems.Thm_OAI_NoiselessRegression_Learner_streaming_success_bound_real
import Theorems.Thm_OAI_NoiselessRegression_precision_from_stream_bound

-- ---- from OAI.Probability.GaussianRegression.Rotational ----
namespace OAI

/-!
Fubini bounds and rotational lower bounds for sequential estimation.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
open InnerProductSpace
open scoped Pointwise

noncomputable section

universe u

namespace NoiselessRegression

section FubiniAux
variable {X Y Z : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
  {μ : Measure X} {ν : Measure Y} [SFinite μ] [SFinite ν]
lemma ae_fiber_aemeasurable {f : X × Y → Z} (hf : AEMeasurable f (μ.prod ν)) :
    ∀ᵐ y ∂ν, AEMeasurable (fun x => f (x,y)) μ := by
  have he := Measure.ae_ae_of_ae_prod hf.prod_swap.ae_eq_mk
  filter_upwards [he] with y hy
  have hm : Measurable (fun x => hf.prod_swap.mk _ (y,x)) :=
    hf.prod_swap.measurable_mk.comp (measurable_const.prodMk measurable_id)
  exact hm.aemeasurable.congr (Filter.EventuallyEq.symm hy)

end FubiniAux

namespace Learner
lemma angularSuccess_nullMeasurable {d M T : ℕ} {Ω : Type u} [MeasurableSpace Ω]
    (L : Learner d M T Ω) (ρ : Measure Ω) (ε : ℝ) (hL : L.Admissible ρ) :
    NullMeasurableSet {z : UnitSphere d × (Ω × Samples d T) |
      angularError z.1 (L.estimate z.1 z.2.1 z.2.2) ≤ ε}
      ((uniformSphere d).prod (ρ.prod (sampleLaw d T))) := by
  apply nullMeasurableSet_le _ aemeasurable_const
  exact Real.continuous_arccos.measurable.comp_aemeasurable
    ((measurable_subtype_coe.comp_aemeasurable hL.uniform_experiment).inner
      (measurable_subtype_coe.comp measurable_fst).aemeasurable)

end Learner

end NoiselessRegression

end

end OAI

-- ---- from OAI.Probability.GaussianRegression.Main ----
namespace OAI

/-!
Quadratic and subquadratic memory lower bounds for Gaussian regression.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
open InnerProductSpace
open scoped Pointwise

noncomputable section

universe u

namespace NoiselessRegression

theorem fixed_quadratic_memory : FixedQuadraticMemory.{u} := by
  intro A hA
  refine ⟨1/(4*(400000+100*A)), by positivity, 32, ?_⟩
  intro d hd M T hM ε hε hε10 Ω _ ρ hρ L hL hs
  let : IsProbabilityMeasure ρ := hρ
  have hT : d ≤ 4*T := by
    by_contra h
    have hb := hs.trans (L.linear_success_bound ρ (by omega) (by omega) hε10 hL)
    have hr := ENNReal.toReal_mono ENNReal.ofReal_ne_top hb
    norm_num [ENNReal.toReal_div] at hr
  let q := (d-1)/4
  let a := 2*q
  have hq : 2 ≤ q := by dsimp [q]; omega
  have hqa : 2*q ≤ a := le_rfl
  have ha : 2*a ≤ d-1 := by dsimp [a, q]; omega
  have hdq : d ≤ 8*q := by dsimp [q]; omega
  have hda : d ≤ 4*a := by dsimp [a]; omega
  exact precision_from_stream_bound hd hT (by omega) hdq hda hM hA hε (by linarith)
    (L.streaming_success_bound_real ρ hL (by omega) hε ha hq hqa hs)

section LowerFubini
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  {μ : Measure X} {ν : Measure Y} [SFinite μ] [SFinite ν]
lemma prod_null_set_lower_bound {S : Set (X × Y)} (hS : NullMeasurableSet S (μ.prod ν))
    {c : ℝ≥0∞} (h : ∀ᵐ x ∂μ, c ≤ ν {y | (x,y) ∈ S}) :
    c * μ univ ≤ (μ.prod ν) S := by
  have hm : AEMeasurable (S.indicator (fun _ => (1 : ℝ≥0∞))) (μ.prod ν) :=
    aemeasurable_const.indicator₀ hS
  rw [← one_mul ((μ.prod ν) S), ← lintegral_indicator_const₀ hS 1, lintegral_prod _ hm]
  have hc : c * μ univ = ∫⁻ _ : X, c ∂μ := (lintegral_const c).symm
  rw [hc]
  apply lintegral_mono_ae
  filter_upwards [h, ae_fiber_aemeasurable hm.prod_swap] with x hx hmx
  have hs : NullMeasurableSet {y | (x,y) ∈ S} ν := by
    have heq : {y | (x,y) ∈ S} = {y | S.indicator (fun _ => (1 : ℝ≥0∞)) (x,y) = 1} := by
      ext y
      by_cases hy : (x,y) ∈ S <;> simp [hy]
    rw [heq]
    exact nullMeasurableSet_eq_fun hmx aemeasurable_const
  change c ≤ ∫⁻ y, ({y | (x,y) ∈ S}).indicator (fun _ => (1 : ℝ≥0∞)) y ∂ν
  simpa [lintegral_indicator_const₀ hs] using hx
end LowerFubini

namespace Learner
lemma uniformSuccess_of_pointwise {d M T : ℕ} {Ω : Type u} [MeasurableSpace Ω]
    (L : Learner d M T Ω) (ρ : Measure Ω) [IsProbabilityMeasure ρ]
    (hL : L.Admissible ρ) (hd : 0 < d) (ε : ℝ) {c : ℝ≥0∞}
    (hs : ∀ s, c ≤ L.success ρ ε s) : c ≤ L.uniformSuccess ρ ε := by
  let : NeZero d := ⟨hd.ne'⟩
  have hb := prod_null_set_lower_bound (L.angularSuccess_nullMeasurable ρ ε hL)
    (c := c) (Filter.Eventually.of_forall hs)
  simpa only [measure_univ, mul_one, uniformSuccess] using hb
end Learner

theorem subquadratic_memory : SubquadraticMemory.{u} := by
  obtain ⟨c, hc, d₁, hfixed⟩ := fixed_quadratic_memory (1 : ℝ) (by norm_num)
  refine ⟨c, hc, ?_⟩
  intro M hM
  obtain ⟨d₂, hd₂⟩ := eventually_atTop.1 hM.eventuallyLE
  refine ⟨max d₁ (max d₂ 1), ?_⟩
  intro d hd T ε hε hε10 Ω _ ρ hρ L hL hs
  let : IsProbabilityMeasure ρ := hρ
  have hmem : (M d : ℝ) ≤ 1 * (d : ℝ)^2 := by
    have hm := hd₂ d (by omega)
    simpa only [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg (M d) : (0 : ℝ) ≤ M d),
      abs_of_nonneg (sq_nonneg (d : ℝ)), one_mul] using hm
  apply hfixed d (by omega) (M d) T hmem ε hε hε10 Ω ρ hρ L hL
  rcases hs with hs | hs
  · exact hs
  · exact L.uniformSuccess_of_pointwise ρ hL (by omega) ε hs

theorem main : SubquadraticMemory.{u} ∧ FixedQuadraticMemory.{u} :=
  ⟨subquadratic_memory, fixed_quadratic_memory⟩

end NoiselessRegression

end

end OAI

-- ---- mission target ----
open OAI OAI.NoiselessRegression
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace
universe u
open scoped ENNReal NNReal RealInnerProductSpace Topology
open InnerProductSpace
open scoped Pointwise

theorem solution : SubquadraticMemory.{u} ∧ FixedQuadraticMemory.{u} := by
  first
    | exact OAI.NoiselessRegression.main
    | (apply OAI.NoiselessRegression.main <;> assumption)
    | (intros; apply OAI.NoiselessRegression.main <;> assumption)
