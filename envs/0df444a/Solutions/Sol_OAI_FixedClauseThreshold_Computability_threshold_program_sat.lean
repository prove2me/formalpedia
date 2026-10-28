-- Prove2me | solution 1 for OAI.FixedClauseThreshold.Computability.threshold_program_sat
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T06:52:55.062988+00:00
-- url     : https://prove2.me/submissions/5638bc1a-5dfd-4549-8668-c4be7caabf03

import Mathlib
import Definitions.Def_DilutedSpin
import Definitions.Def_OAIQ041D000
import Definitions.Def_SATComputability
import Definitions.Def_OAIQ067A002
import Theorems.Thm_OAI_DilutedSpinGlass_symmetric_trial_lower_sat
import Theorems.Thm_OAI_FixedClauseThreshold_Computability_auxiliaryPoissonProbability_supercritical_sat
import Theorems.Thm_OAI_FixedClauseThreshold_Computability_deletion_increment_linear_sat
import Theorems.Thm_OAI_FixedClauseThreshold_Computability_exists_lowerProgram_sat
import Theorems.Thm_OAI_FixedClauseThreshold_Computability_negative_pressure_of_violation_density_sat
import Theorems.Thm_OAI_FixedClauseThreshold_Computability_satTrialEvaluation_sound_sat
import Theorems.Thm_OAI_FixedClauseThreshold_limitingCenter_bounds_sat
import Theorems.Thm_OAI_FixedClauseThreshold_limitingCenter_pos_sat

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_PoissonMoments
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open _root_.MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology
attribute [local instance] DilutedSpinGlass.instMeasurableSpaceCarrier_challenge DilutedSpinGlass.instBorelSpaceCarrier_challenge

namespace DilutedSpinGlass

variable {Ω Λ : Type*} [MeasurableSpace Ω] [MeasurableSpace Λ]
    {μ : Measure Ω} {ν : Measure Λ} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]

/-- Uniform bounds survive averaging a physical root coordinate. -/
theorem abs_integral_le_bound {f : Ω → ℝ} {B : ℝ} (hB : ∀ x, |f x| ≤ B) :
    |∫ x, f x ∂μ| ≤ B := by
  simpa only [Real.norm_eq_abs, probReal_univ, mul_one] using norm_integral_le_of_norm_le_const
    (μ := μ) (f := f) (C := B) (ae_of_all _ (fun x => by simpa only [Real.norm_eq_abs] using hB x))

end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_MarkedPoisson
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open _root_.MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology
attribute [local instance] DilutedSpinGlass.instMeasurableSpaceCarrier_challenge DilutedSpinGlass.instBorelSpaceCarrier_challenge
namespace DilutedSpinGlass

theorem poissonWeight_succ_mul (r : ℝ≥0) (n : ℕ) :
    poissonWeight r (n+1) * (n+1 : ℕ) = (r : ℝ) * poissonWeight r n := by
  unfold poissonWeight
  rw [Nat.factorial_succ, Nat.cast_mul, pow_succ]
  have hn : (n.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  have hn1 : ((n+1 : ℕ) : ℝ) ≠ 0 := by positivity
  field_simp

/-- Integrability of the count is proved from the same add-one recurrence. -/
theorem poisson_integrable_count (r : ℝ≥0) :
    Integrable (fun n : ℕ => (n : ℝ)) (poissonMeasure r) := by
  rw [integrable_poissonMeasure_iff]
  have hs := (hasSum_one_poissonMeasure r).mul_left (r : ℝ)
  have ht : HasSum (fun n => poissonWeight r (n+1) * ((n+1 : ℕ) : ℝ)) r := by
    simp_rw [poissonWeight_succ_mul]
    unfold poissonWeight
    simpa only [mul_one] using hs
  have ht' := HasSum.zero_add (f := fun n => poissonWeight r n * (n : ℝ)) ht
  simp only [Nat.cast_zero, mul_zero, zero_add] at ht'
  simpa only [Real.norm_natCast, poissonWeight] using ht'.summable

end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_CavityBounds
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.DilutedSpinGlass.UniversalDictionary.reservoirLaw_prob _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open _root_.MeasureTheory Filter Set TopologicalSpace
open scoped Topology NNReal ENNReal BigOperators

namespace DilutedSpinGlass

theorem edge_pos {p : ℕ} (theta : Interaction p) (x : Fin p → ℝ) :
    0 < edge theta x := by
  have hb := (weighted_exp_bounds (B := ‖theta‖) (fun s : Fin p → Spin => ∏ l, q (x l) (s l)) theta
    (fun _ => (Finset.prod_pos (fun l _ => q_pos _ _)).le)
    (product_q_sum x) (fun s => norm_le_pi_norm theta s)).1
  simpa only [edge, mul_comm] using (Real.exp_pos _).trans_le hb

/-- The message-free uniform edge bound, with only the physical interaction norm. -/
theorem log_edge_bound {p : ℕ} (theta : Interaction p) (x : Fin p → ℝ) :
    |Real.log (edge theta x)| ≤ ‖theta‖ := by
  simpa only [edge, mul_comm] using
    weighted_log_exp_bound (B := ‖theta‖) (fun s : Fin p → Spin => ∏ l, q (x l) (s l)) theta
      (fun _ => (Finset.prod_pos (fun l _ => q_pos _ _)).le)
      (product_q_sum x) (fun s => norm_le_pi_norm theta s)

end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_MeasureHierarchy
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.DilutedSpinGlass.UniversalDictionary.reservoirLaw_prob _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open _root_.MeasureTheory Filter Set TopologicalSpace
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction

namespace DilutedSpinGlass
attribute [local instance] OAI.DilutedSpinGlass.measureHierarchyStabilityMeasurableSpace
local instance measureHierarchyStabilityBorelSpace (space : TopCat) : BorelSpace space := ⟨rfl⟩

theorem logMean_stability {ι : Type} [Fintype ι] (r : ℕ)
    (f g : (ι → ℝ) → ℝ) (hf : Continuous f) (hg : Continuous g) {B C D : ℝ}
    (hB : ∀ x, |f x| ≤ B) (hC : ∀ x, |g x| ≤ C) (hD : ∀ x, |f x-g x| ≤ D)
    (m : Fin r → ℝ) (hm : ∀ i, 0 < m i) (eta : ι → Hierarchy r) :
    |logMean r f m eta-logMean r g m eta| ≤ D := by
  induction r with
  | zero => exact hD eta
  | succ r ih =>
    obtain ⟨hfc,hfb⟩ := logMean_continuous_bound r f hf hB (fun i => m i.succ) (fun i => hm i.succ)
    obtain ⟨hgc,hgb⟩ := logMean_continuous_bound r g hg hC (fun i => m i.succ) (fun i => hm i.succ)
    exact MeasureMean.logMean_stability (ProbabilityMeasure.pi eta).toMeasure (hm 0)
      hfc.measurable hgc.measurable hfb hgb (ih (fun i => m i.succ) (fun i => hm i.succ))

theorem trialLog_stability {ι : Type} [Fintype ι] (r : ℕ)
    (f g : (ι → ℝ) → ℝ) (hf : Continuous f) (hg : Continuous g) {B C D : ℝ}
    (hB : ∀ x, |f x| ≤ B) (hC : ∀ x, |g x| ≤ C) (hD : ∀ x, |f x-g x| ≤ D)
    (m : Fin r → ℝ) (hm : ∀ i, 0 < m i) (ζ : Hierarchy (r+1)) :
    |trialLog r ζ m f-trialLog r ζ m g| ≤ D := by
  obtain ⟨hfc,hfb⟩ := logMean_continuous_bound r f hf hB m hm
  obtain ⟨hgc,hgb⟩ := logMean_continuous_bound r g hg hC m hm
  let μ := (ProbabilityMeasure.pi (fun _ : ι => ζ)).toMeasure
  have hiF : Integrable (logMean r f m) μ := MeasureMean.bounded_integrable μ hfc.measurable hfb
  have hiG : Integrable (logMean r g m) μ := MeasureMean.bounded_integrable μ hgc.measurable hgb
  change |(∫ eta, logMean r f m eta ∂μ)-(∫ eta, logMean r g m eta ∂μ)| ≤ D
  rw [← integral_sub hiF hiG]
  simpa only [Real.norm_eq_abs, probReal_univ, mul_one] using
    norm_integral_le_of_norm_le_const (μ := μ) (ae_of_all _ (fun eta =>
      (show ‖logMean r f m eta - logMean r g m eta‖ ≤ D from by
        simpa only [Real.norm_eq_abs] using logMean_stability r f g hf hg hB hC hD m hm eta)))

 theorem continuous_edge {p : ℕ} (theta : Interaction p) : Continuous (edge theta) := by
  unfold edge
  apply continuous_finsetSum
  intro s _
  apply continuous_const.mul
  exact continuous_finsetProd _ (fun l _ => (continuous_q (s l)).comp (continuous_apply l))

 theorem continuous_log_edge {p : ℕ} (theta : Interaction p) :
    Continuous (fun x => Real.log (edge theta x)) :=
  (continuous_edge theta).log (fun x => (edge_pos theta x).ne')

end DilutedSpinGlass

namespace DilutedSpinGlass

theorem weighted_exp_pos {ι : Type*} [Fintype ι] (w f : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hs : ∑ i, w i = 1) :
    0 < ∑ i, w i * Real.exp (f i) :=
  (Real.exp_pos (-‖f‖)).trans_le
    (weighted_exp_bounds w f hw hs (fun i => norm_le_pi_norm f i)).1

/-- Stability before any disorder averaging; no lower bound on the positive
message probabilities or moment condition on the messages occurs. -/
theorem weighted_log_exp_stability {ι : Type*} [Fintype ι] (w f g : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hs : ∑ i, w i = 1) {D : ℝ}
    (hD : ∀ i, |f i-g i| ≤ D) :
    |Real.log (∑ i, w i * Real.exp (f i)) -
      Real.log (∑ i, w i * Real.exp (g i))| ≤ D := by
  have aux (f g : ι → ℝ) (h : ∀ i, f i ≤ g i+D) :
      Real.log (∑ i, w i * Real.exp (f i)) ≤
        Real.log (∑ i, w i * Real.exp (g i)) + D := by
    have hle : (∑ i, w i * Real.exp (f i)) ≤
        (∑ i, w i * Real.exp (g i)) * Real.exp D := by
      rw [Finset.sum_mul]
      exact Finset.sum_le_sum (fun i _ => by
        rw [mul_assoc, ← Real.exp_add]
        exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (h i)) (hw i))
    have hl := Real.log_le_log (weighted_exp_pos w f hw hs) hle
    rw [Real.log_mul (weighted_exp_pos w g hw hs).ne' (Real.exp_pos D).ne', Real.log_exp] at hl
    exact hl
  have hfg := aux f g (fun i => by have h := (abs_le.mp (hD i)).2; linarith)
  have hgf := aux g f (fun i => by have h := (abs_le.mp (hD i)).1; linarith)
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem log_edge_stability {p : ℕ} (theta theta' : Interaction p) (x : Fin p → ℝ) :
    |Real.log (edge theta x)-Real.log (edge theta' x)| ≤ ‖theta-theta'‖ := by
  simpa only [edge, mul_comm] using
    weighted_log_exp_stability (fun s : Fin p → Spin => ∏ l, q (x l) (s l)) theta theta'
      (fun _ => (Finset.prod_pos (fun l _ => q_pos _ _)).le)
      (product_q_sum x) (fun s => norm_le_pi_norm (theta-theta') s)

theorem message_stability {p : ℕ} (theta theta' : Interaction p)
    (x : Fin (p-1) → ℝ) (ε : Spin) :
    |message theta x ε-message theta' x ε| ≤ ‖theta-theta'‖ := by
  simpa only [message, mul_comm] using
    weighted_log_exp_stability (fun s : Fin (p-1) → Spin => ∏ l, q (x l) (s l))
      (fun s => theta (appendSpin s ε)) (fun s => theta' (appendSpin s ε))
      (fun _ => (Finset.prod_pos (fun l _ => q_pos _ _)).le)
      (product_q_sum x) (fun s => norm_le_pi_norm (theta-theta') (appendSpin s ε))

theorem siteLog_stability {p k : ℕ} (theta theta' : Fin k → InteractionSample p) (h h' : ℝ)
    (x : (Fin k × Fin (p-1)) → ℝ) :
    |siteLog theta h x - siteLog theta' h' x| ≤
      |h-h'| + ∑ j, ‖(theta j).1-(theta' j).1‖ := by
  have hf : ∀ ε : Spin,
      |(h * spin ε + ∑ j, message (theta j).1 (fun l => x (j,l)) ε) -
        (h' * spin ε + ∑ j, message (theta' j).1 (fun l => x (j,l)) ε)| ≤
        |h-h'| + ∑ j, ‖(theta j).1-(theta' j).1‖ := by
    intro ε
    rw [show (h * spin ε + ∑ j, message (theta j).1 (fun l => x (j,l)) ε) -
        (h' * spin ε + ∑ j, message (theta' j).1 (fun l => x (j,l)) ε) =
        (h-h') * spin ε + ∑ j, (message (theta j).1 (fun l => x (j,l)) ε -
          message (theta' j).1 (fun l => x (j,l)) ε) by rw [Finset.sum_sub_distrib]; ring]
    apply (abs_add_le _ _).trans
    apply add_le_add
    · simp only [abs_mul, abs_spin, mul_one, le_refl]
    · exact (Finset.abs_sum_le_sum_abs _ _).trans
        (Finset.sum_le_sum (fun j _ => message_stability _ _ _ _))
  have hw : (∑ _ε : Spin, (1/2 : ℝ)) = 1 := by norm_num [Fintype.sum_bool]
  have hb := weighted_log_exp_stability (fun _ε : Spin => (1/2 : ℝ))
    (fun ε => h * spin ε + ∑ j, message (theta j).1 (fun l => x (j,l)) ε)
    (fun ε => h' * spin ε + ∑ j, message (theta' j).1 (fun l => x (j,l)) ε)
    (fun _ => by norm_num) hw hf
  simpa only [siteLog, ← Finset.mul_sum, one_div, div_eq_mul_inv, one_mul, mul_comm] using hb

theorem trial_edge_stability {p : ℕ} (r : ℕ) (theta theta' : Interaction p)
    (m : Fin r → ℝ) (hm : ∀ i, 0 < m i) (ζ : Hierarchy (r+1)) :
    |trialLog r ζ m (fun x => Real.log (edge theta x)) -
      trialLog r ζ m (fun x => Real.log (edge theta' x))| ≤ ‖theta-theta'‖ :=
  trialLog_stability r _ _ (continuous_log_edge theta) (continuous_log_edge theta')
    (log_edge_bound theta) (log_edge_bound theta') (log_edge_stability theta theta') m hm ζ

theorem trial_site_stability {p k : ℕ} (r : ℕ)
    (theta theta' : Fin k → InteractionSample p) (h h' : ℝ)
    (m : Fin r → ℝ) (hm : ∀ i, 0 < m i) (ζ : Hierarchy (r+1)) :
    |trialLog r ζ m (siteLog theta h)-trialLog r ζ m (siteLog theta' h')| ≤
      |h-h'| + ∑ j, ‖(theta j).1-(theta' j).1‖ :=
  trialLog_stability r _ _ (continuous_siteLog theta h) (continuous_siteLog theta' h')
    (siteLog_bound theta h) (siteLog_bound theta' h') (siteLog_stability theta theta' h h') m hm ζ

end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_FiniteHierarchyDense
attribute [-instance] _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass
open _root_.MeasureTheory Filter Set TopologicalSpace
open scoped Topology NNReal ENNReal BigOperators

lemma atomicProbability_reindex {X ι κ : Type} [MeasurableSpace X] [Fintype ι] [Fintype κ]
    (e : ι ≃ κ) (x : ι → X) (w : AtomicWeights ι) :
    atomicProbability (fun j => x (e.symm j))
      ⟨fun j => w.val (e.symm j),by rw [e.symm.sum_comp w.val]; exact w.property⟩ =
      atomicProbability x w := by
  apply Subtype.ext
  change (∑ j : κ,(w.val (e.symm j):ℝ≥0∞) • Measure.dirac (x (e.symm j))) = _
  exact e.symm.sum_comp (fun i => (w.val i:ℝ≥0∞) • Measure.dirac (x i))

lemma continuous_atomicProbability_atoms {X ι : Type} [TopologicalSpace X]
    [MeasurableSpace X] [BorelSpace X] [T1Space X] [Fintype ι] (w : AtomicWeights ι) :
    Continuous (fun x : ι → X => atomicProbability x w) := by
  rw [ProbabilityMeasure.continuous_iff_forall_continuous_integral]
  intro f
  simp_rw [integral_atomicProbability]
  exact continuous_finsetSum _ (fun i _ => continuous_const.mul (f.continuous.comp (continuous_apply i)))

/-- Finite laws supported on any dense set are weakly dense. -/
lemma finite_atomic_dense {X : Type} [MetricSpace X] [SeparableSpace X]
    [MeasurableSpace X] [BorelSpace X] (D : Set X) (hD : Dense D) :
    Dense {μ : ProbabilityMeasure X | ∃ (n : ℕ) (x : Fin n → X) (w : AtomicWeights (Fin n)),
      (∀ i,x i ∈ D) ∧ μ = atomicProbability x w} := by
  classical
  let S := {μ : ProbabilityMeasure X | ∃ (n : ℕ) (x : Fin n → X) (w : AtomicWeights (Fin n)),
      (∀ i,x i ∈ D) ∧ μ = atomicProbability x w}
  have ha (ι : Type) [Fintype ι] (x : ι → X) (w : AtomicWeights ι) :
      atomicProbability x w ∈ closure S := by
    have hd : Dense (Set.univ.pi (fun _ : ι => D)) := dense_pi Set.univ (fun _ _ => hD)
    obtain ⟨z,hz,ht⟩ := mem_closure_iff_seq_limit.mp (hd x)
    apply isClosed_closure.mem_of_tendsto ((continuous_atomicProbability_atoms w).tendsto x |>.comp ht)
    apply Eventually.of_forall
    intro n
    apply subset_closure
    let e := Fintype.equivFin ι
    refine ⟨Fintype.card ι,fun j => z n (e.symm j),
      ⟨fun j => w.val (e.symm j),by rw [e.symm.sum_comp w.val]; exact w.property⟩,?_,?_⟩
    · intro j
      exact hz n (e.symm j) (Set.mem_univ _)
    · exact (atomicProbability_reindex e (z n) w).symm
  intro μ
  let h : StronglyMeasurable (id : X → X) := stronglyMeasurable_id
  apply isClosed_closure.mem_of_tendsto (probability_map_tendsto μ h.approx h.tendsto_approx)
  apply Eventually.of_forall
  intro n
  obtain ⟨w,hw⟩ := simple_map_atomic (h.approx n) μ
  rw [← hw]
  exact ha _ _ w

end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_TrialPhysical
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.DilutedSpinGlass.UniversalDictionary.reservoirLaw_prob _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass
open _root_.MeasureTheory Filter
open scoped Topology BigOperators NNReal

lemma trial_edge_lipschitz {p : ℕ} (r : ℕ) (m : Fin r → ℝ) (hm : ∀ i,0 < m i)
    (ζ : Hierarchy (r+1)) :
    LipschitzWith 1 (fun θ : Interaction p => trialLog r ζ m (fun x => Real.log (edge θ x))) := by
  apply LipschitzWith.of_dist_le_mul
  intro θ θ'
  simpa only [Real.dist_eq,dist_eq_norm,Real.norm_eq_abs,NNReal.coe_one,one_mul] using trial_edge_stability r θ θ' m hm ζ

lemma trial_site_lipschitz {p k : ℕ} (r : ℕ) (m : Fin r → ℝ) (hm : ∀ i,0 < m i)
    (ζ : Hierarchy (r+1)) :
    LipschitzWith (k+1) (fun z : (Fin k → InteractionSample p) × ℝ => trialLog r ζ m (siteLog z.1 z.2)) := by
  apply LipschitzWith.of_dist_le_mul
  intro z w
  rw [Real.dist_eq]
  have h1 : |z.2-w.2|≤dist z w := by
    change |z.2-w.2|≤ max (dist z.1 w.1) (dist z.2 w.2)
    simpa only [Real.dist_eq] using le_max_right (dist z.1 w.1) (dist z.2 w.2)
  have h2 : ∑ j,‖(z.1 j).1-(w.1 j).1‖≤(k:ℝ)*dist z w := by
    calc
      _ ≤ ∑ j : Fin k,dist z w := Finset.sum_le_sum (fun j _ => by
        rw [← dist_eq_norm]
        exact (show dist (z.1 j).1 (w.1 j).1≤dist (z.1 j) (w.1 j) from le_max_left _ _).trans
          ((dist_le_pi_dist z.1 w.1 j).trans (show dist z.1 w.1≤dist z w from le_max_left _ _)))
      _ = _ := by simp
  have h := trial_site_stability r z.1 w.1 z.2 w.2 m hm ζ
  push_cast
  nlinarith

lemma trial_edge_bound {p : ℕ} (r : ℕ) (m : Fin r → ℝ) (hm : ∀ i,0 < m i)
    (ζ : Hierarchy (r+1)) (θ : Interaction p) :
    |trialLog r ζ m (fun x => Real.log (edge θ x))|≤‖θ‖ :=
  (trialLog_continuous_bound r _ (continuous_log_edge θ) (log_edge_bound θ) m hm).2 ζ

end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_FunctionalContinuity
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.DilutedSpinGlass.UniversalDictionary.reservoirLaw_prob _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass
open _root_.MeasureTheory ProbabilityTheory Filter
open scoped Topology BigOperators NNReal
variable {p r : ℕ} (M : Model p) (m : Fin r → ℝ) (hm : ∀ i,0 < m i)

include hm in
lemma integrable_trial_site_field (hh : Integrable (fun h : ℝ => |h|) M.field.toMeasure)
    {k : ℕ} (ζ : Hierarchy (r+1)) (θ : Fin k → InteractionSample p) :
    Integrable (fun h => trialLog r ζ m (siteLog θ h)) M.field.toMeasure := by
  apply (hh.add (integrable_const (∑ j,‖(θ j).1‖))).mono'
    (((trial_site_lipschitz r m hm ζ).continuous.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable)
  exact ae_of_all _ (fun h => by simpa only [Real.norm_eq_abs, Pi.add_apply, Function.comp_apply, id_eq] using trial_site_bound r m hm ζ θ h)

include hm in
lemma trialSiteField_bound (hh : Integrable (fun h : ℝ => |h|) M.field.toMeasure)
    {k : ℕ} (ζ : Hierarchy (r+1)) (θ : Fin k → InteractionSample p) :
    |trialSiteField M m ζ θ|≤(∫ h : ℝ,|h| ∂M.field.toMeasure)+∑ j,‖(θ j).1‖ := by
  have hb := norm_integral_le_of_norm_le (f := fun h => trialLog r ζ m (siteLog θ h)) (hh.add (integrable_const (∑ j,‖(θ j).1‖)))
    (ae_of_all _ (fun h => by simpa only [Real.norm_eq_abs, Pi.add_apply, Function.comp_apply, id_eq] using trial_site_bound r m hm ζ θ h))
  simp only [Pi.add_apply] at hb
  simpa only [trialSiteField,Real.norm_eq_abs,integral_add hh (integrable_const _),integral_const,
    probReal_univ,one_smul] using hb

include hm in
lemma stronglyMeasurable_trialSiteField (ζ : Hierarchy (r+1)) (k : ℕ) :
    StronglyMeasurable (trialSiteField M m (k := k) ζ) := by
  let : OpensMeasurableSpace (Fin k → InteractionSample p) := Pi.opensMeasurableSpace
  exact ((trial_site_lipschitz (p := p) (k := k) r m hm ζ).continuous.stronglyMeasurable).integral_prod_right

include hm in
lemma trialSiteField_continuous {k : ℕ} (θ : Fin k → InteractionSample p)
    (hh : Integrable (fun h : ℝ => |h|) M.field.toMeasure) :
    Continuous (fun ζ : Hierarchy (r+1) => trialSiteField M m ζ θ) := by
  apply continuous_of_dominated (bound := fun h : ℝ => |h|+∑ j,‖(θ j).1‖)
  · intro ζ
    exact (integrable_trial_site_field M m hm hh ζ θ).aestronglyMeasurable
  · intro ζ
    exact ae_of_all _ (fun h => by simpa only [Real.norm_eq_abs, Pi.add_apply, Function.comp_apply, id_eq] using trial_site_bound r m hm ζ θ h)
  · exact hh.add (integrable_const _)
  · exact ae_of_all _ (fun h => (trialLog_continuous_bound r _ (continuous_siteLog θ h)
      (siteLog_bound θ h) m hm).1)

lemma interaction_sum_integrable (hθ : Integrable (fun z : InteractionSample p => ‖z.1‖) M.disorder.toMeasure) (k : ℕ) :
    Integrable (fun θ : Fin k → InteractionSample p => ∑ j,‖(θ j).1‖)
      (Measure.pi (fun _ : Fin k => M.disorder.toMeasure)) :=
  integrable_finsetSum _ (fun _ _ => integrable_comp_eval (μ := fun _ : Fin k => M.disorder.toMeasure) hθ)

lemma integral_interaction_sum (hθ : Integrable (fun z : InteractionSample p => ‖z.1‖) M.disorder.toMeasure) (k : ℕ) :
    (∫ θ : Fin k → InteractionSample p,∑ j,‖(θ j).1‖ ∂Measure.pi (fun _ : Fin k => M.disorder.toMeasure)) =
      k*(∫ z : InteractionSample p,‖z.1‖ ∂M.disorder.toMeasure) := by
  rw [integral_finsetSum _ (fun j _ => integrable_comp_eval (μ := fun _ : Fin k => M.disorder.toMeasure) hθ)]
  simp only [integral_comp_eval (μ := fun _ : Fin k => M.disorder.toMeasure) hθ.aestronglyMeasurable,
    Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]

include hm in
lemma trialSiteDisorder_bound (hθ : Integrable (fun z : InteractionSample p => ‖z.1‖) M.disorder.toMeasure)
    (hh : Integrable (fun h : ℝ => |h|) M.field.toMeasure) (ζ : Hierarchy (r+1)) (k : ℕ) :
    |trialSiteDisorder M m ζ k|≤(∫ h : ℝ,|h| ∂M.field.toMeasure)+k*(∫ z : InteractionSample p,‖z.1‖ ∂M.disorder.toMeasure) := by
  have hb := norm_integral_le_of_norm_le (f := trialSiteField M m (k := k) ζ) ((integrable_const _).add (interaction_sum_integrable M hθ k))
    (ae_of_all _ (fun θ => by simpa only [Real.norm_eq_abs, Pi.add_apply, Function.comp_apply, id_eq] using trialSiteField_bound M m hm hh ζ θ))
  simp only [Pi.add_apply] at hb
  simpa only [trialSiteDisorder,Real.norm_eq_abs,integral_add (integrable_const _) (interaction_sum_integrable M hθ k),
    integral_const,probReal_univ,one_smul,integral_interaction_sum M hθ k] using hb

include hm in
lemma trialSiteDisorder_continuous (hθ : Integrable (fun z : InteractionSample p => ‖z.1‖) M.disorder.toMeasure)
    (hh : Integrable (fun h : ℝ => |h|) M.field.toMeasure) (k : ℕ) :
    Continuous (fun ζ : Hierarchy (r+1) => trialSiteDisorder M m ζ k) := by
  apply continuous_of_dominated (bound := fun θ : Fin k → InteractionSample p =>
    (∫ h : ℝ,|h| ∂M.field.toMeasure)+∑ j,‖(θ j).1‖)
  · intro ζ; exact (stronglyMeasurable_trialSiteField M m hm ζ k).aestronglyMeasurable
  · intro ζ; exact ae_of_all _ (fun θ => by simpa only [Real.norm_eq_abs, Pi.add_apply, Function.comp_apply, id_eq] using trialSiteField_bound M m hm hh ζ θ)
  · exact (integrable_const _).add (interaction_sum_integrable M hθ k)
  · exact ae_of_all _ (fun θ => trialSiteField_continuous M m hm θ hh)

include hm in
lemma functional_continuous (hθ : Integrable (fun z : InteractionSample p => ‖z.1‖) M.disorder.toMeasure)
    (hh : Integrable (fun h : ℝ => |h|) M.field.toMeasure) :
    Continuous (fun ζ : Hierarchy (r+1) => functional M r ζ m) := by
  have hs : Continuous (fun ζ : Hierarchy (r+1) => ∫ k,trialSiteDisorder M m ζ k ∂poissonMeasure (M.alpha*p)) := by
    apply continuous_of_dominated (bound := fun k : ℕ =>
      (∫ h : ℝ,|h| ∂M.field.toMeasure)+k*(∫ z : InteractionSample p,‖z.1‖ ∂M.disorder.toMeasure))
    · intro ζ; exact (measurable_of_countable _).aestronglyMeasurable
    · intro ζ; exact ae_of_all _ (fun k => by simpa only [Real.norm_eq_abs, Pi.add_apply, Function.comp_apply, id_eq] using trialSiteDisorder_bound M m hm hθ hh ζ k)
    · exact (integrable_const _).add ((poisson_integrable_count _).mul_const _)
    · exact ae_of_all _ (trialSiteDisorder_continuous M m hm hθ hh)
  have he : Continuous (fun ζ : Hierarchy (r+1) => ∫ θ : InteractionSample p,
      trialLog r ζ m (fun x => Real.log (edge θ.1 x)) ∂M.disorder.toMeasure) := by
    apply continuous_of_dominated (bound := fun θ : InteractionSample p => ‖θ.1‖)
    · intro ζ
      exact (((trial_edge_lipschitz r m hm ζ).continuous.comp continuous_fst).aestronglyMeasurable)
    · intro ζ; exact ae_of_all _ (fun θ => by simpa only [Real.norm_eq_abs, Pi.add_apply, Function.comp_apply, id_eq] using trial_edge_bound r m hm ζ θ.1)
    · exact hθ
    · exact ae_of_all _ (fun θ => (trialLog_continuous_bound r _ (continuous_log_edge θ.1) (log_edge_bound θ.1) m hm).1)
  exact (continuous_const.add hs).sub (continuous_const.mul he)

end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_FinitePoissonSplit
attribute [-instance] _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass
open _root_.MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal BigOperators

lemma integral_finiteUniform {A E : Type*} [Fintype A] [Nonempty A]
    [MeasurableSpace A] [MeasurableSingletonClass A] [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (f : A → E) :
    (∫ x, f x ∂finiteUniform A) = ((Fintype.card A:ℝ)⁻¹) • ∑ x,f x := by
  rw [finiteUniform,PMF.integral_eq_sum]
  simp only [PMF.uniformOfFintype_apply,ENNReal.toReal_inv,ENNReal.toReal_natCast,
    Finset.smul_sum]

end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_RootProductLaw
attribute [-instance] _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass
open _root_.MeasureTheory ProbabilityTheory
open scoped BigOperators

lemma finiteUniform_pi {ι J : Type} [Fintype ι] [DecidableEq ι] [Fintype J] [Nonempty J]
    [MeasurableSpace J] [MeasurableSingletonClass J] :
    Measure.pi (fun _ : ι => finiteUniform J) = finiteUniform (ι → J) := by
  classical
  apply Measure.ext_of_singleton
  intro x
  simp [Measure.pi_singleton,finiteUniform,PMF.uniformOfFintype_apply,ENNReal.inv_pow]

end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.RandomSAT_FiniteMean
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Uniform finite expectations and variances.
-/

namespace FixedClauseThreshold

open Finset

noncomputable section

attribute [local instance] Classical.propDecidable

theorem uniformMean_congr {α : Type*} [Fintype α] {f g : α → ℝ}
    (h : ∀ a, f a = g a) : uniformMean f = uniformMean g := by
  unfold uniformMean
  congr 1
  exact Finset.sum_congr rfl (fun a _ => h a)

theorem uniformMean_const {α : Type*} [Fintype α] [Nonempty α] (c : ℝ) :
    uniformMean (fun _ : α => c) = c := by
  simp [uniformMean, ne_of_gt (Nat.cast_pos.mpr Fintype.card_pos :
    (0 : ℝ) < Fintype.card α)]

theorem uniformMean_nonneg {α : Type*} [Fintype α] {f : α → ℝ}
    (h : ∀ a, 0 ≤ f a) : 0 ≤ uniformMean f := by
  exact div_nonneg (Finset.sum_nonneg (fun a _ => h a)) (Nat.cast_nonneg _)

theorem uniformMean_mono {α : Type*} [Fintype α] {f g : α → ℝ}
    (h : ∀ a, f a ≤ g a) : uniformMean f ≤ uniformMean g := by
  exact div_le_div_of_nonneg_right (Finset.sum_le_sum (fun a _ => h a)) (Nat.cast_nonneg _)

theorem uniformMean_equiv {α β : Type*} [Fintype α] [Fintype β]
    (e : α ≃ β) (f : β → ℝ) : uniformMean (fun a => f (e a)) = uniformMean f := by
  unfold uniformMean
  rw [e.sum_comp, Fintype.card_congr e]

theorem uniformMean_prod {α β : Type*} [Fintype α] [Fintype β]
    (f : α × β → ℝ) : uniformMean f = uniformMean (fun a => uniformMean (fun b => f (a,b))) := by
  simp only [uniformMean, Fintype.sum_prod_type, Fintype.card_prod, Nat.cast_mul,
    ← Finset.sum_div]
  ring

end


end FixedClauseThreshold

end OAI
end

section
-- module Solutions.OAIQ067_SAT.RandomSAT_ClauseProcess
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Coordinate erasure, independent clause averaging, survival probabilities, and
iterated replacement.
-/

namespace FixedClauseThreshold

open Finset

noncomputable section

attribute [local instance] Classical.propDecidable

theorem uniformMean_fin_succ {α : Type*} [Fintype α] {m : ℕ}
    (f : (Fin (m + 1) → α) → ℝ) :
    uniformMean f = uniformMean (fun a => uniformMean (fun F : Fin m → α =>
      f (Fin.cons a F))) := by
  calc
    _ = uniformMean (fun p : α × (Fin m → α) => f (Fin.cons p.1 p.2)) :=
      (uniformMean_equiv (Fin.consEquiv (fun _ => α)) f).symm
    _ = _ := uniformMean_prod _

end


end FixedClauseThreshold

end OAI
end

section
-- module Solutions.OAIQ067_SAT.RandomSAT_Forcing
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.FixedClauseThreshold.Computability.decidableClauseSatisfaction _root_.OAI.FixedClauseThreshold.Computability.decidableFormulaSatisfaction _root_.OAI.FixedClauseThreshold.Computability.decidableSatisfiability _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Deletion and erasure of a coordinate, permutation symmetry, and the integrated
forcing bound.
-/

namespace FixedClauseThreshold

open Finset

noncomputable section

attribute [local instance] Classical.propDecidable

@[simp] theorem deletedMean_zero {v k : ℕ} (hk : 0 < k) (S : Finset (Assignment v)) :
    deletedMean hk 0 S = alive S := by
  have h (F : Formula (v + 1) k 0) :
      deletedSolutions S (fun i => clauseHeadSplit hk (F i)) = S := by
    ext σ
    simp
  simp only [deletedMean, h, uniformMean_const]

@[simp] theorem erasedMean_zero {v k : ℕ} (hk : 0 < k) (S : Finset (Assignment v)) :
    erasedMean hk 0 S = alive S := by
  have h (F : Formula (v + 1) k 0) :
      erasedSolutions S (fun i => clauseHeadSplit hk (F i)) = S := by
    ext σ
    simp
  simp only [erasedMean, h, uniformMean_const]

end


end FixedClauseThreshold

end OAI
end

section
-- module Solutions.OAIQ067_SAT.SATComputability_SATModel
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.bondLaw_probability _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.DilutedSpinGlass.UniversalDictionary.reservoirLaw_prob _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FixedClauseThreshold.Computability

open DilutedSpinGlass _root_.MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal

theorem satModel_supported (a : ℝ≥0) (β : ℝ) :
    ∀ᵐ z ∂(satModel a β).disorder.toMeasure, ∃ J, satSample β J = z := by
  have h := ae_map_mem_range (satSample β) (Set.finite_range _).measurableSet signLaw.toMeasure
  simpa [satModel, ProbabilityMeasure.toMeasure_map] using h

theorem satModel_interaction_integrable (a : ℝ≥0) {β : ℝ} (hβ : 0 ≤ β) :
    Integrable (fun z : InteractionSample 3 => ‖z.1‖) (satModel a β).disorder.toMeasure := by
  apply Integrable.of_bound (by fun_prop) β
  filter_upwards [satModel_supported a β] with z hz
  obtain ⟨J, rfl⟩ := hz
  simpa only [norm_norm, satSample] using satInteraction_norm_le hβ J

theorem satModel_field_integrable (a : ℝ≥0) (β : ℝ) :
    Integrable (fun h : ℝ => |h|) (satModel a β).field.toMeasure := by
  change Integrable (fun h : ℝ => |h|) (Measure.dirac 0)
  exact integrable_dirac (by simp)

theorem signLaw_equiv (e : (Fin 3 → Bool) ≃ (Fin 3 → Bool)) :
    Measure.map e signLaw.toMeasure = signLaw.toMeasure := by
  apply Measure.ext_of_singleton
  intro J
  rw [Measure.map_apply (measurable_of_countable _) (measurableSet_singleton J)]
  have he : e ⁻¹' {J} = {e.symm J} := by
    ext K
    change e K = J ↔ K = e.symm J
    constructor
    · intro h
      simpa using congrArg e.symm h
    · intro h
      simpa using congrArg e h
  rw [he]
  change (PMF.uniformOfFintype (Fin 3 → Bool)).toMeasure {e.symm J} =
    (PMF.uniformOfFintype (Fin 3 → Bool)).toMeasure {J}
  rw [PMF.toMeasure_apply_singleton, PMF.toMeasure_apply_singleton] <;> simp

theorem satInteraction_permute (β : ℝ) (e : Equiv.Perm (Fin 3)) (J s : Fin 3 → Bool) :
    satInteraction β J (fun l => s (e l)) =
      satInteraction β (permuteSigns e J) s := by
  have h : (∀ l, s (e l) ≠ J l) ↔ ∀ l, s l ≠ J (e.symm l) := by
    constructor
    · intro h l
      simpa using h (e.symm l)
    · intro h l
      simpa using h (e l)
  simp only [satInteraction, permuteSigns, Equiv.coe_fn_mk]
  exact if_congr h rfl rfl

theorem satModel_symmetric (a : ℝ≥0) (β : ℝ) (e : Equiv.Perm (Fin 3)) :
    IdentDistrib (fun z : InteractionSample 3 => z.1)
      (fun z : InteractionSample 3 => fun s : Fin 3 → Spin => z.1 (fun l => s (e l)))
      (satModel a β).disorder.toMeasure (satModel a β).disorder.toMeasure := by
  constructor
  · exact measurable_fst.aemeasurable
  · exact (show Measurable (fun z : InteractionSample 3 => fun s : Fin 3 → Spin =>
        z.1 (fun l => s (e l))) by fun_prop).aemeasurable
  · change Measure.map _ (Measure.map (satSample β) signLaw.toMeasure) =
      Measure.map _ (Measure.map (satSample β) signLaw.toMeasure)
    rw [Measure.map_map measurable_fst (measurable_of_countable _),
      Measure.map_map (show Measurable (fun z : InteractionSample 3 => fun s : Fin 3 → Spin =>
        z.1 (fun l => s (e l))) by fun_prop) (measurable_of_countable _)]
    change Measure.map (satInteraction β) signLaw.toMeasure =
      Measure.map (fun J => fun s => satInteraction β J (fun l => s (e l))) signLaw.toMeasure
    simp_rw [satInteraction_permute]
    change Measure.map (satInteraction β) signLaw.toMeasure =
      Measure.map (satInteraction β ∘ permuteSigns e) signLaw.toMeasure
    rw [← Measure.map_map (measurable_of_countable (satInteraction β))
      (measurable_of_countable (permuteSigns e)), signLaw_equiv]

end FixedClauseThreshold.Computability

end OAI
end

section
-- module Solutions.OAIQ067_SAT.SATComputability_SignLaw
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FixedClauseThreshold.Computability

open DilutedSpinGlass _root_.MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal

theorem signLaw_integral (f : (Fin 3 → Bool) → ℝ) :
    (∫ J, f J ∂signLaw.toMeasure) = (FiniteLaw.uniform : FiniteLaw (Fin 3 → Bool)).expect f := by
  change (∫ J, f J ∂(PMF.uniformOfFintype (Fin 3 → Bool)).toMeasure) = _
  rw [PMF.integral_eq_sum]
  simp [FiniteLaw.expect, FiniteLaw.uniform]

end FixedClauseThreshold.Computability

end OAI
end

section
-- module Solutions.OAIQ067_SAT.SATComputability_VariableDeletion
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FixedClauseThreshold.Computability

open Finset

theorem delete_one_per_violation {n m : ℕ} (s : Fin n → Bool)
    (indices : Fin m → Fin 3 → Fin n) (signs : Fin m → Fin 3 → Bool) :
    deletionSatisfiable (relaxedViolations s indices signs) indices signs := by
  let bad := univ.filter fun j => ¬relaxedClauseSatisfied s (indices j) (signs j)
  refine ⟨bad.image (fun j => indices j 0), Finset.card_image_le, s, ?_⟩
  intro j
  by_cases h : relaxedClauseSatisfied s (indices j) (signs j)
  · exact Or.inr h
  · left
    refine ⟨0, Finset.mem_image.mpr ⟨j, ?_, rfl⟩⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ j, h⟩

end FixedClauseThreshold.Computability

end OAI
end

section
-- module Solutions.OAIQ067_SAT.SATComputability_RelaxedEnergy
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FixedClauseThreshold.Computability

open Finset
open scoped BigOperators

theorem relaxedMinimum_attained {n m : ℕ}
    (indices : Fin m → Fin 3 → Fin n) (signs : Fin m → Fin 3 → Bool) :
    ∃ s, relaxedViolations s indices signs = relaxedMinimumViolations indices signs := by
  unfold relaxedMinimumViolations
  exact Nat.find_spec (p := fun v => ∃ s, relaxedViolations s indices signs = v) _

theorem relaxedMinimum_le {n m : ℕ}
    (indices : Fin m → Fin 3 → Fin n) (signs : Fin m → Fin 3 → Bool) (s : Fin n → Bool) :
    relaxedMinimumViolations indices signs ≤ relaxedViolations s indices signs :=
  Nat.find_min' _ ⟨s, rfl⟩

end FixedClauseThreshold.Computability

end OAI
end

section
-- module Solutions.OAIQ067_SAT.SATComputability_RootEnergy
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FixedClauseThreshold.Computability

open DilutedSpinGlass _root_.MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal

theorem clauseMinimum_le_length {n m : ℕ} (cs : Fin m → RelaxedClause n) :
    clauseMinimum cs ≤ m := by
  exact (relaxedMinimum_le _ _ (fun _ => false)).trans
    ((Finset.card_filter_le _ _).trans_eq (Fintype.card_fin m))

end FixedClauseThreshold.Computability

end OAI
end

section
-- module Solutions.OAIQ067_SAT.SATComputability_AuxiliaryEnergy
attribute [-instance] _root_.OAI.FixedClauseThreshold.Computability.decidableClauseSatisfaction _root_.OAI.FixedClauseThreshold.Computability.decidableFormulaSatisfaction _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FixedClauseThreshold.Computability

open DilutedSpinGlass _root_.MeasureTheory ProbabilityTheory
open scoped Classical BigOperators NNReal

theorem finiteClauseAverage_iterate {n m : ℕ} {C : Type*} [Fintype C]
    (sat : C → Assignment n → Prop) (S : Finset (Assignment n)) :
    ((finiteClauseAverage sat)^[m] alive) S =
      uniformMean (fun F : Fin m → C => alive (S.filter (fun s => ∀ j, sat (F j) s))) := by
  induction m generalizing S with
  | zero =>
    simp only [Function.iterate_zero_apply, Fin.forall_fin_zero, Finset.filter_true]
    exact (uniformMean_const _).symm
  | succ m ih =>
    rw [Function.iterate_succ_apply', finiteClauseAverage, uniformMean_fin_succ]
    apply uniformMean_congr
    intro c
    rw [ih]
    apply uniformMean_congr
    intro F
    congr 1
    ext s
    simp only [Finset.mem_filter, Fin.forall_fin_succ, Fin.cons_zero, Fin.cons_succ]
    tauto

theorem relaxedFixedMinimum_nonneg (n m : ℕ) : 0 ≤ relaxedFixedMinimum n m :=
  uniformMean_nonneg (fun _ => Nat.cast_nonneg _)

theorem relaxedFixedMinimum_le (n m : ℕ) [NeZero n] : relaxedFixedMinimum n m ≤ m := by
  calc
    _ ≤ uniformMean (fun _cs : Fin m → RelaxedClause n => (m : ℝ)) :=
      uniformMean_mono (fun cs => by exact_mod_cast clauseMinimum_le_length cs)
    _ = _ := uniformMean_const _

end FixedClauseThreshold.Computability

end OAI
end

section
-- module Solutions.OAIQ067_SAT.SATComputability_CandidateEncoding
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FixedClauseThreshold.Computability

open Finset
open scoped Classical

theorem literalFalse_encode {n : ℕ} (D : Finset (Fin n)) (s : Fin n → Bool)
    (v : Fin n) (b : Bool) :
    ¬literalFalse (encodeDeletion D s) (v, b) ↔ v ∈ D ∨ s v = b := by
  by_cases hv : v ∈ D
  · simp [literalFalse, encodeDeletion, hv]
  · cases hb : s v <;> cases b <;> simp [literalFalse, encodeDeletion, hv, hb]

theorem deletedVariables_encode {n : ℕ} (D : Finset (Fin n)) (s : Fin n → Bool) :
    deletedVariables (encodeDeletion D s) = D := by
  ext v
  by_cases hv : v ∈ D <;> simp [deletedVariables, encodeDeletion, hv]

theorem deletionSatisfiable_iff_candidate {n m r : ℕ}
    (indices : Fin m → Fin 3 → Fin n) (signs : Fin m → Fin 3 → Bool) :
    deletionSatisfiable r indices signs ↔
      ∃ x : DeletionCandidate n, (deletedVariables x).card ≤ r ∧
        ∀ j, ∃ l, ¬literalFalse x (indices j l, signs j l) := by
  constructor
  · rintro ⟨D, hD, s, hs⟩
    refine ⟨encodeDeletion D s, ?_, ?_⟩
    · simpa only [deletedVariables_encode] using hD
    · intro j
      rcases hs j with ⟨l, hl⟩ | ⟨l, hl⟩
      · exact ⟨l, (literalFalse_encode D s _ _).mpr (Or.inl hl)⟩
      · exact ⟨l, (literalFalse_encode D s _ _).mpr (Or.inr hl)⟩
  · rintro ⟨x, hx, hs⟩
    let D := deletedVariables x
    let s : Fin n → Bool := fun v => (x v).getD false
    refine ⟨D, hx, s, ?_⟩
    intro j
    obtain ⟨l, hl⟩ := hs j
    cases hv : x (indices j l) with
    | none =>
        left
        exact ⟨l, by simp [D, deletedVariables, hv]⟩
    | some b =>
        right
        refine ⟨l, ?_⟩
        have hb : b = signs j l := by
          cases b <;> cases hsign : signs j l <;>
            simp_all [literalFalse]
        simpa only [s, hv, Option.getD_some] using hb

end FixedClauseThreshold.Computability

end OAI
end

section
-- module Solutions.OAIQ067_SAT.SATComputability_CandidateProcess
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FixedClauseThreshold.Computability

open DilutedSpinGlass
open scoped BigOperators Classical

theorem candidateStep_mono {n : ℕ} [NeZero n] (k : ℕ) :
    Monotone (candidateStep (n := n) k) := by
  intro f g h U
  exact FiniteLaw.expect_mono _ (fun _ => h _)

theorem candidateKill_iterate {n : ℕ} [NeZero n]
    (U : Finset (DeletionCandidate n)) (k d : ℕ) :
    batchKillProbability U k d = 1 - (candidateStep k)^[d] candidateAlive U := by
  rw [candidateStep_iterate]
  have he (cs : Fin d → Fin k → SignedLiteral n) :
      (if batchKills U cs then (1 : ℝ) else 0) =
        1 - candidateAlive (candidateResidual U cs) := by
    rw [candidateAlive, ← candidateResidual_empty_iff]
    by_cases h : candidateResidual U cs = ∅
    · simp [h]
    · simp [h, Finset.nonempty_iff_ne_empty]
  simp_rw [batchKillProbability, he, FiniteLaw.expect_sub, FiniteLaw.expect_const]

end FixedClauseThreshold.Computability

end OAI
end

section
-- module Solutions.OAIQ067_SAT.SATComputability_DeletionEnergy
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FixedClauseThreshold.Computability

open DilutedSpinGlass
open scoped Classical

theorem minimumDeletions_le_iff {n r : ℕ} {U : Finset (DeletionCandidate n)}
    (hU : U.Nonempty) : minimumDeletions U ≤ r ↔
      ∃ x ∈ U, (deletedVariables x).card ≤ r := by
  rw [minimumDeletions, dite_eq_left hU]
  exact Finset.inf'_le_iff hU

end FixedClauseThreshold.Computability

end OAI
end

section
-- module Solutions.OAIQ067_SAT.SATComputability_PoissonKilling
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FixedClauseThreshold.Computability

open DilutedSpinGlass _root_.MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal

theorem candidateAlive_le_one {n : ℕ} (U : Finset (DeletionCandidate n)) :
    candidateAlive U ≤ 1 := by unfold candidateAlive; split <;> norm_num

theorem candidateStep_alive_le {n : ℕ} [NeZero n] (k : ℕ) :
    candidateStep (n := n) k candidateAlive ≤ candidateAlive := by
  intro U
  by_cases hU : U.Nonempty
  · calc
      _ ≤ (FiniteLaw.uniform : FiniteLaw (Fin k → SignedLiteral n)).expect (fun _ => 1) :=
        FiniteLaw.expect_mono _ (fun _ => candidateAlive_le_one _)
      _ = candidateAlive U := by simp [candidateAlive, hU]
  · have he : U = ∅ := Finset.not_nonempty_iff_eq_empty.mp hU
    simp [he, candidateStep, candidateAlive]

theorem batchKillProbability_mono {n : ℕ} [NeZero n]
    (U : Finset (DeletionCandidate n)) (k : ℕ) : Monotone (batchKillProbability U k) := by
  have hstep (d : ℕ) : (candidateStep k)^[d+1] candidateAlive ≤
      (candidateStep (n := n) k)^[d] candidateAlive := by
    rw [Function.iterate_succ_apply]
    exact (candidateStep_mono k).iterate d (candidateStep_alive_le k)
  have ha : Antitone (fun d => (candidateStep k)^[d] candidateAlive U) :=
    antitone_nat_of_succ_le (fun d => hstep d U)
  intro d e hde
  rw [candidateKill_iterate, candidateKill_iterate]
  linarith [ha hde]

theorem batchKillProbability_nonneg {n : ℕ} [NeZero n]
    (U : Finset (DeletionCandidate n)) (k d : ℕ) : 0 ≤ batchKillProbability U k d := by
  apply FiniteLaw.expect_nonneg
  intro cs
  split <;> norm_num

theorem batchKillProbability_le_one {n : ℕ} [NeZero n]
    (U : Finset (DeletionCandidate n)) (k d : ℕ) : batchKillProbability U k d ≤ 1 := by
  apply (FiniteLaw.expect_mono _ (g := fun _ => 1) ?_).trans_eq (FiniteLaw.expect_const _ _)
  intro cs
  split <;> norm_num

theorem poissonKillProbability_mono_rate {n : ℕ} [NeZero n]
    (U : Finset (DeletionCandidate n)) (k : ℕ) :
    Monotone (poissonKillProbability U k) := by
  have hi (r : ℝ≥0) : Integrable (fun d => batchKillProbability U k d)
      (poissonMeasure r) := by
    apply Integrable.of_bound (measurable_of_countable _).aestronglyMeasurable 1
    exact Eventually.of_forall (fun d => abs_le.mpr
      ⟨by linarith [batchKillProbability_nonneg U k d], batchKillProbability_le_one U k d⟩)
  intro r s hrs
  have hs : s = r + (s-r) := (add_tsub_cancel_of_le hrs).symm
  unfold poissonKillProbability
  rw [hs, ← poissonMeasure_conv_poissonMeasure, integral_conv (by
    simpa only [poissonMeasure_conv_poissonMeasure] using hi (r+(s-r)))]
  apply integral_mono (hi r)
  · apply Integrable.of_bound (measurable_of_countable _).aestronglyMeasurable 1
    exact Eventually.of_forall (fun d => by
      simpa only [Real.norm_eq_abs] using
        (abs_integral_le_bound (μ := poissonMeasure (s-r)) (fun e => abs_le.mpr
          ⟨by linarith [batchKillProbability_nonneg U k (d+e)],
            batchKillProbability_le_one U k (d+e)⟩)))
  · intro d
    have hshift : Integrable (fun e => batchKillProbability U k (d+e))
        (poissonMeasure (s-r)) := by
      apply Integrable.of_bound (measurable_of_countable _).aestronglyMeasurable 1
      exact Eventually.of_forall (fun e => abs_le.mpr
        ⟨by linarith [batchKillProbability_nonneg U k (d+e)], batchKillProbability_le_one U k (d+e)⟩)
    calc
      _ = ∫ _e : ℕ, batchKillProbability U k d ∂poissonMeasure (s-r) := by simp
      _ ≤ _ := integral_mono (integrable_const _) hshift
        (fun e => batchKillProbability_mono U k (Nat.le_add_right d e))

end FixedClauseThreshold.Computability

end OAI
end

section
-- module Solutions.OAIQ067_SAT.SATComputability_PoissonKernel
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FixedClauseThreshold.Computability

open DilutedSpinGlass _root_.MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal

theorem poissonMixture_integrable_expect {Ω : Type*} [Fintype Ω]
    (r : ℝ≥0) (P : ℕ → FiniteLaw Ω) (f : Ω → ℝ) :
    Integrable (fun m => (P m).expect f) (poissonMeasure r) := by
  unfold FiniteLaw.expect
  exact integrable_finsetSum _ (fun x _ => (poisson_weight_integrable r P x).mul_const (f x))

theorem candidateBlock_expect {n : ℕ} [NeZero n]
    (r : ℝ≥0) (k : ℕ) (U : Finset (DeletionCandidate n))
    (f : Finset (DeletionCandidate n) → ℝ) :
    (candidateBlock r k U).expect f =
      ∫ d, (candidateStep k)^[d] f U ∂poissonMeasure r := by
  rw [candidateBlock, poissonMixture_expect]
  simp only [candidateFixedBlock_expect]

end FixedClauseThreshold.Computability

end OAI
end

section
-- module Solutions.OAIQ067_SAT.SATComputability_PoissonSemigroup
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FixedClauseThreshold.Computability

open DilutedSpinGlass _root_.MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal

theorem finite_expect_integral {Ω X : Type*} [Fintype Ω] [MeasurableSpace X]
    (P : FiniteLaw Ω) (μ : Measure X) (f : X → Ω → ℝ)
    (hf : ∀ x, Integrable (fun m => f m x) μ) :
    P.expect (fun x => ∫ m, f m x ∂μ) = ∫ m, P.expect (f m) ∂μ := by
  unfold FiniteLaw.expect
  rw [integral_finsetSum _ (fun x _ => (hf x).const_mul (P.weight x))]
  apply Finset.sum_congr rfl
  intro x _
  rw [integral_const_mul]

theorem candidateStep_iterate_bound {n : ℕ} [NeZero n]
    (k d : ℕ) (f : Finset (DeletionCandidate n) → ℝ) {B : ℝ}
    (hf : ∀ U, |f U| ≤ B) (U : Finset (DeletionCandidate n)) :
    |(candidateStep k)^[d] f U| ≤ B := by
  rw [← candidateFixedBlock_expect]
  exact FiniteLaw.abs_expect_le _ hf

theorem candidateBlock_comp {n : ℕ} [NeZero n]
    (r s : ℝ≥0) (k : ℕ) (U : Finset (DeletionCandidate n))
    (f : Finset (DeletionCandidate n) → ℝ) :
    (candidateBlock (r+s) k U).expect f =
      (candidateBlock r k U).expect (fun V => (candidateBlock s k V).expect f) := by
  let B := ∑ V : Finset (DeletionCandidate n), |f V|
  have hf : ∀ V, |f V| ≤ B := fun V =>
    Finset.single_le_sum (fun W _ => abs_nonneg (f W)) (Finset.mem_univ V)
  have hi (v : ℝ≥0) (V : Finset (DeletionCandidate n)) :
      Integrable (fun d => (candidateStep k)^[d] f V) (poissonMeasure v) := by
    apply Integrable.of_bound (measurable_of_countable _).aestronglyMeasurable B
    exact Eventually.of_forall (fun d => by
      simpa only [Real.norm_eq_abs] using candidateStep_iterate_bound k d f hf V)
  symm
  calc
    _ = (candidateBlock r k U).expect
        (fun V => ∫ e, (candidateStep k)^[e] f V ∂poissonMeasure s) := by
      simp only [candidateBlock_expect]
    _ = ∫ e, (candidateBlock r k U).expect
        (fun V => (candidateStep k)^[e] f V) ∂poissonMeasure s :=
      finite_expect_integral _ _ _ (hi s)
    _ = ∫ e, ∫ d, (candidateStep k)^[d] ((candidateStep k)^[e] f) U
        ∂poissonMeasure r ∂poissonMeasure s := by simp only [candidateBlock_expect]
    _ = ∫ e, ∫ d, (candidateStep k)^[e+d] f U
        ∂poissonMeasure r ∂poissonMeasure s := by
      apply integral_congr_ae
      exact Eventually.of_forall (fun e => integral_congr_ae
        (Eventually.of_forall (fun d => by
          dsimp only
          rw [Nat.add_comm e d, Function.iterate_add_apply])))
    _ = ∫ m, (candidateStep k)^[m] f U ∂poissonMeasure (r+s) := by
      rw [add_comm r s, ← poissonMeasure_conv_poissonMeasure,
        integral_conv (by simpa only [poissonMeasure_conv_poissonMeasure] using hi (s+r) U)]
    _ = _ := (candidateBlock_expect _ _ _ _).symm

end FixedClauseThreshold.Computability

end OAI
end

section
-- module Solutions.OAIQ067_SAT.SATComputability_CandidateMasks
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FixedClauseThreshold.Computability

open DilutedSpinGlass _root_.MeasureTheory ProbabilityTheory
open scoped NNReal Classical

theorem candidateResidual_inter {n k d : ℕ} (U : Finset (DeletionCandidate n))
    (cs : Fin d → Fin k → SignedLiteral n) :
    candidateResidual U cs = U ∩ candidateResidual Finset.univ cs := by
  ext x
  simp only [candidateResidual, Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and]

theorem candidateFixedBlock_mask {n : ℕ} [NeZero n] (k d : ℕ)
    (U : Finset (DeletionCandidate n)) (f : Finset (DeletionCandidate n) → ℝ) :
    (candidateFixedBlock k d Finset.univ).expect (fun V => f (U ∩ V)) =
      (candidateFixedBlock k d U).expect f := by
  simp only [candidateFixedBlock_expect, candidateStep_iterate]
  apply FiniteLaw.expect_congr
  intro cs
  rw [candidateResidual_inter U cs]

theorem candidateBlock_mask {n : ℕ} [NeZero n] (r : ℝ≥0) (k : ℕ)
    (U : Finset (DeletionCandidate n)) (f : Finset (DeletionCandidate n) → ℝ) :
    (candidateBlock r k Finset.univ).expect (fun V => f (U ∩ V)) =
      (candidateBlock r k U).expect f := by
  simp only [candidateBlock, poissonMixture_expect, candidateFixedBlock_mask]

end FixedClauseThreshold.Computability

end OAI
end

section
-- module Solutions.OAIQ067_SAT.SATComputability_MaskLifetime
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FixedClauseThreshold.Computability

open DilutedSpinGlass
open scoped BigOperators NNReal Classical

theorem candidateBlock_zero_expect {n : ℕ} [NeZero n] (k : ℕ)
    (U : Finset (DeletionCandidate n)) (f : Finset (DeletionCandidate n) → ℝ) :
    (candidateBlock 0 k U).expect f = f U := by
  rw [candidateBlock_expect, ProbabilityTheory.integral_poissonMeasure]
  simp [zero_pow_eq, ite_div, ite_mul]

theorem maskLifetime_mean {n : ℕ} [NeZero n] (r : ℝ≥0) (k m : ℕ)
    (U : Finset (DeletionCandidate n)) :
    (FiniteLaw.pi (fun _ : Fin m => candidateBlock r k Finset.univ)).expect
      (maskLifetime m U) =
      ∑ t ∈ Finset.range m, (candidateBlock (r*t) k U).expect candidateAlive := by
  induction m generalizing U with
  | zero => simp [maskLifetime]
  | succ m ih =>
    rw [FiniteLaw.expect_pi_cons]
    simp only [maskLifetime, Fin.cons_zero, Fin.tail_cons, FiniteLaw.expect_add,
      FiniteLaw.expect_const, ih, FiniteLaw.expect_sum]
    rw [Finset.sum_range_succ']
    simp only [Nat.cast_zero, mul_zero, candidateBlock_zero_expect]
    rw [add_comm (candidateAlive U)]
    congr 1
    apply Finset.sum_congr rfl
    intro t _
    rw [candidateBlock_mask r k U (fun V => (candidateBlock (r*t) k V).expect candidateAlive)]
    rw [← candidateBlock_comp]
    congr 2
    push_cast
    ring

end FixedClauseThreshold.Computability

end OAI
end

section
-- module Solutions.OAIQ067_SAT.SATComputability_CandidateProbability
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.FixedClauseThreshold.Computability.decidableClauseSatisfaction _root_.OAI.FixedClauseThreshold.Computability.decidableFormulaSatisfaction _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FixedClauseThreshold.Computability

open DilutedSpinGlass _root_.MeasureTheory ProbabilityTheory
open scoped Classical NNReal

theorem candidate_budget_survival {n m r : ℕ} (cs : Fin m → Fin 3 → SignedLiteral n) :
    (candidateResidual (deletionBudgetMask n r) cs).Nonempty ↔
      deletionSatisfiable r (fun j l => (cs j l).1) (fun j l => (cs j l).2) := by
  rw [deletionSatisfiable_iff_candidate]
  simp only [candidateResidual, deletionBudgetMask, Finset.filter_nonempty_iff,
    Finset.mem_filter, Finset.mem_univ, true_and, not_forall, Prod.eta]

theorem candidate_zero_survival {n m : ℕ} (cs : Fin m → Fin 3 → SignedLiteral n) :
    (candidateResidual (deletionBudgetMask n 0) cs).Nonempty ↔
      (Finset.univ.filter (fun s : Assignment n => ∀ j, auxiliarySatisfies s (cs j))).Nonempty := by
  rw [candidate_budget_survival]
  simp only [Finset.filter_nonempty_iff, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨D,hD,s,hs⟩
    have hD0 : D = ∅ := Finset.card_eq_zero.mp (Nat.eq_zero_of_le_zero hD)
    subst D
    exact ⟨s,fun j => by simpa [auxiliarySatisfies, relaxedClauseSatisfied] using hs j⟩
  · rintro ⟨s,hs⟩
    exact ⟨∅,by simp,s,fun j => Or.inr (hs j)⟩

theorem finite_uniform_expect_eq_mean {A : Type*} [Fintype A] [Nonempty A] (f : A → ℝ) :
    (FiniteLaw.uniform : FiniteLaw A).expect f = uniformMean f := by
  simp only [FiniteLaw.expect, FiniteLaw.uniform, uniformMean,
    div_eq_mul_inv, Finset.sum_mul, mul_comm]

theorem candidateStep_zero_survival {n : ℕ} [NeZero n] (m : ℕ) :
    (candidateStep (n := n) 3)^[m] candidateAlive (deletionBudgetMask n 0) =
      auxiliaryProbability n 3 m := by
  rw [candidateStep_iterate, finite_uniform_expect_eq_mean]
  unfold auxiliaryProbability auxiliarySurvival auxiliaryAverage embeddedAverage
  rw [finiteClauseAverage_iterate]
  apply uniformMean_congr
  intro cs
  unfold candidateAlive alive
  congr 1
  exact propext (candidate_zero_survival cs)

theorem candidateBlock_zero_survival {n : ℕ} [NeZero n] (r : ℝ≥0) :
    (candidateBlock r 3 (deletionBudgetMask n 0)).expect candidateAlive =
      ∫ m : ℕ, auxiliaryProbability n 3 m ∂poissonMeasure r := by
  rw [candidateBlock_expect]
  simp only [candidateStep_zero_survival]

theorem candidate_full_nonempty {n m : ℕ} (cs : Fin m → Fin 3 → SignedLiteral n) :
    (candidateResidual Finset.univ cs).Nonempty := by
  refine ⟨fun _ => none, ?_⟩
  simp only [candidateResidual, Finset.mem_filter, Finset.mem_univ, true_and]
  intro j hj
  have h := hj 0
  simp [literalFalse] at h

theorem candidate_minimumDeletions_le {n m : ℕ} (cs : Fin m → RelaxedClause n) :
    minimumDeletions (candidateResidual Finset.univ (fun j l => ((cs j).1 l, (cs j).2 l))) ≤
      clauseMinimum cs := by
  obtain ⟨s,hs⟩ := relaxedMinimum_attained (fun j => (cs j).1) (fun j => (cs j).2)
  have hd := delete_one_per_violation s (fun j => (cs j).1) (fun j => (cs j).2)
  change relaxedViolations s (fun j => (cs j).1) (fun j => (cs j).2) = clauseMinimum cs at hs
  rw [hs] at hd
  rw [deletionSatisfiable_iff_candidate] at hd
  obtain ⟨x,hx,hxs⟩ := hd
  apply (minimumDeletions_le_iff (candidate_full_nonempty _)).mpr
  refine ⟨x, ?_, hx⟩
  simp only [candidateResidual, Finset.mem_filter, Finset.mem_univ, true_and]
  intro j hj
  obtain ⟨l,hl⟩ := hxs j
  exact hl (hj l)

end FixedClauseThreshold.Computability

end OAI
end

section
-- module Solutions.OAIQ067_SAT.SATComputability_MeanSurvival
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FixedClauseThreshold.Computability

open DilutedSpinGlass
open scoped NNReal BigOperators Classical

theorem candidateBlock_survival_antitone {n : ℕ} [NeZero n] (k : ℕ)
    (U : Finset (DeletionCandidate n)) :
    Antitone (fun r => (candidateBlock r k U).expect candidateAlive) := by
  intro r s hrs
  simp only [candidateBlock_expect_alive]
  exact sub_le_sub_left (poissonKillProbability_mono_rate U k hrs) 1

theorem survival_le_mean_lifetime {n M t : ℕ} [NeZero n]
    (ht : t ≤ M) (U : Finset (DeletionCandidate n)) :
    (t : ℝ)*(candidateBlock (n := n) t 3 U).expect candidateAlive ≤
      (FiniteLaw.pi (fun _ : Fin M => candidateBlock (n := n) 1 3 Finset.univ)).expect
        (maskLifetime M U) := by
  rw [maskLifetime_mean]
  simp only [one_mul]
  calc
    _ = ∑ _s ∈ Finset.range t, (candidateBlock (n := n) t 3 U).expect candidateAlive := by
      simp
    _ ≤ ∑ s ∈ Finset.range t, (candidateBlock (n := n) s 3 U).expect candidateAlive := by
      apply Finset.sum_le_sum
      intro s hs
      exact candidateBlock_survival_antitone 3 U (by exact_mod_cast
        (Finset.mem_range.mp hs).le)
    _ ≤ ∑ s ∈ Finset.range M, (candidateBlock (n := n) s 3 U).expect candidateAlive := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono ht)
      intro s _ _
      exact FiniteLaw.expect_nonneg _ candidateAlive_nonneg

theorem antitone_sum_bound (q : ℕ → ℝ) (hq : Antitone q)
    (h0 : ∀ s, 0 ≤ q s) (h1 : ∀ s, q s ≤ 1) (M t : ℕ) :
    ∑ s ∈ Finset.range M, q s ≤ t + (M : ℝ)*q t := by
  by_cases ht : t ≤ M
  · rw [← Nat.add_sub_of_le ht, Finset.sum_range_add]
    have hfirst : ∑ s ∈ Finset.range t, q s ≤ (t : ℝ) := by
      calc
        _ ≤ ∑ _s ∈ Finset.range t, (1 : ℝ) := Finset.sum_le_sum (fun s _ => h1 s)
        _ = _ := by simp
    have hlast : ∑ s ∈ Finset.range (M-t), q (t+s) ≤ (M-t : ℕ)*q t := by
      calc
        _ ≤ ∑ _s ∈ Finset.range (M-t), q t :=
          Finset.sum_le_sum (fun s _ => hq (Nat.le_add_right t s))
        _ = _ := by simp
    have htail : ((M-t : ℕ) : ℝ)*q t ≤ (t+(M-t) : ℕ)*q t :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.le_add_left (M-t) t) (h0 t)
    push_cast at htail ⊢
    linarith
  · have hMt : M ≤ t := (Nat.lt_of_not_ge ht).le
    calc
      _ ≤ ∑ _s ∈ Finset.range M, (1 : ℝ) := Finset.sum_le_sum (fun s _ => h1 s)
      _ = M := by simp
      _ ≤ t := by exact_mod_cast hMt
      _ ≤ t + (M : ℝ)*q t := le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg M) (h0 t))

theorem zero_lifetime_mean_upper (n : ℕ) [NeZero n] (b : ℝ≥0) :
    (FiniteLaw.pi (fun _ : Fin (20*n) => candidateBlock (n := n) 1 3 Finset.univ)).expect
      (maskLifetime (20*n) (deletionBudgetMask n 0)) ≤
        ⌈(b : ℝ)*n⌉₊ + (20*n : ℕ)*auxiliaryPoissonProbability n b := by
  rw [maskLifetime_mean]
  simp only [one_mul]
  have h := antitone_sum_bound
    (fun s => (candidateBlock (n := n) s 3 (deletionBudgetMask n 0)).expect candidateAlive)
    (fun s t hst => candidateBlock_survival_antitone 3 _ (by exact_mod_cast hst))
    (fun _ => FiniteLaw.expect_nonneg _ candidateAlive_nonneg)
    (fun _ => (FiniteLaw.expect_mono _ candidateAlive_le_one).trans_eq (FiniteLaw.expect_const _ 1))
    (20*n) ⌈(b : ℝ)*n⌉₊
  apply h.trans
  apply add_le_add le_rfl
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  have hb : b*n ≤ (⌈(b : ℝ)*n⌉₊ : ℝ≥0) := by
    apply NNReal.coe_le_coe.mp
    simpa only [NNReal.coe_mul, NNReal.coe_natCast] using Nat.le_ceil ((b : ℝ)*n)
  have hs := candidateBlock_survival_antitone 3 (deletionBudgetMask n 0) hb
  simpa only [candidateBlock_zero_survival, auxiliaryPoissonProbability] using hs

theorem minimumDeletions_survival_lower {n r : ℕ} (hr : r ≤ n+1)
    (U : Finset (DeletionCandidate n)) :
    (r : ℝ)*(1-candidateAlive (U ∩ deletionBudgetMask n r)) ≤ minimumDeletions U := by
  by_cases h : (U ∩ deletionBudgetMask n r).Nonempty
  · simp only [candidateAlive, ite_eq_left h, sub_self, mul_zero]
    exact Nat.cast_nonneg _
  · simp only [candidateAlive, ite_eq_right h, sub_zero, mul_one]
    by_cases hU : U.Nonempty
    · have hm : r < minimumDeletions U := by
        apply Nat.lt_of_not_ge
        intro hm
        obtain ⟨x,hx,hxr⟩ := (minimumDeletions_le_iff hU).mp hm
        exact h ⟨x,Finset.mem_inter.mpr ⟨hx,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hxr⟩⟩⟩
      exact_mod_cast hm.le
    · rw [minimumDeletions, dite_eq_right hU]
      exact_mod_cast hr

theorem block_minimumDeletions_lower {n r : ℕ} [NeZero n] (hr : r ≤ n+1) (t : ℝ≥0) :
    (r : ℝ)*(1-(candidateBlock t 3 (deletionBudgetMask n r)).expect candidateAlive) ≤
      (candidateBlock (n := n) t 3 Finset.univ).expect (fun U => (minimumDeletions U : ℝ)) := by
  have h := (candidateBlock (n := n) t 3 Finset.univ).expect_mono
    (minimumDeletions_survival_lower hr)
  rw [FiniteLaw.expect_mul_left, FiniteLaw.expect_sub, FiniteLaw.expect_const] at h
  have he : (candidateBlock (n := n) t 3 Finset.univ).expect
      (fun x => candidateAlive (x ∩ deletionBudgetMask n r)) =
      (candidateBlock t 3 (deletionBudgetMask n r)).expect candidateAlive := by
    calc
      _ = (candidateBlock (n := n) t 3 Finset.univ).expect
          (fun x => candidateAlive (deletionBudgetMask n r ∩ x)) :=
        FiniteLaw.expect_congr _ (fun x => congrArg candidateAlive (Finset.inter_comm x _))
      _ = _ := candidateBlock_mask t 3 (deletionBudgetMask n r) candidateAlive
  rwa [he] at h

end FixedClauseThreshold.Computability

end OAI
end

section
-- module Solutions.OAIQ067_SAT.SATComputability_CandidateEnergy
attribute [-instance] _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FixedClauseThreshold.Computability

open DilutedSpinGlass _root_.MeasureTheory ProbabilityTheory
open scoped Classical NNReal

theorem candidateStep_minimumDeletions_le {n : ℕ} [NeZero n] (m : ℕ) :
    (candidateStep (n := n) 3)^[m] (fun U => (minimumDeletions U : ℝ)) Finset.univ ≤
      relaxedFixedMinimum n m := by
  rw [candidateStep_iterate, finite_uniform_expect_eq_mean]
  let e := Equiv.piCongrRight (fun _ : Fin m => relaxedClauseEquiv n)
  rw [← uniformMean_equiv e]
  apply uniformMean_mono
  intro cs
  exact_mod_cast candidate_minimumDeletions_le cs

theorem candidateBlock_minimumDeletions_le (n : ℕ) [NeZero n] (a : ℝ≥0) :
    (candidateBlock (n := n) (a*n) 3 Finset.univ).expect
      (fun U => (minimumDeletions U : ℝ)) ≤ relaxedPoissonMinimum n a := by
  rw [candidateBlock_expect, relaxedPoissonMinimum]
  apply integral_mono
  · simpa only [candidateFixedBlock_expect] using
      poissonMixture_integrable_expect (a*n)
        (fun m => candidateFixedBlock (n := n) 3 m Finset.univ)
        (fun U => (minimumDeletions U : ℝ))
  · apply (poisson_integrable_count (a*n)).mono'
      (measurable_of_countable _).aestronglyMeasurable
    exact ae_of_all _ (fun m => by
      simpa only [Real.norm_eq_abs, abs_of_nonneg (relaxedFixedMinimum_nonneg n m)] using
        relaxedFixedMinimum_le n m)
  · exact candidateStep_minimumDeletions_le

theorem mean_lifetime_energy_lower {n r t : ℕ} [NeZero n]
    (hr : r ≤ n+1) (ht : 0 < t) (htM : t ≤ 20*n) (a : ℝ≥0)
    (hta : (t : ℝ≥0) ≤ a*n) :
    (r : ℝ)*(1-
      (FiniteLaw.pi (fun _ : Fin (20*n) => candidateBlock (n := n) 1 3 Finset.univ)).expect
        (maskLifetime (20*n) (deletionBudgetMask n r)) / t) ≤
      relaxedPoissonMinimum n a := by
  have htR : (0 : ℝ) < t := by exact_mod_cast ht
  have hs := survival_le_mean_lifetime htM (deletionBudgetMask n r)
  have hp := candidateBlock_survival_antitone 3 (deletionBudgetMask n r) hta
  have hq : (candidateBlock (n := n) t 3 (deletionBudgetMask n r)).expect candidateAlive ≤
      (FiniteLaw.pi (fun _ : Fin (20*n) => candidateBlock (n := n) 1 3 Finset.univ)).expect
        (maskLifetime (20*n) (deletionBudgetMask n r)) / t :=
    (le_div_iff₀ htR).mpr (by nlinarith only [hs])
  have hb := block_minimumDeletions_lower hr (a*n)
  have hm := candidateBlock_minimumDeletions_le n a
  exact (mul_le_mul_of_nonneg_left (sub_le_sub_left (hp.trans hq) 1)
    (Nat.cast_nonneg r)).trans (hb.trans hm)

end FixedClauseThreshold.Computability

end OAI
end

section
-- module Solutions.OAIQ067_SAT.SATComputability_CavityExpressions
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.DilutedSpinGlass.UniversalDictionary.reservoirLaw_prob
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FixedClauseThreshold.Computability.FiniteArithmetic

open Nat.Partrec DilutedSpinGlass RapidForcing.EffectiveArithmetic
open scoped BigOperators

theorem exp_edgeExpression (β : ℚ) (J : Fin 3 → Bool) (xs : Fin 3 → Code) :
    Real.exp (expressionValue (edgeExpression β J xs)) =
      edge (satInteraction (β : ℝ) J) (fun i => expressionValue (xs i)) := by
  unfold edgeExpression edge
  simp only [exp_binaryLogSumExpression, exp_boltzmannAtom, clausePenalty_cast]
  rw [sum_bool_vector_succ]
  simp_rw [sum_bool_vector_succ]
  simp only [Fintype.sum_unique]
  rfl

theorem edgeExpression_value (β : ℚ) (J : Fin 3 → Bool) (xs : Fin 3 → Code) :
    expressionValue (edgeExpression β J xs) =
      Real.log (edge (satInteraction (β : ℝ) J) (fun i => expressionValue (xs i))) := by
  rw [← exp_edgeExpression, Real.log_exp]

attribute [local irreducible] edgeExpression siteExpression

end FixedClauseThreshold.Computability.FiniteArithmetic

end OAI
end

section
-- module Solutions.OAIQ067_SAT.SATComputability_CertificateSearch
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FixedClauseThreshold.Computability

open Filter
open scoped Topology
open RapidForcing.EffectiveArithmetic

theorem tolerance_pos (r : ℕ) : 0 < tolerance r := by
  unfold tolerance
  positivity

theorem certificateTest_computable {lower upper : ℕ → ℚ} {valid : ℕ → Bool}
    (hl : Computable lower) (hu : Computable upper) (hv : Computable valid) :
    Computable₂ (certificateTest lower upper valid) := by
  unfold Computable₂ certificateTest
  fun_prop

theorem certificateProgram_partrec {lower upper : ℕ → ℚ} {valid : ℕ → Bool}
    (hl : Computable lower) (hu : Computable upper) (hv : Computable valid) :
    Partrec (certificateProgram lower upper valid) :=
  Partrec.rfindOpt (certificateTest_computable hl hu hv)

theorem certificateTest_sound {α : ℝ} {lower upper : ℕ → ℚ} {valid : ℕ → Bool}
    (hl : ∀ i, (lower i : ℝ) ≤ α)
    (hu : ∀ j, valid j = true → α ≤ (upper j : ℝ))
    {r n : ℕ} {q : ℚ} (hq : q ∈ certificateTest lower upper valid r n) :
    |(q : ℝ) - α| ≤ (tolerance r : ℝ) := by
  dsimp only [certificateTest] at hq
  split_ifs at hq with h
  · obtain rfl := Option.mem_some_iff.mp hq
    have hlo := hl n.unpair.1
    have hup := hu n.unpair.2 h.1
    have hwidth : (upper n.unpair.2 : ℝ) - lower n.unpair.1 ≤
        2 * (tolerance r : ℝ) := by exact_mod_cast h.2
    push_cast
    apply abs_le.mpr
    constructor <;> linarith
  · contradiction

theorem certificateProgram_total {α : ℝ} {lower upper : ℕ → ℚ} {valid : ℕ → Bool}
    (hl : ∀ ε : ℝ, 0 < ε → ∃ i, α - ε < (lower i : ℝ))
    (hu : ∀ ε : ℝ, 0 < ε → ∃ j, valid j = true ∧ (upper j : ℝ) < α + ε)
    (r : ℕ) : (certificateProgram lower upper valid r).Dom := by
  have hε : (0 : ℝ) < tolerance r := by exact_mod_cast tolerance_pos r
  obtain ⟨i, hi⟩ := hl (tolerance r) hε
  obtain ⟨j, hj, hj'⟩ := hu (tolerance r) hε
  apply Nat.rfindOpt_dom.mpr
  refine ⟨Nat.pair i j, (lower i + upper j) / 2, ?_⟩
  have hwidth : upper j - lower i ≤ 2 * tolerance r := by
    have : (upper j : ℝ) - lower i ≤ 2 * (tolerance r : ℝ) := by linarith
    exact_mod_cast this
  simp [certificateTest, hj, hwidth]

theorem finite_certificate_search {α : ℝ}
    {lower upper : ℕ → ℚ} {valid : ℕ → Bool}
    (hlc : Computable lower) (huc : Computable upper) (hvc : Computable valid)
    (hls : ∀ i, (lower i : ℝ) ≤ α)
    (hus : ∀ j, valid j = true → α ≤ (upper j : ℝ))
    (hld : ∀ ε : ℝ, 0 < ε → ∃ i, α - ε < (lower i : ℝ))
    (hud : ∀ ε : ℝ, 0 < ε → ∃ j, valid j = true ∧ (upper j : ℝ) < α + ε) :
    ∃ q : ℕ → ℚ, Computable q ∧
      (∀ r, q r ∈ certificateProgram lower upper valid r) ∧
      ∀ r, |(q r : ℝ) - α| ≤ (2 ^ r : ℝ)⁻¹ := by
  let total := certificateProgram_total hld hud
  let q := fun r => (certificateProgram lower upper valid r).get (total r)
  have hq (r : ℕ) : q r ∈ certificateProgram lower upper valid r := Part.get_mem _
  refine ⟨q, (certificateProgram_partrec hlc huc hvc).of_eq_tot hq, hq, ?_⟩
  intro r
  obtain ⟨n, hn⟩ := Nat.rfindOpt_spec (hq r)
  simpa only [tolerance, Rat.cast_inv, Rat.cast_pow, Rat.cast_ofNat] using
    certificateTest_sound hls hus hn

theorem rational_sequence_code {q : ℕ → ℚ} (hq : Computable q) :
    ∃ c : Nat.Partrec.Code, ∀ r,
      Nat.Partrec.Code.eval c r = Part.some (Encodable.encode (q r)) := by
  have hencode := Computable.encode.comp hq
  obtain ⟨c, hc⟩ := Nat.Partrec.Code.exists_code.mp (Partrec.nat_iff.mp hencode)
  exact ⟨c, fun r => congrFun hc r⟩

end FixedClauseThreshold.Computability

end OAI
end

section
-- module Solutions.OAIQ067_SAT.SATComputability_RationalWeights
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.FixedClauseThreshold.Computability.rationalWeightsEncodable _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FixedClauseThreshold.Computability

open DilutedSpinGlass
open scoped BigOperators

theorem exists_rational_weights_near {ι : Type*} [Fintype ι]
    (w : FiniteLaw ι) {ε : ℝ} (hε : 0 < ε) :
    ∃ q : RationalWeights ι, ∀ i, |(q.val i : ℝ) - w.weight i| < ε := by
  classical
  let δ := ε / (2 * (Fintype.card ι + 1))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hsmall : (Fintype.card ι + 1 : ℝ) * δ < ε := by
    dsimp [δ]
    have hn : (0 : ℝ) < Fintype.card ι + 1 := by positivity
    field_simp
    linarith
  have hex (i : ι) : ∃ q : ℚ, w.weight i < q ∧ (q : ℝ) < w.weight i + δ :=
    exists_rat_btwn (by linarith)
  choose v hv using hex
  let S : ℚ := ∑ i, v i
  have hSreal : (S : ℝ) = ∑ i, (v i : ℝ) := by simp [S]
  have hS : 1 ≤ (S : ℝ) := by
    rw [hSreal, ← w.total]
    exact Finset.sum_le_sum (fun i _ => (hv i).1.le)
  have hSupper : (S : ℝ) ≤ 1 + Fintype.card ι * δ := by
    calc
      (S : ℝ) = ∑ i, (v i : ℝ) := hSreal
      _ ≤ ∑ i, (w.weight i + δ) := Finset.sum_le_sum (fun i _ => (hv i).2.le)
      _ = _ := by simp [Finset.sum_add_distrib, w.total]
  have hSpos : 0 < S := by exact_mod_cast (show (0 : ℝ) < S by linarith)
  let q : RationalWeights ι := ⟨fun i => v i / S, by
    constructor
    · intro i
      have hv0 : 0 ≤ v i := by exact_mod_cast ((w.nonneg i).trans (hv i).1.le)
      exact div_nonneg hv0 hSpos.le
    · rw [← Finset.sum_div]
      exact div_self hSpos.ne'⟩
  refine ⟨q, fun i => ?_⟩
  have hwi : w.weight i ≤ 1 := by
    rw [← w.total]
    exact Finset.single_le_sum (fun j _ => w.nonneg j) (Finset.mem_univ i)
  have hvi := hv i
  have hw0 := w.nonneg i
  have hs0 : 0 < (S : ℝ) := by linarith
  have hδsmall : δ < ε := by
    have hn : (1 : ℝ) ≤ Fintype.card ι + 1 := by
      linarith [show (0 : ℝ) ≤ Fintype.card ι from Nat.cast_nonneg _]
    nlinarith
  have hnsmall : (Fintype.card ι : ℝ) * δ < ε := by linarith
  have hprod := mul_le_mul_of_nonneg_left hSupper hw0
  have hcard := mul_le_mul_of_nonneg_right hwi
    (show 0 ≤ (Fintype.card ι : ℝ) * δ by positivity)
  have heps := mul_le_mul_of_nonneg_left hS hε.le
  have hws := mul_le_mul_of_nonneg_left hS hw0
  change |((v i / S : ℚ) : ℝ) - w.weight i| < ε
  rw [Rat.cast_div, abs_lt]
  constructor
  · have : w.weight i - ε < (v i : ℝ) / S := by
      apply (lt_div_iff₀ hs0).mpr
      nlinarith
    linarith
  · have : (v i : ℝ) / S < w.weight i + ε := by
      apply (div_lt_iff₀ hs0).mpr
      nlinarith
    linarith

end FixedClauseThreshold.Computability

end OAI
end

section
-- module Solutions.OAIQ067_SAT.SATComputability_RationalHierarchy
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FixedClauseThreshold.Computability

open DilutedSpinGlass _root_.MeasureTheory Set Filter TopologicalSpace
open scoped Topology BigOperators NNReal

theorem rationalWeights_atomic_dense {ι : Type*} [Fintype ι] :
    DenseRange (RationalWeights.toAtomic (ι := ι)) := by
  intro w
  apply Metric.mem_closure_iff.mpr
  intro ε hε
  let P : FiniteLaw ι := ⟨fun i => w.val i, fun i => (w.val i).property, by
    simpa using congrArg (fun q : ℝ≥0 => (q : ℝ)) w.property⟩
  obtain ⟨q, hq⟩ := exists_rational_weights_near P hε
  refine ⟨q.toAtomic, ⟨q, rfl⟩, ?_⟩
  rw [dist_comm]
  change dist (fun i => (q.toAtomic.val i)) w.val < ε
  apply (dist_pi_lt_iff hε).mpr
  intro i
  change |(q.val i : ℝ) - (w.val i : ℝ)| < ε
  exact hq i

attribute [local instance] OAI.FixedClauseThreshold.Computability.rationalHierarchyMeasurableSpace
local instance rationalHierarchyBorelSpace (space : TopCat) : BorelSpace space := ⟨rfl⟩

theorem rationalTreeValue_dense (r : ℕ) : DenseRange (rationalTreeValue r) := by
  induction r with
  | zero =>
    change DenseRange (fun x : ℚ => (x : ℝ))
    exact Rat.denseRange_cast
  | succ r ih =>
    let : MetrizableSpace (Hierarchy r) := (hierarchy_properties r).1
    let : MetricSpace (Hierarchy r) := metrizableSpaceMetric (Hierarchy r)
    let : SeparableSpace (Hierarchy r) := (hierarchy_properties r).2
    let S := range (rationalTreeValue (r+1))
    let T := {μ : ProbabilityMeasure (Hierarchy r) | ∃ (n : ℕ)
      (x : Fin n → Hierarchy r) (w : AtomicWeights (Fin n)),
      (∀ i, x i ∈ range (rationalTreeValue r)) ∧ μ = atomicProbability x w}
    have hd : Dense T := finite_atomic_dense (range (rationalTreeValue r)) ih
    have hs : T ⊆ closure S := by
      rintro μ ⟨n, x, w, hx, rfl⟩
      choose y hy using hx
      have hnear := mem_closure_image (continuous_atomicProbability x).continuousAt
        (rationalWeights_atomic_dense w)
      apply (closure_mono (show atomicProbability x '' range RationalWeights.toAtomic ⊆ S from ?_)) hnear
      rintro μ ⟨q, ⟨q', rfl⟩, rfl⟩
      refine ⟨⟨n, q', y⟩, ?_⟩
      change atomicProbability (fun i => rationalTreeValue r (y i)) q'.toAtomic = _
      congr 1
      exact funext hy
    intro μ
    have h := (closure_mono hs) (hd μ)
    change μ ∈ closure (closure S) at h
    rw [closure_closure] at h
    exact h

end FixedClauseThreshold.Computability

end OAI
end

section
-- module Solutions.OAIQ067_SAT.SATComputability_HierarchyEncoding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FixedClauseThreshold.Computability

open Encodable Denumerable Nat.Partrec FiniteArithmetic
open scoped BigOperators

theorem rawBranches_encode (bs : List (ℚ × Code)) : rawBranches (encodeBranches bs) = bs := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    simp only [encodeBranches, List.foldr_cons, rawBranches, branchEntry, decodedRational,
      encode_ofNat, encodek, Option.getD_some]
    exact congrArg (b :: ·) ih

theorem normalizedBranches_encode {bs : List (ℚ × Code)}
    (hpos : ∀ b ∈ bs, 0 ≤ b.1) (hs : (bs.map Prod.fst).sum = 1) :
    normalizedBranches (encodeBranches bs) = bs := by
  have ha : bs.map (fun b => |b.1|) = bs.map Prod.fst := by
    apply List.map_congr_left
    intro b hb
    exact abs_of_nonneg (hpos b hb)
  simp only [normalizedBranches, rawBranches_encode, ha, hs, one_ne_zero, ite_false, div_one]
  conv_rhs => rw [← List.map_id bs]
  apply List.map_congr_left
  intro b hb
  exact Prod.ext (abs_of_nonneg (hpos b hb)) rfl

theorem normalizedBranches_encodeTree (r : ℕ) (t : RationalTree (r+1)) :
    normalizedBranches (encodeTree (r+1) t) =
      List.ofFn (fun i : Fin t.1 => (t.2.1.val i, encodeTree r (t.2.2 i))) := by
  apply normalizedBranches_encode
  · intro b hb
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hb
    exact t.2.1.property.1 i
  · rw [List.map_ofFn, List.sum_ofFn]
    exact t.2.1.property.2

theorem rationalTree_node_ext {r n k : ℕ} (hn : n = k)
    (w : RationalWeights (Fin n)) (v : RationalWeights (Fin k))
    (x : Fin n → RationalTree r) (y : Fin k → RationalTree r)
    (hw : ∀ i, w.val i = v.val (Fin.cast hn i))
    (hx : ∀ i, x i = y (Fin.cast hn i)) :
    (⟨n, w, x⟩ : RationalTree (r+1)) = ⟨k, v, y⟩ := by
  subst k
  apply congrArg (Sigma.mk n)
  apply Prod.ext
  · exact Subtype.ext (funext hw)
  · exact funext hx

theorem decodeTree_encodeTree (r : ℕ) (t : RationalTree r) :
    decodeTree r (encodeTree r t) = t := by
  induction r with
  | zero =>
    change decodedRational (ofNat Code (@encode ℚ Rat.instEncodable t)) = t
    simp only [decodedRational, encode_ofNat]
    exact congrArg (fun o : Option ℚ => o.getD 0) (@Encodable.encodek ℚ Rat.instEncodable t)
  | succ r ih =>
    obtain ⟨n, w, x⟩ := t
    let c := encodeTree (r+1) ⟨n, w, x⟩
    have he : normalizedBranches c =
        List.ofFn (fun i : Fin n => (w.val i, encodeTree r (x i))) :=
      normalizedBranches_encodeTree r ⟨n, w, x⟩
    change (⟨(normalizedBranches c).length, branchWeights c,
      fun i => decodeTree r ((normalizedBranches c).get i).2⟩ :
        Σ k : ℕ, RationalWeights (Fin k) × (Fin k → RationalTree r)) = ⟨n, w, x⟩
    have hn : (normalizedBranches c).length = n := by rw [he, List.length_ofFn]
    apply rationalTree_node_ext hn
    · intro i
      change ((normalizedBranches c).get i).1 = w.val (Fin.cast hn i)
      simp only [List.get_eq_getElem, he, List.getElem_ofFn]
      rfl
    · intro i
      simp only [List.get_eq_getElem, he, List.getElem_ofFn]
      exact ih (x (Fin.cast hn i))

end FixedClauseThreshold.Computability

end OAI
end

section
-- module Solutions.OAIQ067_SAT.SATComputability_PacketExpressions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FixedClauseThreshold.Computability

open DilutedSpinGlass Nat.Partrec FiniteArithmetic RapidForcing.EffectiveArithmetic

attribute [local irreducible] fieldExpression edgeExpression siteExpression trialExpression

attribute [local irreducible] fieldVector

attribute [local irreducible] edgeLeaf

theorem edgeLeaf_value (p : ℚ × (Fin 3 → Bool)) (cs : List Code) :
    expressionValue (edgeLeaf p cs) =
      Real.log (edge (satInteraction (p.1 : ℝ) p.2) (leafFields 3 cs)) := by
  simp only [edgeLeaf, edgeExpression_value, fieldVector, fieldExpression_value]
  rfl

theorem edgeTrialExpression_value (β : ℚ) (J : Fin 3 → Bool)
    (root : Code) (ms : List ℚ) :
    expressionValue (edgeTrialExpression β J root ms) =
      trialLog ms.length (rationalTreeValue (ms.length+1) (decodeTree (ms.length+1) root))
        (fun i => (ms.get i : ℝ)) (fun x => Real.log (edge (satInteraction (β : ℝ) J) x)) := by
  exact trialExpression_eq_trialLog edgeLeaf (β,J) _ (fun cs => edgeLeaf_value _ cs) root ms

attribute [local irreducible] siteData

attribute [local irreducible] siteLeaf

end FixedClauseThreshold.Computability

end OAI
end

section
-- module Solutions.OAIQ067_SAT.SATComputability_DisorderEnumeration
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FixedClauseThreshold.Computability

open DilutedSpinGlass Nat.Partrec FiniteArithmetic RapidForcing.EffectiveArithmetic
open scoped BigOperators Classical

attribute [local irreducible] siteTrialExpression edgeTrialExpression

theorem averagedEdgeExpression_value (β : ℚ) (root : Code) (ms : List ℚ) :
    expressionValue (averagedEdgeExpression β root ms) =
      (FiniteLaw.uniform : FiniteLaw (Fin 3 → Bool)).expect (fun J =>
        trialLog ms.length (rationalTreeValue (ms.length+1) (decodeTree (ms.length+1) root))
          (fun i => (ms.get i : ℝ)) (fun x => Real.log (edge (satInteraction (β : ℝ) J) x))) := by
  simp only [averagedEdgeExpression, expressionValue, rationalExpression_value,
    sumExpressions_value, List.map_map, Function.comp_def, signAlphabet, Finset.sum_map_toList,
    edgeTrialExpression_value]
  simp only [FiniteLaw.expect, FiniteLaw.uniform, Fintype.card_fun, Fintype.card_fin,
    Fintype.card_bool, Nat.cast_pow, Nat.cast_ofNat, Rat.cast_div, Rat.cast_one,
    Rat.cast_ofNat, ← Finset.mul_sum]
  norm_num

end FixedClauseThreshold.Computability

end OAI
end

section
-- module Solutions.OAIQ067_SAT.SATComputability_RationalExponents
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FixedClauseThreshold.Computability

open DilutedSpinGlass Set Filter
open scoped Topology

theorem isOpen_exponents (r : ℕ) : IsOpen {m : Fin r → ℝ | Exponents m} := by
  have he : {m : Fin r → ℝ | Exponents m} =
      (⋂ i : Fin r, ⋂ j : Fin r, {m | i < j → m i < m j}) ∩
        (⋂ i : Fin r, {m | 0 < m i ∧ m i < 1}) := by
    ext m
    simp only [mem_ofPred_eq, mem_inter_iff, mem_iInter, Exponents, StrictMono]
  rw [he]
  apply IsOpen.inter
  · apply isOpen_iInter_of_finite
    intro i
    apply isOpen_iInter_of_finite
    intro j
    by_cases h : i < j
    · simpa only [h, true_implies] using isOpen_lt (continuous_apply i) (continuous_apply j)
    · simp only [h, false_implies, ofPred_true]
      exact isOpen_univ
  · apply isOpen_iInter_of_finite
    intro i
    exact (isOpen_lt continuous_const (continuous_apply i)).inter
      (isOpen_lt (continuous_apply i) continuous_const)

theorem rationalExponent_dense (r : ℕ) :
    DenseRange (fun q : Fin r → ℚ => fun i => (q i : ℝ)) :=
  DenseRange.piMap (fun _ => Rat.denseRange_cast)

theorem exists_rational_exponents {r : ℕ} {m : Fin r → ℝ} (hm : Exponents m)
    {s : Set (Fin r → ℝ)} (hs : s ∈ nhds m) :
    ∃ q : Fin r → ℚ, Exponents (fun i => (q i : ℝ)) ∧ (fun i => (q i : ℝ)) ∈ s := by
  have hn : {m : Fin r → ℝ | Exponents m} ∩ s ∈ nhds m :=
    inter_mem ((isOpen_exponents r).mem_nhds hm) hs
  obtain ⟨x, hx, hxs⟩ := mem_closure_iff_nhds.mp ((rationalExponent_dense r) m) _ hn
  obtain ⟨q, rfl⟩ := hxs
  exact ⟨q, hx.1, hx.2⟩

end FixedClauseThreshold.Computability

end OAI
end

section
-- module Solutions.OAIQ067_SAT.SATComputability_ExponentContinuity
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.DilutedSpinGlass.UniversalDictionary.reservoirLaw_prob _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FixedClauseThreshold.Computability

open DilutedSpinGlass _root_.MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BigOperators NNReal

attribute [local instance] OAI.FixedClauseThreshold.Computability.exponentContinuityMeasurable
local instance exponentContinuityBorel (X : TopCat) : BorelSpace X := ⟨rfl⟩

theorem exponentTail_continuous (r : ℕ) :
    Continuous (exponentTail (r := r)) := by
  apply Continuous.subtype_mk
  exact continuous_pi (fun i => (continuous_apply i.succ).comp continuous_subtype_val)

theorem logMean_continuous_exponents {ι : Type} [Fintype ι]
    (r : ℕ) (g : (ι → ℝ) → ℝ) (hg : Continuous g)
    {B : ℝ} (hB : ∀ x, |g x| ≤ B) (eta : ι → Hierarchy r) :
    Continuous (fun m : UnitExponents r => logMean r g m.val eta) := by
  induction r with
  | zero => exact continuous_const
  | succ r ih =>
    let (i : ι) : IsProbabilityMeasure ((eta i).toMeasure) := by
      exact (eta i : ProbabilityMeasure (Hierarchy r)).property
    have hBn : 0 ≤ B := (abs_nonneg (g (fun _ => 0))).trans (hB _)
    have hc : Continuous (fun m : UnitExponents (r+1) =>
        ∫ x : ι → Hierarchy r, Real.exp (m.val 0 * logMean r g (fun i => m.val i.succ) x)
          ∂Measure.pi (fun i => (eta i).toMeasure)) := by
      apply continuous_of_dominated (bound := fun _ => Real.exp B)
      · intro m
        exact (Real.continuous_exp.comp ((logMean_continuous_bound r g hg hB _
          (fun i => (m.property i.succ).1)).1.const_mul (m.val 0))).aestronglyMeasurable
      · intro m
        apply ae_of_all
        intro x
        rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        apply Real.exp_le_exp.mpr
        have hb := (logMean_continuous_bound r g hg hB _
          (fun i => (m.property i.succ).1)).2 x
        calc
          _ ≤ m.val 0 * B := mul_le_mul_of_nonneg_left (le_abs_self _ |>.trans hb) (m.property 0).1.le
          _ ≤ B := by nlinarith [(m.property 0).2]
      · exact integrable_const _
      · apply ae_of_all
        intro x
        exact Real.continuous_exp.comp (((continuous_apply 0).comp continuous_subtype_val).mul
          ((ih x).comp (exponentTail_continuous r)))
    have hpos (m : UnitExponents (r+1)) :
        0 < ∫ x : ι → Hierarchy r,
          Real.exp (m.val 0 * logMean r g (fun i => m.val i.succ) x)
            ∂Measure.pi (fun i => (eta i).toMeasure) :=
      MeasureMean.exp_integral_pos _
        (logMean_continuous_bound r g hg hB _ (fun i => (m.property i.succ).1)).1.measurable
        (logMean_continuous_bound r g hg hB _ (fun i => (m.property i.succ).1)).2 _
    exact (hc.log (fun m => (hpos m).ne')).div
      ((continuous_apply 0).comp continuous_subtype_val) (fun m => (m.property 0).1.ne')

theorem trialLog_continuous_exponents {ι : Type} [Fintype ι]
    (r : ℕ) (g : (ι → ℝ) → ℝ) (hg : Continuous g)
    {B : ℝ} (hB : ∀ x, |g x| ≤ B) (ζ : Hierarchy (r+1)) :
    Continuous (fun m : UnitExponents r => trialLog r ζ m.val g) := by
  let : IsProbabilityMeasure ζ.toMeasure := (ζ : ProbabilityMeasure (Hierarchy r)).property
  apply continuous_of_dominated (bound := fun _ => B)
  · intro m
    exact (logMean_continuous_bound r g hg hB m.val (fun i => (m.property i).1)).1.aestronglyMeasurable
  · intro m
    exact ae_of_all _ (fun eta => by
      simpa only [Real.norm_eq_abs] using
        (logMean_continuous_bound r g hg hB m.val (fun i => (m.property i).1)).2 eta)
  · exact integrable_const _
  · exact ae_of_all _ (logMean_continuous_exponents r g hg hB)

theorem functional_continuous_unit_exponents {p r : ℕ} (M : Model p)
    (hθ : Integrable (fun z : InteractionSample p => ‖z.1‖) M.disorder.toMeasure)
    (hh : Integrable (fun h : ℝ => |h|) M.field.toMeasure)
    (ζ : Hierarchy (r+1)) :
    Continuous (fun m : UnitExponents r => functional M r ζ m.val) := by
  have hcfield (k : ℕ) (θ : Fin k → InteractionSample p) :
      Continuous (fun m : UnitExponents r => trialSiteField M m.val ζ θ) := by
    apply continuous_of_dominated (bound := fun h : ℝ => |h|+∑ j, ‖(θ j).1‖)
    · intro m
      exact (integrable_trial_site_field M m.val (fun i => (m.property i).1) hh ζ θ).aestronglyMeasurable
    · intro m
      exact ae_of_all _ (fun h => by
        simpa only [Real.norm_eq_abs] using (trial_site_bound r m.val (fun i => (m.property i).1) ζ θ h))
    · exact hh.add (integrable_const _)
    · exact ae_of_all _ (fun h => trialLog_continuous_exponents r _
        (continuous_siteLog θ h) (siteLog_bound θ h) ζ)
  have hcdisorder (k : ℕ) :
      Continuous (fun m : UnitExponents r => trialSiteDisorder M m.val ζ k) := by
    apply continuous_of_dominated (bound := fun θ : Fin k → InteractionSample p =>
      (∫ h : ℝ, |h| ∂M.field.toMeasure)+∑ j, ‖(θ j).1‖)
    · intro m
      exact (stronglyMeasurable_trialSiteField M m.val (fun i => (m.property i).1) ζ k).aestronglyMeasurable
    · intro m
      exact ae_of_all _ (fun θ => by
        simpa only [Real.norm_eq_abs] using (trialSiteField_bound M m.val (fun i => (m.property i).1) hh ζ θ))
    · exact (integrable_const _).add (interaction_sum_integrable M hθ k)
    · exact ae_of_all _ (hcfield k)
  have hcsite : Continuous (fun m : UnitExponents r =>
      ∫ k, trialSiteDisorder M m.val ζ k ∂poissonMeasure (M.alpha*p)) := by
    apply continuous_of_dominated (bound := fun k : ℕ =>
      (∫ h : ℝ, |h| ∂M.field.toMeasure)+k*(∫ z : InteractionSample p, ‖z.1‖ ∂M.disorder.toMeasure))
    · intro m
      exact (measurable_of_countable _).aestronglyMeasurable
    · intro m
      exact ae_of_all _ (fun k => by
        simpa only [Real.norm_eq_abs] using (trialSiteDisorder_bound M m.val (fun i => (m.property i).1) hθ hh ζ k))
    · exact (integrable_const _).add ((poisson_integrable_count _).mul_const _)
    · exact ae_of_all _ hcdisorder
  have hcedge : Continuous (fun m : UnitExponents r =>
      ∫ θ : InteractionSample p, trialLog r ζ m.val (fun x => Real.log (edge θ.1 x))
        ∂M.disorder.toMeasure) := by
    apply continuous_of_dominated (bound := fun θ : InteractionSample p => ‖θ.1‖)
    · intro m
      exact (((trial_edge_lipschitz r m.val (fun i => (m.property i).1) ζ).continuous.comp
        continuous_fst).aestronglyMeasurable)
    · intro m
      exact ae_of_all _ (fun θ => by
        simpa only [Real.norm_eq_abs] using (trial_edge_bound r m.val (fun i => (m.property i).1) ζ θ.1))
    · exact hθ
    · exact ae_of_all _ (fun θ => trialLog_continuous_exponents r _
        (continuous_log_edge θ.1) (log_edge_bound θ.1) ζ)
  exact (continuous_const.add hcsite).sub (continuous_const.mul hcedge)

theorem isOpen_unit_exponents (r : ℕ) :
    IsOpen {m : Fin r → ℝ | ∀ i, 0 < m i ∧ m i < 1} := by
  have he : {m : Fin r → ℝ | ∀ i, 0 < m i ∧ m i < 1} =
      ⋂ i : Fin r, {m | 0 < m i ∧ m i < 1} := by ext; simp
  rw [he]
  exact isOpen_iInter_of_finite (fun i =>
    (isOpen_lt continuous_const (continuous_apply i)).inter
      (isOpen_lt (continuous_apply i) continuous_const))

theorem functional_continuousAt_exponents {p r : ℕ} (M : Model p)
    (hθ : Integrable (fun z : InteractionSample p => ‖z.1‖) M.disorder.toMeasure)
    (hh : Integrable (fun h : ℝ => |h|) M.field.toMeasure)
    (ζ : Hierarchy (r+1)) {m : Fin r → ℝ} (hm : Exponents m) :
    ContinuousAt (fun m => functional M r ζ m) m := by
  have hc : ContinuousOn (fun m => functional M r ζ m)
      {m : Fin r → ℝ | ∀ i, 0 < m i ∧ m i < 1} :=
    continuousOn_iff_continuous_domRestrict.mpr
      (functional_continuous_unit_exponents M hθ hh ζ)
  exact (hc m hm.2).continuousAt ((isOpen_unit_exponents r).mem_nhds hm.2)

end FixedClauseThreshold.Computability

end OAI
end

section
-- module Solutions.OAIQ067_SAT.SATComputability_SATVariational
attribute [-instance] _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FixedClauseThreshold.Computability

open DilutedSpinGlass _root_.MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal

theorem exists_rational_trial_near_pressure {a : ℝ≥0} (ha : 0 < a) {β : ℝ} (hβ : 0 < β)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (r : ℕ) (t : RationalTree (r+1)) (m : Fin r → ℝ), Exponents m ∧
      functional (satModel a β) r (rationalTreeValue (r+1) t) m < satPressure a β + ε := by
  obtain ⟨r, ζ, m, hm, happrox⟩ := symmetric_trial_lower_sat (satModel a β) ha
    (satModel_interaction_integrable a hβ.le) (satModel_field_integrable a β)
    (satModel_symmetric a β) (show 0 < ε/2 by positivity)
  have hc := functional_continuous (satModel a β) m (fun i => (hm.2 i).1)
    (satModel_interaction_integrable a hβ.le) (satModel_field_integrable a β)
  have hn : {η | functional (satModel a β) r η m < satPressure a β+ε} ∈ nhds ζ :=
    hc.continuousAt.preimage_mem_nhds (Iio_mem_nhds (by
      change functional (satModel a β) r ζ m ≤ satPressure a β+ε/2 at happrox
      linarith))
  obtain ⟨η, hη, hη'⟩ := mem_closure_iff_nhds.mp ((rationalTreeValue_dense (r+1)) ζ) _ hn
  obtain ⟨t, rfl⟩ := hη'
  exact ⟨r, t, m, hm, hη⟩

theorem exists_fully_rational_trial_near_pressure {a : ℝ≥0} (ha : 0 < a)
    {β : ℝ} (hβ : 0 < β) {ε : ℝ} (hε : 0 < ε) :
    ∃ (r : ℕ) (t : RationalTree (r+1)) (m : Fin r → ℚ),
      Exponents (fun i => (m i : ℝ)) ∧
      functional (satModel a β) r (rationalTreeValue (r+1) t) (fun i => (m i : ℝ)) <
        satPressure a β + ε := by
  obtain ⟨r, t, m, hm, ht⟩ := exists_rational_trial_near_pressure ha hβ hε
  have hc := functional_continuousAt_exponents (satModel a β)
    (satModel_interaction_integrable a hβ.le) (satModel_field_integrable a β)
    (rationalTreeValue (r+1) t) hm
  have hn : {m : Fin r → ℝ | functional (satModel a β) r
      (rationalTreeValue (r+1) t) m < satPressure a β + ε} ∈ nhds m :=
    hc.preimage_mem_nhds (Iio_mem_nhds ht)
  obtain ⟨q, hq, hv⟩ := exists_rational_exponents hm hn
  exact ⟨r, t, q, hq, hv⟩

end FixedClauseThreshold.Computability

end OAI
end

section
-- module Solutions.OAIQ067_SAT.SATComputability_TrialDisorder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FixedClauseThreshold.Computability

open DilutedSpinGlass _root_.MeasureTheory ProbabilityTheory Nat.Partrec FiniteArithmetic
open scoped BigOperators NNReal Classical

theorem integral_sat_packet (a : ℝ≥0) (β : ℝ) (k : ℕ)
    (f : (Fin k → InteractionSample 3) → ℝ) (hf : Measurable f) :
    (∫ θ, f θ ∂Measure.pi (fun _ : Fin k => (satModel a β).disorder.toMeasure)) =
      (FiniteLaw.uniform : FiniteLaw (Fin k → Fin 3 → Bool)).expect
        (fun J => f (fun i => satSample β (J i))) := by
  change (∫ θ, f θ ∂Measure.pi (fun _ : Fin k =>
    Measure.map (satSample β) signLaw.toMeasure)) = _
  rw [← Measure.pi_map_pi (μ := fun _ : Fin k => signLaw.toMeasure)
    (f := fun _ J => satSample β J) (fun _ => (measurable_of_countable _).aemeasurable)]
  rw [integral_map
    (φ := fun J : Fin k → Fin 3 → Bool => fun i => satSample β (J i))
    (Measurable.of_eval (fun i => (measurable_of_countable (satSample β)).comp
      (measurable_pi_apply i))).aemeasurable hf.aestronglyMeasurable]
  have he : signLaw.toMeasure = finiteUniform (Fin 3 → Bool) := rfl
  rw [he, finiteUniform_pi, integral_finiteUniform]
  simp only [FiniteLaw.expect, FiniteLaw.uniform, smul_eq_mul, ← Finset.mul_sum]

theorem integral_sat_edge (a : ℝ≥0) (β : ℝ) (f : InteractionSample 3 → ℝ) (hf : Measurable f) :
    (∫ θ, f θ ∂(satModel a β).disorder.toMeasure) =
      (FiniteLaw.uniform : FiniteLaw (Fin 3 → Bool)).expect (fun J => f (satSample β J)) := by
  change (∫ θ, f θ ∂Measure.map (satSample β) signLaw.toMeasure) = _
  rw [integral_map (measurable_of_countable _).aemeasurable
    hf.aestronglyMeasurable, signLaw_integral]

theorem packet_functional (a : ℝ≥0) (β : ℚ) (root : Code) (ms : List ℚ)
    (hm : ∀ i : Fin ms.length, 0 < ms.get i) :
    functional (satModel a β) ms.length
      (rationalTreeValue (ms.length+1) (decodeTree (ms.length+1) root))
      (fun i => (ms.get i : ℝ)) =
    Real.log 2 + (∫ k, packetSiteValue β root ms k ∂poissonMeasure (a*3)) -
      (a : ℝ)*2*packetEdgeValue β root ms := by
  let ζ := rationalTreeValue (ms.length+1) (decodeTree (ms.length+1) root)
  let m : Fin ms.length → ℝ := fun i => ms.get i
  have hp : ∀ i, 0 < m i := fun i => by
    dsimp only [m]
    exact_mod_cast hm i
  have hs (k : ℕ) : (∫ θ : Fin k → InteractionSample 3,
      ∫ h, trialLog ms.length ζ m (siteLog θ h) ∂(satModel a β).field.toMeasure
      ∂Measure.pi (fun _ => (satModel a β).disorder.toMeasure)) =
      packetSiteValue β root ms k := by
    change (∫ θ : Fin k → InteractionSample 3,
      ∫ h, trialLog ms.length ζ m (siteLog θ h) ∂Measure.dirac 0
      ∂Measure.pi (fun _ => (satModel a β).disorder.toMeasure)) = _
    simp only [integral_dirac]
    have hf : Measurable (fun θ : Fin k → InteractionSample 3 =>
        trialLog ms.length ζ m (siteLog θ 0)) := by
      simpa only [Function.comp_def, id_eq] using
        ((trial_site_lipschitz ms.length m hp ζ).continuous.comp
          (continuous_id.prodMk (continuous_const (y := (0 : ℝ))))).measurable
    rw [integral_sat_packet a (β : ℝ) k _ hf]
    exact (averagedSiteExpression_value β root ms k).symm
  have he : (∫ θ : InteractionSample 3,
      trialLog ms.length ζ m (fun x => Real.log (edge θ.1 x))
      ∂(satModel a β).disorder.toMeasure) = packetEdgeValue β root ms := by
    have hf : Measurable (fun θ : InteractionSample 3 =>
        trialLog ms.length ζ m (fun x => Real.log (edge θ.1 x))) := by
      simpa only [Function.comp_def] using
        ((trial_edge_lipschitz ms.length m hp ζ).continuous.comp
          (continuous_fst (X := Interaction 3) (Y := ℝ × ℝ × (Fin 3 → Bool → ℝ)))).measurable
    rw [integral_sat_edge a (β : ℝ) _ hf]
    exact (averagedEdgeExpression_value β root ms).symm
  unfold functional
  congr 2
  apply integral_congr_ae
  exact ae_of_all _ hs

end FixedClauseThreshold.Computability

end OAI
end

section
-- module Solutions.OAIQ067_SAT.SATComputability_TrialDescriptions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FixedClauseThreshold.Computability

open DilutedSpinGlass Nat.Partrec FiniteArithmetic RapidForcing.EffectiveArithmetic

theorem rationalAt_get (ms : List ℚ) (i : Fin ms.length) : rationalAt ms i.val = ms.get i := by
  simp [rationalAt]

attribute [local irreducible] rationalAt

theorem exponentCheck_iff (ms : List ℚ) :
    exponentCheck ms = true ↔ Exponents (fun i : Fin ms.length => (ms.get i : ℝ)) := by
  simp only [exponentCheck, List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq, List.mem_range]
  constructor
  · intro h
    constructor
    · intro i j hij
      have hi := ((h i.val i.isLt).2 j.val j.isLt).resolve_left (Nat.not_le_of_gt hij)
      rw [rationalAt_get ms i, rationalAt_get ms j] at hi
      change (ms.get i : ℝ) < ms.get j
      exact_mod_cast hi
    · intro i
      have hi := (h i.val i.isLt).1
      rw [rationalAt_get ms i] at hi
      change 0 < (ms.get i : ℝ) ∧ (ms.get i : ℝ) < 1
      exact ⟨by exact_mod_cast hi.1, by exact_mod_cast hi.2⟩
  · intro h i hi
    refine ⟨?_, ?_⟩
    · have hb := h.2 ⟨i,hi⟩
      change 0 < (ms.get ⟨i,hi⟩ : ℝ) ∧ (ms.get ⟨i,hi⟩ : ℝ) < 1 at hb
      rw [rationalAt_get ms ⟨i,hi⟩]
      exact ⟨by exact_mod_cast hb.1, by exact_mod_cast hb.2⟩
    · intro j hj
      by_cases hij : j ≤ i
      · exact Or.inl hij
      right
      have hm := h.1 (show (⟨i,hi⟩ : Fin ms.length) < ⟨j,hj⟩ from Nat.lt_of_not_ge hij)
      change (ms.get ⟨i,hi⟩ : ℝ) < ms.get ⟨j,hj⟩ at hm
      rw [rationalAt_get ms ⟨i,hi⟩, rationalAt_get ms ⟨j,hj⟩]
      exact_mod_cast hm

theorem exponentCheck_positive {ms : List ℚ} (h : exponentCheck ms = true) :
    positiveExponents ms = true := by
  rw [positiveExponents_iff]
  intro i
  have hp := (((exponentCheck_iff ms).mp h).2 i).1
  change 0 < (ms.get i : ℝ) at hp
  exact_mod_cast hp

end FixedClauseThreshold.Computability

end OAI
end

section
-- module Solutions.OAIQ067_SAT.SATComputability_EffectiveTrialValues
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FixedClauseThreshold.Computability

open DilutedSpinGlass _root_.MeasureTheory ProbabilityTheory Nat.Partrec FiniteArithmetic
open PeriodicLattice.CertifiedReal RapidForcing.EffectiveArithmetic
open scoped NNReal

attribute [local irreducible] averagedSiteExpression averagedEdgeExpression positiveExponents

attribute [local irreducible] guardedSiteValue packetEdgeValue

theorem trialValue_eq_functional (t : TrialData)
    (hm : exponentCheck t.2.2.2 = true) :
    trialValue t = functional (satModel (trialDensityNN t) (t.2.1 : ℝ)) t.2.2.2.length
      (rationalTreeValue (t.2.2.2.length+1) (decodeTree (t.2.2.2.length+1) t.2.2.1))
      (fun i => (t.2.2.2.get i : ℝ)) := by
  have hp := exponentCheck_positive hm
  have he (k : ℕ) : guardedSiteValue t k = packetSiteValue (t.2.1 : ℚ) t.2.2.1 t.2.2.2 k := by
    simp only [guardedSiteValue, guardedSiteExpression, hp, ite_true, packetSiteValue]
  have hf := packet_functional (trialDensityNN t) (t.2.1 : ℚ) t.2.2.1 t.2.2.2
    ((positiveExponents_iff _).mp hp)
  simp only [Rat.cast_natCast] at hf
  rw [hf]
  have hc : (trialDensityNN t : ℝ) = (max 0 t.1 : ℚ) := rfl
  simp only [trialValue, he, hc]
  push_cast
  ring

end FixedClauseThreshold.Computability

end OAI
end

section
-- module Solutions.OAIQ067_SAT.SATComputability_UpperCertificates
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FixedClauseThreshold.Computability

open Filter
open scoped Topology
open RapidForcing.EffectiveArithmetic

theorem tolerance_tendsto :
    Tendsto (fun r => (tolerance r : ℝ)) atTop (nhds 0) := by
  simpa only [tolerance, Rat.cast_inv, Rat.cast_pow, Rat.cast_ofNat, inv_pow] using
    (tendsto_pow_atTop_nhds_zero_of_lt_one
      (by norm_num : (0 : ℝ) ≤ 2⁻¹) (by norm_num : (2 : ℝ)⁻¹ < 1))

theorem TrialEvaluation.certified_computable (T : TrialEvaluation) :
    Computable T.certified := by
  have := T.valid_computable
  have := T.approximate_computable
  unfold TrialEvaluation.certified
  fun_prop

theorem TrialEvaluation.upper_computable (T : TrialEvaluation) :
    Computable T.upper := by
  have := T.density_computable
  unfold TrialEvaluation.upper
  fun_prop

theorem TrialEvaluation.certified_negative (T : TrialEvaluation) {n : ℕ}
    (hn : T.certified n = true) :
    T.valid n.unpair.1 = true ∧ T.value n.unpair.1 < 0 := by
  have h : T.valid n.unpair.1 = true ∧
      T.approximate (n.unpair.1, n.unpair.2) + tolerance n.unpair.2 < 0 := by
    simpa only [TrialEvaluation.certified, decide_eq_true_eq] using hn
  refine ⟨h.1, ?_⟩
  have he := (abs_le.mp (T.approximation_error n.unpair.1 n.unpair.2 h.1)).1
  have hn' : (T.approximate (n.unpair.1, n.unpair.2) : ℝ) +
      (tolerance n.unpair.2 : ℝ) < 0 := by exact_mod_cast h.2
  linarith

theorem TrialEvaluation.negative_eventually_certified (T : TrialEvaluation) {j : ℕ}
    (hj : T.valid j = true) (hneg : T.value j < 0) :
    ∃ s, T.certified (Nat.pair j s) = true := by
  have hsmall := tolerance_tendsto.eventually_lt_const
    (show (0 : ℝ) < -T.value j / 2 by linarith)
  obtain ⟨s, hs⟩ := hsmall.exists
  have he := (abs_le.mp (T.approximation_error j s hj)).2
  have h : T.approximate (j, s) + tolerance s < 0 := by
    have : (T.approximate (j, s) : ℝ) + (tolerance s : ℝ) < 0 := by linarith
    exact_mod_cast this
  exact ⟨s, by simp [TrialEvaluation.certified, hj, h]⟩

theorem TrialSeparation.upper_sound {T : TrialEvaluation} {α : ℝ}
    (h : TrialSeparation T α) (n : ℕ) (hn : T.certified n = true) :
    α ≤ (T.upper n : ℝ) := by
  obtain ⟨hv, hg⟩ := T.certified_negative hn
  exact h.sound _ hv hg

theorem TrialSeparation.upper_dense {T : TrialEvaluation} {α : ℝ}
    (h : TrialSeparation T α) (ε : ℝ) (hε : 0 < ε) :
    ∃ n, T.certified n = true ∧ (T.upper n : ℝ) < α + ε := by
  obtain ⟨a, ha, ha'⟩ := exists_rat_btwn (show α < α + ε by linarith)
  obtain ⟨j, hj, hd, hn⟩ := h.complete a ha
  obtain ⟨s, hs⟩ := T.negative_eventually_certified hj hn
  exact ⟨Nat.pair j s, hs, by simpa [TrialEvaluation.upper, hd] using ha'⟩

theorem computable_of_trial_separation {T : TrialEvaluation} {α : ℝ}
    (h : TrialSeparation T α) {lower : ℕ → ℚ} (hl : Computable lower)
    (hls : ∀ i, (lower i : ℝ) ≤ α)
    (hld : ∀ ε : ℝ, 0 < ε → ∃ i, α - ε < (lower i : ℝ)) :
    ∃ q : ℕ → ℚ, Computable q ∧
      ∀ r, |(q r : ℝ) - α| ≤ (2 ^ r : ℝ)⁻¹ := by
  obtain ⟨q, hq, _, he⟩ := finite_certificate_search hl T.upper_computable
    T.certified_computable hls h.upper_sound hld h.upper_dense
  exact ⟨q, hq, he⟩

end FixedClauseThreshold.Computability

end OAI
end

section
-- module Solutions.OAIQ067_SAT.SATComputability_CompiledTrials
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FixedClauseThreshold.Computability

open DilutedSpinGlass Nat.Partrec PeriodicLattice.CertifiedReal
open scoped NNReal

theorem decodeTrial_encode (t : TrialData) : decodeTrial (Encodable.encode t) = t := by
  simp [decodeTrial]

end FixedClauseThreshold.Computability

end OAI
end

section
-- module Solutions.OAIQ067_SAT.SATComputability_DeletionScaling
attribute [-instance] _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FixedClauseThreshold.Computability

open DilutedSpinGlass Filter
open scoped NNReal Topology

theorem deletionSlope_tendsto : Tendsto deletionSlope atTop (nhds 0) := by
  change Tendsto (fun q : ℕ => 6*uniformFreeConstant^(5/6 : ℝ)*
    ((q : ℝ)⁻¹)^(1/6 : ℝ)) atTop (nhds 0)
  have h := (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop).rpow_const_nhds_zero
    (by norm_num : (0 : ℝ) < 1/6)
  simpa only [Function.comp_apply, mul_zero] using h.const_mul (6*uniformFreeConstant^(5/6 : ℝ))

theorem deletionSlope_small {δ : ℝ} (hδ : 0 < δ) :
    ∃ q : ℕ, 0 < q ∧ deletionSlope q < δ := by
  obtain ⟨q,hq,hs⟩ := ((eventually_gt_atTop 0).and
    (deletionSlope_tendsto.eventually (gt_mem_nhds hδ))).exists
  exact ⟨q,hq,hs⟩

end FixedClauseThreshold.Computability

end OAI
end

section
-- module Solutions.OAIQ067_SAT.SATComputability_LowerProgram
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FixedClauseThreshold.Computability

open Filter RapidForcing.EffectiveArithmetic
open scoped Topology

attribute [local irreducible] rationalCenter

theorem threshold_program_of_trial_separation {T : TrialEvaluation}
    (hT : TrialSeparation T (limitingCenter 3)) :
    ∃ (q : ℕ → ℚ) (c : Nat.Partrec.Code),
      Computable q ∧
      (∀ r, c.eval r = Part.some (Encodable.encode (q r))) ∧
      (∀ r, |(q r : ℝ) - limitingCenter 3| ≤ (2 ^ r : ℝ)⁻¹) := by
  obtain ⟨lower, hl, hs, hd⟩ := exists_lowerProgram_sat
  obtain ⟨q, hq, he⟩ := computable_of_trial_separation hT hl hs hd
  obtain ⟨c, hc⟩ := rational_sequence_code hq
  exact ⟨q, c, hq, hc, he⟩

end FixedClauseThreshold.Computability

end OAI
end

section
-- module Solutions.OAIQ067_SAT.SATComputability_SupercriticalEnergy
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FixedClauseThreshold.Computability

open DilutedSpinGlass Filter
open scoped NNReal Topology

theorem zero_lifetime_linear {n : ℕ} [NeZero n] (b : ℝ≥0) {δ : ℝ}
    (hδ : 0 < δ) (hn : 2/δ ≤ (n : ℝ))
    (hP : auxiliaryPoissonProbability n b ≤ δ/40) :
    deletionLifetimeMean n 0 ≤ ((b : ℝ)+δ)*n := by
  have hc := (Nat.ceil_lt_add_one (mul_nonneg b.coe_nonneg (Nat.cast_nonneg n))).le
  have htail := mul_le_mul_of_nonneg_left hP (by positivity : (0 : ℝ) ≤ 20*n)
  have hn' : 2 ≤ δ*(n : ℝ) := by
    have h := (div_le_iff₀ hδ).mp hn
    nlinarith
  have h := zero_lifetime_mean_upper n b
  change deletionLifetimeMean n 0 ≤ _ at h
  push_cast at h
  nlinarith

theorem quotient_linear_lower {n q : ℕ} (hq : 0 < q) (hn : q ≤ n) :
    (n : ℝ)/(2*(q : ℝ)) ≤ (n/q : ℕ) := by
  have hr : 1 ≤ n/q := Nat.div_pos hn hq
  have hdiv := Nat.lt_mul_div_succ n hq
  have hb : n ≤ 2*q*(n/q) := by nlinarith
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2*(q : ℝ))).mpr
  have hbR : (n : ℝ) ≤ 2*(q : ℝ)*((n/q : ℕ) : ℝ) := by exact_mod_cast hb
  nlinarith only [hbR]

theorem relaxedPoissonMinimum_supercritical {a : ℝ≥0}
    (ha : limitingCenter 3 < (a : ℝ)) :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ᶠ n : ℕ in atTop, ε ≤ relaxedPoissonMinimum n a/n := by
  have hα10 : limitingCenter 3 < 10 := by
    have h := (limitingCenter_bounds_sat 3 (by decide)).2
    norm_num at h
    linarith
  obtain ⟨d,hαd,hd⟩ := exists_between (lt_min ha hα10)
  have hda : d < (a : ℝ) := hd.trans_le (min_le_left _ _)
  have hd10 : d < 10 := hd.trans_le (min_le_right _ _)
  obtain ⟨b,hαb,hbd⟩ := exists_between hαd
  have hb : 0 < b := (limitingCenter_pos_sat 3 (by decide)).trans hαb
  have hd0 : 0 < d := hb.trans hbd
  let δ : ℝ := (d-b)/4
  have hδ : 0 < δ := div_pos (sub_pos.mpr hbd) (by norm_num)
  have hδd : b+4*δ = d := by dsimp [δ]; ring
  let bNN : ℝ≥0 := ⟨b,hb.le⟩
  obtain ⟨q,hq,hslope⟩ := deletionSlope_small hδ
  let ε : ℝ := (δ/d)/(2*(q : ℝ))
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hε : 0 < ε := by dsimp [ε]; positivity
  refine ⟨ε,hε,?_⟩
  have hprob := (auxiliaryPoissonProbability_supercritical_sat (a := bNN) hαb).eventually
    (gt_mem_nhds (show (0 : ℝ) < δ/40 by positivity))
  have hsize : ∀ᶠ n : ℕ in atTop, 2/δ ≤ (n : ℝ) :=
    (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop).eventually
      (eventually_ge_atTop (2/δ))
  filter_upwards [hprob,hsize,eventually_ge_atTop q] with n hP hnsize hnq
  have hn0 : 0 < n := hq.trans_le hnq
  let : NeZero n := ⟨hn0.ne'⟩
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
  let r := n/q
  let t := ⌊d*(n : ℝ)⌋₊
  have htUpper : (t : ℝ) ≤ d*n := Nat.floor_le (by positivity)
  have htLower : (d-δ)*(n : ℝ) ≤ t := by
    have hf := Nat.sub_one_lt_floor (d*(n : ℝ))
    have hh := (div_le_iff₀ hδ).mp hnsize
    dsimp [t]
    nlinarith
  have hdδ : 0 < d-δ := by linarith
  have htR : (0 : ℝ) < t := (mul_pos hdδ hnR).trans_le htLower
  have ht : 0 < t := by exact_mod_cast htR
  have htM : t ≤ 20*n := by
    have h : (t : ℝ) ≤ 20*n := htUpper.trans
      (mul_le_mul_of_nonneg_right (by linarith : d ≤ 20) hnR.le)
    exact_mod_cast h
  have hta : (t : ℝ≥0) ≤ a*n := by
    apply NNReal.coe_le_coe.mp
    change (t : ℝ) ≤ (a : ℝ)*n
    exact htUpper.trans (mul_le_mul_of_nonneg_right hda.le hnR.le)
  have hzero := zero_lifetime_linear bNN hδ hnsize hP.le
  have hinc := deletion_increment_linear_sat n q hq
  change deletionLifetimeMean n r - deletionLifetimeMean n 0 ≤ deletionSlope q*n at hinc
  have hmean : deletionLifetimeMean n r ≤ (b+2*δ)*n := by
    change deletionLifetimeMean n 0 ≤ (b+δ)*n at hzero
    have hs := mul_le_mul_of_nonneg_right hslope.le hnR.le
    linarith
  have hgap : δ/d ≤ 1-deletionLifetimeMean n r/t := by
    have he : 1-deletionLifetimeMean n r/t = (t-deletionLifetimeMean n r)/t := by
      field_simp
    rw [he, div_le_div_iff₀ hd0 htR]
    have hg : δ*(n : ℝ) ≤ (t : ℝ)-deletionLifetimeMean n r := by nlinarith
    have h1 := mul_le_mul_of_nonneg_left hg hd0.le
    have h2 := mul_le_mul_of_nonneg_left htUpper hδ.le
    nlinarith
  have hr : r ≤ n+1 := (Nat.div_le_self n q).trans (Nat.le_succ n)
  have hlower := mean_lifetime_energy_lower hr ht htM a hta
  change (r : ℝ)*(1-deletionLifetimeMean n r/t) ≤ relaxedPoissonMinimum n a at hlower
  have hquot := quotient_linear_lower hq hnq
  have hprod : ε*n ≤ (r : ℝ)*(δ/d) := by
    have h := mul_le_mul_of_nonneg_right hquot (div_nonneg hδ.le hd0.le)
    dsimp only [ε,r]
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    ring
  apply (le_div_iff₀ hnR).mpr
  exact hprod.trans ((mul_le_mul_of_nonneg_left hgap (Nat.cast_nonneg r)).trans hlower)

end FixedClauseThreshold.Computability

end OAI
end

section
-- module Solutions.OAIQ067_SAT.SATComputability_TrialCompleteness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FixedClauseThreshold.Computability

open DilutedSpinGlass Nat.Partrec
open scoped NNReal

theorem functional_list_encoding (a : ℝ≥0) (β : ℝ) {r : ℕ}
    (ms : List ℚ) (hlen : ms.length = r) (t : RationalTree (r+1)) (m : Fin r → ℚ)
    (hget : ∀ i, ms.get i = m (Fin.cast hlen i)) :
    functional (satModel a β) ms.length
      (rationalTreeValue (ms.length+1) (decodeTree (ms.length+1) (encodeTree (r+1) t)))
      (fun i => (ms.get i : ℝ)) =
      functional (satModel a β) r (rationalTreeValue (r+1) t) (fun i => (m i : ℝ)) := by
  subst r
  rw [decodeTree_encodeTree]
  congr 1
  funext i
  exact congrArg (fun q : ℚ => (q : ℝ)) (hget i)

theorem satTrialEvaluation_dense (a : ℚ) (ha : 0 < a) (b : ℕ) (hb : 0 < b)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ j, satTrialEvaluation.valid j = true ∧ satTrialEvaluation.density j = a ∧
      (decodeTrial j).2.1 = b ∧
      satTrialEvaluation.value j < satPressure ⟨(a : ℝ), by exact_mod_cast ha.le⟩ b + ε := by
  let aNN : ℝ≥0 := ⟨a, by exact_mod_cast ha.le⟩
  have haNN : 0 < aNN := by
    change (0 : ℝ) < (a : ℝ)
    exact_mod_cast ha
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  obtain ⟨r,t,m,hm,hval⟩ := exists_fully_rational_trial_near_pressure haNN hbR hε
  let ms := List.ofFn m
  let code := encodeTree (r+1) t
  let data : TrialData := (a,b,code,ms)
  have hlen : ms.length = r := List.length_ofFn
  have hget (i : Fin ms.length) : ms.get i = m (Fin.cast hlen i) := List.get_ofFn _ _
  have hm' : Exponents (fun i : Fin ms.length => (ms.get i : ℝ)) := by
    constructor
    · intro i j hij
      simpa only [hget] using hm.1 (show Fin.cast hlen i < Fin.cast hlen j from hij)
    · intro i
      simpa only [hget] using hm.2 (Fin.cast hlen i)
  have he : exponentCheck ms = true := (exponentCheck_iff ms).mpr hm'
  have hd : trialDataValid data = true := (trialDataValid_iff data).mpr ⟨ha,hb,he⟩
  have hrate : trialDensityNN data = aNN := by
    apply Subtype.ext
    simp only [trialDensityNN, data, aNN, max_eq_right ha.le]
  refine ⟨Encodable.encode data, ?_, ?_, ?_, ?_⟩
  · simpa only [satTrialEvaluation, decodeTrial_encode] using hd
  · simp only [satTrialEvaluation, decodeTrial_encode, data]
  · simp only [decodeTrial_encode, data]
  · change trialValue (decodeTrial (Encodable.encode data)) < _
    rw [decodeTrial_encode, trialValue_eq_functional data he, hrate]
    change functional (satModel aNN (b : ℝ)) ms.length
      (rationalTreeValue (ms.length+1) (decodeTree (ms.length+1) (encodeTree (r+1) t)))
      (fun i => (ms.get i : ℝ)) < _
    rw [functional_list_encoding aNN b ms hlen t m hget]
    exact hval

theorem satTrialEvaluation_negative_witness (a : ℚ) (ha : 0 < a) (b : ℕ) (hb : 0 < b)
    (hneg : satPressure ⟨(a : ℝ), by exact_mod_cast ha.le⟩ b < 0) :
    ∃ j, satTrialEvaluation.valid j = true ∧ satTrialEvaluation.density j = a ∧
      satTrialEvaluation.value j < 0 := by
  obtain ⟨j,hj,hd,_,hv⟩ := satTrialEvaluation_dense a ha b hb _ (neg_pos.mpr hneg)
  exact ⟨j,hj,hd,by simpa only [add_neg_cancel] using hv⟩

end FixedClauseThreshold.Computability

end OAI
end

section
-- module Solutions.OAIQ067_SAT.SATComputability_Main
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FixedClauseThreshold.Computability

open Filter
open scoped Topology NNReal

theorem satTrialSeparation : TrialSeparation satTrialEvaluation (limitingCenter 3) := by
  constructor
  · exact fun _ hj hn => satTrialEvaluation_sound_sat hj hn
  · intro a ha
    have haR : (0 : ℝ) < a := (limitingCenter_pos_sat 3 (by decide)).trans ha
    have haQ : 0 < a := by exact_mod_cast haR
    let aNN : ℝ≥0 := ⟨a,haR.le⟩
    have haNN : 0 < aNN := haR
    obtain ⟨ε,hε,hV⟩ := relaxedPoissonMinimum_supercritical (a := aNN) ha
    obtain ⟨b,hb,hnegative⟩ := negative_pressure_of_violation_density_sat haNN hε hV
    exact satTrialEvaluation_negative_witness a haQ b hb hnegative

theorem threshold_program_sat_oai :
    ∃ (q : ℕ → ℚ) (c : Nat.Partrec.Code),
      Computable q ∧
      (∀ r, c.eval r = Part.some (Encodable.encode (q r))) ∧
      (∀ r, |(q r : ℝ)-limitingCenter 3| ≤ (2^r : ℝ)⁻¹) :=
  threshold_program_of_trial_separation satTrialSeparation

end FixedClauseThreshold.Computability

end OAI
end

theorem solution : type_of% @OAI.FixedClauseThreshold.Computability.threshold_program_sat_oai := @OAI.FixedClauseThreshold.Computability.threshold_program_sat_oai
