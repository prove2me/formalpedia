-- Prove2me | solution 1 for OAI.GaussianPropeller.Reduction.minimal_loss_constraint
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T08:51:39.003391+00:00
-- url     : https://prove2.me/submissions/f9be2985-2681-4f00-b844-8cb6b44c9903

-- Generated from openai/math@1581d4c lean/OAI/Probability/GaussianPropeller/CellBounds.lean:L96-L132
-- (upload_full_project.md Phase 4): solution for node OAI.GaussianPropeller.Reduction.minimal_loss_constraint. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_GaussianPropeller
import Definitions.Def_OAI_Probability_GaussianPropeller_Moments
import Definitions.Def_OAI_Probability_GaussianPropeller_Dual
import Definitions.Def_OAI_Probability_GaussianPropeller_Deletion
import Definitions.Def_OAI_Probability_GaussianPropeller_Translation
import Definitions.Def_OAI_Probability_GaussianPropeller_HeatConvolution
import Definitions.Def_OAI_Probability_GaussianPropeller_Quantile
import Definitions.Def_OAI_Probability_GaussianPropeller_QuantileCalculus
import Definitions.Def_OAI_Probability_GaussianPropeller_HeatMaximum
import Definitions.Def_OAI_Probability_GaussianPropeller_SmoothedConcavity
import Definitions.Def_OAI_Probability_GaussianPropeller_SoftMinimum
import Definitions.Def_OAI_Probability_GaussianPropeller_ConeConcavity
import Definitions.Def_OAI_Probability_GaussianPropeller_OneCell
import Definitions.Def_OAI_Probability_GaussianPropeller_Mills
import Definitions.Def_OAI_Probability_GaussianPropeller_Taylor
import Definitions.Def_OAI_Probability_GaussianPropeller_ProbabilityBounds
import Definitions.Def_OAI_Probability_GaussianPropeller_Attainment
import Theorems.Thm_OAI_GaussianPropeller_Reduction_active_probability_mem
import Theorems.Thm_OAI_GaussianPropeller_Reduction_minimal_loss_upper
import Theorems.Thm_OAI_GaussianPropeller_Reduction_optimal_loss_lower
import Theorems.Thm_OAI_GaussianPropeller_Reduction_recentered_norm_sq
import Theorems.Thm_OAI_GaussianPropeller_sum_centroid_eq_zero

-- ---- from OAI.Probability.GaussianPropeller.Quantile ----
namespace OAI

universe uX

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal RealInnerProductSpace
open Filter
open scoped Topology

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology

namespace GaussianPropeller.Quantile

lemma q_of_mem {p : ℝ} (hp : p ∈ Ioo (0:ℝ) 1) : q p = cdfIso.symm ⟨p,hp⟩ := by
  simp [q, hp]
lemma q_Φ (x : ℝ) : q (Φ x) = x := by
  rw [q_of_mem (Φ_mem x)]
  exact cdfIso.symm_apply_apply x
section Integration
variable {X : Type uX} [MeasurableSpace X] {μ : Measure X} [IsProbabilityMeasure μ]

end Integration
end GaussianPropeller.Quantile

end OAI

-- ---- from OAI.Probability.GaussianPropeller.OneCell ----
namespace OAI

universe uE

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal RealInnerProductSpace
open Filter
open scoped Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
open scoped RealInnerProductSpace
open Set Filter
open scoped Topology RealInnerProductSpace
open scoped NNReal
open Set Filter
open scoped Topology RealInnerProductSpace NNReal

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology RealInnerProductSpace

namespace GaussianPropeller.OneCell

lemma density_integrable : Integrable density := by
  change Integrable (fun x : ℝ => Real.exp (-x^2/2))
  simpa only [ show ∀ x : ℝ, -x^2/2 = -(1/2:ℝ)*x^2 by intro x; ring]
    using integrable_exp_neg_mul_sq (by norm_num : (0:ℝ) < 1/2)

lemma hasDerivAt_density (x : ℝ) : HasDerivAt density (-x*density x) x := by
  unfold density
  convert (((hasDerivAt_pow 2 x).neg.div_const 2).exp) using 1 <;>
  first | rfl | (solve | ring) | (dsimp; ring)

lemma tail_zero : gaussianConst*tail 0 = 1/2 := by
  have h : tail 0 = Real.sqrt (2*Real.pi)/2 := by
    simpa only [tail, density, show ∀ x : ℝ, -x^2/2 = -(1/2:ℝ)*x^2 by intro x; ring,
      show Real.pi/(1/2:ℝ) = 2*Real.pi by ring] using integral_gaussian_Ioi (1/2)
  rw [h, gaussianConst]
  field_simp

section GeneralCell
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

end GeneralCell
end GaussianPropeller.OneCell

end OAI

-- ---- from OAI.Probability.GaussianPropeller.Mills ----
namespace OAI

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal RealInnerProductSpace
open Filter
open scoped Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
open scoped RealInnerProductSpace
open Set Filter
open scoped Topology RealInnerProductSpace
open scoped NNReal
open Set Filter
open scoped Topology RealInnerProductSpace NNReal
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology RealInnerProductSpace

namespace GaussianPropeller.Mills
open OneCell

lemma tail_pos (x : ℝ) : 0 < tail x := by
  apply (setIntegral_pos_iff_support_of_nonneg_ae
    (ae_of_all _ (fun x => (Real.exp_pos _).le)) density_integrable.integrableOn).mpr
  simp [Function.support, Real.exp_ne_zero]

lemma hasDerivAt_tail (x : ℝ) : HasDerivAt tail (-density x) x := by
  have heq : tail = fun a => tail 0 - ∫ t in (0:ℝ)..a, density t := by
    funext a
    have hi := intervalIntegral.integral_Ioi_sub_Ioi'
      (a := 0) (b := a) density_integrable.integrableOn density_integrable.integrableOn
    change tail 0-tail a = _ at hi
    linarith only [hi]
  rw [heq]
  exact (intervalIntegral.integral_hasDerivAt_right
    (density_integrable.intervalIntegrable)
    (by exact (show StronglyMeasurable density by unfold density; fun_prop).stronglyMeasurableAtFilter) (hasDerivAt_density x).continuousAt).const_sub _

end GaussianPropeller.Mills

end OAI

-- ---- from OAI.Probability.GaussianPropeller.ProbabilityBounds ----
namespace OAI

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal RealInnerProductSpace
open Filter
open scoped Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
open scoped RealInnerProductSpace
open Set Filter
open scoped Topology RealInnerProductSpace
open scoped NNReal
open Set Filter
open scoped Topology RealInnerProductSpace NNReal
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology BigOperators

namespace GaussianPropeller.ProbabilityBounds
open OneCell Mills Taylor
lemma hasDerivAt_p (x : ℝ) : HasDerivAt p (-gaussianConst*density x) x := by
  convert (hasDerivAt_tail x).const_mul gaussianConst using 1 <;> first | rfl | ring

lemma exists_p {P : ℝ} (hP : 0 < P) (hPh : P ≤ 1/2) : ∃ x ≥ (0:ℝ), p x=P := by
  have ht : Tendsto p atTop (𝓝 0) := by
    convert! (tendsto_integral_Ioi_zero (f := density) (μ := volume) tendsto_id).const_mul gaussianConst using 1
    simp only [mul_zero]
  have hh := isPreconnected_Ici.intermediate_value_Ioc (a := (0:ℝ)) self_mem_Ici
    (le_principal_iff.mpr (Ici_mem_atTop (0:ℝ)))
    (show ContinuousOn p (Ici 0) from fun x _ => (hasDerivAt_p x).continuousAt.continuousWithinAt) ht
  have hm : P ∈ Ioc 0 (p 0) := by exact ⟨hP, by simpa [p,tail_zero] using hPh⟩
  exact hh hm

lemma loss_eq (x : ℝ) : loss x=gaussianConst^2*density x*(density x-x*tail x) := by
  unfold loss p G lambda
  field_simp [(tail_pos x).ne']

end GaussianPropeller.ProbabilityBounds

end OAI

-- ---- from OAI.Probability.GaussianPropeller.CellBounds ----
namespace OAI

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal RealInnerProductSpace
open Filter
open scoped Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
open scoped RealInnerProductSpace
open Set Filter
open scoped Topology RealInnerProductSpace
open scoped NNReal
open Set Filter
open scoped Topology RealInnerProductSpace NNReal
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology

namespace GaussianPropeller.Reduction
open Set GaussianPropeller.Quantile GaussianPropeller.OneCell GaussianPropeller.ProbabilityBounds
open scoped RealInnerProductSpace
variable {d k : ℕ} [NeZero k]

lemma p_eq_Φ_neg (x : ℝ) : p x=Φ (-x) := by
  rw [Φ_neg, Φ_eq_one_sub_tail]
  simp only [φ, OneCell.gaussianConst, p, OneCell.tail, OneCell.density]
  rw [integral_const_mul]
  ring

lemma loss_eq_quantile {P : ℝ} (_hP : P ∈ Ioo (0:ℝ) 1) {x : ℝ} (hx : p x=P) :
    loss x = φ (q P)*(q P*P+φ (q P)) := by
  have hq : q P = -x := by rw [← hx, p_eq_Φ_neg, q_Φ]
  rw [hq, φ_neg, loss_eq]
  rw [← hx]
  simp only [p, φ, OneCell.gaussianConst, OneCell.density]
  ring

lemma loss_rationalize {C α r L : ℝ} (_hC : 0 < C) (hα : 0 < α)
    (_hr : 0 ≤ r) (hs : 0 ≤ 1-α*r^2)
    (hl : C*(1-Real.sqrt (1-α*r^2)) ≤ α*L) :
    C*r^2/(1+Real.sqrt (1-α*r^2)) ≤ L := by
  have hq := Real.sqrt_nonneg (1-α*r^2)
  have hq2 := Real.sq_sqrt hs
  rw [div_le_iff₀ (by positivity)]
  have hm := mul_le_mul_of_nonneg_right hl (show 0 ≤ 1+Real.sqrt (1-α*r^2) by positivity)
  have heq : C*(1-Real.sqrt (1-α*r^2))*(1+Real.sqrt (1-α*r^2)) = α*(C*r^2) := by
    calc
      _ = C*(1-Real.sqrt (1-α*r^2)^2) := by ring
      _ = _ := by rw [hq2]; ring
  rw [heq] at hm
  exact (mul_le_mul_iff_right₀ hα).mp (by simpa only [mul_assoc] using hm)

lemma minimal_loss_constraint (hk : 2 ≤ k) {A : Fin k → Set (Space d)}
    (hA : MinimalOptimal A) (hC : 9/(8*Real.pi) < value A)
    (hall : ∀ j, gaussian d (A j) ≠ 0) (i : Fin k) :
    ∃ x ≥ (0:ℝ), p x=(gaussian d).real (A i) ∧
      (value A)*(‖centroid (A i)‖/Real.sqrt (value A))^2 /
      (1+Real.sqrt (1-((k:ℝ)/((k:ℝ)-1))*(‖centroid (A i)‖/Real.sqrt (value A))^2)) ≤ loss x := by
  let C := value A
  let r := ‖centroid (A i)‖/Real.sqrt C
  let α := (k:ℝ)/((k:ℝ)-1)
  have hCp : 0 < C := (by positivity : (0:ℝ)<9/(8*Real.pi)).trans hC
  have hk1 : (1:ℝ)<k := by exact_mod_cast (show 1<k by omega)
  have hα : 0<α := div_pos (by linarith) (by linarith)
  have hP := active_probability_mem hk hA hCp (hall i)
  obtain ⟨x,hx,hpx⟩ := exists_p hP.1 hP.2
  refine ⟨x,hx,hpx,?_⟩
  have hl := (optimal_loss_lower hk hA.1 i).trans (minimal_loss_upper hk hA hCp hall i)
  rw [mul_assoc, ← loss_eq_quantile ⟨hP.1,by linarith [hP.2]⟩ hpx] at hl
  have hsq : ‖centroid (A i)‖^2 = C*r^2 := by
    dsimp [r]
    rw [div_pow, Real.sq_sqrt hCp.le]
    field_simp
  have hnon : 0 ≤ C-α*‖centroid (A i)‖^2 := by
    change 0 ≤ (∑ j, ‖centroid (A j)‖^2) - ((k:ℝ)/((k:ℝ)-1))*‖centroid (A i)‖^2
    rw [← recentered_norm_sq hk (fun j => centroid (A j)) (sum_centroid_eq_zero hA.1.1) i]
    positivity
  have hs : 0 ≤ 1-α*r^2 := by
    rw [hsq] at hnon
    nlinarith only [hnon,hCp]
  have hsqrt : Real.sqrt (C-α*‖centroid (A i)‖^2) = Real.sqrt C*Real.sqrt (1-α*r^2) := by
    rw [hsq, show C-α*(C*r^2)=C*(1-α*r^2) by ring, Real.sqrt_mul hCp.le]
  change C-Real.sqrt C*Real.sqrt (C-α*‖centroid (A i)‖^2) ≤ α*loss x at hl
  rw [hsqrt] at hl
  have ht := Real.sq_sqrt hCp.le
  apply loss_rationalize hCp hα (by positivity : 0≤r) hs
  have he : C-Real.sqrt C*(Real.sqrt C*Real.sqrt (1-α*r^2)) = C*(1-Real.sqrt (1-α*r^2)) := by
    rw [←mul_assoc, ←pow_two, ht]; ring
  rwa [he] at hl

end GaussianPropeller.Reduction

end OAI

-- ---- platform node ----
open OAI OAI.GaussianPropeller OAI.GaussianPropeller.Reduction
open MeasureTheory ProbabilityTheory
open scoped ENNReal
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal RealInnerProductSpace
open Filter
open scoped Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
open scoped RealInnerProductSpace
open Set Filter
open scoped Topology RealInnerProductSpace
open scoped NNReal
open Set Filter
open scoped Topology RealInnerProductSpace NNReal
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology
open Set GaussianPropeller.Quantile GaussianPropeller.OneCell GaussianPropeller.ProbabilityBounds
open scoped RealInnerProductSpace


theorem solution : type_of% @_root_.OAI.GaussianPropeller.Reduction.minimal_loss_constraint := @_root_.OAI.GaussianPropeller.Reduction.minimal_loss_constraint
