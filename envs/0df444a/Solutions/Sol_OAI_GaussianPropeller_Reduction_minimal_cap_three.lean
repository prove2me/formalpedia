-- Prove2me | solution 1 for OAI.GaussianPropeller.Reduction.minimal_cap_three
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T13:54:01.39484+00:00
-- url     : https://prove2.me/submissions/8d00878e-34e8-4208-a0e2-87e1c8c725a8

-- Generated from openai/math@1581d4c lean/OAI/Probability/GaussianPropeller/SmallCell.lean:L53-L69
-- (upload_full_project.md Phase 4): solution for node OAI.GaussianPropeller.Reduction.minimal_cap_three. The node keeps its source
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
import Definitions.Def_OAI_Probability_GaussianPropeller_PairIntegral
import Definitions.Def_OAI_Probability_GaussianPropeller_ResidualBounds
import Definitions.Def_OAI_Probability_GaussianPropeller_Polar
import Definitions.Def_OAI_Probability_GaussianPropeller_CapIntegral
import Definitions.Def_OAI_Probability_GaussianPropeller_Coordinates
import Definitions.Def_OAI_Probability_GaussianPropeller_CapBounds
import Definitions.Def_OAI_Probability_GaussianPropeller_CapNumeric
import Definitions.Def_OAI_Probability_GaussianPropeller_Geometry
import Definitions.Def_OAI_Probability_GaussianPropeller_QuarticCertificates
import Definitions.Def_OAI_Probability_GaussianPropeller_CapCertificates
import Definitions.Def_OAI_Probability_GaussianPropeller_Scalar
import Theorems.Thm_OAI_GaussianPropeller_Cap_cone_three
import Theorems.Thm_OAI_GaussianPropeller_Reduction_active_eq_closedCell_ae
import Theorems.Thm_OAI_GaussianPropeller_Reduction_active_probability_mem
import Theorems.Thm_OAI_GaussianPropeller_Reduction_exists_span_cone
import Theorems.Thm_OAI_GaussianPropeller_sum_centroid_eq_zero

-- ---- from OAI.Probability.GaussianPropeller.Moments ----
namespace OAI

universe uF

open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace GaussianPropeller

open scoped RealInnerProductSpace

theorem integrable_id_gaussian (d : ℕ) :
    Integrable (fun x : Space d => x) (gaussian d) := by
  exact IsGaussian.integrable_id (μ := stdGaussian (Space d))

end GaussianPropeller

end OAI

-- ---- from OAI.Probability.GaussianPropeller.Dual ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace GaussianPropeller
open scoped RealInnerProductSpace

namespace Reduction

variable {d k : ℕ} [NeZero k]

omit [NeZero k] in
theorem merge_partition {A : Fin k → Set (Space d)} (hA : IsPartition A)
    {i j : Fin k} (hij : i ≠ j) : IsPartition (merge A i j) := by
  classical
  constructor
  · intro l
    by_cases hli : l = i
    · simpa [merge, hli] using (hA.1 i).union (hA.1 j)
    · by_cases hlj : l = j
      · simp [merge, hlj, hij.symm]
      · simpa [merge, hli, hlj] using hA.1 l
  · filter_upwards [hA.2] with x hx
    obtain ⟨l, hl, huniq⟩ := hx
    by_cases hlj : l = j
    · subst l
      refine ⟨i, ?_, ?_⟩
      · simp [merge, hl]
      · intro q hq
        by_cases hqi : q = i
        · exact hqi
        · by_cases hqj : q = j
          · simp [merge, hqj, hij.symm] at hq
          · have hqA : x ∈ A q := by simpa [merge, hqi, hqj] using hq
            exact False.elim (hqj (huniq q hqA))
    · refine ⟨l, ?_, ?_⟩
      · by_cases hli : l = i
        · subst l
          simp [merge, hl]
        · simp [merge, hli, hlj, hl]
      · intro q hq
        by_cases hqi : q = i
        · subst q
          have h : x ∈ A i ∨ x ∈ A j := by simpa [merge] using hq
          rcases h with hi | hj
          · exact huniq i hi
          · exact False.elim (hlj (huniq j hj).symm)
        · by_cases hqj : q = j
          · simp [merge, hqj, hij.symm] at hq
          · apply huniq q
            simpa [merge, hqi, hqj] using hq

omit [NeZero k] in
theorem centroid_union {A : Fin k → Set (Space d)} (hA : IsPartition A)
    {i j : Fin k} (hij : i ≠ j) : centroid (A i ∪ A j) = centroid (A i) + centroid (A j) := by
  have hind : (A i ∪ A j).indicator (fun x => x) =ᵐ[gaussian d]
      (fun x => (A i).indicator (fun x => x) x + (A j).indicator (fun x => x) x) := by
    filter_upwards [hA.2] with x hx
    obtain ⟨l, _, huniq⟩ := hx
    by_cases hi : x ∈ A i <;> by_cases hj : x ∈ A j
    · exact False.elim (hij ((huniq i hi).trans (huniq j hj).symm))
    all_goals simp [Set.indicator, hi, hj]
  unfold centroid
  rw [← integral_indicator ((hA.1 i).union (hA.1 j)), integral_congr_ae hind,
    integral_add ((integrable_id_gaussian d).indicator (hA.1 i))
      ((integrable_id_gaussian d).indicator (hA.1 j)),
    integral_indicator (hA.1 i), integral_indicator (hA.1 j)]

omit [NeZero k] in
theorem value_merge {A : Fin k → Set (Space d)} (hA : IsPartition A)
    {i j : Fin k} (hij : i ≠ j) :
    value (merge A i j) = value A + 2 * ⟪centroid (A i), centroid (A j)⟫ := by
  classical
  have hcent : centroid (A i ∪ A j) = centroid (A i) + centroid (A j) := centroid_union hA hij
  have hfun (l : Fin k) : ‖centroid (merge A i j l)‖ ^ 2 =
      ‖centroid (A l)‖ ^ 2 +
      (if l = i then ‖centroid (A i) + centroid (A j)‖ ^ 2 - ‖centroid (A i)‖ ^ 2 else 0) +
      (if l = j then -‖centroid (A j)‖ ^ 2 else 0) := by
    by_cases hli : l = i
    · subst l
      simp [merge, hij, hcent]
    · by_cases hlj : l = j
      · subst l
        simp [merge, hij.symm]
      · simp [merge, hli, hlj]
  unfold value
  simp_rw [hfun, Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [norm_add_sq_real]
  ring

omit [NeZero k] in
theorem activeCount_merge_lt {A : Fin k → Set (Space d)} {i j : Fin k}
    (hij : i ≠ j) (hi : gaussian d (A i) ≠ 0) (hj : gaussian d (A j) ≠ 0) :
    activeCount (merge A i j) < activeCount A := by
  classical
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  constructor
  · intro l hl
    simp only [activeLabels, Finset.mem_filter, Finset.mem_univ, true_and] at hl ⊢
    by_cases hli : l = i
    · simpa only [hli] using hi
    · by_cases hlj : l = j
      · simp [merge, hlj, hij.symm] at hl
      · simpa only [merge, ite_eq_right hli, ite_eq_right hlj] using hl
  · intro heq
    have hs : j ∈ activeLabels (merge A i j) := by
      rw [heq]
      simpa only [activeLabels, Finset.mem_filter, Finset.mem_univ, true_and] using hj
    have hnon : gaussian d (merge A i j j) ≠ 0 := (Finset.mem_filter.mp hs).2
    exact hnon (by simp [merge, hij.symm])

omit [NeZero k] in
theorem negative_inner_of_minimal {A : Fin k → Set (Space d)} (hA : MinimalOptimal A)
    {i j : Fin k} (hij : i ≠ j) (hi : gaussian d (A i) ≠ 0) (hj : gaussian d (A j) ≠ 0) :
    ⟪centroid (A i), centroid (A j)⟫ < 0 := by
  have hpart := merge_partition hA.1.1 hij
  have hvalue := value_merge hA.1.1 hij
  have hbound := hA.1.2 _ hpart
  have hle : ⟪centroid (A i), centroid (A j)⟫ ≤ 0 := by linarith
  apply lt_of_le_of_ne hle
  intro heq
  have heqval : value (merge A i j) = value A := by rw [heq, mul_zero, add_zero] at hvalue; exact hvalue
  have hopt : Optimal (merge A i j) := ⟨hpart, fun B hB => by rw [heqval]; exact hA.1.2 B hB⟩
  exact (not_lt_of_ge (hA.2 _ hopt)) (activeCount_merge_lt hij hi hj)

omit [NeZero k] in
theorem centroid_eq_zero_of_null {A : Set (Space d)} (hA : gaussian d A = 0) : centroid A = 0 := by
  unfold centroid
  rw [Measure.restrict_eq_zero.mpr hA, integral_zero_measure]

omit [NeZero k] in

theorem two_nonzero_centroids {A : Fin k → Set (Space d)} (hA : IsPartition A)
    (hpos : 0 < value A) : ∃ i j, i ≠ j ∧ centroid (A i) ≠ 0 ∧ centroid (A j) ≠ 0 := by
  classical
  have hi : ∃ i, centroid (A i) ≠ 0 := by
    by_contra! h
    have hz : value A = 0 := by simp [value, h]
    linarith
  obtain ⟨i, hi⟩ := hi
  have hj : ∃ j, j ≠ i ∧ centroid (A j) ≠ 0 := by
    by_contra! h
    have hz : ∑ j, centroid (A j) = centroid (A i) := by
      apply Finset.sum_eq_single i
      · intro j _ hji
        exact h j hji
      · simp
    exact hi (hz.symm.trans (sum_centroid_eq_zero hA))
  obtain ⟨j, hji, hj⟩ := hj
  exact ⟨i, j, hji.symm, hi, hj⟩

omit [NeZero k] in
theorem active_centroid_ne_zero {A : Fin k → Set (Space d)} (hA : MinimalOptimal A)
    (hpos : 0 < value A) {i : Fin k} (hi : gaussian d (A i) ≠ 0) : centroid (A i) ≠ 0 := by
  obtain ⟨j, l, hjl, hj, hl⟩ := two_nonzero_centroids hA.1.1 hpos
  have hjm : gaussian d (A j) ≠ 0 := fun hz => hj (centroid_eq_zero_of_null hz)
  have hlm : gaussian d (A l) ≠ 0 := fun hz => hl (centroid_eq_zero_of_null hz)
  by_cases hij : i = j
  · simpa only [hij] using hj
  · have hneg := negative_inner_of_minimal hA hij hi hjm
    intro hz
    simp only [hz, inner_zero_left] at hneg
    exact (lt_irrefl 0) hneg

end Reduction

end GaussianPropeller

end OAI

-- ---- from OAI.Probability.GaussianPropeller.ResidualBounds ----
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
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology ENNReal
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology ENNReal

namespace GaussianPropeller.Reduction

open scoped RealInnerProductSpace

variable {d k : ℕ} [NeZero k]

theorem centroid_closedCell {A : Fin k → Set (Space d)} (hA : MinimalOptimal A)
    (hpos : 0 < value A) {i : Fin k} (hi : gaussian d (A i) ≠ 0) :
    centroid (closedCell (fun j => centroid (A j)) i) = centroid (A i) := by
  exact setIntegral_congr_set (active_eq_closedCell_ae hA hpos hi).symm

end GaussianPropeller.Reduction

end OAI

-- ---- from OAI.Probability.GaussianPropeller.CapReduction ----
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
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology ENNReal
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology ENNReal
open Metric
open MeasureTheory ProbabilityTheory Set
open scoped RealInnerProductSpace ENNReal

namespace GaussianPropeller.Reduction
open Coords
variable {d k n : ℕ} [NeZero k]

lemma minimal_span_cone {A:Fin k→Set (Space d)} (hA:MinimalOptimal A)
    (hpos:0<value A) (hactive:∀ j,gaussian d (A j)≠0) (i:Fin k) (hdim:k-1=n+1) :
    ∃ K : Set (Space (n+1)), MeasurableSet K ∧
      (∀ r:ℝ, 0<r → ∀ x, r•x∈K ↔ x∈K) ∧
      (gaussian (n+1)).real K=(gaussian d).real (A i) ∧
      (∫ x, K.indicator (fun x : Space (n+1)=> x 0) x ∂gaussian (n+1))=‖centroid (A i)‖ := by
  obtain ⟨K,hK,hcone,hP,hM⟩ := exists_span_cone (sum_centroid_eq_zero hA.1.1)
    (fun j l hjl => negative_inner_of_minimal hA hjl (hactive j) (hactive l))
    i (active_centroid_ne_zero hA hpos (hactive i)) hdim
    (centroid_closedCell hA hpos (hactive i))
  refine ⟨K,hK,hcone,hP.trans ?_,hM⟩
  rw [measureReal_def,measureReal_def,measure_congr (active_eq_closedCell_ae hA hpos (hactive i))]

end GaussianPropeller.Reduction

end OAI

-- ---- from OAI.Probability.GaussianPropeller.SmallCell ----
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
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology ENNReal
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology ENNReal
open Metric
open MeasureTheory ProbabilityTheory Set
open scoped RealInnerProductSpace ENNReal

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal RealInnerProductSpace

namespace GaussianPropeller.Reduction
open OneCell
variable {d:ℕ}

lemma sqrt_threshold {C:ℝ} (hC:9/(8*Real.pi)<C) :
    (3/2:ℝ)*gaussianConst < Real.sqrt C := by
  have hCp:0<C := (by positivity : (0:ℝ)<9/(8*Real.pi)).trans hC
  have hc0:0≤gaussianConst := by unfold gaussianConst; positivity
  have hc2:gaussianConst^2=1/(2*Real.pi) := by
    rw [gaussianConst,inv_pow,Real.sq_sqrt (by positivity),one_div]
  apply (sq_lt_sq₀ (by positivity : 0≤(3/2:ℝ)*gaussianConst) (Real.sqrt_nonneg C)).mp
  rw [mul_pow,hc2,Real.sq_sqrt hCp.le]
  have he : (3/2:ℝ)^2*(1/(2*Real.pi))=9/(8*Real.pi) := by field_simp; ring
  rwa [he]

lemma minimal_cap_three {A:Fin 4→Set (Space d)} (hA:MinimalOptimal A)
    (hC:9/(8*Real.pi)<value A) (hall:∀ j,gaussian d (A j)≠0) (i:Fin 4) :
    ‖centroid (A i)‖/Real.sqrt (value A) ≤
      (8/3:ℝ)*(gaussian d).real (A i)*(1-(gaussian d).real (A i)) := by
  have hCp:0<value A := (by positivity : (0:ℝ)<9/(8*Real.pi)).trans hC
  obtain ⟨K,hK,hcone,hP,hM⟩ := minimal_span_cone (n:=2) hA hCp hall i (by norm_num)
  have hp := active_probability_mem (by norm_num) hA hCp (hall i)
  have hb := Cap.cone_three K hK hcone (by change (gaussian 3).real K∈Set.Ioo (0:ℝ) 1; rw [hP]; exact ⟨hp.1,by linarith only [hp.2]⟩)
    (by change (gaussian 3).real K≤1/2; rw [hP]; exact hp.2)
  change (∫ x, K.indicator (fun x:Space 3=>x 0) x ∂gaussian 3) ≤
    4*gaussianConst*(gaussian 3).real K*(1-(gaussian 3).real K) at hb
  rw [hP,hM] at hb
  apply (div_le_iff₀ (Real.sqrt_pos.mpr hCp)).mpr
  have hs := sqrt_threshold hC
  have hh := mul_le_mul_of_nonneg_right (show 4*gaussianConst ≤ (8/3:ℝ)*Real.sqrt (value A) by linarith only [hs])
    (show 0≤(gaussian d).real (A i)*(1-(gaussian d).real (A i)) by exact mul_nonneg hp.1.le (by linarith only [hp.2]))
  nlinarith only [hb,hh]

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
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology ENNReal
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology ENNReal
open Metric
open MeasureTheory ProbabilityTheory Set
open scoped RealInnerProductSpace ENNReal
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal RealInnerProductSpace
open OneCell


theorem solution : type_of% @_root_.OAI.GaussianPropeller.Reduction.minimal_cap_three := @_root_.OAI.GaussianPropeller.Reduction.minimal_cap_three
