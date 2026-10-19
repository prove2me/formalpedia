-- Prove2me | solution 1 for OAI.GaussianPropeller.Reduction.active_probability_mem
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T08:48:42.863728+00:00
-- url     : https://prove2.me/submissions/f646d761-8605-4d7c-b8a1-14b347114c48

-- Generated from openai/math@1581d4c lean/OAI/Probability/GaussianPropeller/CellBounds.lean:L42-L65
-- (upload_full_project.md Phase 4): solution for node OAI.GaussianPropeller.Reduction.active_probability_mem. The node keeps its source
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
import Theorems.Thm_OAI_GaussianPropeller_Reduction_active_eq_closedCell_ae
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

lemma Φ_zero : Φ 0 = 1/2 := by
  have h := Φ_neg 0
  simp only [neg_zero] at h
  linarith only [h]
section Integration
variable {X : Type uX} [MeasurableSpace X] {μ : Measure X} [IsProbabilityMeasure μ]

end Integration
end GaussianPropeller.Quantile

end OAI

-- ---- from OAI.Probability.GaussianPropeller.ConeConcavity ----
namespace OAI

universe uX uι uκ

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

namespace GaussianPropeller.EhrhardCone
open GaussianPropeller.Quantile GaussianPropeller.EhrhardSmooth
variable {ι : Type uι} {κ : Type uκ} [Fintype ι] [Fintype κ] [Nonempty κ]
local notation "E" => EuclideanSpace ℝ ι
local notation "γ" => stdGaussian E

end GaussianPropeller.EhrhardCone

namespace GaussianPropeller.Quantile

lemma Φ_eq_gaussianReal (a : ℝ) : Φ a = (gaussianReal 0 1).real (Iic a) := by
  rw [measureReal_def, gaussianReal_apply_eq_integral 0 (by norm_num : (1:NNReal) ≠ 0),
    ENNReal.toReal_ofReal (integral_nonneg (fun x => gaussianPDFReal_nonneg 0 1 x))]
  unfold Φ
  congr 1
  funext x
  simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero, φ]

end GaussianPropeller.Quantile

namespace GaussianPropeller.EhrhardCone
open GaussianPropeller.Quantile
variable {ι : Type uι} {κ : Type uκ} [Fintype ι] [Fintype κ] [Nonempty κ]
local notation "E" => EuclideanSpace ℝ ι
local notation "γ" => stdGaussian E

end GaussianPropeller.EhrhardCone

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

section GeneralCell
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma map_unit_inner_gaussian (e : E) (he : ‖e‖=1) :
    (stdGaussian E).map (fun x => ⟪e,x⟫) = gaussianReal 0 1 := by
  change (stdGaussian E).map (InnerProductSpace.toDual ℝ E e) = _
  rw [IsGaussian.map_eq_gaussianReal, integral_strongDual_stdGaussian,
    variance_dual_stdGaussian, LinearIsometryEquiv.norm_map, he]
  norm_num

end GeneralCell
end GaussianPropeller.OneCell

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

lemma winning_inner_nonneg (z : Fin k → Space d) (hz : ∑ j,z j=0)
    (i : Fin k) {x : Space d} (hx : x ∈ closedCell z i) : 0 ≤ ⟪z i,x⟫ := by
  have hh : (0:ℝ) ≤ ∑ j : Fin k, (⟪z i,x⟫-⟪z j,x⟫) :=
    Finset.sum_nonneg (fun j _ => sub_nonneg.mpr (hx j))
  have hz' : (∑ j,⟪z j,x⟫)=0 := by rw [← sum_inner,hz,inner_zero_left]
  rw [Finset.sum_sub_distrib, hz', sub_zero,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hh
  exact nonneg_of_mul_nonneg_right hh (by exact_mod_cast (NeZero.pos k))

lemma active_probability_mem (_hk : 2 ≤ k) {A : Fin k → Set (Space d)}
    (hA : MinimalOptimal A) (hpos : 0 < value A) {i : Fin k}
    (hi : gaussian d (A i) ≠ 0) : 0 < (gaussian d).real (A i) ∧ (gaussian d).real (A i) ≤ 1/2 := by
  let : IsProbabilityMeasure (gaussian d) := inferInstanceAs (IsProbabilityMeasure (stdGaussian (Space d)))
  have hP : 0 < (gaussian d).real (A i) := ENNReal.toReal_pos hi (measure_ne_top _ _)
  have hzn : centroid (A i) ≠ 0 := active_centroid_ne_zero hA hpos hi
  let e : Space d := - (‖centroid (A i)‖⁻¹ • centroid (A i))
  have he : ‖e‖=1 := by simp [e, norm_smul, norm_ne_zero_iff.mpr hzn]
  have hmap := OneCell.map_unit_inner_gaussian e he
  have hs : closedCell (fun j => centroid (A j)) i ⊆ {x | ⟪e,x⟫ ≤ 0} := by
    intro x hx
    have hn := winning_inner_nonneg (fun j => centroid (A j)) (sum_centroid_eq_zero hA.1.1) i hx
    simp only [Set.mem_ofPred_eq,e,inner_neg_left,real_inner_smul_left]
    exact neg_nonpos.mpr (mul_nonneg (inv_nonneg.mpr (norm_nonneg _)) hn)
  have heq : (gaussian d) {x | ⟪e,x⟫ ≤ 0} = (gaussianReal 0 1) (Iic 0) := by
    rw [← hmap, Measure.map_apply (by fun_prop) measurableSet_Iic]
    rfl
  refine ⟨hP, ?_⟩
  have hh := measure_mono (μ:=gaussian d) hs
  rw [← measure_congr (active_eq_closedCell_ae hA hpos hi), heq] at hh
  have hh' := ENNReal.toReal_mono (measure_ne_top _ _) hh
  change (gaussian d).real (A i) ≤ (gaussianReal 0 1).real (Iic 0) at hh'
  rw [← Φ_eq_gaussianReal, Φ_zero] at hh'
  exact hh'

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


theorem solution : type_of% @_root_.OAI.GaussianPropeller.Reduction.active_probability_mem := @_root_.OAI.GaussianPropeller.Reduction.active_probability_mem
