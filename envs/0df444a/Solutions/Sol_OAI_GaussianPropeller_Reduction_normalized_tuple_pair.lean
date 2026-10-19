-- Prove2me | solution 1 for OAI.GaussianPropeller.Reduction.normalized_tuple_pair
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T11:24:12.577427+00:00
-- url     : https://prove2.me/submissions/bb5712d7-b02a-4b0c-ad1d-66f1a81c054e

-- Generated from openai/math@1581d4c lean/OAI/Probability/GaussianPropeller/FourReduction.lean:L86-L110
-- (upload_full_project.md Phase 4): solution for node OAI.GaussianPropeller.Reduction.normalized_tuple_pair. The node keeps its source
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
import Theorems.Thm_OAI_GaussianPropeller_Reduction_minimal_residual_pair

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

end Reduction

end GaussianPropeller

end OAI

-- ---- from OAI.Probability.GaussianPropeller.PairBounds ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
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
open MeasureTheory Set Filter
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology ENNReal

open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology ENNReal

namespace GaussianPropeller.PairGeometry

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

end GaussianPropeller.PairGeometry

namespace GaussianPropeller.Pair

-- [generator] trimmed: open GaussianPropeller.Analytic GaussianPropeller.PairIntegral GaussianPropeller.PairGeometry
open GaussianPropeller.PairIntegral

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

end GaussianPropeller.Pair

namespace GaussianPropeller.Pair

-- [generator] trimmed: open GaussianPropeller.Analytic GaussianPropeller.PairIntegral
open GaussianPropeller.PairIntegral

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma sqrt_gram_smul {u v : E} {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.sqrt (‖a • u‖^2*‖b • v‖^2-⟪a • u,b • v⟫^2) =
      a*b*Real.sqrt (‖u‖^2*‖v‖^2-⟪u,v⟫^2) := by
  simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg ha, abs_of_nonneg hb,
    inner_smul_left, inner_smul_right, starRingEnd_apply, star_trivial]
  rw [show (a*‖u‖)^2*(b*‖v‖)^2-(b*(a*⟪u,v⟫))^2 =
    (a*b)^2*(‖u‖^2*‖v‖^2-⟪u,v⟫^2) by ring,
    Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (mul_nonneg ha hb)]

end GaussianPropeller.Pair

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

omit [NeZero k] in
theorem residualCoefficient_pos {z y : Space d} (h : ⟪z,y⟫ < 0) :
    0 < residualCoefficient z y := by
  have hz : z ≠ 0 := by intro hz; simp [hz] at h
  exact div_pos (neg_pos.mpr h) (sq_pos_of_pos (norm_pos_iff.mpr hz))

end GaussianPropeller.Reduction

end OAI

-- ---- from OAI.Probability.GaussianPropeller.SpanReduction ----
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

lemma sqrt_value_lower {C : ℝ} (hC : 9/(8*Real.pi) < C) :
    3/(2*Real.sqrt (2*Real.pi)) < Real.sqrt C := by
  have hCp : 0 < C := (by positivity : (0:ℝ) < 9/(8*Real.pi)).trans hC
  have hs : 0 < Real.sqrt (2*Real.pi) := by positivity
  have hs2 : (Real.sqrt (2*Real.pi))^2 = 2*Real.pi := Real.sq_sqrt (by positivity)
  have hrel : (3/(2*Real.sqrt (2*Real.pi)))^2 = 9/(8*Real.pi) := by
    rw [div_pow, mul_pow, hs2]
    ring
  have ht2 := Real.sq_sqrt hCp.le
  have hn : 0 ≤ 3/(2*Real.sqrt (2*Real.pi)) := by positivity
  nlinarith only [hrel,hC,ht2,Real.sqrt_nonneg C]

lemma normalize_pair_constant {C z L M D : ℝ} (hC : 9/(8*Real.pi) < C)
    (hz : 0 ≤ z) (hL : 0 ≤ L) (hM : 0 ≤ M)
    (hD : D ≤ 9*z*L*M/(2*Real.pi*Real.sqrt (2*Real.pi))) :
    (Real.sqrt C)⁻¹*(Real.sqrt C)⁻¹*D ≤ (3/Real.pi)*(z/Real.sqrt C)*L*M := by
  have hCp : 0 < C := (by positivity : (0:ℝ) < 9/(8*Real.pi)).trans hC
  have ht : 0 < Real.sqrt C := Real.sqrt_pos.mpr hCp
  have hq : 0 < Real.sqrt (2*Real.pi) := by positivity
  have hp : 0 < Real.pi := Real.pi_pos
  have hh := le_of_lt (sqrt_value_lower hC)
  have hh' : 3 ≤ Real.sqrt C*(2*Real.sqrt (2*Real.pi)) := (div_le_iff₀ (by positivity)).mp hh
  have hb : 9/(2*Real.pi*Real.sqrt (2*Real.pi)) ≤ (3/Real.pi)*Real.sqrt C := by
    apply (div_le_iff₀ (by positivity)).mpr
    calc
      9 ≤ 3*(Real.sqrt C*(2*Real.sqrt (2*Real.pi))) := by linarith only [hh']
      _ = _ := by field_simp
  have hDb : D ≤ (3/Real.pi)*Real.sqrt C*z*L*M := by
    calc
      D ≤ (9/(2*Real.pi*Real.sqrt (2*Real.pi)))*z*L*M := by
        convert hD using 1
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hb hz) hL) hM
  have hm := mul_le_mul_of_nonneg_left hDb
    (show 0 ≤ (Real.sqrt C)⁻¹*(Real.sqrt C)⁻¹ by positivity)
  convert! hm using 1
  field_simp

variable {d k : ℕ} [NeZero k]

theorem minimal_normalized_pair {A : Fin k → Set (Space d)} (hA : MinimalOptimal A)
    (hC : 9/(8*Real.pi) < value A) {i j l : Fin k}
    (hi : gaussian d (A i) ≠ 0) (hj : gaussian d (A j) ≠ 0)
    (hl : gaussian d (A l) ≠ 0) (hij : i ≠ j) (hil : i ≠ l) :
    let z := centroid (A i)
    let r := (Real.sqrt (value A))⁻¹ • residualVector z (centroid (A j))
    let s := (Real.sqrt (value A))⁻¹ • residualVector z (centroid (A l))
    Real.sqrt (‖r‖^2*‖s‖^2-⟪r,s⟫^2) ≤
      (3/Real.pi)*(‖z‖/Real.sqrt (value A))*(1+residualCoefficient z (centroid (A j)))*
        (1+residualCoefficient z (centroid (A l))) := by
  dsimp only
  rw [GaussianPropeller.Pair.sqrt_gram_smul (by positivity) (by positivity)]
  apply normalize_pair_constant hC (norm_nonneg _)
    (le_of_lt (lt_trans (by norm_num : (0:ℝ)<1) (lt_add_of_pos_right _
      (residualCoefficient_pos (negative_inner_of_minimal hA hij hi hj)))))
    (le_of_lt (lt_trans (by norm_num : (0:ℝ)<1) (lt_add_of_pos_right _
      (residualCoefficient_pos (negative_inner_of_minimal hA hil hi hl)))))
  exact minimal_residual_pair hA ((by positivity : (0:ℝ)<9/(8*Real.pi)).trans hC) hi hj hl hij hil

end GaussianPropeller.Reduction

end OAI

-- ---- from OAI.Probability.GaussianPropeller.Geometry ----
namespace OAI

universe uE uι

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

namespace GaussianPropeller.Geometry

open scoped RealInnerProductSpace

section InnerProduct
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma gram_det_nonneg (u v : E) : 0 ≤ ‖u‖^2*‖v‖^2-⟪u,v⟫^2 := by
  have h := real_inner_mul_inner_self_le u v
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at h
  nlinarith only [h]

end InnerProduct

end GaussianPropeller.Geometry

end OAI

-- ---- from OAI.Probability.GaussianPropeller.FourReduction ----
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
variable {d k : ℕ}

lemma residualCoefficient_smul {s:ℝ} (hs:0<s) (z y:Space d) :
    residualCoefficient (s•z) (s•y)=residualCoefficient z y := by
  simp only [residualCoefficient,real_inner_smul_left,real_inner_smul_right,norm_smul,
    Real.norm_eq_abs,abs_of_pos hs,mul_pow]
  field_simp

lemma residualVector_smul {s:ℝ} (hs:0<s) (z y:Space d) :
    residualVector (s•z) (s•y)=s•residualVector z y := by
  rw [residualVector,residualCoefficient_smul hs,residualVector,smul_add,smul_comm]

lemma normalized_tuple_pair [NeZero k] {A:Fin k→Set (Space d)} (hA:MinimalOptimal A)
    (hC:9/(8*Real.pi)<value A) (hall:∀ j,gaussian d (A j)≠0)
    {i j l:Fin k} (hij:i≠j) (hil:i≠l) :
    let z := fun j=>(Real.sqrt (value A))⁻¹•centroid (A j)
    let u := residualVector (z i) (z j)
    let v := residualVector (z i) (z l)
    ‖u‖^2*‖v‖^2-⟪u,v⟫^2 ≤ (3/Real.pi)^2*‖z i‖^2*
      (1+residualCoefficient (z i) (z j))^2*(1+residualCoefficient (z i) (z l))^2 := by
  dsimp only
  have hCp : 0<value A := (by positivity : (0:ℝ)<9/(8*Real.pi)).trans hC
  have hs : 0<(Real.sqrt (value A))⁻¹ := inv_pos.mpr (Real.sqrt_pos.mpr hCp)
  rw [residualVector_smul hs,residualVector_smul hs,residualCoefficient_smul hs,
    residualCoefficient_smul hs]
  have h := minimal_normalized_pair hA hC (hall i) (hall j) (hall l) hij hil
  dsimp only at h
  have hb : 0 ≤ (3/Real.pi)*(‖centroid (A i)‖/Real.sqrt (value A))*
      (1+residualCoefficient (centroid (A i)) (centroid (A j)))*
      (1+residualCoefficient (centroid (A i)) (centroid (A l))) := by
    have hj:=residualCoefficient_pos (negative_inner_of_minimal hA hij (hall i) (hall j))
    have hl:=residualCoefficient_pos (negative_inner_of_minimal hA hil (hall i) (hall l))
    positivity
  have hh := (sq_le_sq₀ (Real.sqrt_nonneg _) hb).mpr h
  rw [Real.sq_sqrt (Geometry.gram_det_nonneg _ _)] at hh
  convert hh using 1 <;>
  first | rfl | (simp only [norm_smul,Real.norm_eq_abs,abs_of_pos hs,mul_pow,div_pow]; ring)

end GaussianPropeller.Reduction

namespace GaussianPropeller.Reduction
variable {d k:ℕ}

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


theorem solution : type_of% @_root_.OAI.GaussianPropeller.Reduction.normalized_tuple_pair := @_root_.OAI.GaussianPropeller.Reduction.normalized_tuple_pair
