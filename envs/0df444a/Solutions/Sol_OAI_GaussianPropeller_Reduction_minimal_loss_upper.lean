-- Prove2me | solution 1 for OAI.GaussianPropeller.Reduction.minimal_loss_upper
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T08:23:09.744389+00:00
-- url     : https://prove2.me/submissions/ecee2a99-0aee-45e2-9318-957143f8698d

-- Generated from openai/math@1581d4c lean/OAI/Probability/GaussianPropeller/ConeReduction.lean:L70-L129
-- (upload_full_project.md Phase 4): solution for node OAI.GaussianPropeller.Reduction.minimal_loss_upper. The node keeps its source
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
import Theorems.Thm_OAI_GaussianPropeller_EhrhardCone_integral_prob_upper
import Theorems.Thm_OAI_GaussianPropeller_Gram_exists_translation
import Theorems.Thm_OAI_GaussianPropeller_Reduction_active_eq_closedCell_ae
import Theorems.Thm_OAI_GaussianPropeller_Reduction_scoreMax_recentered
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

theorem exists_scoreMax (v : Fin k → Space d) (x : Space d) :
    ∃ i, ⟪v i, x⟫ = scoreMax v x := by
  obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty (fun i => ⟪v i, x⟫)
  exact ⟨i, hi.symm⟩

theorem continuous_scoreMax (v : Fin k → Space d) : Continuous (scoreMax v) := by
  exact Continuous.finset_sup'_apply Finset.univ_nonempty (fun _ _ => by fun_prop)

theorem norm_scoreMax_le (v : Tuple d k) (x : Space d) :
    ‖scoreMax v.ofLp x‖ ≤ ‖v‖ * ‖x‖ := by
  obtain ⟨i, hi⟩ := exists_scoreMax v.ofLp x
  rw [← hi]
  exact (norm_inner_le_norm _ _).trans
    (mul_le_mul_of_nonneg_right (PiLp.norm_apply_le v i) (norm_nonneg x))

theorem integrable_scoreMax (v : Tuple d k) :
    Integrable (scoreMax v.ofLp) (gaussian d) := by
  apply ((integrable_id_gaussian d).norm.const_mul ‖v‖).mono'
    (continuous_scoreMax v.ofLp).aestronglyMeasurable
  exact Filter.Eventually.of_forall (norm_scoreMax_le v)

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

-- ---- from OAI.Probability.GaussianPropeller.Deletion ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

open MeasureTheory ProbabilityTheory
open scoped ENNReal

open scoped RealInnerProductSpace

namespace GaussianPropeller.Reduction

variable {d k : ℕ} [NeZero k]

lemma omittedMax_integrable (hk : 2 ≤ k) (z : Fin k → Space d)
    (hz : ∑ j, z j = 0) (i : Fin k) :
    Integrable (omittedMax hk z i) (gaussian d) := by
  have heq : omittedMax hk z i = fun x => scoreMax (recentered z i).ofLp x -
      ⟪((k:ℝ)-1)⁻¹ • z i,x⟫ := by
    funext x
    rw [scoreMax_recentered hk z hz i x]
    ring
  rw [heq]
  exact (integrable_scoreMax _).sub
    (Integrable.const_inner _ (integrable_id_gaussian d))

end GaussianPropeller.Reduction

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

end GaussianPropeller.Quantile

namespace GaussianPropeller.EhrhardCone
open GaussianPropeller.Quantile
variable {ι : Type uι} {κ : Type uκ} [Fintype ι] [Fintype κ] [Nonempty κ]
local notation "E" => EuclideanSpace ℝ ι
local notation "γ" => stdGaussian E

omit [Fintype κ] [Nonempty κ] in
lemma prob_zero [Fintype κ] [Nonempty κ] (v : κ → E) : prob v 0 = (γ).real (cone v) := by
  simp only [prob, shifted, zero_add, ofPred_mem_eq]

end GaussianPropeller.EhrhardCone

end OAI

-- ---- from OAI.Probability.GaussianPropeller.ConeReduction ----
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

namespace GaussianPropeller.Reduction
open Set GaussianPropeller.Quantile
open scoped RealInnerProductSpace
variable {d k : ℕ} [NeZero k]

omit [NeZero k] in
lemma difference_cone_eq [NeZero k] (z : Fin k → Space d) (i : Fin k) :
    EhrhardCone.cone (fun j : {j : Fin k // j ≠ i} => z i-z j) = closedCell z i := by
  ext x
  constructor
  · intro hx j
    by_cases hji : j = i
    · subst j; rfl
    · have hh := hx ⟨j,hji⟩
      simp only [inner_sub_left] at hh
      linarith only [hh]
  · intro hx j
    change 0 ≤ ⟪z i-z j,x⟫
    rw [inner_sub_left]
    exact sub_nonneg.mpr (hx j)

omit [NeZero k] in
lemma gap_event_eq [NeZero k] (hk : 2 ≤ k) (z : Fin k → Space d) (i : Fin k)
    (h : Space d) (hh : ∀ j, j ≠ i → ⟪h,z i-z j⟫ = 1) {u : ℝ} (hu : 0 < u) :
    {x | u ≤ max (⟪z i,x⟫ - omittedMax hk z i x) 0} =
      EhrhardCone.shifted (fun j : {j : Fin k // j ≠ i} => z i-z j) (-u•h) := by
  classical
  ext x
  have hpair (j : {j : Fin k // j ≠ i}) : ⟪z i-z j,-u•h+x⟫ = -u+(⟪z i,x⟫-⟪z j,x⟫) := by
    have hcomm : ⟪z i-z j,h⟫=1 := (real_inner_comm _ _).trans (hh j j.property)
    rw [inner_add_right, inner_smul_right, hcomm, mul_one, inner_sub_left]
  change (u ≤ max (⟪z i,x⟫ - omittedMax hk z i x) 0) ↔
    ∀ j : {j : Fin k // j ≠ i}, 0 ≤ ⟪z i-z j,-u•h+x⟫
  simp only [le_max_iff, not_le.mpr hu, or_false, hpair]
  constructor
  · intro hx j
    have hm := Finset.le_sup' (fun j => ⟪z j,x⟫)
      (Finset.mem_erase.mpr ⟨j.property,Finset.mem_univ _⟩)
    change ⟪z j,x⟫ ≤ omittedMax hk z i x at hm
    linarith only [hx,hm]
  · intro hx
    have hm : omittedMax hk z i x ≤ ⟪z i,x⟫-u := by
      apply Finset.sup'_le
      intro j hj
      have hj' := hx ⟨j, Finset.ne_of_mem_erase hj⟩
      linarith only [hj']
    linarith only [hm]

lemma minimal_loss_upper (hk : 2 ≤ k) {A : Fin k → Set (Space d)}
    (hA : MinimalOptimal A) (hpos : 0 < value A)
    (hall : ∀ j, gaussian d (A j) ≠ 0) (i : Fin k) :
    (∫ x, max (⟪centroid (A i),x⟫ -
      omittedMax hk (fun j => centroid (A j)) i x) 0 ∂gaussian d) ≤
      ((k:ℝ)/((k:ℝ)-1)) * φ (q ((gaussian d).real (A i))) *
      (q ((gaussian d).real (A i)) * (gaussian d).real (A i)+φ (q ((gaussian d).real (A i)))) := by
  classical
  let : IsProbabilityMeasure (gaussian d) := inferInstanceAs (IsProbabilityMeasure (stdGaussian (Space d)))
  let z : Fin k → Space d := fun j => centroid (A j)
  let v : {j : Fin k // j ≠ i} → Space d := fun j => z i-z j
  have : Nonempty {j : Fin k // j ≠ i} := by
    obtain ⟨j,hj⟩ := erase_univ_nonempty hk i
    exact ⟨j,Finset.ne_of_mem_erase hj⟩
  have hneg : Pairwise (fun j l => ⟪z j,z l⟫ < 0) := fun j l hjl =>
    negative_inner_of_minimal hA hjl (hall j) (hall l)
  have hz : ∑ j, z j = 0 := sum_centroid_eq_zero hA.1.1
  obtain ⟨h,_,hh,hpair⟩ := Gram.exists_translation z hneg hz i
  simp only [Fintype.card_fin] at hpair
  have hcone : EhrhardCone.cone v = closedCell z i := difference_cone_eq z i
  have hae : A i =ᵐ[gaussian d] EhrhardCone.cone v := by
    rw [hcone]; exact active_eq_closedCell_ae hA hpos (hall i)
  have hcentroid : (∫ x in EhrhardCone.cone v, x ∂gaussian d) = z i :=
    setIntegral_congr_set hae.symm
  have hp : EhrhardCone.prob v 0 = (gaussian d).real (A i) := by
    rw [EhrhardCone.prob_zero]
    exact congrArg ENNReal.toReal (measure_congr hae.symm)
  have he (j : {j : Fin k // j ≠ i}) : 0 < ⟪v j,z i⟫ := by
    dsimp [v]
    rw [inner_sub_left, real_inner_self_eq_norm_sq]
    have hn := hneg j.property
    nlinarith only [hn, sq_nonneg ‖z i‖]
  have hk0 : (0:ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hk1 : (1:ℝ) < k := by exact_mod_cast (show 1 < k by omega)
  have hβ : 0 < ⟪h, ∫ x in EhrhardCone.cone v, x ∂stdGaussian (Space d)⟫ := by
    change 0 < ⟪h, ∫ x in EhrhardCone.cone v, x ∂gaussian d⟫
    rw [hcentroid,hpair]
    exact div_pos (by linarith) hk0
  have hup := EhrhardCone.integral_prob_upper v (z i) he h hβ
  change (∫ u in Ioi (0:ℝ), EhrhardCone.prob v (-u•h)) ≤ _ at hup
  change _ ≤ φ (q (EhrhardCone.prob v 0)) *
    (q (EhrhardCone.prob v 0)*EhrhardCone.prob v 0+φ (q (EhrhardCone.prob v 0))) /
      ⟪h, ∫ x in EhrhardCone.cone v, x ∂gaussian d⟫ at hup
  rw [hp,hcentroid,hpair] at hup
  have hfi : Integrable (fun x => max (⟪z i,x⟫-omittedMax hk z i x) 0) (gaussian d) :=
    ((Integrable.const_inner _ (integrable_id_gaussian d)).sub
      (omittedMax_integrable hk z hz i)).sup (integrable_const 0)
  rw [hfi.integral_eq_integral_meas_le (ae_of_all _ (fun x => le_max_right _ _))]
  have heq : (∫ u in Ioi (0:ℝ), (gaussian d).real {x | u ≤ max (⟪z i,x⟫-omittedMax hk z i x) 0}) =
      ∫ u in Ioi (0:ℝ), EhrhardCone.prob v (-u•h) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro u hu
    change (gaussian d).real {x | u ≤ max (⟪z i,x⟫-omittedMax hk z i x) 0} = _
    rw [gap_event_eq hk z i h hh hu]
    rfl
  change (∫ u in Ioi (0:ℝ), (gaussian d).real {x | u ≤ max (⟪z i,x⟫-omittedMax hk z i x) 0}) ≤ _
  rw [heq]
  convert hup using 1
  simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
  ring

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
open Set GaussianPropeller.Quantile
open scoped RealInnerProductSpace


theorem solution : type_of% @_root_.OAI.GaussianPropeller.Reduction.minimal_loss_upper := @_root_.OAI.GaussianPropeller.Reduction.minimal_loss_upper
