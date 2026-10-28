-- Prove2me | solution 1 for OAI.StandardMapEntropy.actual_cyclic_weakBernoulli_component_q44
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T12:38:46.308147+00:00
-- url     : https://prove2.me/submissions/cc300e60-2a91-4496-9795-59f9611b8dba

import Mathlib
import Definitions.Def_StandardMapComponents
import Definitions.Def_OAIQ44C002
import Theorems.Thm_OAI_StandardMapEntropy_ReversibleGraphRectangle_exists_weakBernoulli_partitions_q44
import Theorems.Thm_OAI_StandardMapEntropy_exists_reversibleRectangleBlock_q44

section
-- module Solutions.OAIQ44_CM.StandardMap_LocalScarcity
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace _root_.OAI.StandardMapEntropy.circleVolumeNullSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

namespace StandardMapEntropy

theorem measurePreserving_standardMap (k : ℝ) : MeasurePreserving (standardMap k) area area := by
  unfold area
  have hkick : MeasurePreserving
      (fun z : Torus => (z.1, z.2 + kick k z.1))
        ((volume : Measure Circle).prod volume) (volume.prod volume) := by
    refine (MeasurePreserving.id (volume : Measure Circle)).skew_product
      (g := fun x y : Circle => y + kick k x) ?_ ?_
    · exact measurable_snd.add ((continuous_kick k).measurable.comp measurable_fst)
    · exact Filter.Eventually.of_forall (fun x => map_add_right_eq_self volume (kick k x))
  convert (measurePreserving_add_prod (volume : Measure Circle) volume).comp hkick using 1
  all_goals try with_reducible_and_instances rfl
  funext z
  simp only [Function.comp_apply, standardMap, kick]
  congr 1
  abel

lemma recurrenceCoordinates_involutive : Function.Involutive recurrenceCoordinates := by
  intro z
  apply Prod.ext <;> simp [recurrenceCoordinates]

lemma standardMap_conjugacy (k : ℝ) (z : Torus) :
    recurrenceCoordinates (standardMap k z) =
      recurrenceMap k (recurrenceCoordinates z) := by
  apply Prod.ext <;> simp only [recurrenceCoordinates, recurrenceMap, standardMap, kick, two_smul]
  · abel
  · abel

open scoped Matrix.Norms.Operator

open Filter
open scoped Topology

open Metric

end StandardMapEntropy
open MeasureTheory Set Filter
open scoped Topology ENNReal
open MeasureTheory Set Filter Metric
open scoped Topology ENNReal

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_PlaneGeometry
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter Metric
open scoped Topology ENNReal
namespace StandardMapEntropy
lemma abs_dot_le_norm_mul (z w : ℂ) : |dot z w| ≤ ‖z‖*‖w‖ := by
  have h := dot_wedge_sq z w
  have h0 := sq_nonneg (wedge z w)
  have hs : (dot z w)^2 ≤ (‖z‖*‖w‖)^2 := by nlinarith
  exact (abs_le_of_sq_le_sq hs (mul_nonneg (norm_nonneg z) (norm_nonneg w)))
lemma abs_wedge_le_norm_mul (z w : ℂ) : |wedge z w| ≤ ‖z‖*‖w‖ := by
  have h := dot_wedge_sq z w
  have hs : (wedge z w)^2 ≤ (‖z‖*‖w‖)^2 := by nlinarith [sq_nonneg (dot z w)]
  exact (abs_le_of_sq_le_sq hs (mul_nonneg (norm_nonneg z) (norm_nonneg w)))
lemma wedge_add_left (z w a : ℂ) : wedge (z+w) a = wedge z a + wedge w a := by
  simp [wedge]; ring
lemma wedge_smul_left (t : ℝ) (z w : ℂ) : wedge (t • z) w = t*wedge z w := by
  simp [wedge]; ring
lemma wedge_add_right (z w a : ℂ) : wedge z (w+a) = wedge z w + wedge z a := by
  simp [wedge]; ring
lemma wedge_smul_right (t : ℝ) (z w : ℂ) : wedge z (t • w) = t*wedge z w := by
  simp [wedge]; ring
lemma wedge_refl (z : ℂ) : wedge z z = 0 := by dsimp [wedge]; ring
lemma wedge_swap (z w : ℂ) : wedge z w = -wedge w z := by dsimp [wedge]; ring
lemma wedge_sine_triangle (a b c : ℂ) (ha : ‖a‖=1) (hb : ‖b‖=1) (hc : ‖c‖=1) :
    |wedge a c| ≤ |wedge a b|+|wedge b c| := by
  have he : wedge a c = dot b a * wedge b c + wedge b a * wedge (quarterTurn b) c := by
    conv_lhs => rw [unit_expansion b a hb]
    rw [wedge_add_left, wedge_smul_left, wedge_smul_left]
  rw [he]
  calc
    _ ≤ |dot b a| * |wedge b c|+|wedge b a| * |wedge (quarterTurn b) c| := by
      simpa only [abs_mul] using abs_add_le (dot b a * wedge b c) (wedge b a * wedge (quarterTurn b) c)
    _ ≤ |wedge b c|+|wedge b a| := by
      have h1 : |dot b a|≤1 := by simpa [ha,hb] using abs_dot_le_norm_mul b a
      have h2 : |wedge (quarterTurn b) c|≤1 := by simpa [norm_quarterTurn,hb,hc] using abs_wedge_le_norm_mul (quarterTurn b) c
      nlinarith [abs_nonneg (wedge b c), abs_nonneg (wedge b a)]
    _ = _ := by rw [wedge_swap b a, abs_neg]; ring
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_PlaneTransfer
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter Metric
open scoped Topology ENNReal
namespace StandardMapEntropy
lemma dot_quarterTurn_right (a z : ℂ) : dot a (quarterTurn z) = -wedge a z := by
  simp [dot,wedge,quarterTurn]; ring
lemma expanded_projection_bound {A : ℂ →L[ℝ] ℂ} (h : PlaneAreaPreserving A)
    (a : ℂ) (ha : ‖a‖=1) (hA : ‖A a‖=‖A‖) (z : ℂ) :
    ‖A‖*|dot a z| ≤ ‖A z‖ := by
  have hs := h.norm_map_sq a ha hA z
  have hnon := mul_nonneg (sq_nonneg (wedge a z)) (sq_nonneg (‖A‖⁻¹))
  have hsq : (‖A‖*|dot a z|)^2≤‖A z‖^2 := by nlinarith [sq_abs (dot a z)]
  exact (sq_le_sq₀ (mul_nonneg (norm_nonneg A) (abs_nonneg _)) (norm_nonneg _)).mp hsq
lemma two_singular_upper {A : ℂ →L[ℝ] ℂ} (h : PlaneAreaPreserving A)
    (a : ℂ) (ha : ‖a‖=1) (hA : ‖A a‖=‖A‖) (z : ℂ) :
    ‖A z‖ ≤ ‖A‖*|dot a z| + ‖A‖⁻¹*|wedge a z| := by
  have hd := orthogonal_image_of_max A a ha hA
  have hs := h.norm_map_sq a ha hA (quarterTurn a)
  rw [dot_quarterTurn,wedge_quarterTurn,ha] at hs
  have hb : ‖A (quarterTurn a)‖=‖A‖⁻¹ := by
    apply (sq_eq_sq₀ (norm_nonneg _) (inv_nonneg.mpr (norm_nonneg _))).mp
    simpa using hs
  conv_lhs => rw [unit_expansion a z ha]
  rw [map_add,map_smul,map_smul]
  calc
    _ ≤ ‖(dot a z : ℝ) • A a‖+‖(wedge a z : ℝ) • A (quarterTurn a)‖ := norm_add_le _ _
    _ = _ := by rw [norm_smul,norm_smul,Real.norm_eq_abs,Real.norm_eq_abs,hA,hb]; ring
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_BridgeLinear
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter Metric
open scoped Topology ENNReal
namespace StandardMapEntropy
lemma wedge_quarterTurn_both (a b : ℂ) : wedge (quarterTurn a) (quarterTurn b)=wedge a b := by
  simp [wedge,quarterTurn]
  ring
lemma wedge_chain_bound (s : ℕ → ℂ) (e : ℕ → ℝ) (a b : ℕ) (hab : a ≤ b)
    (hu : ∀ i, a ≤ i → i ≤ b → ‖s i‖=1)
    (he : ∀ i, a ≤ i → i < b → |wedge (s i) (s (i+1))| ≤ e i) :
    |wedge (s a) (s b)| ≤ ∑ i ∈ Finset.Ico a b, e i := by
  induction b,hab using Nat.le_induction with
  | base => simp [wedge_refl]
  | succ b hab ih =>
    have hh:=ih (fun i hai hib => hu i hai (by omega)) (fun i hai hib => he i hai (by omega))
    have ht:=wedge_sine_triangle (s a) (s b) (s (b+1)) (hu a le_rfl (by omega))
      (hu b hab (by omega)) (hu (b+1) (by omega) le_rfl)
    rw [Finset.sum_Ico_succ_top hab]
    exact ht.trans (add_le_add hh (he b hab (by omega)))

lemma stable_direction_step {A B : ℂ →L[ℝ] ℂ} (hA : PlaneAreaPreserving A)
    (a b : ℂ) (ha : ‖a‖=1) (_hb : ‖b‖=1)
    (hAa : ‖A a‖=‖A‖) (hBb : ‖B (quarterTurn b)‖=‖B‖⁻¹)
    (M : ℝ) (hB : 0 < ‖B‖) (hstep : ∀ z, ‖A z‖ ≤ M*‖B z‖) :
    |wedge (quarterTurn a) (quarterTurn b)| ≤ M/(‖A‖*‖B‖) := by
  have hpos : 0 < ‖A‖ := lt_of_lt_of_le zero_lt_one hA.singular_pair.choose_spec.2.2.2.2
  have hp:=expanded_projection_bound hA a ha hAa (quarterTurn b)
  rw [dot_quarterTurn_right] at hp
  have hs:=hstep (quarterTurn b)
  rw [hBb] at hs
  rw [wedge_quarterTurn_both]
  apply (le_div_iff₀ (mul_pos hpos hB)).mpr
  rw [abs_neg] at hp
  have hh := mul_le_mul_of_nonneg_right (hp.trans hs) hB.le
  calc
    _ = (‖A‖*|wedge a b|)*‖B‖ := by ring
    _  ≤  (M*‖B‖⁻¹)*‖B‖ := hh
    _ = M := by field_simp

lemma stable_prefix_finite_bound (A : ℕ → ℂ →L[ℝ] ℂ) (a : ℕ → ℂ)
    (D : ℕ → ℝ) (M : ℝ) (l B : ℕ) (hl : 1 ≤ l) (hlB : l ≤ B)
    (harea : ∀ i, 1 ≤ i → i ≤ B → PlaneAreaPreserving (A i))
    (hunit : ∀ i, 1 ≤ i → i ≤ B → ‖a i‖=1)
    (hnorm : ∀ i, 1 ≤ i → i ≤ B → ‖A i‖=D i)
    (hmax : ∀ i, 1 ≤ i → i ≤ B → ‖A i (a i)‖=D i)
    (hstable : ∀ i, 1 ≤ i → i ≤ B → ‖A i (quarterTurn (a i))‖=(D i)⁻¹)
    (hstep : ∀ i, 1 ≤ i → i < B → ∀ z, ‖A i z‖ ≤ M*‖A (i+1) z‖) :
    ‖A l (quarterTurn (a B))‖ ≤ (D l)⁻¹+D l*∑ i ∈ Finset.Ico l B, M/(D i*D (i+1)) := by
  have hpos (i : ℕ) (hi : 1 ≤ i) (hiB : i ≤ B) : 0 < ‖A i‖ :=
    lt_of_lt_of_le zero_lt_one (harea i hi hiB).singular_pair.choose_spec.2.2.2.2
  have hchain:=wedge_chain_bound (fun i => quarterTurn (a i))
    (fun i => M/(D i*D (i+1))) l B hlB
    (fun i hli hiB => by rw [norm_quarterTurn]; exact hunit i (by omega) hiB)
    (by
      intro i hli hiB
      have hh:=stable_direction_step (harea i (by omega) (by omega)) (a i) (a (i+1))
        (hunit i (by omega) (by omega)) (hunit (i+1) (by omega) (by omega))
        (by rw [hmax i (by omega) (by omega),hnorm i (by omega) (by omega)])
        (by rw [hstable (i+1) (by omega) (by omega),hnorm (i+1) (by omega) (by omega)])
        M (hpos (i+1) (by omega) (by omega)) (hstep i (by omega) hiB)
      simpa only [hnorm i (by omega) (by omega),hnorm (i+1) (by omega) (by omega)] using hh)
  rw [wedge_quarterTurn_both] at hchain
  have hup:=two_singular_upper (harea l hl hlB) (a l) (hunit l hl hlB)
    (by rw [hmax l hl hlB,hnorm l hl hlB]) (quarterTurn (a B))
  rw [dot_quarterTurn_right,abs_neg,hnorm l hl hlB] at hup
  have hw:=abs_wedge_le_norm_mul (a l) (quarterTurn (a B))
  rw [norm_quarterTurn,hunit l hl hlB,hunit B (by omega) le_rfl,mul_one] at hw
  have hD : 0 ≤ D l := by rw [← hnorm l hl hlB]; exact norm_nonneg _
  calc
    _  ≤  D l*|wedge (a l) (a B)|+(D l)⁻¹*|wedge (a l) (quarterTurn (a B))| := hup
    _  ≤  D l*(∑ i ∈ Finset.Ico l B, M/(D i*D (i+1)))+(D l)⁻¹*1 :=
      add_le_add (mul_le_mul_of_nonneg_left hchain hD) (mul_le_mul_of_nonneg_left hw (inv_nonneg.mpr hD))
    _ = _ := by ring
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_TorusDynamics
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace _root_.OAI.StandardMapEntropy.circleVolumeNullSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter Metric
open scoped ENNReal Topology
namespace StandardMapEntropy
lemma measurePreserving_recurrenceCoordinates : MeasurePreserving recurrenceCoordinates area area := by
  unfold area
  apply (MeasurePreserving.id (volume : Measure Circle)).skew_product
  · exact measurable_fst.sub measurable_snd
  · exact Eventually.of_forall fun x => (Measure.measurePreserving_sub_left (volume : Measure Circle) x).map_eq
lemma measurePreserving_torusStep (k : ℝ) : MeasurePreserving (torusStep k) area area := by
  have hh := measurePreserving_recurrenceCoordinates.comp
    ((measurePreserving_standardMap k).comp measurePreserving_recurrenceCoordinates)
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  funext z
  simp only [Function.comp_apply,standardMap_conjugacy,torusStep_apply]
  rw [recurrenceCoordinates_involutive z]
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_CancellationVector
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace _root_.OAI.StandardMapEntropy.circleVolumeNullSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter Metric
open scoped ENNReal Topology
namespace StandardMapEntropy
lemma torusPotential_bound (k : ℝ) (hk : 0 ≤ k) (x : Circle) : |torusPotential k x|+1 ≤ growthBase k := by
  obtain ⟨t,rfl⟩ := Quotient.mk_surjective x
  exact potential_bound k t hk
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_Lyapunov_Definitions
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace StandardMapEntropy
open MeasureTheory Set Filter
open scoped Topology ENNReal

lemma standardDerivativeProduct_zero (k : ℝ) (z : Torus) :
    standardDerivativeProduct k z 0 = ContinuousLinearMap.id ℝ ℂ := rfl

attribute [local instance] OAI.StandardMapEntropy.realTangentCompTriple
lemma standardDerivativeProduct_succ (k : ℝ) (z : Torus) (n : ℕ) :
    standardDerivativeProduct k z (n + 1) =
      (standardDerivative k ((standardMap k)^[n] z)).comp
        (standardDerivativeProduct k z n) := rfl

end StandardMapEntropy
end
end

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_Lyapunov_Subadditive
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators

namespace BoundedSubadditive

variable {X : Type*}

lemma excess_nonneg (T : X → X) (h : X → ℝ) (δ : ℝ) (n : ℕ) (x : X) :
    0 ≤ excess T h δ n x := by
  cases n with
  | zero => rfl
  | succ n => exact le_max_left _ _

lemma excess_succ_mono (T : X → X) (h : X → ℝ) (δ : ℝ) (n : ℕ) (x : X) :
    excess T h δ n x ≤ excess T h δ (n + 1) x := by
  induction n generalizing x with
  | zero => exact excess_nonneg T h δ 1 x
  | succ n ih =>
    exact max_le_max le_rfl (add_le_add le_rfl (ih (T x)))

lemma excess_mono (T : X → X) (h : X → ℝ) (δ : ℝ) (x : X) :
    Monotone (fun n => excess T h δ n x) :=
  monotone_nat_of_le_succ (fun n => excess_succ_mono T h δ n x)

lemma sum_sub_le_excess (T : X → X) (h : X → ℝ) (δ : ℝ) (n : ℕ) (x : X) :
    birkhoffSum T h n x - (n : ℝ) * δ ≤ excess T h δ n x := by
  induction n generalizing x with
  | zero => simp [birkhoffSum, excess]
  | succ n ih =>
    rw [birkhoffSum_succ']
    have hm : h x - δ + excess T h δ n (T x) ≤ excess T h δ (n + 1) x :=
      le_max_right _ _
    have hi := ih (T x)
    push_cast
    linarith

lemma excess_account (T : X → X) (h : X → ℝ) (δ : ℝ)
    (hh : ∀ x, 0 ≤ h x) (n : ℕ) (x : X) :
    (if 0 < excess T h δ (n + 1) x then δ else 0) ≤
      h x + excess T h δ (n + 1) (T x) - excess T h δ (n + 1) x := by
  split_ifs with hp
  · have he : excess T h δ (n + 1) x = h x - δ + excess T h δ n (T x) := by
      apply max_eq_right
      change 0 < max 0 (h x - δ + excess T h δ n (T x)) at hp
      exact (lt_max_iff.mp hp).resolve_left (lt_irrefl 0) |>.le
    rw [he]
    linarith [excess_succ_mono T h δ n (T x)]
  · have he : excess T h δ (n + 1) x = 0 :=
      le_antisymm (not_lt.mp hp) (excess_nonneg T h δ _ x)
    rw [he]
    linarith [hh x, excess_nonneg T h δ (n + 1) (T x)]

section Measure
variable [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]
variable {T : X → X} {h : X → ℝ} {δ : ℝ}

lemma measurable_excess (hT : Measurable T) (hh : Measurable h) (n : ℕ) :
    Measurable (excess T h δ n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih => exact measurable_const.max ((hh.sub measurable_const).add (ih.comp hT))

lemma integrable_excess (hT : MeasurePreserving T μ μ) (hh : Integrable h μ) (n : ℕ) :
    Integrable (excess T h δ n) μ := by
  induction n with
  | zero => exact integrable_const 0
  | succ n ih =>
    exact (integrable_const (0 : ℝ)).sup
      ((hh.sub (integrable_const δ)).add (hT.integrable_comp_of_integrable ih))

omit [IsFiniteMeasure μ] in
lemma integral_comp (hT : MeasurePreserving T μ μ) {g : X → ℝ}
    (hg : AEStronglyMeasurable g μ) : (∫ x, g (T x) ∂μ) = ∫ x, g x ∂μ := by
  have hg' : AEStronglyMeasurable g (Measure.map T μ) := by rwa [hT.map_eq]
  simpa only [hT.map_eq] using (integral_map hT.measurable.aemeasurable hg').symm

lemma excess_measure_bound (hT : MeasurePreserving T μ μ) (hm : Measurable h)
    (hi : Integrable h μ) (h0 : ∀ x, 0 ≤ h x) (hδ : 0 < δ) (n : ℕ) :
    μ {x | 0 < excess T h δ n x} ≤ ENNReal.ofReal ((∫ x, h x ∂μ) / δ) := by
  cases n with
  | zero => simp [excess]
  | succ n =>
    let s : Set X := {x | 0 < excess T h δ (n + 1) x}
    have hs : MeasurableSet s := measurableSet_lt measurable_const
      (measurable_excess hT.measurable hm _)
    have he := integrable_excess (δ := δ) hT hi (n + 1)
    have heT : Integrable (fun x => excess T h δ (n + 1) (T x)) μ :=
      hT.integrable_comp_of_integrable he
    have hb : (∫ x, s.indicator (fun _ => δ) x ∂μ) ≤
        ∫ x, h x + excess T h δ (n + 1) (T x) - excess T h δ (n + 1) x ∂μ := by
      apply integral_mono ((integrable_const δ).indicator hs)
        ((hi.add heT).sub he)
      intro x
      simpa only [Set.indicator, s, Set.mem_ofPred_eq, Pi.sub_apply, Pi.add_apply, Function.comp_apply] using excess_account T h δ h0 n x
    have hsub := integral_sub (hi.add heT) he
    have hadd := integral_add hi heT
    simp only [Pi.add_apply] at hsub hadd
    rw [integral_indicator_const δ hs, hsub, hadd,
      integral_comp hT he.aestronglyMeasurable] at hb
    have hb' : μ.real s ≤ (∫ x, h x ∂μ) / δ := by
      apply (le_div_iff₀ hδ).mpr
      simpa only [smul_eq_mul, add_sub_cancel_right] using hb
    calc
      μ s = ENNReal.ofReal (μ.real s) := (ENNReal.ofReal_toReal (measure_ne_top μ s)).symm
      _ ≤ _ := ENNReal.ofReal_le_ofReal hb'

lemma maximal_measure_bound (hT : MeasurePreserving T μ μ) (hm : Measurable h)
    (hi : Integrable h μ) (h0 : ∀ x, 0 ≤ h x) (hδ : 0 < δ) :
    μ {x | ∃ n : ℕ, (n : ℝ) * δ < birkhoffSum T h n x} ≤
      ENNReal.ofReal ((∫ x, h x ∂μ) / δ) := by
  have hsub : {x | ∃ n : ℕ, (n : ℝ) * δ < birkhoffSum T h n x} ⊆
      ⋃ n : ℕ, {x | 0 < excess T h δ n x} := by
    rintro x ⟨n, hn⟩
    apply mem_iUnion.mpr
    refine ⟨n, ?_⟩
    exact lt_of_lt_of_le (sub_pos.mpr hn) (sum_sub_le_excess T h δ n x)
  refine (measure_mono hsub).trans ?_
  have hm' : Monotone (fun n : ℕ => {x | 0 < excess T h δ n x}) := by
    intro m n hmn x hx
    exact lt_of_lt_of_le hx (excess_mono T h δ x hmn)
  rw [hm'.measure_iUnion]
  exact iSup_le (fun n => excess_measure_bound hT hm hi h0 hδ n)

end Measure

namespace Cocycle
variable [MeasurableSpace X] {T : X → X} (f : Cocycle X T)

lemma average_bounds (n : ℕ) (x : X) : 0 ≤ f.average n x ∧ f.average n x ≤ 1 := by
  refine ⟨div_nonneg (f.nonneg n x) (Nat.cast_nonneg n), ?_⟩
  by_cases hn : n = 0
  · simp [average, hn]
  · exact (div_le_one (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn))).mpr (f.le_time n x)

lemma average_bdd_above (x : X) : IsBoundedUnder (· ≤ ·) atTop (fun n => f.average n x) :=
  isBoundedUnder_of ⟨1, fun n => (f.average_bounds n x).2⟩

lemma average_bdd_below (x : X) : IsBoundedUnder (· ≥ ·) atTop (fun n => f.average n x) :=
  isBoundedUnder_of ⟨0, fun n => (f.average_bounds n x).1⟩

lemma lowerRate_bounds (x : X) : 0 ≤ f.lowerRate x ∧ f.lowerRate x ≤ 1 := by
  constructor
  · exact le_liminf_of_le (f.average_bdd_above x).isCoboundedUnder_ge
      (Eventually.of_forall fun n => (f.average_bounds n x).1)
  · have hh := liminf_le_liminf (Eventually.of_forall fun n => (f.average_bounds n x).2)
      (f.average_bdd_below x) (isBoundedUnder_const.isCoboundedUnder_ge)
    simpa only [liminf_const, lowerRate] using hh

lemma measurable_average (n : ℕ) : Measurable (f.average n) :=
  (f.measurable n).div_const _

lemma measurable_lowerRate : Measurable f.lowerRate :=
  Measurable.liminf (fun n => f.measurable_average n)

lemma average_shift_bound (n : ℕ) (x : X) :
    |f.average n (T x) - f.average n x| ≤ 2 / (n : ℝ) := by
  rw [average, average, ← sub_div, abs_div, abs_of_nonneg (show (0 : ℝ) ≤ n from Nat.cast_nonneg n)]
  exact div_le_div_of_nonneg_right (f.shift_bound n x) (Nat.cast_nonneg n)

lemma lowerRate_shift (x : X) : f.lowerRate (T x) = f.lowerRate x := by
  have hc : Tendsto (fun n : ℕ => (2 : ℝ) / n) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have haux (a b : X) (hab : ∀ n, f.average n a - f.average n b ≤ 2 / (n : ℝ)) :
      f.lowerRate a ≤ f.lowerRate b := by
    apply le_of_forall_pos_le_add
    intro ε hε
    have he : ∀ᶠ n : ℕ in atTop, f.average n a ≤ f.average n b + ε := by
      filter_upwards [hc.eventually (gt_mem_nhds hε)] with n hn
      linarith [hab n]
    have hb : IsBoundedUnder (· ≤ ·) atTop (fun n => f.average n b + ε) :=
      isBoundedUnder_of ⟨1 + ε, fun n => add_le_add (f.average_bounds n b).2 le_rfl⟩
    have hh := liminf_le_liminf he (f.average_bdd_below a) hb.isCoboundedUnder_ge
    rw [liminf_add_const atTop (fun n => f.average n b) ε
      (f.average_bdd_above b).isCoboundedUnder_ge (f.average_bdd_below b)] at hh
    exact hh
  apply le_antisymm
  · exact haux (T x) x (fun n => (abs_le.mp (f.average_shift_bound n x)).2)
  · apply haux x (T x)
    intro n
    have hh := (abs_le.mp (f.average_shift_bound n x)).1
    linarith

lemma lowerRate_iterate (n : ℕ) (x : X) : f.lowerRate (T^[n] x) = f.lowerRate x := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', f.lowerRate_shift, ih]

lemma measurableSet_badSet (ε : ℝ) (N : ℕ) : MeasurableSet (f.badSet ε N) := by
  apply MeasurableSet.compl
  apply MeasurableSet.biUnion (Set.to_countable _)
  intro n hn
  exact measurableSet_le (f.measurable n)
    (measurable_const.mul (f.measurable_lowerRate.add_const ε))

lemma measurable_badObservation (ε : ℝ) (N : ℕ) : Measurable (f.badObservation ε N) :=
  measurable_const.indicator (f.measurableSet_badSet ε N)

lemma badObservation_bounds (ε : ℝ) (N : ℕ) (x : X) :
    0 ≤ f.badObservation ε N x ∧ f.badObservation ε N x ≤ 1 := by
  classical
  by_cases hx : x ∈ f.badSet ε N <;> simp [badObservation, hx]

lemma exists_good_block (x : X) (ε : ℝ) (hε : 0 < ε) :
    ∃ n : ℕ, 0 < n ∧ f.value n x ≤ (n : ℝ) * (f.lowerRate x + ε) := by
  have hh : ∃ᶠ n : ℕ in atTop, f.average n x < f.lowerRate x + ε :=
    frequently_lt_of_liminf_lt (f.average_bdd_above x).isCoboundedUnder_ge (lt_add_of_pos_right _ hε)
  obtain ⟨n, hn, he⟩ := frequently_atTop.mp hh 1
  have hn' : 0 < n := by omega
  refine ⟨n, hn', ?_⟩
  have hi := (div_lt_iff₀ (Nat.cast_pos.mpr hn')).mp he
  nlinarith

lemma badObservation_tendsto_zero (x : X) (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun N => f.badObservation ε N x) atTop (𝓝 0) := by
  obtain ⟨n, hn, hg⟩ := f.exists_good_block x ε hε
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop n] with N hN
  symm
  apply Set.indicator_of_notMem
  simp only [badSet, mem_compl_iff, mem_iUnion, mem_ofPred_eq, not_not]
  exact ⟨n, ⟨hn, hN⟩, hg⟩

lemma birkhoff_bad_nonneg (ε : ℝ) (N n : ℕ) (x : X) :
    0 ≤ birkhoffSum T (f.badObservation ε N) n x := by
  exact Finset.sum_nonneg fun i hi => (f.badObservation_bounds ε N (T^[i] x)).1

lemma block_bound (ε : ℝ) (hε : 0 ≤ ε) (N n : ℕ) (x : X) :
    f.value n x ≤ (n : ℝ) * (f.lowerRate x + ε) +
      birkhoffSum T (f.badObservation ε N) n x + (N : ℝ) := by
  classical
  induction n using Nat.strong_induction_on generalizing x with
  | h n ih =>
    have ha : 0 ≤ f.lowerRate x + ε := add_nonneg (f.lowerRate_bounds x).1 hε
    by_cases hn : n ≤ N
    · have hcast : (n : ℝ) ≤ N := by exact_mod_cast hn
      have hp := mul_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ n) ha
      linarith [f.le_time n x, f.birkhoff_bad_nonneg ε N n x]
    · by_cases hx : x ∈ f.badSet ε N
      · have hn0 : 1 ≤ n := by omega
        have he : 1 + (n - 1) = n := by omega
        have hs := f.subadd 1 (n - 1) x
        simp only [he, Function.iterate_one] at hs
        have hi := ih (n - 1) (by omega) (T x)
        rw [f.lowerRate_shift] at hi
        rw [Nat.cast_sub hn0, Nat.cast_one, sub_mul, one_mul] at hi
        have hb : f.badObservation ε N x = 1 := by simp [badObservation, hx]
        have hsum : birkhoffSum T (f.badObservation ε N) n x =
            1 + birkhoffSum T (f.badObservation ε N) (n - 1) (T x) := by
          conv_lhs => rw [show n = (n - 1) + 1 by omega]
          rw [birkhoffSum_succ', hb]
        rw [hsum]
        have h1 := f.le_time 1 x
        norm_num only [Nat.cast_one] at h1
        linarith
      · have hg : x ∈ ⋃ m ∈ Set.Ioc 0 N,
            {y | f.value m y ≤ (m : ℝ) * (f.lowerRate y + ε)} := not_not.mp hx
        obtain ⟨m, hgm⟩ := mem_iUnion.mp hg
        obtain ⟨hm, hfm⟩ := mem_iUnion.mp hgm
        have hmn : m ≤ n := by have := hm.2; omega
        have he : m + (n - m) = n := Nat.add_sub_of_le hmn
        have hs := f.subadd m (n - m) x
        rw [he] at hs
        have hi := ih (n - m) (by have := hm.1; omega) (T^[m] x)
        rw [f.lowerRate_iterate, Nat.cast_sub hmn, sub_mul] at hi
        have hsum : birkhoffSum T (f.badObservation ε N) n x =
            birkhoffSum T (f.badObservation ε N) m x +
              birkhoffSum T (f.badObservation ε N) (n - m) (T^[m] x) := by
          simpa only [he] using birkhoffSum_add T (f.badObservation ε N) m (n - m) x
        rw [hsum]
        have hp := f.birkhoff_bad_nonneg ε N m x
        change f.value m x ≤ (m : ℝ) * (f.lowerRate x + ε) at hfm
        linarith

lemma upperRate_le_of_bad_averages (ε : ℝ) (hε : 0 ≤ ε) (N : ℕ) (δ : ℝ) (x : X)
    (hb : ∀ n, birkhoffSum T (f.badObservation ε N) n x ≤ (n : ℝ) * δ) :
    f.upperRate x ≤ f.lowerRate x + ε + δ := by
  apply le_of_forall_pos_le_add
  intro γ hγ
  have hc : Tendsto (fun n : ℕ => (N : ℝ) / n) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  apply limsup_le_of_le (f.average_bdd_below x).isCoboundedUnder_le
  filter_upwards [hc.eventually (gt_mem_nhds hγ), eventually_gt_atTop 0] with n hsmall hn
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hN := (div_lt_iff₀ hn').mp hsmall
  apply (div_le_iff₀ hn').mpr
  have hB := f.block_bound ε hε N n x
  have hbad := hb n
  nlinarith

section Measure
variable {μ : Measure X} [IsFiniteMeasure μ]

lemma integrable_badObservation (ε : ℝ) (N : ℕ) :
    Integrable (f.badObservation ε N) μ :=
  (integrable_const (1 : ℝ)).indicator (f.measurableSet_badSet ε N)

lemma integral_badObservation_tendsto_zero (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun N => ∫ x, f.badObservation ε N x ∂μ) atTop (𝓝 0) := by
  have hh := tendsto_integral_of_dominated_convergence (μ := μ) (fun _ : X => (1 : ℝ))
    (fun N => (f.measurable_badObservation ε N).aestronglyMeasurable)
    (integrable_const 1)
    (fun N => Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (f.badObservation_bounds ε N x).1]
      exact (f.badObservation_bounds ε N x).2)
    (Eventually.of_forall fun x => f.badObservation_tendsto_zero x ε hε)
  simpa only [integral_zero] using hh

lemma ae_upperRate_le_add (hT : MeasurePreserving T μ μ) (ε : ℝ) (hε : 0 < ε) :
    ∀ᵐ x ∂μ, f.upperRate x ≤ f.lowerRate x + 2 * ε := by
  let E : Set X := {x | f.lowerRate x + 2 * ε < f.upperRate x}
  have hbound (N : ℕ) : μ E ≤
      ENNReal.ofReal ((∫ x, f.badObservation ε N x ∂μ) / ε) := by
    have hsub : E ⊆ {x | ∃ n : ℕ, (n : ℝ) * ε < birkhoffSum T (f.badObservation ε N) n x} := by
      intro x hx
      by_contra hn
      change ¬ ∃ n : ℕ, (n : ℝ) * ε < birkhoffSum T (f.badObservation ε N) n x at hn
      push Not at hn
      have hh := f.upperRate_le_of_bad_averages ε hε.le N ε x hn
      change f.lowerRate x + 2 * ε < f.upperRate x at hx
      linarith
    exact (measure_mono hsub).trans
      (maximal_measure_bound hT (f.measurable_badObservation ε N)
        (f.integrable_badObservation ε N) (fun x => (f.badObservation_bounds ε N x).1) hε)
  have hc : Tendsto (fun N => ENNReal.ofReal ((∫ x, f.badObservation ε N x ∂μ) / ε))
      atTop (𝓝 0) := by
    have hh := (f.integral_badObservation_tendsto_zero (μ := μ) ε hε).div_const ε
    simpa only [Function.comp_def, zero_div, ENNReal.ofReal_zero] using
      ENNReal.continuous_ofReal.continuousAt.tendsto.comp hh
  have hzero : μ E = 0 := le_antisymm (ge_of_tendsto' hc hbound) zero_le
  simpa only [ae_iff, not_le] using hzero

theorem ae_tendsto_average (hT : MeasurePreserving T μ μ) :
    ∀ᵐ x ∂μ, Tendsto (fun n => f.average n x) atTop (𝓝 (f.lowerRate x)) := by
  have ha : ∀ᵐ x ∂μ, ∀ j : ℕ, f.upperRate x ≤ f.lowerRate x + 2 * (1 / ((j : ℝ) + 1)) := by
    apply ae_all_iff.mpr
    intro j
    exact f.ae_upperRate_le_add hT _ (by positivity)
  filter_upwards [ha] with x hx
  have hc : Tendsto (fun j : ℕ => f.lowerRate x + 2 * (1 / ((j : ℝ) + 1)))
      atTop (𝓝 (f.lowerRate x)) := by
    simpa using tendsto_const_nhds.add
      (tendsto_const_nhds.mul (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)))
  have hu : f.upperRate x ≤ f.lowerRate x := ge_of_tendsto' hc hx
  exact tendsto_of_le_liminf_of_limsup_le le_rfl hu
    (f.average_bdd_above x) (f.average_bdd_below x)

lemma integrable_lowerRate : Integrable f.lowerRate μ :=
  (integrable_const (1 : ℝ)).mono' f.measurable_lowerRate.aestronglyMeasurable
    (Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (f.lowerRate_bounds x).1]
      exact (f.lowerRate_bounds x).2)

theorem tendsto_integral_average (hT : MeasurePreserving T μ μ) :
    Tendsto (fun n => ∫ x, f.average n x ∂μ) atTop (𝓝 (∫ x, f.lowerRate x ∂μ)) := by
  exact tendsto_integral_of_dominated_convergence (fun _ : X => (1 : ℝ))
    (fun n => (f.measurable_average n).aestronglyMeasurable) (integrable_const 1)
    (fun n => Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (f.average_bounds n x).1]
      exact (f.average_bounds n x).2)
    (f.ae_tendsto_average hT)

end Measure
end Cocycle
end BoundedSubadditive

namespace StandardMapEntropy
open BoundedSubadditive

lemma lognorm_average_eq (k : ℝ) (hk : 0 ≤ k) (n : ℕ) (z : Torus) :
    Real.log ‖torusSegmentTransfer k z 0 n‖ / (n : ℝ) =
      Real.log (growthBase k) * (transferCocycle k hk).average n z := by
  change _ = Real.log (growthBase k) * (productDistance k z 0 (n : ℤ) / (n : ℝ))
  have hf : productDistance k z 0 (n : ℤ) =
      Real.log ‖torusSegmentTransfer k z 0 n‖ / Real.log (growthBase k) := by
    simpa only [zero_add] using productDistance_forward k z 0 n
  rw [hf]
  have hlog := (log_growthBase_pos k hk).ne'
  calc
    _ = (Real.log (growthBase k) * (Real.log ‖torusSegmentTransfer k z 0 n‖ /
        Real.log (growthBase k))) / (n : ℝ) := by rw [mul_div_cancel₀ _ hlog]
    _ = _ := by ring

lemma transferLyapunov_limit (k : ℝ) (hk : 0 ≤ k) :
    TransferLimit k (transferLyapunov k hk) := by
  let f := transferCocycle k hk
  refine ⟨measurable_const.mul f.measurable_lowerRate,
    f.integrable_lowerRate.const_mul _, ?_, ?_, ?_⟩
  · intro z
    exact mul_nonneg (log_growthBase_pos k hk).le (f.lowerRate_bounds z).1
  · intro z
    exact congrArg (fun a => Real.log (growthBase k) * a) (f.lowerRate_shift z)
  · filter_upwards [f.ae_tendsto_average (measurePreserving_torusStep k)] with z hz
    have hh : Tendsto (fun n => Real.log (growthBase k) * f.average n z) atTop
        (𝓝 (Real.log (growthBase k) * f.lowerRate z)) := tendsto_const_nhds.mul hz
    simpa only [transferLyapunov, f, ← lognorm_average_eq] using hh

end StandardMapEntropy

end
end

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_Lyapunov_DerivativeGrowth
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace StandardMapEntropy
open MeasureTheory Set Filter
open scoped Topology ENNReal ContDiff

lemma tangentCoordinates_norm_le : ‖tangentCoordinates‖ ≤ 3 := by
  apply tangentCoordinates.opNorm_le_bound (by norm_num)
  intro z
  have hr := Complex.abs_re_le_norm z
  have hi := Complex.abs_im_le_norm z
  calc
    ‖tangentCoordinates z‖ ≤ |z.re| + |z.re-z.im| := by
      simpa only [tangentCoordinates_re, tangentCoordinates_im]
        using Complex.norm_le_abs_re_add_abs_im (tangentCoordinates z)
    _ ≤ |z.re| + (|z.re|+|z.im|) := add_le_add le_rfl (abs_sub _ _)
    _ ≤ 3*‖z‖ := by linarith

lemma standardDerivativeProduct_norm_ge_one (k : ℝ) (z : Torus) (n : ℕ) :
    1 ≤ ‖standardDerivativeProduct k z n‖ :=
  (standardDerivativeProduct_area k z n).singular_pair.choose_spec.2.2.2.2

lemma complexProjection_standardInverseLift (k : ℝ) (z : ℂ) :
    complexProjection (standardInverseLift k z) = inverseMap k (complexProjection z) := by
  ext <;> simp [complexProjection, standardInverseLift, inverseMap, kick,
    ← QuotientAddGroup.mk_sub]

lemma continuous_standardDerivative (k : ℝ) : Continuous (standardDerivative k) :=
  continuous_const.clm_comp
    ((continuous_transferStep.comp ((continuous_torusPotential k).comp continuous_fst)).clm_comp
      continuous_const)

lemma recurrenceCoordinates_iterate (k : ℝ) (n : ℕ) (z : Torus) :
    recurrenceCoordinates ((standardMap k)^[n] z) =
      (torusStep k)^[n] (recurrenceCoordinates z) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', standardMap_conjugacy, ih]
    rfl

lemma standardDerivativeProduct_conjugate (k : ℝ) (z : Torus) (n : ℕ) :
    standardDerivativeProduct k z n = tangentCoordinates.comp
      ((torusSegmentTransfer k (recurrenceCoordinates z) 0 n).comp tangentCoordinates) := by
  induction n with
  | zero =>
    apply ContinuousLinearMap.ext
    intro w
    simpa only [standardDerivativeProduct_zero, torusSegmentTransfer, transferProduct,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] using
      (tangentCoordinates_involutive w).symm
  | succ n ih =>
    have hcoeff : torusSegmentCoefficient k (recurrenceCoordinates z) 0 (n+1) =
        torusPotential k ((standardMap k)^[n] z).1 := by
      unfold torusSegmentCoefficient
      simp only [Nat.cast_add, Nat.cast_one, zero_add, add_sub_cancel_right]
      rw [torusIter_nat_apply, ← recurrenceCoordinates_iterate]
      rfl
    apply ContinuousLinearMap.ext
    intro w
    simp only [standardDerivativeProduct_succ, ih, standardDerivative, torusSegmentTransfer,
      transferProduct, ContinuousLinearMap.comp_apply, tangentCoordinates_involutive, hcoeff]

lemma conjugate_norm_le (A : ℂ →L[ℝ] ℂ) :
    ‖tangentCoordinates.comp (A.comp tangentCoordinates)‖ ≤ 9*‖A‖ := by
  calc
    _ ≤ ‖tangentCoordinates‖ * (‖A‖ * ‖tangentCoordinates‖) :=
      (ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))
    _ ≤ 3 * (‖A‖ * 3) := by gcongr <;> exact tangentCoordinates_norm_le
    _ = _ := by ring

lemma conjugate_norm_lower (A : ℂ →L[ℝ] ℂ) :
    ‖A‖ ≤ 9*‖tangentCoordinates.comp (A.comp tangentCoordinates)‖ := by
  convert conjugate_norm_le (tangentCoordinates.comp (A.comp tangentCoordinates)) using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  apply ContinuousLinearMap.ext
  intro z
  simp only [ContinuousLinearMap.comp_apply, tangentCoordinates_involutive]

lemma derivative_log_difference_bound (k : ℝ) (hk : 0 ≤ k) (z : Torus) (n : ℕ) :
    |Real.log ‖standardDerivativeProduct k z n‖-
      Real.log ‖torusSegmentTransfer k (recurrenceCoordinates z) 0 n‖| ≤ Real.log 9 := by
  have hA : 0 < ‖torusSegmentTransfer k (recurrenceCoordinates z) 0 n‖ :=
    lt_of_lt_of_le zero_lt_one (torusSegmentTransfer_norm_bounds k hk _ _ _).1
  have hB : 0 < ‖standardDerivativeProduct k z n‖ :=
    lt_of_lt_of_le zero_lt_one (standardDerivativeProduct_norm_ge_one k z n)
  have h₁ := conjugate_norm_le (torusSegmentTransfer k (recurrenceCoordinates z) 0 n)
  have h₂ := conjugate_norm_lower (torusSegmentTransfer k (recurrenceCoordinates z) 0 n)
  rw [← standardDerivativeProduct_conjugate] at h₁ h₂
  have hlog₁ := Real.log_le_log hB h₁
  have hlog₂ := Real.log_le_log hA h₂
  rw [Real.log_mul (by norm_num) hA.ne'] at hlog₁
  rw [Real.log_mul (by norm_num) hB.ne'] at hlog₂
  exact abs_le.mpr ⟨by linarith, by linarith⟩

end StandardMapEntropy

namespace StandardMapEntropy
open MeasureTheory Set Filter
open scoped Topology ENNReal ContDiff

lemma contDiff_standardLift (k : ℝ) : ContDiff ℝ ∞ (standardLift k) := by
  have hr : ContDiff ℝ ∞ (fun z : ℂ => z.re) := Complex.reCLM.contDiff
  have hi : ContDiff ℝ ∞ (fun z : ℂ => z.im) := Complex.imCLM.contDiff
  have hs : ContDiff ℝ ∞ (fun z : ℂ => k*Real.sin (2*Real.pi*z.re)) :=
    contDiff_const.mul (contDiff_const.mul hr).sin
  exact Complex.equivRealProdCLM.symm.toContinuousLinearMap.contDiff.comp
    (((hr.add hi).add hs).prodMk (hi.add hs))

lemma complexProjection_iterate (k : ℝ) (n : ℕ) (z : ℂ) :
    complexProjection ((standardLift k)^[n] z) = (standardMap k)^[n] (complexProjection z) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', complexProjection_standardLift, ih]

lemma hasFDerivAt_standardLift_iterate (k : ℝ) (n : ℕ) (z : ℂ) :
    HasFDerivAt ((standardLift k)^[n])
      (standardDerivativeProduct k (complexProjection z) n) z := by
  induction n with
  | zero => exact hasFDerivAt_id z
  | succ n ih =>
    have hh := (hasFDerivAt_standardLift k ((standardLift k)^[n] z)).comp z ih
    simpa only [complexProjection_iterate, ← Function.iterate_succ', standardDerivativeProduct] using hh

lemma derivative_rate_of_transfer_rate (k : ℝ) (hk : 0 ≤ k) (z : Torus) (l : ℝ)
    (hl : Tendsto
      (fun n : ℕ => Real.log ‖torusSegmentTransfer k (recurrenceCoordinates z) 0 n‖ / (n : ℝ))
      atTop (𝓝 l)) :
    Tendsto (fun n : ℕ => Real.log ‖standardDerivativeProduct k z n‖ / (n : ℝ))
      atTop (𝓝 l) := by
  have hd : Tendsto (fun n : ℕ =>
      (Real.log ‖standardDerivativeProduct k z n‖ -
        Real.log ‖torusSegmentTransfer k (recurrenceCoordinates z) 0 n‖) / (n : ℝ))
      atTop (𝓝 0) := by
    apply squeeze_zero_norm (fun n => ?_)
      (tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop :
        Tendsto (fun n : ℕ => Real.log 9 / (n : ℝ)) atTop (𝓝 0))
    rw [Real.norm_eq_abs, abs_div, Nat.abs_cast]
    exact div_le_div_of_nonneg_right (derivative_log_difference_bound k hk z n) (Nat.cast_nonneg _)
  have hh := hd.add hl
  simpa only [sub_div, sub_add_cancel, zero_add] using hh

lemma measurable_recurrenceCoordinates : Measurable recurrenceCoordinates :=
  measurable_fst.prodMk (measurable_fst.sub measurable_snd)

lemma measurable_standardLyapunov (k : ℝ) (hk : 0 ≤ k) :
    Measurable (standardLyapunov k hk) :=
  (transferLyapunov_limit k hk).1.comp measurable_recurrenceCoordinates

lemma standardLyapunov_nonneg (k : ℝ) (hk : 0 ≤ k) (z : Torus) :
    0 ≤ standardLyapunov k hk z := (transferLyapunov_limit k hk).2.2.1 _

lemma standardLyapunov_invariant (k : ℝ) (hk : 0 ≤ k) (z : Torus) :
    standardLyapunov k hk (standardMap k z) = standardLyapunov k hk z := by
  unfold standardLyapunov
  rw [standardMap_conjugacy]
  exact (transferLyapunov_limit k hk).2.2.2.1 _

lemma ae_standardLyapunov_rate (k : ℝ) (hk : 0 ≤ k) :
    ∀ᵐ z ∂area, Tendsto
      (fun n : ℕ => Real.log ‖standardDerivativeProduct k z n‖ / (n : ℝ))
      atTop (𝓝 (standardLyapunov k hk z)) := by
  have hh := measurePreserving_recurrenceCoordinates.quasiMeasurePreserving.ae
    (transferLyapunov_limit k hk).2.2.2.2
  filter_upwards [hh] with z hz
  exact derivative_rate_of_transfer_rate k hk z _ hz

end StandardMapEntropy

namespace StandardMapEntropy
open MeasureTheory Set Filter
open scoped Topology ENNReal

lemma standardDerivative_norm_bound (k : ℝ) (hk : 0 ≤ k) (z : Torus) :
    ‖standardDerivative k z‖ ≤ 9*growthBase k := by
  calc
    _ ≤ 9*‖transferStep (torusPotential k z.1)‖ := conjugate_norm_le _
    _ ≤ 9*(|torusPotential k z.1|+1) :=
      mul_le_mul_of_nonneg_left (transferStep_norm _) (by norm_num)
    _ ≤ _ := mul_le_mul_of_nonneg_left (torusPotential_bound k hk z.1) (by norm_num)

lemma standardDerivativeProduct_step_lower (k : ℝ) (hk : 0 ≤ k) (z : Torus) (n : ℕ) (v : ℂ) :
    ‖standardDerivativeProduct k z n v‖ ≤
      (9*growthBase k)*‖standardDerivativeProduct k z (n+1) v‖ := by
  exact ((standardDerivative_area k ((standardMap k)^[n] z)).norm_lower
    (standardDerivativeProduct k z n v)).trans
    (mul_le_mul_of_nonneg_right (standardDerivative_norm_bound k hk _) (norm_nonneg _))

end StandardMapEntropy
end
end

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_Lyapunov_PlaneLyapunov
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace StandardMapEntropy
open MeasureTheory Set Filter Metric
open scoped Topology BigOperators

namespace PlaneLyapunov

variable (A : ℕ → ℂ →L[ℝ] ℂ)

lemma norm_pos (hA : ∀ n, PlaneAreaPreserving (A n)) (n : ℕ) : 0 < ‖A n‖ :=
  lt_of_lt_of_le zero_lt_one (hA n).singular_pair.choose_spec.2.2.2.2

lemma image_norm_pos (hA : ∀ n, PlaneAreaPreserving (A n)) {v : ℂ} (hv : v ≠ 0) (n : ℕ) :
    0 < ‖A n v‖ := by
  have hh := (hA n).norm_lower v
  by_contra h
  have hz : ‖A n v‖ = 0 := le_antisymm (not_lt.mp h) (norm_nonneg _)
  rw [hz, mul_zero] at hh
  exact (norm_pos_iff.mpr hv).not_ge hh

lemma eventual_exp_lower (hA : ∀ n, PlaneAreaPreserving (A n)) {l α : ℝ}
    (hl : Tendsto (fun n : ℕ => Real.log ‖A n‖ / (n : ℝ)) atTop (𝓝 l)) (hα : α < l) :
    ∀ᶠ n : ℕ in atTop, Real.exp (α*(n : ℝ)) ≤ ‖A n‖ := by
  filter_upwards [(tendsto_order.mp hl).1 α hα, eventually_gt_atTop 0] with n hn hn0
  have hp : (0 : ℝ) < n := by exact_mod_cast hn0
  calc
    _ ≤ Real.exp (Real.log ‖A n‖) := Real.exp_le_exp.mpr ((le_div_iff₀ hp).mp hn.le)
    _ = _ := Real.exp_log (norm_pos A hA n)

lemma tailConstant_pos {M α : ℝ} (hM : 0 < M) (hα : 0 < α) : 0 < tailConstant M α := by
  unfold tailConstant
  apply div_pos (mul_pos hM (Real.exp_pos _))
  exact sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith))

lemma stable_error_exp_bound (D : ℕ → ℝ) (M α : ℝ) (hM : 0 ≤ M) (hα : 0 < α)
    (n B : ℕ) (_hnB : n ≤ B)
    (hD : ∀ i, n ≤ i → i ≤ B → Real.exp (α*(i : ℝ)) ≤ D i) :
    (∑ i ∈ Finset.Ico n B, M/(D i*D (i+1))) ≤
      tailConstant M α * Real.exp (-2*α*(n : ℝ)) := by
  have hq0 : 0 ≤ Real.exp (-2*α) := (Real.exp_pos _).le
  have hq1 : Real.exp (-2*α) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have he (i : ℕ) (hi : i ∈ Finset.Ico n B) :
      M/(D i*D (i+1)) ≤ M*Real.exp (-α)*(Real.exp (-2*α))^i := by
    have hi0 := (Finset.mem_Ico.mp hi).1
    have hiB := (Finset.mem_Ico.mp hi).2
    have hl := hD i hi0 hiB.le
    have hr := hD (i+1) (by omega) (by omega)
    have hp := mul_le_mul hl hr (Real.exp_pos _).le ((Real.exp_pos _).trans_le hl).le
    calc
      _ ≤ M/(Real.exp (α*(i : ℝ))*Real.exp (α*((i+1 : ℕ) : ℝ))) :=
        div_le_div_of_nonneg_left hM (mul_pos (Real.exp_pos _) (Real.exp_pos _)) hp
      _ = _ := by
        rw [← Real.exp_add, div_eq_mul_inv, ← Real.exp_neg, ← Real.exp_nat_mul]
        rw [mul_assoc, ← Real.exp_add]
        congr 2
        push_cast
        ring
  calc
    _ ≤ ∑ i ∈ Finset.Ico n B, M*Real.exp (-α)*(Real.exp (-2*α))^i :=
      Finset.sum_le_sum he
    _ = (M*Real.exp (-α)) * ∑ i ∈ Finset.Ico n B, (Real.exp (-2*α))^i := by
      rw [Finset.mul_sum]
    _ ≤ (M*Real.exp (-α)) * ((Real.exp (-2*α))^n/(1-Real.exp (-2*α))) :=
      mul_le_mul_of_nonneg_left (geom_sum_Ico_le_of_lt_one hq0 hq1) (by positivity)
    _ = _ := by
      rw [← Real.exp_nat_mul]
      unfold tailConstant
      rw [show (n : ℝ)*(-2*α) = -2*α*(n : ℝ) by ring]
      ring

lemma inverse_bound_by_exp (D α : ℝ) (n : ℕ) (hD : Real.exp (α*(n : ℝ)) ≤ D) :
    D⁻¹ ≤ D*Real.exp (-2*α*(n : ℝ)) := by
  have hp : 0 < D := (Real.exp_pos _).trans_le hD
  calc
    _ ≤ (Real.exp (α*(n : ℝ)))⁻¹ := (inv_le_inv₀ hp (Real.exp_pos _)).mpr hD
    _ = Real.exp (α*(n : ℝ))*Real.exp (-2*α*(n : ℝ)) := by
      rw [← Real.exp_neg, ← Real.exp_add]
      congr 1
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hD (Real.exp_pos _).le

lemma exists_stable_bound (hA : ∀ n, PlaneAreaPreserving (A n))
    (M : ℝ) (hM : 0 < M)
    (hstep : ∀ n v, ‖A n v‖ ≤ M*‖A (n+1) v‖)
    {l : ℝ} (hl : Tendsto (fun n : ℕ => Real.log ‖A n‖ / (n : ℝ)) atTop (𝓝 l)) :
    ∃ s : ℂ, ‖s‖=1 ∧ ∀ α : ℝ, 0 < α → α < l →
      ∀ᶠ n : ℕ in atTop, ‖A n s‖ ≤
        ‖A n‖*(1+tailConstant M α)*Real.exp (-2*α*(n : ℝ)) := by
  classical
  choose a hau ham hao has hnorm using fun n => (hA n).singular_pair
  have hu (n : ℕ) : quarterTurn (a n) ∈ sphere (0 : ℂ) 1 := by
    simp only [mem_sphere, dist_zero_right, norm_quarterTurn, hau]
  obtain ⟨s, hs, φ, hφ, hlim⟩ := (isCompact_sphere (0 : ℂ) 1).tendsto_subseq hu
  have hsunit : ‖s‖=1 := by simpa only [mem_sphere, dist_zero_right] using hs
  refine ⟨s, hsunit, ?_⟩
  intro α hα hαl
  obtain ⟨N, hN⟩ := eventually_atTop.mp (eventual_exp_lower A hA hl hαl)
  filter_upwards [eventually_ge_atTop (max N 1)] with n hn
  have hnN : N ≤ n := (le_max_left _ _).trans hn
  have hn1 : 1 ≤ n := (le_max_right _ _).trans hn
  have hb : ‖A n s‖ ≤ ‖A n‖⁻¹ + ‖A n‖ *
      (tailConstant M α * Real.exp (-2*α*(n : ℝ))) := by
    apply le_of_tendsto ((A n).continuous.norm.tendsto s |>.comp hlim)
    filter_upwards [hφ.tendsto_atTop.eventually (eventually_ge_atTop n)] with j hj
    have hh := stable_prefix_finite_bound A a (fun i => ‖A i‖) M n (φ j) hn1 hj
      (fun i _ _ => hA i) (fun i _ _ => hau i) (fun _ _ _ => rfl)
      (fun i _ _ => ham i) (fun i _ _ => has i) (fun i _ _ => hstep i)
    have ht := stable_error_exp_bound (fun i => ‖A i‖) M α hM.le hα n (φ j) hj
      (fun i hni _ => hN i (hnN.trans hni))
    exact hh.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left ht (norm_nonneg _)))
  have hi := inverse_bound_by_exp ‖A n‖ α n (hN n hnN)
  calc
    _ ≤ ‖A n‖*Real.exp (-2*α*(n : ℝ)) +
        ‖A n‖*(tailConstant M α*Real.exp (-2*α*(n : ℝ))) := add_le_add hi le_rfl |>.trans' hb
    _ = _ := by ring

lemma all_growth_zero (hA : ∀ n, PlaneAreaPreserving (A n))
    (hl : Tendsto (fun n : ℕ => Real.log ‖A n‖ / (n : ℝ)) atTop (𝓝 0))
    (v : ℂ) (hv : v ≠ 0) : Growth A v 0 := by
  refine ⟨hv, ?_⟩
  have hvpos := norm_pos_iff.mpr hv
  have hc : Tendsto (fun n : ℕ => Real.log ‖v‖ / (n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hlo : Tendsto (fun n : ℕ =>
      Real.log ‖v‖/(n : ℝ)-Real.log ‖A n‖/(n : ℝ)) atTop (𝓝 0) := by
    simpa only [sub_zero] using hc.sub hl
  have hup : Tendsto (fun n : ℕ =>
      Real.log ‖A n‖/(n : ℝ)+Real.log ‖v‖/(n : ℝ)) atTop (𝓝 0) := by
    simpa only [add_zero] using hl.add hc
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hup
  · filter_upwards [eventually_gt_atTop 0] with n hn
    have hh := Real.log_le_log hvpos ((hA n).norm_lower v)
    rw [Real.log_mul (norm_pos A hA n).ne' (image_norm_pos A hA hv n).ne'] at hh
    have hh' : Real.log ‖v‖-Real.log ‖A n‖ ≤ Real.log ‖A n v‖ := by linarith
    simpa only [sub_div] using div_le_div_of_nonneg_right hh' (Nat.cast_nonneg n)
  · filter_upwards [eventually_gt_atTop 0] with n hn
    have hh := Real.log_le_log (image_norm_pos A hA hv n) ((A n).le_opNorm v)
    rw [Real.log_mul (norm_pos A hA n).ne' hvpos.ne'] at hh
    simpa only [add_div] using div_le_div_of_nonneg_right hh (Nat.cast_nonneg n)

lemma stable_growth (hA : ∀ n, PlaneAreaPreserving (A n)) (M : ℝ) (hM : 0 < M)
    {l : ℝ} (hlpos : 0 < l)
    (hl : Tendsto (fun n : ℕ => Real.log ‖A n‖ / (n : ℝ)) atTop (𝓝 l))
    (s : ℂ) (hs : ‖s‖=1)
    (hbound : ∀ α : ℝ, 0 < α → α < l →
      ∀ᶠ n : ℕ in atTop, ‖A n s‖ ≤
        ‖A n‖*(1+tailConstant M α)*Real.exp (-2*α*(n : ℝ))) : Growth A s (-l) := by
  have hsne : s ≠ 0 := by intro h; simp [h] at hs
  have hlow (n : ℕ) : -Real.log ‖A n‖/(n : ℝ) ≤ Real.log ‖A n s‖/(n : ℝ) := by
    have hh := (hA n).norm_lower s
    rw [hs] at hh
    have hhlog := Real.log_le_log zero_lt_one hh
    rw [Real.log_one, Real.log_mul (norm_pos A hA n).ne'
      (image_norm_pos A hA hsne n).ne'] at hhlog
    apply div_le_div_of_nonneg_right (by linarith) (Nat.cast_nonneg n)
  refine ⟨hsne, tendsto_order.mpr ⟨?_, ?_⟩⟩
  · intro b hb
    have hh : Tendsto (fun n : ℕ => -Real.log ‖A n‖/(n : ℝ)) atTop (𝓝 (-l)) := by
      simpa only [neg_div] using hl.neg
    filter_upwards [(tendsto_order.mp hh).1 b hb] with n hn
    exact hn.trans_le (hlow n)
  · intro b hb
    have hc : max 0 ((l-b)/2) < l := max_lt hlpos (by linarith)
    obtain ⟨α, hαlo, hαhi⟩ := exists_between hc
    have hα : 0 < α := (le_max_left _ _).trans_lt hαlo
    have hαb : l-2*α < b := by
      have := (le_max_right 0 ((l-b)/2)).trans_lt hαlo
      linarith
    have hC : 0 < 1+tailConstant M α := by
      have := tailConstant_pos hM hα
      linarith
    have hu : Tendsto (fun n : ℕ =>
        Real.log ‖A n‖/(n : ℝ)+Real.log (1+tailConstant M α)/(n : ℝ)-2*α)
        atTop (𝓝 (l-2*α)) := by
      have hh := (hl.add (tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop :
        Tendsto (fun n : ℕ => Real.log (1+tailConstant M α)/(n : ℝ)) atTop (𝓝 0))).sub
        (tendsto_const_nhds (x := 2*α))
      simpa only [add_zero] using hh
    filter_upwards [hbound α hα hαhi, (tendsto_order.mp hu).2 b hαb,
      eventually_gt_atTop 0] with n hn hnb hn0
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn0
    have hh := Real.log_le_log (image_norm_pos A hA hsne n) hn
    rw [Real.log_mul (mul_pos (norm_pos A hA n) hC).ne' (Real.exp_pos _).ne',
      Real.log_mul (norm_pos A hA n).ne' hC.ne', Real.log_exp] at hh
    have hdiv := div_le_div_of_nonneg_right hh hnpos.le
    have he : (Real.log ‖A n‖+Real.log (1+tailConstant M α)+ -2*α*(n : ℝ))/(n : ℝ) =
        Real.log ‖A n‖/(n : ℝ)+Real.log (1+tailConstant M α)/(n : ℝ)-2*α := by
      rw [add_div, add_div, mul_div_cancel_right₀ _ hnpos.ne']
      ring
    rw [he] at hdiv
    exact hdiv.trans_lt hnb

lemma growth_on_line (hA : ∀ n, PlaneAreaPreserving (A n))
    {s : ℂ} {l : ℝ} (hsunit : ‖s‖=1) (hs : Growth A s l)
    (v : ℂ) (hv : v ≠ 0) (halign : wedge s v=0) : Growth A v l := by
  have he : v = dot s v • s := by simpa only [halign, zero_smul, add_zero] using unit_expansion s v hsunit
  have hd : dot s v ≠ 0 := by
    intro hz
    rw [hz, zero_smul] at he
    exact hv he
  have hc : Tendsto (fun n : ℕ => Real.log |dot s v|/(n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  refine ⟨hv, ?_⟩
  have hh := hc.add hs.2
  simp only [zero_add] at hh
  apply hh.congr'
  exact Eventually.of_forall fun n => by
    dsimp only
    conv_rhs => rw [he, map_smul, norm_smul, Real.norm_eq_abs,
      Real.log_mul (abs_pos.mpr hd).ne' (image_norm_pos A hA hs.1 n).ne', add_div]

lemma growth_off_line (hA : ∀ n, PlaneAreaPreserving (A n))
    {l : ℝ} (hl : Tendsto (fun n : ℕ => Real.log ‖A n‖ / (n : ℝ)) atTop (𝓝 l))
    {s : ℂ} (hs : Growth A s (-l)) (v : ℂ) (hv : v ≠ 0) (hoff : wedge s v ≠ 0) :
    Growth A v l := by
  have hws : 0 < |wedge s v| := abs_pos.mpr hoff
  have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hlo : Tendsto (fun n : ℕ =>
      Real.log |wedge s v|/(n : ℝ)-Real.log ‖A n s‖/(n : ℝ)) atTop (𝓝 l) := by
    have hc : Tendsto (fun n : ℕ => Real.log |wedge s v|/(n : ℝ)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
    simpa using hc.sub hs.2
  have hup : Tendsto (fun n : ℕ =>
      Real.log ‖A n‖/(n : ℝ)+Real.log ‖v‖/(n : ℝ)) atTop (𝓝 l) := by
    have hc : Tendsto (fun n : ℕ => Real.log ‖v‖/(n : ℝ)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
    simpa using hl.add hc
  refine ⟨hv, tendsto_of_tendsto_of_tendsto_of_le_of_le hlo hup ?_ ?_⟩
  · intro n
    have hh := abs_wedge_le_norm_mul (A n s) (A n v)
    rw [hA n] at hh
    have hhlog := Real.log_le_log hws hh
    rw [Real.log_mul (image_norm_pos A hA hs.1 n).ne' (image_norm_pos A hA hv n).ne'] at hhlog
    have hsub : Real.log |wedge s v|-Real.log ‖A n s‖ ≤ Real.log ‖A n v‖ := by linarith
    simpa only [sub_div] using div_le_div_of_nonneg_right hsub (Nat.cast_nonneg n)
  · intro n
    have hh := Real.log_le_log (image_norm_pos A hA hv n) ((A n).le_opNorm v)
    rw [Real.log_mul (norm_pos A hA n).ne' hvpos.ne'] at hh
    simpa only [add_div] using div_le_div_of_nonneg_right hh (Nat.cast_nonneg n)

theorem positive_flag (hA : ∀ n, PlaneAreaPreserving (A n))
    (M : ℝ) (hM : 0 < M) (hstep : ∀ n v, ‖A n v‖ ≤ M*‖A (n+1) v‖)
    {l : ℝ} (hlpos : 0 < l)
    (hl : Tendsto (fun n : ℕ => Real.log ‖A n‖ / (n : ℝ)) atTop (𝓝 l)) :
    ∃ s : ℂ, s ≠ 0 ∧ ∀ v : ℂ, v ≠ 0 → Growth A v (if wedge s v=0 then -l else l) := by
  obtain ⟨s, hsunit, hsbound⟩ := exists_stable_bound A hA M hM hstep hl
  have hs := stable_growth A hA M hM hlpos hl s hsunit hsbound
  refine ⟨s, hs.1, ?_⟩
  intro v hv
  by_cases hw : wedge s v=0
  · simp only [ite_eq_left hw]
    exact growth_on_line A hA hsunit hs v hv hw
  · simp only [ite_eq_right hw]
    exact growth_off_line A hA hl hs v hv hw

end PlaneLyapunov
end StandardMapEntropy

end
end

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_Lyapunov_ActualLyapunov
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace StandardMapEntropy
open MeasureTheory Set Filter
open scoped Topology ENNReal

lemma ae_standardLyapunov_spectrum (k : ℝ) (hk : 0 ≤ k) :
    ∀ᵐ z ∂area, LyapunovSpectrumAt k z (standardLyapunov k hk z) := by
  filter_upwards [ae_standardLyapunov_rate k hk] with z hz
  refine ⟨standardLyapunov_nonneg k hk z, ?_⟩
  rcases eq_or_lt_of_le (standardLyapunov_nonneg k hk z) with hzero | hpos
  · refine Or.inl ⟨hzero.symm, ?_⟩
    intro v hv
    apply PlaneLyapunov.all_growth_zero (standardDerivativeProduct k z)
      (standardDerivativeProduct_area k z) _ v hv
    simpa only [← hzero] using hz
  · refine Or.inr ⟨hpos, ?_⟩
    exact PlaneLyapunov.positive_flag (standardDerivativeProduct k z)
      (standardDerivativeProduct_area k z) (9*growthBase k)
      (mul_pos (by norm_num) (by have := growthBase_ge_four k hk; linarith))
      (standardDerivativeProduct_step_lower k hk z) hpos hz

end StandardMapEntropy

end
end

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_Lyapunov_HyperbolicSet
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace StandardMapEntropy
open MeasureTheory Set Filter
open scoped Topology ENNReal

lemma normalizedArea_probability {E : Set Torus} (hE : 0 < area E) :
    IsProbabilityMeasure (normalizedArea E) := by
  constructor
  simp only [normalizedArea, Measure.smul_apply, Measure.restrict_apply_univ,
    smul_eq_mul]
  exact ENNReal.inv_mul_cancel hE.ne' (measure_lt_top area E).ne

lemma normalizedArea_ae_mem {E : Set Torus} (hE : MeasurableSet E) :
    ∀ᵐ z ∂normalizedArea E, z ∈ E :=
  (ae_restrict_mem hE).filter_mono (Measure.ae_smul_measure_le _)

end StandardMapEntropy

end
end

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_Lyapunov_InverseLyapunov
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace StandardMapEntropy
open MeasureTheory Set Filter
open scoped Topology ENNReal

lemma complexProjection_inverse_iterate (k : ℝ) (n : ℕ) (z : ℂ) :
    complexProjection ((standardInverseLift k)^[n] z) = (inverseMap k)^[n] (complexProjection z) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
      complexProjection_standardInverseLift, ih]

end StandardMapEntropy

end
end

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_Lyapunov_TransverseLines
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace StandardMapEntropy
open MeasureTheory Set Filter
open scoped Topology ENNReal

lemma measurePreserving_inverseMap (k : ℝ) : MeasurePreserving (inverseMap k) area area :=
  (measurePreserving_standardMap k).symm (standardMap_measurableEquiv k)

end StandardMapEntropy

end
end

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_Lyapunov_BoundedTempering
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace StandardMapEntropy
open MeasureTheory Set Filter
open scoped Topology ENNReal

lemma planeCoframe_frame (s u : ℂ) {a b : ℝ} (ha : a≠0) (hb : b≠0)
    (hw : wedge s u≠0) :
    (planeCoframe s u a b).comp (planeFrame s u a b)=ContinuousLinearMap.id ℝ ℂ := by
  apply ContinuousLinearMap.ext
  intro v
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply, planeCoframe_apply,
    planeFrame_apply, wedge_add_left, wedge_add_right, wedge_smul_left, wedge_smul_right,
    wedge_refl]
  apply Complex.ext <;> dsimp only
  all_goals (field_simp [ha,hb,hw]; ring)

lemma lyapunovCoframe_frame (k χ : ℝ) (z : Torus)
    (hw : wedge (stableVector k z) (unstableVector k z)≠0) :
    (lyapunovCoframe k χ z).comp (lyapunovFrame k χ z)=ContinuousLinearMap.id ℝ ℂ :=
  planeCoframe_frame _ _ (ne_of_gt (zero_lt_one.trans_le (stableScale_ge_one k χ z)))
    (ne_of_gt (zero_lt_one.trans_le (unstableScale_ge_one k χ z))) hw

end StandardMapEntropy

end
end

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_Lyapunov_MeasurableFrame
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace StandardMapEntropy
open MeasureTheory Set Filter
open scoped Topology ENNReal

namespace TemperedControl

variable {X : Type*} [MeasurableSpace X]

lemma radius_le_one (e : X ≃ᵐ X) {c : X → ℝ} (hc : ∀ x, 0 ≤ c x) (ε : ℝ) (x : X) :
    radius e c ε x≤1 := by
  have := control_nonneg e hc ε x
  exact (inv_le_one₀ (by linarith : 0<1+control e c ε x)).mpr (by linarith)

end TemperedControl
end StandardMapEntropy

end
section
namespace StandardMapEntropy
open MeasureTheory Set Filter
open scoped Topology ENNReal

lemma diagonalPlane_apply (α β : ℝ) (v : ℂ) :
    diagonalPlane α β v = ⟨α*v.re, β*v.im⟩ := by
  apply Complex.ext <;> simp [diagonalPlane] <;> ring

end StandardMapEntropy

end
section
namespace StandardMapEntropy
open MeasureTheory Set Filter
open scoped Topology ENNReal

lemma chartRadius_le_one (k χ ε : ℝ) (z : Torus) : chartRadius k χ ε z≤1 :=
  TemperedControl.radius_le_one _ (fun z => zero_le_one.trans (chartControl_ge_one k χ z)) ε z

end StandardMapEntropy

end
end

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_Stable_SmoothRemainder
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace StandardMapEntropy.NonlinearStable
open Filter
open scoped Topology NNReal

variable {ℓ δ : ℝ≥0}

lemma solution_initial (r : Recurrence ℓ δ) (h : ℓ+δ<1) (s : ℝ) : (r.solution h s 0).1=s := by
  have hh := congrArg (fun x : Sequence => (x 0).1) (solution_fixed r h s)
  exact hh.symm

lemma solution_orbit (r : Recurrence ℓ δ) (h : ℓ+δ<1) (s : ℝ) (n : ℕ) :
    r.solution h s (n+1)=r.step n (r.solution h s n) := by
  have hh := congrArg (fun x : Sequence => x (n+1)) (solution_fixed r h s)
  have hh' := congrArg (fun x : Sequence => x n) (solution_fixed r h s)
  apply Prod.ext
  · exact (congrArg Prod.fst hh).symm
  · have he := congrArg Prod.snd hh'
    change (r.b n)⁻¹*((r.solution h s (n+1)).2-(r.remainder n (r.solution h s n)).2)=
      (r.solution h s n).2 at he
    change _=r.b n*(r.solution h s n).2+(r.remainder n (r.solution h s n)).2
    have he' := congrArg (fun t : ℝ => r.b n*t) he
    rw [← mul_assoc, mul_inv_cancel₀ (r.b_ne n), one_mul] at he'
    linarith

lemma solution_lipschitz (r : Recurrence ℓ δ) (h : ℓ+δ<1) (s t : ℝ) :
    ‖r.solution h s-r.solution h t‖≤|s-t| := by
  apply bound_of_max_contraction (abs_nonneg _) (show ((ℓ+δ : ℝ≥0) : ℝ)<1 from h)
  apply (BoundedContinuousFunction.norm_le (le_trans (abs_nonneg _) (le_max_left _ _))).mpr
  intro n
  have hh := perronValue_sub_bound r (le_trans (le_add_of_nonneg_right (show (0 : ℝ≥0) ≤ δ from bot_le)) h.le)
    s t (r.solution h s) (r.solution h t) n
  have h1 := congrArg (fun x : Sequence => x n) (solution_fixed r h s)
  have h2 := congrArg (fun x : Sequence => x n) (solution_fixed r h t)
  change r.perronValue s (r.solution h s) n=r.solution h s n at h1
  change r.perronValue t (r.solution h t) n=r.solution h t n at h2
  rwa [h1,h2] at hh

end StandardMapEntropy.NonlinearStable

end
section
namespace StandardMapEntropy.NonlinearStable
open Filter
open scoped Topology NNReal
variable {ℓ δ : ℝ≥0}

lemma orbit_fixed (r : Recurrence ℓ δ) (h : ℓ+δ<1) (s : ℝ) (x : Sequence)
    (h0 : (x 0).1=s) (horbit : ∀ n, x (n+1)=r.step n (x n)) :
    r.perron (le_trans (le_add_of_nonneg_right (show (0 : ℝ≥0)≤δ from bot_le)) h.le) s x=x := by
  apply BoundedContinuousFunction.ext
  intro n
  apply Prod.ext
  · cases n with
    | zero => exact h0.symm
    | succ n => exact (congrArg Prod.fst (horbit n)).symm
  · have hh := congrArg Prod.snd (horbit n)
    change (x (n+1)).2=r.b n*(x n).2+(r.remainder n (x n)).2 at hh
    change (r.b n)⁻¹*((x (n+1)).2-(r.remainder n (x n)).2)=(x n).2
    rw [hh,add_sub_cancel_right,←mul_assoc,inv_mul_cancel₀ (r.b_ne n),one_mul]

lemma solution_unique (r : Recurrence ℓ δ) (h : ℓ+δ<1) (s : ℝ) (x : Sequence)
    (h0 : (x 0).1=s) (horbit : ∀ n, x (n+1)=r.step n (x n)) :
    x=r.solution h s :=
  (perron_contracting r h (s := s)).fixedPoint_unique (orbit_fixed r h s x h0 horbit)

lemma solution_tail (r : Recurrence ℓ δ) (h : ℓ+δ<1) (s : ℝ) (m : ℕ) :
    (r.solution h s).tail m=(r.tail m).solution h (r.solution h s m).1 := by
  apply solution_unique
  · simp only [tail_apply,Nat.add_zero]
  · intro n
    simpa only [tail_apply,Recurrence.tail,Recurrence.step,Nat.add_assoc] using
      solution_orbit r h s (m+n)

lemma solution_cone (r : Recurrence ℓ δ) (h : ℓ+δ<1) (s t : ℝ) (n : ℕ) :
    ‖r.solution h s n-r.solution h t n‖≤|(r.solution h s n).1-(r.solution h t n).1| := by
  have hh := solution_lipschitz (r.tail n) h (r.solution h s n).1 (r.solution h t n).1
  rw [←solution_tail,←solution_tail] at hh
  have hb := (point_sub_bound ((r.solution h s).tail n) ((r.solution h t).tail n) 0).trans hh
  simpa only [tail_apply,Nat.add_zero] using hb

lemma step_fst_sub_bound (r : Recurrence ℓ δ) (n : ℕ) (v w : Plane) :
    |(r.step n v).1-(r.step n w).1|≤((ℓ+δ : ℝ≥0) : ℝ)*‖v-w‖ := by
  have hr := (r.lipschitz n).dist_le_mul v w
  rw [dist_eq_norm,dist_eq_norm] at hr
  have hrf := (norm_fst_le (r.remainder n v-r.remainder n w)).trans hr
  have hvw : |v.1-w.1|≤‖v-w‖ := norm_fst_le (v-w)
  change |r.a n*v.1+(r.remainder n v).1-(r.a n*w.1+(r.remainder n w).1)|≤_
  calc
    _ = |r.a n*(v.1-w.1)+((r.remainder n v).1-(r.remainder n w).1)| := by congr 1; ring
    _ ≤ |r.a n| * |v.1-w.1|+|(r.remainder n v).1-(r.remainder n w).1| := by
      simpa only [abs_mul] using abs_add_le (r.a n*(v.1-w.1)) ((r.remainder n v).1-(r.remainder n w).1)
    _ ≤ (ℓ : ℝ)*‖v-w‖+(δ : ℝ)*‖v-w‖ := add_le_add
      (mul_le_mul (r.stable_bound n) hvw (abs_nonneg _) ℓ.coe_nonneg) hrf
    _ = _ := by push_cast; ring

lemma solution_step_contraction (r : Recurrence ℓ δ) (h : ℓ+δ<1) (s t : ℝ) (n : ℕ) :
    ‖r.solution h s (n+1)-r.solution h t (n+1)‖≤
      ((ℓ+δ : ℝ≥0) : ℝ)*‖r.solution h s n-r.solution h t n‖ := by
  apply (solution_cone r h s t (n+1)).trans
  rw [solution_orbit,solution_orbit]
  exact step_fst_sub_bound r n _ _

lemma solution_exponential_contraction (r : Recurrence ℓ δ) (h : ℓ+δ<1) (s t : ℝ) (n : ℕ) :
    ‖r.solution h s n-r.solution h t n‖≤((ℓ+δ : ℝ≥0) : ℝ)^n*|s-t| := by
  induction n with
  | zero => simpa only [pow_zero,one_mul,solution_initial] using solution_cone r h s t 0
  | succ n ih =>
    apply (solution_step_contraction r h s t n).trans
    calc
      _ ≤ ((ℓ+δ : ℝ≥0) : ℝ)*(((ℓ+δ : ℝ≥0) : ℝ)^n*|s-t|) :=
        mul_le_mul_of_nonneg_left ih (ℓ+δ).coe_nonneg
      _ = _ := by rw [pow_succ]; ring

lemma graph_lipschitz (r : Recurrence ℓ δ) (h : ℓ+δ<1) : LipschitzWith 1 (r.graph h) := by
  apply LipschitzWith.of_dist_le_mul
  intro s t
  rw [dist_eq_norm,dist_eq_norm,NNReal.coe_one,one_mul]
  exact (norm_snd_le (r.solution h s 0-r.solution h t 0)).trans
    ((point_sub_bound _ _ 0).trans (solution_lipschitz r h s t))

lemma solution_zero (r : Recurrence ℓ δ) (h : ℓ+δ<1) : r.solution h 0=0 := by
  exact norm_eq_zero.mp (le_antisymm (by simpa only [abs_zero] using solution_norm_bound r h 0) (norm_nonneg _))

@[simp] lemma graph_zero (r : Recurrence ℓ δ) (h : ℓ+δ<1) : r.graph h 0=0 := by
  simp [Recurrence.graph,solution_zero]

end StandardMapEntropy.NonlinearStable

end
section
namespace StandardMapEntropy
open MeasureTheory Set Filter
open scoped Topology NNReal

lemma flatInverse_frame {q : ℝ} (hq : q≠0) {F C : ℂ →L[ℝ] ℂ}
    (hCF : C.comp F=ContinuousLinearMap.id ℝ ℂ) (v : RealPlane) :
    flatInverse q C (flatFrame q F v)=v := by
  have hh : C (F (pairToComplex v))=pairToComplex v := congrArg (fun D : ℂ →L[ℝ] ℂ => D (pairToComplex v)) hCF
  simp only [flatInverse,flatFrame,ContinuousLinearMap.comp_apply,smul_apply,map_smul,
    hh,smul_smul,mul_inv_cancel₀ hq,one_smul,complexToPair_pairToComplex]

lemma flat_diagonal {q p : ℝ} (D F C : ℂ →L[ℝ] ℂ) {a b : ℝ}
    (h : C.comp (D.comp F)=diagonalPlane a b) (v : RealPlane) :
    flatInverse p C (D (flatFrame q F v))=(q/p*a*v.1,q/p*b*v.2) := by
  have hh : C (D (F (pairToComplex v)))=diagonalPlane a b (pairToComplex v) :=
    congrArg (fun T : ℂ →L[ℝ] ℂ => T (pairToComplex v)) h
  simp only [flatInverse,flatFrame,ContinuousLinearMap.comp_apply,smul_apply,map_smul]
  rw [hh]
  simp only [diagonalPlane_apply,complexToPair_apply,pairToComplex_apply]
  apply Prod.ext <;> simp only [Prod.smul_fst,Prod.smul_snd,smul_eq_mul,div_eq_mul_inv] <;> ring

end StandardMapEntropy

end
end

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_Stable_LocalStable
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace StandardMapEntropy.NonlinearStable
open Filter
open scoped Topology NNReal

variable {ℓ δ : ℝ≥0}

lemma extend_step_eq (r : LocalRecurrence ℓ δ) (n : ℕ) {v : Plane} (hv : ‖v‖≤1) :
    r.extend.step n v=r.step n v := by
  simp only [LocalRecurrence.extend,Recurrence.step,LocalRecurrence.step,planeClip_eq hv]

lemma local_solution_orbit (r : LocalRecurrence ℓ δ) (h : ℓ+δ<1) {s : ℝ} (hs : |s|≤1) (n : ℕ) :
    r.extend.solution h s (n+1)=r.step n (r.extend.solution h s n) := by
  rw [solution_orbit,extend_step_eq r n (local_solution_bound r h hs n)]

end StandardMapEntropy.NonlinearStable

end
section
namespace StandardMapEntropy.NonlinearStable
open Filter
open scoped Topology NNReal
variable {ℓ δ : ℝ≥0}

lemma linearRate_lt_one (h : ℓ+δ<1) : (ℓ : ℝ)<1 := by
  have he : ℓ≤ℓ+δ := le_add_of_nonneg_right (show (0 : ℝ≥0)≤δ from bot_le)
  exact lt_of_le_of_lt he h

lemma solution_snd_bound_of_forcing (r : Recurrence ℓ δ) (h : ℓ+δ<1) (s t : ℝ)
    {B : ℝ} (hB : 0≤B)
    (hr : ∀ n, ‖r.remainder n (r.solution h s n)-r.remainder n (r.solution h t n)‖≤B) :
    ‖sndSequence (r.solution h s)-sndSequence (r.solution h t)‖≤(ℓ : ℝ)*B/(1-(ℓ : ℝ)) := by
  let U := ‖sndSequence (r.solution h s)-sndSequence (r.solution h t)‖
  have hU : 0≤U := norm_nonneg _
  have hcon : U≤(ℓ : ℝ)*(U+B) := by
    apply (BoundedContinuousFunction.norm_le (mul_nonneg ℓ.coe_nonneg (add_nonneg hU hB))).mpr
    intro n
    have hs := congrArg (fun x : Sequence => (x n).2) (solution_fixed r h s)
    have ht := congrArg (fun x : Sequence => (x n).2) (solution_fixed r h t)
    change (r.b n)⁻¹*((r.solution h s (n+1)).2-(r.remainder n (r.solution h s n)).2)=
      (r.solution h s n).2 at hs
    change (r.b n)⁻¹*((r.solution h t (n+1)).2-(r.remainder n (r.solution h t n)).2)=
      (r.solution h t n).2 at ht
    change |(r.solution h s n).2-(r.solution h t n).2|≤_
    rw [←hs,←ht]
    have hu : |(r.solution h s (n+1)).2-(r.solution h t (n+1)).2|≤U :=
      (sndSequence (r.solution h s)-sndSequence (r.solution h t)).norm_coe_le_norm (n+1)
    have hb : |(r.remainder n (r.solution h s n)).2-(r.remainder n (r.solution h t n)).2|≤B :=
      (norm_snd_le _).trans (hr n)
    calc
      _ = |(r.b n)⁻¹| * |((r.solution h s (n+1)).2-(r.solution h t (n+1)).2)-
          ((r.remainder n (r.solution h s n)).2-(r.remainder n (r.solution h t n)).2)| := by
        rw [←abs_mul]; congr 1; ring
      _ ≤ |(r.b n)⁻¹| * (|(r.solution h s (n+1)).2-(r.solution h t (n+1)).2|+
          |(r.remainder n (r.solution h s n)).2-(r.remainder n (r.solution h t n)).2|) :=
        mul_le_mul_of_nonneg_left (abs_sub _ _) (abs_nonneg _)
      _ ≤ _ := mul_le_mul (r.inverse_bound n) (add_le_add hu hb) (by positivity) ℓ.coe_nonneg
  apply (le_div_iff₀ (sub_pos.mpr (linearRate_lt_one h))).mpr
  dsimp [U] at hcon ⊢
  nlinarith

lemma graph_slope_bound (r : Recurrence ℓ δ) (h : ℓ+δ<1) (s t : ℝ) :
    |r.graph h s-r.graph h t|≤((ℓ : ℝ)*(δ : ℝ)/(1-(ℓ : ℝ)))*|s-t| := by
  have hforce (n : ℕ) : ‖r.remainder n (r.solution h s n)-r.remainder n (r.solution h t n)‖≤
      (δ : ℝ)*|s-t| :=
    (remainder_sub_bound r _ _ n).trans (mul_le_mul_of_nonneg_left (solution_lipschitz r h s t) δ.coe_nonneg)
  have hh := solution_snd_bound_of_forcing r h s t (mul_nonneg δ.coe_nonneg (abs_nonneg _)) hforce
  have hb := (sndSequence (r.solution h s)-sndSequence (r.solution h t)).norm_coe_le_norm 0
  apply hb.trans
  exact hh.trans_eq (by ring)

end StandardMapEntropy.NonlinearStable

end
end

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_Stable_PerronStability
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace StandardMapEntropy.NonlinearStable
open Filter
open scoped Topology NNReal
variable {ℓ δ : ℝ≥0}

lemma perron_defect_bound (r : Recurrence ℓ δ) (hℓ : ℓ≤1) (s : ℝ) (x : Sequence)
    {B : ℝ} (hB : 0≤B) (h0 : (x 0).1=s)
    (hstep : ∀ n, ‖x (n+1)-r.step n (x n)‖≤B) :
    ‖r.perron hℓ s x-x‖≤B := by
  apply (BoundedContinuousFunction.norm_le hB).mpr
  intro n
  rw [Prod.norm_def]
  apply max_le
  · cases n with
    | zero => simpa only [BoundedContinuousFunction.sub_apply,perron_apply,Recurrence.perronValue,
        Prod.fst_sub,h0,sub_self,norm_zero] using hB
    | succ n =>
      have hh := (norm_fst_le (x (n+1)-r.step n (x n))).trans (hstep n)
      change |r.a n*(x n).1+(r.remainder n (x n)).1-(x (n+1)).1|≤B
      rw [abs_sub_comm]
      exact hh
  · have hh := (norm_snd_le (x (n+1)-r.step n (x n))).trans (hstep n)
    change |(r.b n)⁻¹*((x (n+1)).2-(r.remainder n (x n)).2)-(x n).2|≤B
    calc
      _ = |(r.b n)⁻¹| * |(x (n+1)).2-(r.b n*(x n).2+(r.remainder n (x n)).2)| := by
        rw [←abs_mul]
        congr 1
        have hb := inv_mul_cancel₀ (r.b_ne n)
        calc
          _ = (r.b n)⁻¹*((x (n+1)).2-(r.remainder n (x n)).2)-
              ((r.b n)⁻¹*r.b n)*(x n).2 := by rw [hb,one_mul]
          _ = _ := by ring
      _ ≤ (ℓ : ℝ)*B := mul_le_mul (r.inverse_bound n) hh (abs_nonneg _) ℓ.coe_nonneg
      _ ≤ B := (mul_le_mul_of_nonneg_right (show (ℓ : ℝ)≤1 from hℓ) hB).trans_eq (one_mul _)

lemma near_orbit_solution_bound (r : Recurrence ℓ δ) (h : ℓ+δ<1) (s : ℝ) (x : Sequence)
    {B : ℝ} (hB : 0≤B) (h0 : (x 0).1=s)
    (hstep : ∀ n, ‖x (n+1)-r.step n (x n)‖≤B) :
    ‖x-r.solution h s‖≤B/(1-((ℓ+δ : ℝ≥0) : ℝ)) := by
  have hh := (perron_contracting r h (s := s)).dist_fixedPoint_le x
  rw [dist_eq_norm,dist_eq_norm] at hh
  change ‖x-r.solution h s‖≤_ at hh
  have hp := perron_defect_bound r (le_trans (le_add_of_nonneg_right (show (0 : ℝ≥0)≤δ from bot_le)) h.le)
    s x hB h0 hstep
  rw [norm_sub_rev] at hp
  exact hh.trans (div_le_div_of_nonneg_right hp (sub_nonneg.mpr (show ((ℓ+δ : ℝ≥0) : ℝ)≤1 from h.le)))

lemma linearized_step_smul (r : LocalRecurrence ℓ δ) (D : ℕ → Plane →L[ℝ] Plane)
    (hD : ∀ n, ‖D n‖≤δ) (n : ℕ) (t : ℝ) (v : Plane) :
    (r.linearized D hD).step n (t • v)=t • (r.linearized D hD).step n v := by
  apply Prod.ext <;> simp only [LocalRecurrence.linearized,Recurrence.step,Prod.smul_fst,Prod.smul_snd,
    map_smul,smul_eq_mul] <;> ring

lemma linearized_solution_smul (r : LocalRecurrence ℓ δ) (D : ℕ → Plane →L[ℝ] Plane)
    (hD : ∀ n, ‖D n‖≤δ) (h : ℓ+δ<1) (t : ℝ) :
    (r.linearized D hD).solution h t=t • (r.linearized D hD).solution h 1 := by
  symm
  apply solution_unique
  · change (t • (r.linearized D hD).solution h 1 0).1=t
    rw [Prod.smul_fst,solution_initial,smul_eq_mul,mul_one]
  · intro n
    change t • (r.linearized D hD).solution h 1 (n+1)=
      (r.linearized D hD).step n (t • (r.linearized D hD).solution h 1 n)
    rw [solution_orbit,linearized_step_smul]

lemma hasDerivAt_of_quadratic_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} {v : E} {x C : ℝ} (hC : 0≤C)
    (h : ∀ᶠ y in 𝓝 x, ‖f y-f x-(y-x) • v‖≤C*|y-x|^2) : HasDerivAt f v x := by
  rw [hasDerivAt_iff_isLittleO,Asymptotics.isLittleO_iff]
  intro ε hε
  have he : 0<ε/(C+1) := div_pos hε (by linarith)
  have hsmall : ∀ᶠ y in 𝓝 x, |y-x|<ε/(C+1) := by
    filter_upwards [Metric.ball_mem_nhds x he] with y hy
    simpa only [Metric.mem_ball,Real.dist_eq] using hy
  filter_upwards [h,hsmall] with y hy hys
  rw [Real.norm_eq_abs]
  apply hy.trans
  have hb : C*|y-x|≤ε := by
    have hh := (lt_div_iff₀ (show 0<C+1 by linarith)).mp hys
    nlinarith [abs_nonneg (y-x)]
  calc
    _ = (C*|y-x|)*|y-x| := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hb (abs_nonneg _)

end StandardMapEntropy.NonlinearStable

end
section
namespace StandardMapEntropy
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal

lemma quadratic_taylor_of_derivative_lipschitz {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E → F) (D : E → E →L[ℝ] F) (hD : ∀ x, HasFDerivAt f (D x) x)
    {M : ℝ} (hM : 0≤M) (hLip : ∀ x y, ‖D x-D y‖≤M*‖x-y‖) (v w : E) :
    ‖f w-f v-D v (w-v)‖≤M*‖w-v‖^2 := by
  let g : E → F := fun x => f x-f v-D v (x-v)
  have hg (x : E) : HasFDerivAt g (D x-D v) x := by
    have hh := ((hD x).sub_const (f v)).sub ((D v).hasFDerivAt.comp x ((hasFDerivAt_id x).sub_const v))
    convert! hh using 1
    all_goals try with_reducible_and_instances rfl
  have hlocal (x : E) (hx : x∈Metric.closedBall v ‖w-v‖) : ‖D x-D v‖≤M*‖w-v‖ := by
    refine (hLip x v).trans (mul_le_mul_of_nonneg_left ?_ hM)
    simpa only [Metric.mem_closedBall,dist_eq_norm] using hx
  have hh := (convex_closedBall v ‖w-v‖).norm_image_sub_le_of_norm_hasFDerivWithin_le
    (fun x _ => (hg x).hasFDerivWithinAt) hlocal
    (show v∈Metric.closedBall v ‖w-v‖ by simpa only [Metric.mem_closedBall,dist_self] using norm_nonneg (w-v))
    (show w∈Metric.closedBall v ‖w-v‖ by simp only [Metric.mem_closedBall,dist_eq_norm,le_refl])
  simpa only [g,sub_self,map_zero,sub_zero,pow_two,mul_assoc] using hh

lemma hasFDerivAt_flatRemainder (k : ℝ) (z : ℂ) (F : RealPlane →L[ℝ] ℂ)
    (C : ℂ →L[ℝ] RealPlane) (v : RealPlane) :
    HasFDerivAt (flatRemainder k z F C) (flatRemainderDerivative k z F C v) v := by
  exact C.hasFDerivAt.comp v ((hasFDerivAt_liftRemainder k z (F v)).comp v F.hasFDerivAt)

lemma flatRemainderDerivative_lipschitz (k : ℝ) (z : ℂ) (F : RealPlane →L[ℝ] ℂ)
    (C : ℂ →L[ℝ] RealPlane) (v w : RealPlane) :
    ‖flatRemainderDerivative k z F C v-flatRemainderDerivative k z F C w‖≤
      (‖C‖*derivativeVariationBound k*‖F‖^2)*‖v-w‖ := by
  have he : flatRemainderDerivative k z F C v-flatRemainderDerivative k z F C w=
      C.comp ((standardDerivative k (complexProjection (z+F v))-
        standardDerivative k (complexProjection (z+F w))).comp F) := by
    apply ContinuousLinearMap.ext
    intro u
    simp only [flatRemainderDerivative,sub_apply,ContinuousLinearMap.comp_apply,map_sub]
    abel
  have hd := standardDerivative_lift_sub_bound k (z+F v) (z+F w)
  rw [add_sub_add_left_eq_sub,←map_sub] at hd
  have hd' := hd.trans (mul_le_mul_of_nonneg_left (F.le_opNorm (v-w)) (derivativeVariationBound_nonneg k))
  rw [he]
  calc
    _ ≤ ‖C‖*‖(standardDerivative k (complexProjection (z+F v))-
      standardDerivative k (complexProjection (z+F w))).comp F‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖C‖*(‖standardDerivative k (complexProjection (z+F v))-
        standardDerivative k (complexProjection (z+F w))‖*‖F‖) :=
      mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg C)
    _ ≤ ‖C‖*((derivativeVariationBound k*(‖F‖*‖v-w‖))*‖F‖) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hd' (norm_nonneg F)) (norm_nonneg C)
    _ = _ := by ring

end StandardMapEntropy

end
section
namespace StandardMapEntropy.NonlinearStable
open Filter Set
open scoped Topology NNReal
variable {ℓ δ : ℝ≥0}

lemma linearized_difference_residual (r : LocalRecurrence ℓ δ) (h : ℓ+δ<1)
    (D : ℕ → Plane →L[ℝ] Plane) (hD : ∀ n, ‖D n‖≤δ)
    {s t : ℝ} (hs : |s|≤1) (ht : |t|≤1) (n : ℕ) :
    (r.extend.solution h t-r.extend.solution h s) (n+1)-
      (r.linearized D hD).step n ((r.extend.solution h t-r.extend.solution h s) n) =
      r.remainder n (r.extend.solution h t n)-r.remainder n (r.extend.solution h s n)-
        D n (r.extend.solution h t n-r.extend.solution h s n) := by
  simp only [BoundedContinuousFunction.sub_apply,local_solution_orbit r h hs,local_solution_orbit r h ht]
  apply Prod.ext <;> simp only [Prod.fst_sub,Prod.snd_sub,LocalRecurrence.step,LocalRecurrence.linearized,Recurrence.step] <;> ring

lemma solution_quadratic_approximation (r : LocalRecurrence ℓ δ) (h : ℓ+δ<1)
    (D : ℕ → Plane →L[ℝ] Plane) (hD : ∀ n, ‖D n‖≤δ)
    {M : ℝ} (hM : 0≤M) {s t : ℝ} (hs : |s|≤1) (ht : |t|≤1)
    (hTaylor : ∀ n, ‖r.remainder n (r.extend.solution h t n)-r.remainder n (r.extend.solution h s n)-
        D n (r.extend.solution h t n-r.extend.solution h s n)‖≤
      M*‖r.extend.solution h t n-r.extend.solution h s n‖^2) :
    ‖r.extend.solution h t-r.extend.solution h s-(t-s) • (r.linearized D hD).solution h 1‖≤
      (M/(1-((ℓ+δ : ℝ≥0) : ℝ)))*|t-s|^2 := by
  have hstep (n : ℕ) : ‖(r.extend.solution h t-r.extend.solution h s) (n+1)-
      (r.linearized D hD).step n ((r.extend.solution h t-r.extend.solution h s) n)‖≤M*|t-s|^2 := by
    rw [linearized_difference_residual r h D hD hs ht n]
    apply (hTaylor n).trans
    apply mul_le_mul_of_nonneg_left _ hM
    exact pow_le_pow_left₀ (norm_nonneg _) ((point_sub_bound _ _ n).trans (solution_lipschitz r.extend h t s)) 2
  have h0 : ((r.extend.solution h t-r.extend.solution h s) 0).1=t-s := by
    simp only [BoundedContinuousFunction.sub_apply,Prod.fst_sub,solution_initial]
  have hh := near_orbit_solution_bound (r.linearized D hD) h (t-s) (r.extend.solution h t-r.extend.solution h s)
    (mul_nonneg hM (sq_nonneg _)) h0 hstep
  rw [linearized_solution_smul] at hh
  exact hh.trans_eq (by ring)

lemma solution_hasDerivAt (r : LocalRecurrence ℓ δ) (h : ℓ+δ<1)
    (D : ℕ → Plane → Plane →L[ℝ] Plane)
    (hD : ∀ n v, ‖v‖≤1 → ‖D n v‖≤δ)
    {M : ℝ} (hM : 0≤M)
    (hTaylor : ∀ n v w, ‖v‖≤1 → ‖w‖≤1 →
      ‖r.remainder n w-r.remainder n v-D n v (w-v)‖≤M*‖w-v‖^2)
    {s : ℝ} (hs : |s|<1) :
    HasDerivAt (r.extend.solution h) (graphLinearization r h D hD s hs.le) s := by
  apply hasDerivAt_of_quadratic_bound (div_nonneg hM (sub_nonneg.mpr (show ((ℓ+δ : ℝ≥0) : ℝ)≤1 from h.le)))
  have hnear : Ioo (-1 : ℝ) 1∈𝓝 s := isOpen_Ioo.mem_nhds (abs_lt.mp hs)
  filter_upwards [hnear] with t ht
  have ht' : |t|≤1 := abs_le.mpr ⟨ht.1.le,ht.2.le⟩
  exact solution_quadratic_approximation r h _ _ hM hs.le ht'
    (fun n => hTaylor n _ _ (local_solution_bound r h hs.le n) (local_solution_bound r h ht' n))

lemma graph_hasDerivAt (r : LocalRecurrence ℓ δ) (h : ℓ+δ<1)
    (D : ℕ → Plane → Plane →L[ℝ] Plane)
    (hD : ∀ n v, ‖v‖≤1 → ‖D n v‖≤δ)
    {M : ℝ} (hM : 0≤M)
    (hTaylor : ∀ n v w, ‖v‖≤1 → ‖w‖≤1 →
      ‖r.remainder n w-r.remainder n v-D n v (w-v)‖≤M*‖w-v‖^2)
    {s : ℝ} (hs : |s|<1) :
    HasDerivAt (r.extend.graph h) (graphLinearization r h D hD s hs.le 0).2 s := by
  have hh := ((sequenceEval 0).hasFDerivAt.comp_hasDerivAt s (solution_hasDerivAt r h D hD hM hTaylor hs)).snd
  exact hh

lemma linearized_difference_of_fields (r : LocalRecurrence ℓ δ)
    (D E : ℕ → Plane →L[ℝ] Plane) (hD : ∀ n, ‖D n‖≤δ) (hE : ∀ n, ‖E n‖≤δ)
    (n : ℕ) (v : Plane) :
    (r.linearized D hD).step n v-(r.linearized E hE).step n v=(D n-E n) v := by
  apply Prod.ext <;> simp only [LocalRecurrence.linearized,Recurrence.step,Prod.fst_sub,Prod.snd_sub,
    sub_apply] <;> ring

lemma linearized_solution_field_bound (r : LocalRecurrence ℓ δ) (h : ℓ+δ<1)
    (D E : ℕ → Plane →L[ℝ] Plane) (hD : ∀ n, ‖D n‖≤δ) (hE : ∀ n, ‖E n‖≤δ)
    {B : ℝ} (hB : 0≤B) (hDE : ∀ n, ‖D n-E n‖≤B) :
    ‖(r.linearized D hD).solution h 1-(r.linearized E hE).solution h 1‖≤B/(1-((ℓ+δ : ℝ≥0) : ℝ)) := by
  apply near_orbit_solution_bound _ h 1 _ hB (solution_initial _ h 1)
  intro n
  rw [solution_orbit,linearized_difference_of_fields]
  have hn : ‖(r.linearized D hD).solution h 1 n‖≤1 :=
    ((r.linearized D hD).solution h 1).norm_coe_le_norm n |>.trans (by simpa using solution_norm_bound _ h 1)
  calc
    _ ≤ ‖D n-E n‖*‖(r.linearized D hD).solution h 1 n‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ B*1 := mul_le_mul (hDE n) hn (norm_nonneg _) hB
    _ = _ := mul_one _

lemma graphLinearization_lipschitz (r : LocalRecurrence ℓ δ) (h : ℓ+δ<1)
    (D : ℕ → Plane → Plane →L[ℝ] Plane)
    (hD : ∀ n v, ‖v‖≤1 → ‖D n v‖≤δ)
    {M : ℝ} (hM : 0≤M)
    (hLip : ∀ n v w, ‖v‖≤1 → ‖w‖≤1 → ‖D n v-D n w‖≤M*‖v-w‖)
    {s t : ℝ} (hs : |s|≤1) (ht : |t|≤1) :
    ‖graphLinearization r h D hD s hs-graphLinearization r h D hD t ht‖≤
      (M/(1-((ℓ+δ : ℝ≥0) : ℝ)))*|s-t| := by
  have hfields (n : ℕ) : ‖D n (r.extend.solution h s n)-D n (r.extend.solution h t n)‖≤M*|s-t| :=
    (hLip n _ _ (local_solution_bound r h hs n) (local_solution_bound r h ht n)).trans
      (mul_le_mul_of_nonneg_left ((point_sub_bound _ _ n).trans (solution_lipschitz _ h s t)) hM)
  exact (linearized_solution_field_bound r h _ _ _ _ (mul_nonneg hM (abs_nonneg _)) hfields).trans_eq (by ring)

end StandardMapEntropy.NonlinearStable

end
section
namespace StandardMapEntropy.NonlinearStable
open Filter Set
open scoped Topology NNReal
variable {ℓ δ : ℝ≥0}

lemma graph_deriv_lipschitzOn (r : LocalRecurrence ℓ δ) (h : ℓ+δ<1)
    (D : ℕ → Plane → Plane →L[ℝ] Plane)
    (hD : ∀ n v, ‖v‖≤1 → ‖D n v‖≤δ)
    {M : ℝ} (hM : 0≤M)
    (hTaylor : ∀ n v w, ‖v‖≤1 → ‖w‖≤1 →
      ‖r.remainder n w-r.remainder n v-D n v (w-v)‖≤M*‖w-v‖^2)
    (hLip : ∀ n v w, ‖v‖≤1 → ‖w‖≤1 → ‖D n v-D n w‖≤M*‖v-w‖) :
    LipschitzOnWith ⟨M/(1-((ℓ+δ : ℝ≥0) : ℝ)),
      div_nonneg hM (sub_nonneg.mpr (show ((ℓ+δ : ℝ≥0) : ℝ)≤1 by exact_mod_cast h.le))⟩
      (deriv (r.extend.graph h)) (Ioo (-1 : ℝ) 1) := by
  refine lipschitzOnWith_iff_norm_sub_le.mpr ?_
  intro s hs t ht
  have hs' : |s|<1 := abs_lt.mpr hs
  have ht' : |t|<1 := abs_lt.mpr ht
  rw [(graph_hasDerivAt r h D hD hM hTaylor hs').deriv,
    (graph_hasDerivAt r h D hD hM hTaylor ht').deriv]
  exact (norm_snd_le _).trans ((point_sub_bound _ _ 0).trans
    (graphLinearization_lipschitz r h D hD hM hLip hs'.le ht'.le))

lemma graph_contDiffOn (r : LocalRecurrence ℓ δ) (h : ℓ+δ<1)
    (D : ℕ → Plane → Plane →L[ℝ] Plane)
    (hD : ∀ n v, ‖v‖≤1 → ‖D n v‖≤δ)
    {M : ℝ} (hM : 0≤M)
    (hTaylor : ∀ n v w, ‖v‖≤1 → ‖w‖≤1 →
      ‖r.remainder n w-r.remainder n v-D n v (w-v)‖≤M*‖w-v‖^2)
    (hLip : ∀ n v w, ‖v‖≤1 → ‖w‖≤1 → ‖D n v-D n w‖≤M*‖v-w‖) :
    ContDiffOn ℝ 1 (r.extend.graph h) (Ioo (-1 : ℝ) 1) := by
  rw [contDiffOn_one_iff_derivWithin isOpen_Ioo.uniqueDiffOn]
  refine ⟨fun s hs => (graph_hasDerivAt r h D hD hM hTaylor (abs_lt.mpr hs)).differentiableAt.differentiableWithinAt, ?_⟩
  exact (graph_deriv_lipschitzOn r h D hD hM hTaylor hLip).continuousOn.congr
    (fun s hs => derivWithin_of_isOpen isOpen_Ioo hs)

end StandardMapEntropy.NonlinearStable

end
section
namespace StandardMapEntropy
open MeasureTheory Set Filter
open scoped Topology ENNReal

lemma tangentReversal_inverseLift (k : ℝ) (w : ℂ) :
    tangentReversal (standardInverseLift k w)=standardLift k (tangentReversal w) := by
  apply Complex.ext <;> simp [standardInverseLift,standardLift] <;> ring
lemma tangentReversal_inverse_lift_iterate (k : ℝ) (n : ℕ) (w : ℂ) :
    tangentReversal ((standardInverseLift k)^[n] w)=(standardLift k)^[n] (tangentReversal w) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply',tangentReversal_inverseLift,ih,Function.iterate_succ_apply']
lemma inverse_lift_iterate_reversed (k : ℝ) (n : ℕ) (w : ℂ) :
    (standardInverseLift k)^[n] (tangentReversal w)=tangentReversal ((standardLift k)^[n] w) := by
  have hh := congrArg tangentReversal (tangentReversal_inverse_lift_iterate k n (tangentReversal w))
  simpa only [tangentReversal_involutive] using hh
lemma tangentReversal_norm_le (w : ℂ) : ‖tangentReversal w‖≤3*‖w‖ := by
  have hh := Complex.norm_le_abs_re_add_abs_im (tangentReversal w)
  simp only [tangentReversal_re,tangentReversal_im,abs_neg] at hh
  have hh' := abs_sub w.re w.im
  have hr := Complex.abs_re_le_norm w
  have hi := Complex.abs_im_le_norm w
  linarith

end StandardMapEntropy

end
end

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_Entropy_FineCharts
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace StandardMapEntropy
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal

lemma fineSize_le_scale (k χ ε : ℝ) {δ : ℝ} (hδ : 0<δ) (z : Torus) : fineSize k χ ε δ z≤fineScale k ε δ :=
  (mul_le_mul_of_nonneg_left (chartRadius_le_one k χ ε z) (fineScale_pos k ε hδ).le).trans_eq (mul_one _)
lemma fineInverse_frame (k χ ε : ℝ) {δ : ℝ} (hδ : 0<δ) (z : Torus)
    (hw : wedge (stableVector k z) (unstableVector k z)≠0) (v : RealPlane) :
    fineInverse k χ ε δ z (fineFrame k χ ε δ z v)=v :=
  flatInverse_frame (ne_of_gt (fineSize_pos k χ ε hδ z)) (lyapunovCoframe_frame k χ z hw) v

end StandardMapEntropy

end
section
namespace StandardMapEntropy
open MeasureTheory Set Filter
open scoped Topology ENNReal
lemma codingScale_pos (k ε : ℝ) {δ : ℝ} (hδ : 0<δ) : 0 < codingScale k ε δ := by
  unfold codingScale
  exact div_pos (lt_min zero_lt_one (fineScale_pos k ε hδ)) (by positivity)
lemma codingScale_le (k ε : ℝ) {δ : ℝ} (hδ : 0<δ) :
    codingScale k ε δ≤fineScale k ε δ/100 := by
  have hη := fineScale_pos k ε hδ
  unfold codingScale
  calc
    _ ≤ fineScale k ε δ/(100*(1+|9*growthBase k|)) := div_le_div_of_nonneg_right (min_le_right _ _) (by positivity)
    _ ≤ _ := div_le_div_of_nonneg_left hη.le (by norm_num) (by nlinarith [abs_nonneg (9*growthBase k)])
lemma codingRadius_pos (k χ ε : ℝ) {δ : ℝ} (hδ : 0<δ) (z : Torus) : 0 < codingRadius k χ ε δ z :=
  mul_pos (codingScale_pos k ε hδ) (sq_pos_of_pos (chartRadius_pos k χ ε z))
lemma codingRadius_ratio (k χ ε : ℝ) {δ : ℝ} (hδ : 0<δ) (z : Torus) (hz : FineRegular k χ ε z) :
    codingRadius k χ ε δ z≤Real.exp (2*ε)*codingRadius k χ ε δ (standardMap k z) ∧
    codingRadius k χ ε δ (standardMap k z)≤Real.exp (2*ε)*codingRadius k χ ε δ z := by
  have he : 0<Real.exp ε := Real.exp_pos ε
  have hex : (Real.exp ε)^2=Real.exp (2*ε) := by rw [sq,←Real.exp_add]; congr 1; ring
  have hh : chartRadius k χ ε z≤Real.exp ε*chartRadius k χ ε (standardMap k z) := by
    have ht := mul_le_mul_of_nonneg_left hz.2.2.2.2.2.1 he.le
    rw [←mul_assoc,←Real.exp_add,add_neg_cancel,Real.exp_zero,one_mul] at ht
    exact ht
  have hh' : chartRadius k χ ε (standardMap k z)≤Real.exp ε*chartRadius k χ ε z := by
    have ht := mul_le_mul_of_nonneg_left hz.2.2.2.2.2.2 he.le
    rw [←mul_assoc,←Real.exp_add,add_neg_cancel,Real.exp_zero,one_mul] at ht
    exact ht
  have general (x y : Torus) (h : chartRadius k χ ε x≤Real.exp ε*chartRadius k χ ε y) :
      codingRadius k χ ε δ x≤Real.exp (2*ε)*codingRadius k χ ε δ y := by
    have hs := sq_le_sq₀ (chartRadius_pos k χ ε x).le (mul_nonneg he.le (chartRadius_pos k χ ε y).le) |>.mpr h
    rw [mul_pow,hex] at hs
    have ht := mul_le_mul_of_nonneg_left hs (codingScale_pos k ε hδ).le
    simpa only [codingRadius,mul_left_comm] using ht
  exact ⟨general _ _ hh,general _ _ hh'⟩
lemma fineInverse_codingRadius (k χ ε : ℝ) {δ : ℝ} (hδ : 0<δ) (z : Torus) (hz : FineRegular k χ ε z) :
    ‖fineInverse k χ ε δ z‖*codingRadius k χ ε δ z≤1/100 := by
  let r := chartRadius k χ ε z
  let η := fineScale k ε δ
  let c := codingScale k ε δ
  have hr : 0 < r := chartRadius_pos k χ ε z
  have hη : 0<η := fineScale_pos k ε hδ
  have hc : 0 < c := codingScale_pos k ε hδ
  have hb : ‖fineInverse k χ ε δ z‖≤(η*r)⁻¹*‖lyapunovCoframe k χ z‖ :=
    flatInverse_norm_le (fineSize_pos k χ ε hδ z).le _
  calc
    _ ≤ ((η*r)⁻¹*‖lyapunovCoframe k χ z‖)*(c*r^2) := mul_le_mul_of_nonneg_right hb (by positivity)
    _ = (c/η)*(r*‖lyapunovCoframe k χ z‖) := by field_simp
    _ ≤ (c/η)*1 := mul_le_mul_of_nonneg_left hz.2.2.2.2.1 (by positivity)
    _ ≤ 1/100 := by
      rw [mul_one]
      exact (div_le_iff₀ hη).mpr (by simpa only [div_eq_mul_inv,mul_comm,one_mul,c,η] using codingScale_le k ε hδ)

end StandardMapEntropy

end
section
namespace StandardMapEntropy.NonlinearStable
open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal
variable {ℓ δ : ℝ≥0}

lemma Recurrence.unstable_size_lower (r : Recurrence ℓ δ) (n : ℕ) : 1≤(ℓ : ℝ)*|r.b n| := by
  have hh := mul_le_mul_of_nonneg_right (r.inverse_bound n) (abs_nonneg (r.b n))
  simpa only [abs_inv,inv_mul_cancel₀ (abs_ne_zero.mpr (r.b_ne n))] using hh
lemma Recurrence.unstable_size_ge_one (r : Recurrence ℓ δ) (h : ℓ+δ<1) (n : ℕ) : 1≤|r.b n| := by
  have hℓ : (ℓ : ℝ)≤1 := NNReal.coe_le_coe.mpr ((le_add_of_nonneg_right (show (0 : ℝ≥0)≤δ from bot_le)).trans h.le)
  exact (r.unstable_size_lower n).trans ((mul_le_mul_of_nonneg_right hℓ (abs_nonneg _)).trans_eq (one_mul _))
lemma Recurrence.unstable_expansion (r : Recurrence ℓ δ) (h : ℓ+δ<1) (n : ℕ) :
    1≤((ℓ+δ : ℝ≥0) : ℝ)*(|r.b n|-(δ : ℝ)) := by
  have hq : ((ℓ+δ : ℝ≥0) : ℝ)≤1 := NNReal.coe_le_coe.mpr h.le
  have hb : ((ℓ+δ : ℝ≥0) : ℝ)≤|r.b n| := hq.trans (r.unstable_size_ge_one h n)
  have hd := mul_nonneg δ.coe_nonneg (sub_nonneg.mpr hb)
  have hl := r.unstable_size_lower n
  simp only [NNReal.coe_add] at hd ⊢
  nlinarith

lemma Recurrence.step_snd_lower (r : Recurrence ℓ δ) (n : ℕ) (v w : Plane) :
    |r.b n| *|v.2-w.2|≤|(r.step n v).2-(r.step n w).2|+(δ : ℝ)*‖v-w‖ := by
  have hr := (r.lipschitz n).dist_le_mul v w
  rw [dist_eq_norm,dist_eq_norm] at hr
  have hri := (norm_snd_le (r.remainder n v-r.remainder n w)).trans hr
  have he : r.b n*(v.2-w.2)=((r.step n v).2-(r.step n w).2)-
      ((r.remainder n v).2-(r.remainder n w).2) := by dsimp only [Recurrence.step]; ring
  rw [←abs_mul,he]
  exact (abs_sub _ _).trans (add_le_add le_rfl hri)

lemma Recurrence.unstable_cone_step (r : Recurrence ℓ δ) (h : ℓ+δ<1) (n : ℕ) (v w : Plane)
    (hcone : |v.1-w.1|≤|v.2-w.2|) :
    |(r.step n v).1-(r.step n w).1|≤|(r.step n v).2-(r.step n w).2| ∧
    |v.2-w.2|≤((ℓ+δ : ℝ≥0) : ℝ)*|(r.step n v).2-(r.step n w).2| := by
  have hvw : ‖v-w‖=|v.2-w.2| := max_eq_right hcone
  have hl := r.step_snd_lower n v w
  rw [hvw] at hl
  have hl' : (|r.b n|-(δ : ℝ))*|v.2-w.2|≤|(r.step n v).2-(r.step n w).2| := by nlinarith
  have hb : |v.2-w.2|≤((ℓ+δ : ℝ≥0) : ℝ)*|(r.step n v).2-(r.step n w).2| := by
    calc
      _ ≤ (((ℓ+δ : ℝ≥0) : ℝ)*(|r.b n|-(δ : ℝ)))*|v.2-w.2| := by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right (r.unstable_expansion h n) (abs_nonneg (v.2-w.2))
      _ = ((ℓ+δ : ℝ≥0) : ℝ)*((|r.b n|-(δ : ℝ))*|v.2-w.2|) := mul_assoc _ _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left hl' (ℓ+δ).coe_nonneg
  refine ⟨?_,hb⟩
  have hf := step_fst_sub_bound r n v w
  rw [hvw] at hf
  have hq : ((ℓ+δ : ℝ≥0) : ℝ)≤1 := NNReal.coe_le_coe.mpr h.le
  have hc : ((ℓ+δ : ℝ≥0) : ℝ)*|v.2-w.2|≤|v.2-w.2| :=
    (mul_le_mul_of_nonneg_right hq (abs_nonneg _)).trans_eq (one_mul _)
  have hb' : ((ℓ+δ : ℝ≥0) : ℝ)*|(r.step n v).2-(r.step n w).2|≤|(r.step n v).2-(r.step n w).2| :=
    (mul_le_mul_of_nonneg_right hq (abs_nonneg _)).trans_eq (one_mul _)
  exact hf.trans (hc.trans (hb.trans hb'))

lemma Recurrence.orbit_continuous (r : Recurrence ℓ δ) (n : ℕ) : Continuous (fun v => r.orbit v n) := by
  induction n with
  | zero => exact continuous_id
  | succ n ih =>
    exact ((continuous_const.mul ih.fst).add ((r.lipschitz n).continuous.comp ih).fst).prodMk
      ((continuous_const.mul ih.snd).add ((r.lipschitz n).continuous.comp ih).snd)

end StandardMapEntropy.NonlinearStable

end
section
namespace StandardMapEntropy
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal

lemma fine_derivative_diagonal (k χ ε δ : ℝ) (z : Torus) (hz : FineRegular k χ ε z) (v : RealPlane) :
    fineInverse k χ ε δ (standardMap k z) (standardDerivative k z (fineFrame k χ ε δ z v)) =
      (fineStableMultiplier k χ ε δ z*v.1,fineUnstableMultiplier k χ ε δ z*v.2) :=
  flat_diagonal _ _ _ hz.2.1 v
lemma fine_step (k χ ε δ : ℝ) (z : ℂ) (hz : FineRegular k χ ε (complexProjection z)) (v : RealPlane) :
    fineInverse k χ ε δ (standardMap k (complexProjection z))
      (standardLift k (z+fineFrame k χ ε δ (complexProjection z) v)-standardLift k z) =
      (fineStableMultiplier k χ ε δ (complexProjection z)*v.1+(fineRemainder k χ ε δ z v).1,
        fineUnstableMultiplier k χ ε δ (complexProjection z)*v.2+(fineRemainder k χ ε δ z v).2) := by
  have hdiff : standardLift k (z+fineFrame k χ ε δ (complexProjection z) v)-standardLift k z =
      standardDerivative k (complexProjection z) (fineFrame k χ ε δ (complexProjection z) v)+
        liftRemainder k z (fineFrame k χ ε δ (complexProjection z) v) := by unfold liftRemainder; abel
  rw [hdiff,map_add,fine_derivative_diagonal k χ ε δ _ hz]
  rfl
lemma fine_lift_step (k χ ε : ℝ) {δ : ℝ} (hδ : 0<δ) (z : ℂ)
    (hz : FineRegular k χ ε (complexProjection z)) (hn : FineRegular k χ ε (standardMap k (complexProjection z))) (v : RealPlane) :
    standardLift k (z+fineFrame k χ ε δ (complexProjection z) v) = standardLift k z+
      fineFrame k χ ε δ (standardMap k (complexProjection z))
        (fineStableMultiplier k χ ε δ (complexProjection z)*v.1+(fineRemainder k χ ε δ z v).1,
          fineUnstableMultiplier k χ ε δ (complexProjection z)*v.2+(fineRemainder k χ ε δ z v).2) := by
  have hh := congrArg (fineFrame k χ ε δ (standardMap k (complexProjection z))) (fine_step k χ ε δ z hz v)
  rw [fineFrame_inverse k χ ε hδ _ hn.1] at hh
  exact (sub_eq_iff_eq_add.mp hh).trans (add_comm _ _)

end StandardMapEntropy

end
section
namespace StandardMapEntropy
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
open NonlinearStable

lemma fineCoordinate_initial (k χ ε : ℝ) {δ : ℝ} (hδ : 0<δ) (w : ℂ)
    (hw : FineRegular k χ ε (complexProjection w)) (v : RealPlane) :
    fineCoordinate k χ ε δ w (w+fineFrame k χ ε δ (complexProjection w) v) 0=v := by
  change fineInverse k χ ε δ (complexProjection w) (w+fineFrame k χ ε δ (complexProjection w) v-w)=v
  rw [add_sub_cancel_left,fineInverse_frame k χ ε hδ _ hw.1]
lemma fineCoordinate_step (k χ ε δ : ℝ) (hδ : 0<δ) (w p : ℂ)
    (hw : ∀ n : ℕ, FineRegular k χ ε (complexProjection ((standardLift k)^[n] w))) (n : ℕ) :
    fineCoordinate k χ ε δ w p (n+1)=
      (fineLocalRecurrence k χ ε δ hδ w hw).step n (fineCoordinate k χ ε δ w p n) := by
  have he : (standardLift k)^[n] p=(standardLift k)^[n] w+
      fineFrame k χ ε δ (complexProjection ((standardLift k)^[n] w)) (fineCoordinate k χ ε δ w p n) := by
    dsimp only [fineCoordinate]
    rw [fineFrame_inverse k χ ε hδ _ (hw n).1]
    abel
  conv_lhs => simp only [fineCoordinate,Function.iterate_succ_apply']
  rw [he]
  simpa only [Function.iterate_succ_apply',complexProjection_standardLift,fineLocalRecurrence,LocalRecurrence.step] using
    fine_step k χ ε δ ((standardLift k)^[n] w) (hw n) (fineCoordinate k χ ε δ w p n)

end StandardMapEntropy

end
end

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_Entropy_PhysicalVolume
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace StandardMapEntropy
open MeasureTheory Set Filter
open scoped Topology ENNReal

lemma volume_pairToComplex_image {S : Set RealPlane} (hS : MeasurableSet S) :
    volume (pairToComplex '' S)=volume S := by
  have he : pairToComplex '' S=Complex.measurableEquivRealProd ⁻¹' S := by
    ext z
    constructor
    · rintro ⟨v,hv,rfl⟩; exact hv
    · intro hz
      exact ⟨complexToPair z,hz,pairToComplex_complexToPair z⟩
  rw [he]
  exact Complex.volume_preserving_equiv_real_prod.measure_preimage hS.nullMeasurableSet

end StandardMapEntropy

end
end

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_Holonomy_DerivativeQuantitative
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace StandardMapEntropy
open MeasureTheory Set Filter
open scoped Topology ENNReal

lemma log_difference_of_lower {a b D : ℝ} (hD : 0<D) (ha : 1≤D*a) (hb : 1≤D*b) :
    |Real.log a-Real.log b|≤D*|a-b| := by
  have ha0 : 0<a := by nlinarith
  have hb0 : 0<b := by nlinarith
  have hab := Real.log_le_sub_one_of_pos (div_pos ha0 hb0)
  have hba := Real.log_le_sub_one_of_pos (div_pos hb0 ha0)
  rw [Real.log_div ha0.ne' hb0.ne'] at hab
  rw [Real.log_div hb0.ne' ha0.ne'] at hba
  have hab' : a/b-1≤D*|a-b| := by
    apply (sub_le_iff_le_add).mpr
    apply (div_le_iff₀ hb0).mpr
    nlinarith [le_abs_self (a-b),mul_le_mul_of_nonneg_left hb (abs_nonneg (a-b))]
  have hba' : b/a-1≤D*|a-b| := by
    apply (sub_le_iff_le_add).mpr
    apply (div_le_iff₀ ha0).mpr
    nlinarith [neg_le_abs (a-b),mul_le_mul_of_nonneg_left ha (abs_nonneg (a-b))]
  exact abs_le.mpr ⟨by linarith,hab.trans hab'⟩

end StandardMapEntropy

end
section
namespace StandardMapEntropy
open Finset

lemma sum_of_backward_contraction (a : ℕ → ℝ) (ha : ∀ n,0≤a n) {q : ℝ}
    (hq0 : 0≤q) (hq1 : q<1) (N : ℕ) (hstep : ∀ j : ℕ,j<N → a j≤q*a (j+1)) :
    (∑ j ∈ Finset.range N,a j)≤a N/(1-q) := by
  have hh : (∑ j ∈ Finset.range N,a j)≤q*(∑ j ∈ Finset.range N,a (j+1)) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun j hj => hstep j (Finset.mem_range.mp hj)
  have he : (∑ j ∈ Finset.range N,a (j+1))+a 0=(∑ j ∈ Finset.range N,a j)+a N := by
    rw [←Finset.sum_range_succ',←Finset.sum_range_succ]
  apply (le_div_iff₀ (sub_pos.mpr hq1)).mpr
  have hlast := mul_le_mul_of_nonneg_right hq1.le (ha N)
  have hfirst := mul_nonneg hq0 (ha 0)
  nlinarith

namespace NonlinearStable
open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal
variable {ℓ δ : ℝ≥0}

lemma Recurrence.orbit_cone (r : Recurrence ℓ δ) (h : ℓ+δ<1) {v : Plane}
    (hv : |v.1|≤|v.2|) (n : ℕ) :
    |(r.orbit v n).1|≤|(r.orbit v n).2| ∧
    |(r.orbit v n).2|≤((ℓ+δ : ℝ≥0) : ℝ)*|(r.orbit v (n+1)).2| := by
  have hcone (m : ℕ) : |(r.orbit v m).1|≤|(r.orbit v m).2| := by
    induction m with
    | zero => exact hv
    | succ m ih =>
      simpa only [Recurrence.orbit,r.step_zero,Prod.fst_zero,Prod.snd_zero,sub_zero] using
        (r.unstable_cone_step h m (r.orbit v m) 0 (by simpa only [Prod.fst_zero,Prod.snd_zero,sub_zero] using ih)).1
  refine ⟨hcone n,?_⟩
  simpa only [Recurrence.orbit,r.step_zero,Prod.snd_zero,sub_zero] using
    (r.unstable_cone_step h n (r.orbit v n) 0 (by simpa only [Prod.fst_zero,Prod.snd_zero,sub_zero] using hcone n)).2
lemma Recurrence.orbit_norm_eq_snd (r : Recurrence ℓ δ) (h : ℓ+δ<1) {v : Plane}
    (hv : |v.1|≤|v.2|) (n : ℕ) : ‖r.orbit v n‖=|(r.orbit v n).2| :=
  max_eq_right (r.orbit_cone h hv n).1
lemma Recurrence.orbit_snd_ne_zero (r : Recurrence ℓ δ) (h : ℓ+δ<1) {v : Plane}
    (hv : |v.1|≤|v.2|) (hv0 : v.2≠0) (n : ℕ) : (r.orbit v n).2≠0 := by
  induction n with
  | zero => exact hv0
  | succ n ih =>
    intro he
    have hc := (r.orbit_cone h hv n).2
    rw [he,abs_zero,mul_zero] at hc
    exact (abs_pos.mpr ih).not_ge hc

end NonlinearStable
end StandardMapEntropy

end
section
namespace StandardMapEntropy
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
open NonlinearStable

lemma hasFDerivAt_fineRemainder (k χ ε δ : ℝ) (z : ℂ) (v : RealPlane) :
    HasFDerivAt (fineRemainder k χ ε δ z) (fineRemainderDerivative k χ ε δ z v) v :=
  hasFDerivAt_flatRemainder _ _ _ _ _
lemma fineRemainderDerivative_lipschitz (k χ ε : ℝ) {δ : ℝ} (hδ : 0<δ) (z : ℂ)
    (hz : FineRegular k χ ε (complexProjection z))
    (hn : FineRegular k χ ε (standardMap k (complexProjection z))) (v w : RealPlane) :
    ‖fineRemainderDerivative k χ ε δ z v-fineRemainderDerivative k χ ε δ z w‖≤δ*‖v-w‖ :=
  (flatRemainderDerivative_lipschitz k z _ _ v w).trans
    (mul_le_mul_of_nonneg_right (fine_nonlinearity_coefficient k χ ε hδ _ hz hn) (norm_nonneg _))
lemma fineRemainderDerivative_bound (k χ ε : ℝ) {δ : ℝ} (hδ : 0<δ) (z : ℂ)
    (hz : FineRegular k χ ε (complexProjection z))
    (hn : FineRegular k χ ε (standardMap k (complexProjection z)))
    {v : RealPlane} (hv : ‖v‖≤1) : ‖fineRemainderDerivative k χ ε δ z v‖≤δ := by
  have hh := fineRemainderDerivative_lipschitz k χ ε hδ z hz hn v 0
  simp only [fineRemainderDerivative_zero,sub_zero] at hh
  exact hh.trans ((mul_le_mul_of_nonneg_left hv hδ.le).trans_eq (mul_one _))
lemma fineRemainder_taylor (k χ ε : ℝ) {δ : ℝ} (hδ : 0<δ) (z : ℂ)
    (hz : FineRegular k χ ε (complexProjection z))
    (hn : FineRegular k χ ε (standardMap k (complexProjection z))) (v w : RealPlane) :
    ‖fineRemainder k χ ε δ z w-fineRemainder k χ ε δ z v-
      fineRemainderDerivative k χ ε δ z v (w-v)‖≤δ*‖w-v‖^2 :=
  quadratic_taylor_of_derivative_lipschitz _ _ (hasFDerivAt_fineRemainder k χ ε δ z)
    hδ.le (fineRemainderDerivative_lipschitz k χ ε hδ z hz hn) v w

end StandardMapEntropy

end
end

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_Holonomy_FineStableGeometry
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace StandardMapEntropy
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
open NonlinearStable

@[simp] lemma fineStableCurve_zero (k χ ε δ : ℝ) (hδ : 0<δ) (hq : Real.exp (-χ+ε)+δ<1)
    (w : ℂ) (hw : ∀ n : ℕ, FineRegular k χ ε (complexProjection ((standardLift k)^[n] w))) :
    fineStableCurve k χ ε δ hδ hq w hw 0=w := by
  have hz := NonlinearStable.graph_zero (fineLocalRecurrence k χ ε δ hδ w hw).extend hq
  dsimp only [fineStableCurve,fineStableGraph]
  rw [hz,Prod.mk_zero_zero,map_zero,add_zero]

lemma fineStableCurve_orbit (k χ ε δ : ℝ) (hδ : 0<δ) (hq : Real.exp (-χ+ε)+δ<1)
    (w : ℂ) (hw : ∀ n : ℕ, FineRegular k χ ε (complexProjection ((standardLift k)^[n] w)))
    {s : ℝ} (hs : |s|≤1) (n : ℕ) :
    (standardLift k)^[n] (fineStableCurve k χ ε δ hδ hq w hw s)=(standardLift k)^[n] w+
      fineFrame k χ ε δ (complexProjection ((standardLift k)^[n] w))
        ((fineLocalRecurrence k χ ε δ hδ w hw).extend.solution hq s n) := by
  induction n with
  | zero =>
    have hi : (fineLocalRecurrence k χ ε δ hδ w hw).extend.solution hq s 0=
        (s,fineStableGraph k χ ε δ hδ hq w hw s) := Prod.ext (solution_initial _ _ s) rfl
    simp only [Function.iterate_zero,id_eq,hi,fineStableCurve]
  | succ n ih =>
    rw [Function.iterate_succ_apply',ih,fine_lift_step k χ ε hδ _ (hw n) (fine_regular_lift_next k χ ε w hw n)]
    rw [local_solution_orbit _ hq hs n]
    simp only [Function.iterate_succ_apply',complexProjection_standardLift,fineLocalRecurrence,LocalRecurrence.step]

lemma fineStableCoordinate (k χ ε δ : ℝ) (hδ : 0<δ) (hq : Real.exp (-χ+ε)+δ<1)
    (w : ℂ) (hw : ∀ n : ℕ, FineRegular k χ ε (complexProjection ((standardLift k)^[n] w)))
    {s : ℝ} (hs : |s|≤1) (n : ℕ) :
    fineCoordinate k χ ε δ w (fineStableCurve k χ ε δ hδ hq w hw s) n=
      (fineLocalRecurrence k χ ε δ hδ w hw).extend.solution hq s n := by
  dsimp only [fineCoordinate]
  rw [fineStableCurve_orbit k χ ε δ hδ hq w hw hs n,add_sub_cancel_left,
    fineInverse_frame k χ ε hδ _ (hw n).1]

lemma fineStableCurve_contraction (k χ ε δ : ℝ) (hδ : 0<δ) (hq : Real.exp (-χ+ε)+δ<1)
    (w : ℂ) (hw : ∀ n : ℕ, FineRegular k χ ε (complexProjection ((standardLift k)^[n] w)))
    {s t : ℝ} (hs : |s|≤1) (ht : |t|≤1) (n : ℕ) :
    ‖(standardLift k)^[n] (fineStableCurve k χ ε δ hδ hq w hw s)-
      (standardLift k)^[n] (fineStableCurve k χ ε δ hδ hq w hw t)‖≤
      (2*fineScale k ε δ)*(Real.exp (-χ+ε)+δ)^n*|s-t| := by
  rw [fineStableCurve_orbit k χ ε δ hδ hq w hw hs,fineStableCurve_orbit k χ ε δ hδ hq w hw ht,
    add_sub_add_left_eq_sub,←map_sub]
  have hn : ‖fineFrame k χ ε δ (complexProjection ((standardLift k)^[n] w))‖≤2*fineScale k ε δ :=
    (fineFrame_norm_le k χ ε hδ _).trans (mul_le_mul_of_nonneg_left (fineSize_le_scale k χ ε hδ _) (by norm_num))
  have hx := solution_exponential_contraction (fineLocalRecurrence k χ ε δ hδ w hw).extend hq s t n
  exact ((ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul hn hx (norm_nonneg _)
    (by linarith [fineScale_pos k ε hδ]))).trans_eq (by
      change (2*fineScale k ε δ)*((Real.exp (-χ+ε)+δ)^n*|s-t|)=_; ring)

lemma fineStableGraph_contDiffOn (k χ ε δ : ℝ) (hδ : 0<δ) (hq : Real.exp (-χ+ε)+δ<1)
    (w : ℂ) (hw : ∀ n : ℕ, FineRegular k χ ε (complexProjection ((standardLift k)^[n] w))) :
    ContDiffOn ℝ 1 (fineStableGraph k χ ε δ hδ hq w hw) (Ioo (-1 : ℝ) 1) := by
  apply graph_contDiffOn (fineLocalRecurrence k χ ε δ hδ w hw) hq
    (fun n => fineRemainderDerivative k χ ε δ ((standardLift k)^[n] w))
    (fun n v hv => fineRemainderDerivative_bound k χ ε hδ _ (hw n) (fine_regular_lift_next k χ ε w hw n) hv) hδ.le
  · intro n v u _ _
    exact fineRemainder_taylor k χ ε hδ _ (hw n) (fine_regular_lift_next k χ ε w hw n) v u
  · intro n v u _ _
    exact fineRemainderDerivative_lipschitz k χ ε hδ _ (hw n) (fine_regular_lift_next k χ ε w hw n) v u
lemma fineStableCurve_contDiffOn (k χ ε δ : ℝ) (hδ : 0<δ) (hq : Real.exp (-χ+ε)+δ<1)
    (w : ℂ) (hw : ∀ n : ℕ, FineRegular k χ ε (complexProjection ((standardLift k)^[n] w))) :
    ContDiffOn ℝ 1 (fineStableCurve k χ ε δ hδ hq w hw) (Ioo (-1 : ℝ) 1) :=
  contDiffOn_const.add ((fineFrame k χ ε δ (complexProjection w)).contDiff.comp_contDiffOn
    (contDiffOn_id.prodMk (fineStableGraph_contDiffOn k χ ε δ hδ hq w hw)))

theorem fineStableCurve_unique (k χ ε δ : ℝ) (hδ : 0<δ) (hq : Real.exp (-χ+ε)+δ<1)
    (w p : ℂ) (hw : ∀ n : ℕ, FineRegular k χ ε (complexProjection ((standardLift k)^[n] w)))
    (hp : ∀ n : ℕ, ‖fineCoordinate k χ ε δ w p n‖≤1) :
    p=fineStableCurve k χ ε δ hδ hq w hw (fineCoordinate k χ ε δ w p 0).1 := by
  let x : Sequence := BoundedContinuousFunction.ofNormedAddCommGroupDiscrete
    (fineCoordinate k χ ε δ w p) 1 hp
  have hx : x=(fineLocalRecurrence k χ ε δ hδ w hw).extend.solution hq (x 0).1 := by
    apply solution_unique
    · rfl
    · intro n
      change fineCoordinate k χ ε δ w p (n+1)=
        (fineLocalRecurrence k χ ε δ hδ w hw).extend.step n (fineCoordinate k χ ε δ w p n)
      rw [extend_step_eq _ n (hp n),fineCoordinate_step]
  have hi := congrArg (fun u : Sequence => u 0) hx
  have he : x 0=((x 0).1,fineStableGraph k χ ε δ hδ hq w hw (x 0).1) := by
    exact hi.trans (Prod.ext (solution_initial _ hq _) rfl)
  have he' := congrArg (fun v => w+fineFrame k χ ε δ (complexProjection w) v) he
  change w+fineFrame k χ ε δ (complexProjection w)
    (fineInverse k χ ε δ (complexProjection w) (p-w))=_ at he'
  have hw0 : FineRegular k χ ε (complexProjection w) := hw 0
  rw [fineFrame_inverse k χ ε hδ _ hw0.1] at he'
  have hx0 : x 0=fineCoordinate k χ ε δ w p 0 := rfl
  rw [hx0] at he'
  dsimp only [fineStableCurve]
  simpa only [add_sub_cancel] using he'

end StandardMapEntropy

end
section
namespace StandardMapEntropy
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
open NonlinearStable

lemma slow_sequence_ratio {a : ℕ → ℝ} {b : ℝ} (hb : 0≤b)
    (h : ∀ n : ℕ, a n≤b*a (n+1)) (n : ℕ) : a 0≤b^n*a n := by
  induction n with
  | zero => simp
  | succ n ih =>
    apply ih.trans
    exact (mul_le_mul_of_nonneg_left (h n) (pow_nonneg hb n)).trans_eq (by rw [pow_succ]; ring)

lemma fineInverse_forward_radius_bound (k χ ε δ : ℝ) (hδ : 0<δ) (w : ℂ)
    (hw : ∀ n : ℕ, FineRegular k χ ε (complexProjection ((standardLift k)^[n] w))) (n : ℕ) :
    ‖fineInverse k χ ε δ (complexProjection ((standardLift k)^[n] w))‖*
      codingRadius k χ ε δ (complexProjection w)≤(Real.exp (2*ε))^n/100 := by
  have hstep (j : ℕ) : codingRadius k χ ε δ (complexProjection ((standardLift k)^[j] w))≤
      Real.exp (2*ε)*codingRadius k χ ε δ (complexProjection ((standardLift k)^[j+1] w)) := by
    simpa only [Function.iterate_succ_apply',complexProjection_standardLift] using
      (codingRadius_ratio k χ ε hδ _ (hw j)).1
  have hr := slow_sequence_ratio (Real.exp_pos (2*ε)).le hstep n
  calc
    _ ≤ ‖fineInverse k χ ε δ (complexProjection ((standardLift k)^[n] w))‖*
        ((Real.exp (2*ε))^n*codingRadius k χ ε δ (complexProjection ((standardLift k)^[n] w))) :=
      mul_le_mul_of_nonneg_left hr (norm_nonneg _)
    _ = (Real.exp (2*ε))^n*(‖fineInverse k χ ε δ (complexProjection ((standardLift k)^[n] w))‖*
        codingRadius k χ ε δ (complexProjection ((standardLift k)^[n] w))) := by ring
    _ ≤ (Real.exp (2*ε))^n*(1/100) :=
      mul_le_mul_of_nonneg_left (fineInverse_codingRadius k χ ε hδ _ (hw n)) (by positivity)
    _ = _ := by ring

lemma fineCoordinate_tracking_difference (k χ ε δ : ℝ) (hδ : 0<δ) (w p p' : ℂ)
    (hw : ∀ n : ℕ, FineRegular k χ ε (complexProjection ((standardLift k)^[n] w)))
    {D r : ℝ} (hD : 0≤D) (hr : 0 ≤ r) (hslow : Real.exp (2*ε)*r≤1)
    (htrack : ∀ n : ℕ, ‖(standardLift k)^[n] p-(standardLift k)^[n] p'‖≤D*r^n) (n : ℕ) :
    ‖fineCoordinate k χ ε δ w p n-fineCoordinate k χ ε δ w p' n‖≤
      D/(100*codingRadius k χ ε δ (complexProjection w)) := by
  let R := codingRadius k χ ε δ (complexProjection w)
  have hR : 0<R := codingRadius_pos k χ ε hδ _
  have hI := fineInverse_forward_radius_bound k χ ε δ hδ w hw n
  have hI' : ‖fineInverse k χ ε δ (complexProjection ((standardLift k)^[n] w))‖≤
      (Real.exp (2*ε))^n/(100*R) := by
    apply (le_div_iff₀ (mul_pos (by norm_num) hR)).mpr
    dsimp [R] at ⊢
    nlinarith
  have hpow : (Real.exp (2*ε)*r)^n≤1 := pow_le_one₀ (mul_nonneg (Real.exp_pos _).le hr) hslow
  have he : fineCoordinate k χ ε δ w p n-fineCoordinate k χ ε δ w p' n=
      fineInverse k χ ε δ (complexProjection ((standardLift k)^[n] w))
        ((standardLift k)^[n] p-(standardLift k)^[n] p') := by
    dsimp only [fineCoordinate]
    rw [←map_sub,sub_sub_sub_cancel_right]
  rw [he]
  calc
    _ ≤ ‖fineInverse k χ ε δ (complexProjection ((standardLift k)^[n] w))‖*
        ‖(standardLift k)^[n] p-(standardLift k)^[n] p'‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ ((Real.exp (2*ε))^n/(100*R))*(D*r^n) := mul_le_mul hI' (htrack n) (norm_nonneg _) (by positivity)
    _ = (D/(100*R))*(Real.exp (2*ε)*r)^n := by rw [mul_pow]; ring
    _ ≤ (D/(100*R))*1 := mul_le_mul_of_nonneg_left hpow (by positivity)
    _ = _ := mul_one _

lemma fineStableCoordinate_bound (k χ ε δ : ℝ) (hδ : 0<δ) (hq : Real.exp (-χ+ε)+δ<1)
    (w : ℂ) (hw : ∀ n : ℕ, FineRegular k χ ε (complexProjection ((standardLift k)^[n] w)))
    {s : ℝ} (hs : |s|≤1) (n : ℕ) :
    ‖fineCoordinate k χ ε δ w (fineStableCurve k χ ε δ hδ hq w hw s) n‖≤|s| := by
  rw [fineStableCoordinate k χ ε δ hδ hq w hw hs n]
  exact ((fineLocalRecurrence k χ ε δ hδ w hw).extend.solution hq s).norm_coe_le_norm n |>.trans
    (solution_norm_bound _ hq s)

end StandardMapEntropy

end
section
namespace StandardMapEntropy.NonlinearStable
open Set Filter
open scoped Topology NNReal
variable {ℓ δ : ℝ≥0}

lemma perronApprox_eq_iterate (r : Recurrence ℓ δ) (hℓ : ℓ≤1) (s : ℝ) (N n : ℕ) :
    r.perronApprox s N n=((r.perron hℓ s)^[N] 0) n := by
  induction N generalizing n with
  | zero => rfl
  | succ N ih =>
    rw [Function.iterate_succ_apply']
    simp only [Recurrence.perronApprox,perron_apply,Recurrence.perronValue,ih] <;> rfl

lemma perronApprox_error (r : Recurrence ℓ δ) (h : ℓ+δ<1) (s : ℝ) (N n : ℕ) :
    ‖r.perronApprox s N n-r.solution h s n‖≤((ℓ+δ : ℝ≥0) : ℝ)^N*|s| := by
  let hℓ : ℓ≤1 := le_trans (le_add_of_nonneg_right (show (0 : ℝ≥0)≤δ from bot_le)) h.le
  have hc := (perron_contracting r h (s := s)).2.iterate N
  have he : (r.perron hℓ s)^[N] (r.solution h s)=r.solution h s :=
    by
      clear hc
      induction N with
      | zero => rfl
      | succ N ih => rw [Function.iterate_succ_apply',ih,solution_fixed]
  have hb := hc.dist_le_mul 0 (r.solution h s)
  rw [he,dist_zero_left,dist_eq_norm,NNReal.coe_pow] at hb
  rw [perronApprox_eq_iterate r hℓ]
  apply (point_sub_bound _ _ n).trans
  exact hb.trans (mul_le_mul_of_nonneg_left (solution_norm_bound r h s) (by positivity))

lemma continuous_perronApprox {X : Type*} [TopologicalSpace X] (r : X → Recurrence ℓ δ)
    (hA : ∀ n, Continuous (fun x => (r x).a n))
    (hB : ∀ n, Continuous (fun x => ((r x).b n)⁻¹))
    (hR : ∀ n, Continuous (fun p : X×Plane => (r p.1).remainder n p.2)) (N n : ℕ) :
    Continuous (fun p : X×ℝ => (r p.1).perronApprox p.2 N n) := by
  induction N generalizing n with
  | zero => exact continuous_const
  | succ N ih =>
    have hm (j : ℕ) : Continuous (fun p : X×ℝ => (r p.1).remainder j ((r p.1).perronApprox p.2 N j)) :=
      (hR j).comp (continuous_fst.prodMk (ih j))
    apply Continuous.prodMk
    · cases n with
      | zero => exact continuous_snd
      | succ m => exact ((hA m).comp continuous_fst |>.mul (ih m).fst).add (hm m).fst
    · exact ((hB n).comp continuous_fst).mul ((ih (n+1)).snd.sub (hm n).snd)

theorem continuous_solution_eval_on_strip {X : Type*} [TopologicalSpace X]
    (r : X → Recurrence ℓ δ) (h : ℓ+δ<1)
    (hA : ∀ n, Continuous (fun x => (r x).a n))
    (hB : ∀ n, Continuous (fun x => ((r x).b n)⁻¹))
    (hR : ∀ n, Continuous (fun p : X×Plane => (r p.1).remainder n p.2)) (n : ℕ) :
    Continuous (fun p : X×Icc (-1 : ℝ) 1 => (r p.1).solution h p.2 n) := by
  let f (N : ℕ) (p : X×Icc (-1 : ℝ) 1) := (r p.1).perronApprox p.2 N n
  have hf (N : ℕ) : Continuous (f N) :=
    (continuous_perronApprox r hA hB hR N n).comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
  have hq0 : 0≤((ℓ+δ : ℝ≥0) : ℝ) := (ℓ+δ).coe_nonneg
  have hpow := tendsto_pow_atTop_nhds_zero_of_lt_one hq0 (show ((ℓ+δ : ℝ≥0) : ℝ)<1 from h)
  have ht : TendstoUniformly f (fun p : X×Icc (-1 : ℝ) 1 => (r p.1).solution h p.2 n) atTop := by
    rw [Metric.tendstoUniformly_iff]
    intro ε hε
    filter_upwards [hpow.eventually (gt_mem_nhds hε)] with N hN
    intro p
    have hs : |(p.2 : ℝ)|≤1 := abs_le.mpr p.2.2
    have he := (perronApprox_error (r p.1) h (p.2 : ℝ) N n).trans
      ((mul_le_mul_of_nonneg_left hs (pow_nonneg hq0 N)).trans_eq (mul_one _))
    change ‖(r p.1).solution h (p.2 : ℝ) n-(r p.1).perronApprox (p.2 : ℝ) N n‖<ε
    rw [norm_sub_rev]
    exact he.trans_lt hN
  exact ht.continuous (Filter.Eventually.frequently (Filter.Eventually.of_forall hf))

end StandardMapEntropy.NonlinearStable

end
section
namespace StandardMapEntropy
open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal
open NonlinearStable

lemma continuous_complexProjection : Continuous complexProjection :=
  ((AddCircle.continuous_mk' (1 : ℝ)).comp Complex.continuous_re).prodMk
    ((AddCircle.continuous_mk' (1 : ℝ)).comp Complex.continuous_im)
lemma continuous_liftRemainder (k : ℝ) : Continuous (fun p : ℂ × ℂ => liftRemainder k p.1 p.2) :=
  (((contDiff_standardLift k).continuous.comp (continuous_fst.add continuous_snd)).sub
    ((contDiff_standardLift k).continuous.comp continuous_fst)).sub
    (((continuous_standardDerivative k).comp (continuous_complexProjection.comp continuous_fst)).clm_apply continuous_snd)

lemma continuous_fineFrame_of_data {X : Type*} [TopologicalSpace X] (k χ ε δ : ℝ)
    (z : X → Torus) (h : Continuous (fun x => lyapunovChartData k χ ε (z x))) :
    Continuous (fun x => fineFrame k χ ε δ (z x)) :=
  ((continuous_const.mul h.snd.snd).smul h.fst).clm_comp continuous_const
lemma continuous_fineInverse_of_data {X : Type*} [TopologicalSpace X] (k χ ε δ : ℝ) (hδ : 0<δ)
    (z : X → Torus) (h : Continuous (fun x => lyapunovChartData k χ ε (z x))) :
    Continuous (fun x => fineInverse k χ ε δ (z x)) :=
  continuous_const.clm_comp (((continuous_const.mul h.snd.snd).inv₀
    (fun x => (fineSize_pos k χ ε hδ (z x)).ne')).smul h.snd.fst)

theorem continuous_fineStableCurve_family {X : Type*} [TopologicalSpace X]
    (k χ ε δ : ℝ) (hδ : 0<δ) (hq : Real.exp (-χ+ε)+δ<1)
    (w : X → ℂ) (hwc : Continuous w)
    (hw : ∀ x, ∀ n : ℕ, FineRegular k χ ε (complexProjection ((standardLift k)^[n] (w x))))
    (hdata : ∀ n : ℕ, Continuous (fun x => lyapunovChartData k χ ε
      (complexProjection ((standardLift k)^[n] (w x))))) :
    Continuous (fun p : X×Icc (-1 : ℝ) 1 => fineStableCurve k χ ε δ hδ hq (w p.1) (hw p.1) p.2) := by
  let z (n : ℕ) (x : X) := complexProjection ((standardLift k)^[n] (w x))
  have hzc (n : ℕ) : Continuous (z n) :=
    continuous_complexProjection.comp (((contDiff_standardLift k).continuous.iterate n).comp hwc)
  have hF (n : ℕ) : Continuous (fun x => fineFrame k χ ε δ (z n x)) :=
    continuous_fineFrame_of_data k χ ε δ _ (hdata n)
  have hI (n : ℕ) : Continuous (fun x => fineInverse k χ ε δ (z n x)) :=
    continuous_fineInverse_of_data k χ ε δ hδ _ (hdata n)
  have hNext (n : ℕ) : Continuous (fun x => fineInverse k χ ε δ (standardMap k (z n x))) := by
    simpa only [z,Function.iterate_succ_apply',complexProjection_standardLift] using hI (n+1)
  have hDc (n : ℕ) : Continuous (fun x => standardDerivative k (z n x)) :=
    (continuous_standardDerivative k).comp (hzc n)
  have hA (n : ℕ) : Continuous (fun x => fineStableMultiplier k χ ε δ (z n x)) := by
    have hc := ((hNext n).clm_apply ((hDc n).clm_apply ((hF n).clm_apply
      (continuous_const : Continuous (fun _ : X => ((1,0) : RealPlane)))))).fst
    have he : (fun x => (fineInverse k χ ε δ (standardMap k (z n x))
        (standardDerivative k (z n x) (fineFrame k χ ε δ (z n x) (1,0)))).1)=
        (fun x => fineStableMultiplier k χ ε δ (z n x)) := by
      funext x
      simpa only [mul_one] using congrArg Prod.fst (fine_derivative_diagonal k χ ε δ (z n x) (hw x n) (1,0))
    rwa [he] at hc
  have hB (n : ℕ) : Continuous (fun x => (fineUnstableMultiplier k χ ε δ (z n x))⁻¹) := by
    have hc := ((hNext n).clm_apply ((hDc n).clm_apply ((hF n).clm_apply
      (continuous_const : Continuous (fun _ : X => ((0,1) : RealPlane)))))).snd
    have he : (fun x => (fineInverse k χ ε δ (standardMap k (z n x))
        (standardDerivative k (z n x) (fineFrame k χ ε δ (z n x) (0,1)))).2)=
        (fun x => fineUnstableMultiplier k χ ε δ (z n x)) := by
      funext x
      simpa only [mul_one] using congrArg Prod.snd (fine_derivative_diagonal k χ ε δ (z n x) (hw x n) (0,1))
    rw [he] at hc
    exact hc.inv₀ (fun x => fineUnstableMultiplier_ne k χ ε hδ _ (hw x n))
  have hR (n : ℕ) : Continuous (fun p : X×RealPlane => fineRemainder k χ ε δ
      ((standardLift k)^[n] (w p.1)) p.2) := by
    have hW : Continuous (fun x : X => (standardLift k)^[n] (w x)) :=
      ((contDiff_standardLift k).continuous.iterate n).comp hwc
    exact ((hNext n).comp continuous_fst).clm_apply ((continuous_liftRemainder k).comp
      ((hW.comp continuous_fst).prodMk (((hF n).comp continuous_fst).clm_apply continuous_snd)))
  let r (x : X) := (fineLocalRecurrence k χ ε δ hδ (w x) (hw x)).extend
  have hR' (n : ℕ) : Continuous (fun p : X×Plane => (r p.1).remainder n p.2) :=
    (hR n).comp (continuous_fst.prodMk (planeClip_lipschitz.continuous.comp continuous_snd))
  have hs := continuous_solution_eval_on_strip r hq hA hB hR' 0
  have hFrame : Continuous (fun p : X×Icc (-1 : ℝ) 1 => fineFrame k χ ε δ (complexProjection (w p.1))) :=
    (hF 0).comp continuous_fst
  exact (hwc.comp continuous_fst).add (hFrame.clm_apply
    ((continuous_subtype_val.comp continuous_snd).prodMk hs.snd))

end StandardMapEntropy

end
end

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_Holonomy_FiniteOrbitDecay
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace StandardMapEntropy.NonlinearStable
open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal
variable {ℓ δ : ℝ≥0}

lemma Recurrence.stable_cone_backward (r : Recurrence ℓ δ) (h : ℓ+δ<1) (n : ℕ) (v : Plane)
    (hv : |(r.step n v).2|≤|(r.step n v).1|) :
    |v.2|≤|v.1| ∧ ‖r.step n v‖≤((ℓ+δ : ℝ≥0) : ℝ)*‖v‖ := by
  let q : ℝ := ((ℓ+δ : ℝ≥0) : ℝ)
  have hq0 : 0≤q := (ℓ+δ).coe_nonneg
  have hq1 : q<1 := h
  have hn : ‖r.step n v‖=|(r.step n v).1| := max_eq_left hv
  have hf : ‖r.step n v‖≤q*‖v‖ := by
    rw [hn]
    simpa only [r.step_zero,Prod.fst_zero,sub_zero] using step_fst_sub_bound r n v 0
  refine ⟨?_,hf⟩
  by_contra hc
  have hc' : |v.1| < |v.2| := lt_of_not_ge hc
  have hp : 0<‖v‖ := by
    rw [show ‖v‖=|v.2| from max_eq_right hc'.le]
    exact (abs_nonneg _).trans_lt hc'
  have hb := (r.unstable_cone_step h n v 0 (by simpa only [Prod.fst_zero,Prod.snd_zero,sub_zero] using hc'.le)).2
  simp only [r.step_zero,Prod.snd_zero,sub_zero] at hb
  have hnb : ‖v‖≤q*‖r.step n v‖ := by
    rw [show ‖v‖=|v.2| from max_eq_right hc'.le]
    have hsnd : |(r.step n v).2|≤‖r.step n v‖ := norm_snd_le (r.step n v)
    exact hb.trans (mul_le_mul_of_nonneg_left hsnd hq0)
  have hh := mul_le_mul_of_nonneg_left hf hq0
  have hsqr : q*q<1 := by nlinarith
  nlinarith

lemma Recurrence.stable_orbit_bound (r : Recurrence ℓ δ) (h : ℓ+δ<1) (v : Plane) (n : ℕ)
    (hv : |(r.orbit v n).2|≤|(r.orbit v n).1|) :
    ‖r.orbit v n‖≤((ℓ+δ : ℝ≥0) : ℝ)^n*‖v‖ := by
  induction n with
  | zero => simp only [Recurrence.orbit,pow_zero,one_mul,le_refl]
  | succ n ih =>
    have hh := r.stable_cone_backward h n (r.orbit v n) hv
    exact hh.2.trans ((mul_le_mul_of_nonneg_left (ih hh.1) (ℓ+δ).coe_nonneg).trans_eq (by rw [pow_succ]; ring))

lemma Recurrence.unstable_orbit_bound (r : Recurrence ℓ δ) (h : ℓ+δ<1) (v : Plane)
    (hv : |v.1|≤|v.2|) (n : ℕ) :
    ‖v‖≤((ℓ+δ : ℝ≥0) : ℝ)^n*‖r.orbit v n‖ := by
  induction n with
  | zero => simp only [Recurrence.orbit,pow_zero,one_mul,le_refl]
  | succ n ih =>
    have hh := (r.orbit_cone h hv n).2
    rw [←r.orbit_norm_eq_snd h hv n,←r.orbit_norm_eq_snd h hv (n+1)] at hh
    exact ih.trans ((mul_le_mul_of_nonneg_left hh (pow_nonneg (ℓ+δ).coe_nonneg n)).trans_eq (by rw [pow_succ]; ring))

lemma Recurrence.orbit_tail (r : Recurrence ℓ δ) (v : Plane) (j n : ℕ) :
    (r.tail j).orbit (r.orbit v j) n=r.orbit v (j+n) := by
  induction n with
  | zero => simp only [Recurrence.orbit,Nat.add_zero]
  | succ n ih =>
    rw [Recurrence.orbit,Nat.add_succ,Recurrence.orbit,ih]
    rfl

lemma Recurrence.trappedBox_two_ended (r : Recurrence ℓ δ) (h : ℓ+δ<1) {N : ℕ} {v : Plane}
    (hv : v∈r.trappedBox N) {j : ℕ} (hj : j≤N) :
    ‖r.orbit v j‖≤((ℓ+δ : ℝ≥0) : ℝ)^j+((ℓ+δ : ℝ≥0) : ℝ)^(N-j) := by
  rcases le_total |(r.orbit v j).1| |(r.orbit v j).2| with hc|hc
  · have hh := (r.tail j).unstable_orbit_bound h (r.orbit v j) hc (N-j)
    rw [r.orbit_tail,Nat.add_sub_of_le hj] at hh
    have he := hh.trans ((mul_le_mul_of_nonneg_left (hv N le_rfl) (pow_nonneg (ℓ+δ).coe_nonneg _)).trans_eq (mul_one _))
    exact he.trans (le_add_of_nonneg_left (pow_nonneg (ℓ+δ).coe_nonneg j))
  · have hh := r.stable_orbit_bound h v j hc
    have he := hh.trans ((mul_le_mul_of_nonneg_left (hv 0 (Nat.zero_le N)) (pow_nonneg (ℓ+δ).coe_nonneg _)).trans_eq (mul_one _))
    exact he.trans (le_add_of_nonneg_right (pow_nonneg (ℓ+δ).coe_nonneg (N-j)))

lemma geometric_partial_bound {q : ℝ} (hq0 : 0≤q) (hq1 : q<1) (N : ℕ) :
    (∑ j ∈ Finset.range N,q^j)≤1/(1-q) := by
  apply (le_div_iff₀ (sub_pos.mpr hq1)).mpr
  rw [geom_sum_mul_neg]
  linarith [pow_nonneg hq0 N]

lemma Recurrence.trappedBox_sum_norm (r : Recurrence ℓ δ) (h : ℓ+δ<1) {N : ℕ} {v : Plane}
    (hv : v∈r.trappedBox N) :
    (∑ j ∈ Finset.range N,‖r.orbit v j‖)≤2/(1-((ℓ+δ : ℝ≥0) : ℝ)) := by
  let q : ℝ := ((ℓ+δ : ℝ≥0) : ℝ)
  have hq0 : 0≤q := (ℓ+δ).coe_nonneg
  have hq1 : q<1 := h
  have hb : (∑ j ∈ Finset.range N,q^(N-j))≤1/(1-q) := by
    have hh := StandardMapEntropy.sum_of_backward_contraction (fun j => q^(N-j)) (fun _ => pow_nonneg hq0 _)
      hq0 hq1 N (fun j hj => ?_)
    · simpa only [Nat.sub_self,pow_zero] using hh
    · have he : N-j=N-(j+1)+1 := by omega
      rw [he,pow_succ]
      exact le_of_eq (mul_comm _ _)
  calc
    _ ≤ ∑ j ∈ Finset.range N,(q^j+q^(N-j)) :=
      Finset.sum_le_sum fun j hj => r.trappedBox_two_ended h hv (Finset.mem_range.mp hj).le
    _ = (∑ j ∈ Finset.range N,q^j)+(∑ j ∈ Finset.range N,q^(N-j)) := Finset.sum_add_distrib
    _ ≤ 1/(1-q)+1/(1-q) := add_le_add (geometric_partial_bound hq0 hq1 N) hb
    _ = _ := by ring

end StandardMapEntropy.NonlinearStable

end
section
namespace StandardMapEntropy.NonlinearStable
open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal
variable {ℓ δ : ℝ≥0}

lemma scalar_log_relative_error {b y e d : ℝ} (hb : 1≤|b|) (hy : y≠0)
    (hd0 : 0≤d) (hd1 : d≤1/2) (he : |e|≤d*|y|) :
    abs (Real.log |b*y+e|-Real.log |b|-Real.log |y|)≤2*d := by
  have hyp : 0 < |y| := abs_pos.mpr hy
  have hbp : 0 < |b| := lt_of_lt_of_le zero_lt_one hb
  have hsmall : |e|≤|y|/2 := he.trans (by
    nlinarith [mul_le_mul hd1 (le_refl |y|) hyp.le (hd0.trans hd1)])
  have hlower : |y|/2≤|b*y+e| := by
    have hh : |b*y|≤|b*y+e|+|e| := by
      simpa only [add_sub_cancel_right] using abs_sub (b*y+e) e
    rw [abs_mul] at hh
    have hb' := mul_le_mul_of_nonneg_right hb (abs_nonneg y)
    nlinarith
  have hD : 0<2/|y| := div_pos (by norm_num) hyp
  have hx : 1≤(2/|y|)*|b*y+e| := by
    have hc := mul_le_mul_of_nonneg_left hlower hD.le
    have heq : (2/|y|)*(|y|/2)=1 := by field_simp
    rwa [heq] at hc
  have hb' : 1≤(2/|y|)*|b*y| := by
    rw [abs_mul]
    have heq : (2/|y|)*(|b| *|y|)=2*|b| := by field_simp
    rw [heq]; linarith
  have hl := StandardMapEntropy.log_difference_of_lower hD hx hb'
  have hnorm : abs (|b*y+e|-|b*y|)≤|e| := by
    simpa only [add_sub_cancel_left] using abs_abs_sub_abs_le_abs_sub (b*y+e) (b*y)
  have hh := hl.trans (mul_le_mul_of_nonneg_left (hnorm.trans he) hD.le)
  rw [abs_mul,Real.log_mul hbp.ne' hyp.ne'] at hh
  have hright : (2/|y|)*(d*|y|)=2*d := by field_simp
  rw [hright] at hh
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  ring

lemma LocalRecurrence.trueOrbit_eq_extend (r : LocalRecurrence ℓ δ) {v : Plane} {N : ℕ}
    (hv : v∈r.extend.trappedBox N) {n : ℕ} (hn : n≤N) : r.trueOrbit v n=r.extend.orbit v n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [LocalRecurrence.trueOrbit,ih (by omega),Recurrence.orbit,extend_step_eq _ n (hv n (by omega))]

end StandardMapEntropy.NonlinearStable

end
section
namespace StandardMapEntropy.NonlinearStable
open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal
variable {ℓ δ : ℝ≥0}

lemma continuous_injective_abs_sub_le {f : ℝ → ℝ} (hc : Continuous f)
    (hi : Function.Injective f) {s t u : ℝ} (hst : s≤t) (htu : t≤u) :
    |f t-f s|≤|f u-f s| := by
  rcases hc.strictMono_of_inj hi with hm | hm
  · rw [abs_of_nonneg (sub_nonneg.mpr (hm.monotone hst)),
      abs_of_nonneg (sub_nonneg.mpr (hm.monotone (hst.trans htu)))]
    exact sub_le_sub_right (hm.monotone htu) _
  · rw [abs_of_nonpos (sub_nonpos.mpr (hm.antitone hst)),
      abs_of_nonpos (sub_nonpos.mpr (hm.antitone (hst.trans htu)))]
    linarith [hm.antitone htu]

end StandardMapEntropy.NonlinearStable

end
section
namespace StandardMapEntropy.NonlinearStable
open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal
variable {ℓ δ : ℝ≥0}

lemma LocalRecurrence.trueOrbit_continuous (r : LocalRecurrence ℓ δ)
    (hc : ∀ j, Continuous (r.remainder j)) (n : ℕ) : Continuous (fun v => r.trueOrbit v n) := by
  induction n with
  | zero => exact continuous_id
  | succ n ih =>
    exact ((continuous_const.mul ih.fst).add ((hc n).comp ih).fst).prodMk
      ((continuous_const.mul ih.snd).add ((hc n).comp ih).snd)

lemma exp_bounds_of_log_error {J A C : ℝ} (hJ : J≠0) (h : |Real.log |J|-A|≤C) :
    Real.exp (A-C)≤|J| ∧ |J|≤Real.exp (A+C) := by
  have hh := abs_le.mp h
  have hpos := abs_pos.mpr hJ
  constructor
  · rw [←Real.exp_log hpos]
    exact Real.exp_le_exp.mpr (by linarith)
  · rw [←Real.exp_log hpos]
    exact Real.exp_le_exp.mpr (by linarith)

end StandardMapEntropy.NonlinearStable

end
section
namespace StandardMapEntropy.NonlinearStable
open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal
variable {ℓ δ : ℝ≥0}

lemma Recurrence.orbit_pair_cone (r : Recurrence ℓ δ) (h : ℓ+δ<1) {v w : Plane}
    (hv : |v.1-w.1|≤|v.2-w.2|) (n : ℕ) :
    |(r.orbit v n).1-(r.orbit w n).1|≤|(r.orbit v n).2-(r.orbit w n).2| ∧
    |v.2-w.2|≤((ℓ+δ : ℝ≥0) : ℝ)^n*|(r.orbit v n).2-(r.orbit w n).2| := by
  induction n with
  | zero => exact ⟨hv,by simp only [Recurrence.orbit,pow_zero,one_mul,le_refl]⟩
  | succ n ih =>
    have hh := r.unstable_cone_step h n (r.orbit v n) (r.orbit w n) ih.1
    refine ⟨hh.1,ih.2.trans ?_⟩
    exact (mul_le_mul_of_nonneg_left hh.2 (pow_nonneg (ℓ+δ).coe_nonneg n)).trans_eq
      (by simp only [Recurrence.orbit,pow_succ]; ring)
lemma affine_cone {V : Plane} (hV : |V.1|≤|V.2|) (p : Plane) (t u : ℝ) :
    |(p+t•V).1-(p+u•V).1|≤|(p+t•V).2-(p+u•V).2| := by
  have he : p+t•V-(p+u•V)=(t-u)•V := by rw [add_sub_add_left_eq_sub,sub_smul]
  change |(p+t•V-(p+u•V)).1|≤|(p+t•V-(p+u•V)).2|
  rw [he]
  change |(t-u)*V.1|≤|(t-u)*V.2|
  rw [abs_mul,abs_mul]
  exact mul_le_mul_of_nonneg_left hV (abs_nonneg _)

lemma Recurrence.affine_transverse_injective (r : Recurrence ℓ δ) (h : ℓ+δ<1)
    {V : Plane} (hV : |V.1|≤|V.2|) (hV0 : V.2≠0) (p : Plane) (n : ℕ) :
    Function.Injective (fun t : ℝ => (r.orbit (p+t•V) n).2) := by
  intro t u he
  change (r.orbit (p+t•V) n).2=(r.orbit (p+u•V) n).2 at he
  have hh := (r.orbit_pair_cone h (affine_cone hV p t u) n).2
  rw [he,sub_self,abs_zero,mul_zero] at hh
  have hz := sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm hh (abs_nonneg _)))
  simp only [Prod.snd_add] at hz
  exact (mul_left_inj' hV0).mp (add_left_cancel hz)

lemma Recurrence.affine_interval_trapped (r : Recurrence ℓ δ) (h : ℓ+δ<1)
    {V : Plane} (hV : |V.1|≤|V.2|) (hV0 : V.2≠0) (p : Plane)
    {t u v : ℝ} (htu : t≤u) (huv : u≤v) {N : ℕ}
    (ht : ∀ n : ℕ,n≤N → ‖r.orbit (p+t•V) n‖≤1/3)
    (hv : ∀ n : ℕ,n≤N → ‖r.orbit (p+v•V) n‖≤1/3) :
    p+u•V∈r.trappedBox N := by
  intro n hn
  have hc := (r.orbit_pair_cone h (affine_cone hV p u t) n).1
  have hd := continuous_injective_abs_sub_le
    ((r.orbit_continuous n).comp (continuous_const.add (continuous_id.smul continuous_const))).snd
    (r.affine_transverse_injective h hV hV0 p n) htu huv
  change |(r.orbit (p+u•V) n).2-(r.orbit (p+t•V) n).2|≤
    |(r.orbit (p+v•V) n).2-(r.orbit (p+t•V) n).2| at hd
  have ht' := norm_snd_le (r.orbit (p+t•V) n) |>.trans (ht n hn)
  have hv' := norm_snd_le (r.orbit (p+v•V) n) |>.trans (hv n hn)
  have hdiff : ‖r.orbit (p+u•V) n-r.orbit (p+t•V) n‖≤2/3 := by
    change max _ _ ≤ _
    simp only [Prod.fst_sub,Prod.snd_sub,Real.norm_eq_abs] at ht' hv' ⊢
    rw [max_eq_right hc]
    exact hd.trans ((abs_sub _ _).trans (by linarith))
  have hh := norm_add_le (r.orbit (p+u•V) n-r.orbit (p+t•V) n) (r.orbit (p+t•V) n)
  rw [sub_add_cancel] at hh
  linarith [ht n hn]

theorem LocalRecurrence.linearized_cone_log_distortion (r : LocalRecurrence ℓ δ) (h : ℓ+δ<1)
    (hδ : (δ : ℝ)≤1/2) (D : ℕ → Plane →L[ℝ] Plane) (hD : ∀ n, ‖D n‖≤δ)
    {N : ℕ} {v : Plane} (hv : v∈r.extend.trappedBox N)
    {V : Plane} (hcone : |V.1|≤|V.2|) (hnz : V.2≠0)
    (hsmall : ∀ j : ℕ,j<N → ‖D j‖≤(δ : ℝ)*‖r.extend.orbit v j‖) :
    abs (Real.log |((r.linearized D hD).orbit V N).2|-Real.log |V.2|-
      ∑ j ∈ Finset.range N,Real.log |r.b j|)≤4*(δ : ℝ)/(1-((ℓ+δ : ℝ≥0) : ℝ)) := by
  let R := r.linearized D hD
  let y := fun j : ℕ => |(R.orbit V j).2|
  have hstep (j : ℕ) (hj : j<N) :
      abs ((Real.log (y (j+1))-Real.log (y j))-Real.log |r.b j|)≤2*(δ : ℝ)*‖r.extend.orbit v j‖ := by
    have hy := R.orbit_snd_ne_zero h (v := V) hcone hnz j
    have hδj : (δ : ℝ)*‖r.extend.orbit v j‖≤1/2 :=
      ((mul_le_mul_of_nonneg_left (hv j hj.le) δ.coe_nonneg).trans_eq (mul_one _)).trans hδ
    have he : |(D j (R.orbit V j)).2|≤
        ((δ : ℝ)*‖r.extend.orbit v j‖)*|(R.orbit V j).2| := by
      have hh := (norm_snd_le (D j (R.orbit V j))).trans
        (((D j).le_opNorm _).trans (mul_le_mul_of_nonneg_right (hsmall j hj) (norm_nonneg _)))
      simpa only [Real.norm_eq_abs,R.orbit_norm_eq_snd h (v := V) hcone j] using hh
    have hb : 1≤|r.b j| := R.unstable_size_ge_one h j
    have hh := scalar_log_relative_error hb hy (mul_nonneg δ.coe_nonneg (norm_nonneg _)) hδj he
    change abs (Real.log |r.b j*(R.orbit V j).2+(D j (R.orbit V j)).2|-
      Real.log |(R.orbit V j).2|-Real.log |r.b j|)≤_
    convert hh using 1
    · congr 1; ring
    · ring
  have htel : (∑ j ∈ Finset.range N,((Real.log (y (j+1))-Real.log (y j))-Real.log |r.b j|))=
      Real.log (y N)-Real.log |V.2|-(∑ j ∈ Finset.range N,Real.log |r.b j|) := by
    rw [Finset.sum_sub_distrib,Finset.sum_range_sub (fun j => Real.log (y j))]
    rfl
  calc
    _ = abs (∑ j ∈ Finset.range N,((Real.log (y (j+1))-Real.log (y j))-Real.log |r.b j|)) := congrArg abs htel.symm
    _ ≤ ∑ j ∈ Finset.range N,abs ((Real.log (y (j+1))-Real.log (y j))-Real.log |r.b j|) := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ Finset.range N,2*(δ : ℝ)*‖r.extend.orbit v j‖ :=
      Finset.sum_le_sum fun j hj => hstep j (Finset.mem_range.mp hj)
    _ = (2*(δ : ℝ))*(∑ j ∈ Finset.range N,‖r.extend.orbit v j‖) := (Finset.mul_sum _ _ _).symm
    _ ≤ (2*(δ : ℝ))*(2/(1-((ℓ+δ : ℝ≥0) : ℝ))) :=
      mul_le_mul_of_nonneg_left (r.extend.trappedBox_sum_norm h hv) (by positivity)
    _ = _ := by ring

lemma LocalRecurrence.trueOrbit_affine_hasDerivAt (r : LocalRecurrence ℓ δ)
    (D : ℕ → Plane → Plane →L[ℝ] Plane)
    (hDeriv : ∀ j u, HasFDerivAt (r.remainder j) (D j u) u)
    (L : ℕ → Plane →L[ℝ] Plane) (hL : ∀ n, ‖L n‖≤δ)
    (p V : Plane) (x : ℝ) {N : ℕ} (hmatch : ∀ j : ℕ,j<N → L j=D j (r.trueOrbit (p+x•V) j))
    {n : ℕ} (hn : n≤N) :
    HasDerivAt (fun t : ℝ => r.trueOrbit (p+t•V) n) ((r.linearized L hL).orbit V n) x := by
  induction n with
  | zero =>
    have h1 : HasDerivAt (fun t : ℝ => p.1+t*V.1) V.1 x := by
      convert ((hasDerivAt_id x).mul_const V.1).const_add p.1 using 1 <;> first | rfl | simp only [one_mul]
    have h2 : HasDerivAt (fun t : ℝ => p.2+t*V.2) V.2 x := by
      convert ((hasDerivAt_id x).mul_const V.2).const_add p.2 using 1 <;> first | rfl | simp only [one_mul]
    exact h1.prodMk h2
  | succ n ih =>
    have hi := ih (by omega)
    have rem := (hDeriv n (r.trueOrbit (p+x•V) n)).comp_hasDerivAt x hi
    have hrem : HasDerivAt (fun t : ℝ => r.remainder n (r.trueOrbit (p+t•V) n))
        (L n ((r.linearized L hL).orbit V n)) x := by
      rw [hmatch n (by omega)]
      exact rem
    have hifst : HasDerivAt (fun t : ℝ => (r.trueOrbit (p+t•V) n).1)
        ((r.linearized L hL).orbit V n).1 x := by
      exact hi.fst
    have hisnd : HasDerivAt (fun t : ℝ => (r.trueOrbit (p+t•V) n).2)
        ((r.linearized L hL).orbit V n).2 x := by
      exact hi.snd
    have hrfst : HasDerivAt (fun t : ℝ => (r.remainder n (r.trueOrbit (p+t•V) n)).1)
        (L n ((r.linearized L hL).orbit V n)).1 x := by
      exact hrem.fst
    have hrsnd : HasDerivAt (fun t : ℝ => (r.remainder n (r.trueOrbit (p+t•V) n)).2)
        (L n ((r.linearized L hL).orbit V n)).2 x := by
      exact hrem.snd
    exact ((hifst.const_mul (r.a n)).add hrfst).prodMk
      ((hisnd.const_mul (r.b n)).add hrsnd)

end StandardMapEntropy.NonlinearStable

end
end

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_Holonomy_ConeIntervalDistortion
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace StandardMapEntropy.NonlinearStable
open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal
variable {ℓ δ : ℝ≥0}

lemma LocalRecurrence.trapped_affine_derivative (r : LocalRecurrence ℓ δ) (h : ℓ+δ<1)
    (hδ : (δ : ℝ)≤1/2) (D : ℕ → Plane → Plane →L[ℝ] Plane)
    (hd : ∀ n v, HasFDerivAt (r.remainder n) (D n v) v)
    (hsmall : ∀ n v, ‖v‖≤1 → ‖D n v‖≤(δ : ℝ)*‖v‖)
    (p V : Plane) (hcone : |V.1|≤|V.2|) (hV0 : V.2≠0)
    (x : ℝ) {N : ℕ} (hv : p+x•V∈r.extend.trappedBox N) :
    ∃ J : ℝ, HasDerivAt (fun t : ℝ => (r.trueOrbit (p+t•V) N).2) J x ∧
      J≠0 ∧ |Real.log |J|-Real.log |V.2|-(∑ j ∈ Finset.range N,Real.log |r.b j|)|≤
        4*(δ : ℝ)/(1-((ℓ+δ : ℝ≥0) : ℝ)) := by
  classical
  let L (n : ℕ) : Plane →L[ℝ] Plane := if n<N then D n (r.trueOrbit (p+x•V) n) else 0
  have hLs (n : ℕ) (hn : n<N) : ‖L n‖≤(δ : ℝ)*‖r.extend.orbit (p+x•V) n‖ := by
    dsimp only [L]
    rw [ite_eq_left hn,r.trueOrbit_eq_extend hv hn.le]
    exact hsmall n _ (hv n hn.le)
  have hL (n : ℕ) : ‖L n‖≤δ := by
    by_cases hn : n<N
    · exact (hLs n hn).trans ((mul_le_mul_of_nonneg_left (hv n hn.le) δ.coe_nonneg).trans_eq (mul_one _))
    · simp only [L,ite_eq_right hn,norm_zero]; exact δ.coe_nonneg
  let R := r.linearized L hL
  refine ⟨(R.orbit V N).2,?_,R.orbit_snd_ne_zero h hcone hV0 N,
    r.linearized_cone_log_distortion h hδ L hL hv hcone hV0 hLs⟩
  exact (r.trueOrbit_affine_hasDerivAt D hd L hL p V x (fun n hn => ite_eq_left hn) (le_refl N)).snd

theorem LocalRecurrence.affine_interval_distortion (r : LocalRecurrence ℓ δ) (h : ℓ+δ<1)
    (hδ : (δ : ℝ)≤1/2) (D : ℕ → Plane → Plane →L[ℝ] Plane)
    (hd : ∀ n v, HasFDerivAt (r.remainder n) (D n v) v)
    (hsmall : ∀ n v, ‖v‖≤1 → ‖D n v‖≤(δ : ℝ)*‖v‖)
    (p V : Plane) (hcone : |V.1|≤|V.2|) (hV0 : V.2≠0)
    {t u : ℝ} (htu : t≤u) {N : ℕ}
    (ht : ∀ n : ℕ,n≤N → ‖r.extend.orbit (p+t•V) n‖≤1/3)
    (hu : ∀ n : ℕ,n≤N → ‖r.extend.orbit (p+u•V) n‖≤1/3) :
    let A := Real.log |V.2|+∑ j ∈ Finset.range N,Real.log |r.b j|
    let C := 4*(δ : ℝ)/(1-((ℓ+δ : ℝ≥0) : ℝ))
    Real.exp (A-C)*(u-t)≤|(r.trueOrbit (p+u•V) N).2-(r.trueOrbit (p+t•V) N).2| ∧
      |(r.trueOrbit (p+u•V) N).2-(r.trueOrbit (p+t•V) N).2|≤Real.exp (A+C)*(u-t) := by
  dsimp only
  rcases htu.eq_or_lt with he | htu
  · subst u; simp
  let f : ℝ → ℝ := fun v => (r.trueOrbit (p+v•V) N).2
  have hfc : Continuous f := ((r.trueOrbit_continuous (fun n => continuous_iff_continuousAt.mpr
    fun v => (hd n v).continuousAt) N).comp (continuous_const.add (continuous_id.smul continuous_const))).snd
  have htrap (v : ℝ) (hv : v∈Icc t u) : (p+v•V)∈r.extend.trappedBox N :=
    r.extend.affine_interval_trapped h hcone hV0 p hv.1 hv.2 ht hu
  have hf (v : ℝ) (hv : v∈Icc t u) : ∃ J : ℝ, HasDerivAt f J v ∧ J≠0 ∧
      |Real.log |J|-Real.log |V.2|-(∑ j ∈ Finset.range N,Real.log |r.b j|)|≤
        4*(δ : ℝ)/(1-((ℓ+δ : ℝ≥0) : ℝ)) :=
    r.trapped_affine_derivative h hδ D hd hsmall p V hcone hV0 v (htrap v hv)
  obtain ⟨c,hc,he⟩ := exists_deriv_eq_slope f htu hfc.continuousOn
    (fun v hv => (hf v ⟨hv.1.le,hv.2.le⟩).choose_spec.1.differentiableAt.differentiableWithinAt)
  obtain ⟨J,hJ,hJn,hJL⟩ := hf c ⟨hc.1.le,hc.2.le⟩
  rw [hJ.deriv] at he
  have hab : f u-f t=J*(u-t) := (eq_div_iff (sub_ne_zero.mpr htu.ne')).mp he |>.symm
  have heq : |f u-f t|=|J| *(u-t) := by rw [hab,abs_mul,abs_of_pos (sub_pos.mpr htu)]
  change _≤|f u-f t| ∧ |f u-f t|≤_
  rw [heq]
  have hJL' : |Real.log |J|-(Real.log |V.2|+∑ j ∈ Finset.range N,Real.log |r.b j|)|≤
      4*(δ : ℝ)/(1-((ℓ+δ : ℝ≥0) : ℝ)) := by
    convert hJL using 1
    all_goals try with_reducible_and_instances rfl
    congr 1
    ring
  have hb := exp_bounds_of_log_error hJn hJL'
  exact ⟨mul_le_mul_of_nonneg_right hb.1 (sub_nonneg.mpr htu.le),
    mul_le_mul_of_nonneg_right hb.2 (sub_nonneg.mpr htu.le)⟩

end StandardMapEntropy.NonlinearStable

end
section
namespace StandardMapEntropy.NonlinearStable
open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal
variable {ℓ δ : ℝ≥0}

lemma Recurrence.pair_norm_eq_snd (r : Recurrence ℓ δ) (h : ℓ+δ<1) {v w : Plane}
    (hv : |v.1-w.1|≤|v.2-w.2|) (n : ℕ) :
    ‖r.orbit v n-r.orbit w n‖=|(r.orbit v n).2-(r.orbit w n).2| := by
  change max _ _ = _
  exact max_eq_right (r.orbit_pair_cone h hv n).1

lemma Recurrence.exists_orbit_escape (r : Recurrence ℓ δ) (h : ℓ+δ<1) {v w : Plane}
    (hv : |v.1-w.1|≤|v.2-w.2|) (hne : v.2≠w.2)
    {R : ℝ} (hw : ∀ n, ‖r.orbit w n‖≤R) : ∃ n, R<‖r.orbit v n‖ := by
  by_contra hn
  push Not at hn
  have hbound (n : ℕ) : |v.2-w.2|≤((ℓ+δ : ℝ≥0) : ℝ)^n*(2*R) := by
    have hb : |(r.orbit v n).2-(r.orbit w n).2|≤2*R :=
      (abs_sub _ _).trans (by
        have h₁ := (norm_snd_le (r.orbit v n)).trans (hn n)
        have h₂ := (norm_snd_le (r.orbit w n)).trans (hw n)
        simp only [Real.norm_eq_abs] at h₁ h₂
        linarith)
    exact (r.orbit_pair_cone h hv n).2.trans (mul_le_mul_of_nonneg_left hb (by positivity))
  have ht := (tendsto_pow_atTop_nhds_zero_of_lt_one (ℓ+δ).coe_nonneg
    (show ((ℓ+δ : ℝ≥0) : ℝ)<1 from h)).mul_const (2*R)
  have hz : |v.2-w.2|≤0 := by simpa only [zero_mul] using
    (le_of_tendsto_of_tendsto tendsto_const_nhds ht (Filter.Eventually.of_forall hbound))
  exact (abs_pos.mpr (sub_ne_zero.mpr hne)).not_ge hz

lemma last_trapped_time {P : ℕ → Prop} [DecidablePred P] (hbad : ∃ n, ¬P n)
    {N₀ : ℕ} (hprefix : ∀ n, n≤N₀ → P n) :
    ∃ N : ℕ, N₀≤N ∧ (∀ n, n≤N → P n) ∧ ¬P (N+1) := by
  let j := Nat.find hbad
  have hj : ¬P j := Nat.find_spec hbad
  have hmin (n : ℕ) (hn : n<j) : P n := by
    exact not_not.mp (Nat.find_min hbad hn)
  have hNj : N₀<j := by
    by_contra hh
    exact hj (hprefix j (le_of_not_gt hh))
  refine ⟨j-1,by omega,?_,?_⟩
  · intro n hn; exact hmin n (by omega)
  · have he : j-1+1=j := by omega
    rwa [he]

lemma Recurrence.escape_vertical_lower (r : Recurrence ℓ δ) (h : ℓ+δ<1)
    {v w : Plane} (hc : |v.1-w.1|≤|v.2-w.2|)
    {M a : ℝ} (hM : 0<M) (ha : 0<a)
    (hstep : ∀ n u, ‖r.step n u‖≤M*a^n*‖u‖) {N : ℕ}
    (hescape : 1/3<‖r.orbit v (N+1)‖)
    (hw : ‖r.orbit w N‖≤1/(6*M*a^N)) :
    1/(6*M*a^N)< |(r.orbit v N).2-(r.orbit w N).2| := by
  have hp : 0<M*a^N := mul_pos hM (pow_pos ha N)
  have hl : 1/(3*M*a^N)<‖r.orbit v N‖ := by
    have hh := hescape.trans_le (hstep N (r.orbit v N))
    apply (div_lt_iff₀ (by positivity : 0<3*M*a^N)).mpr
    nlinarith
  have hh := norm_add_le (r.orbit v N-r.orbit w N) (r.orbit w N)
  rw [sub_add_cancel,r.pair_norm_eq_snd h hc] at hh
  have he : 1/(3*M*a^N)=1/(6*M*a^N)+1/(6*M*a^N) := by field_simp; ring
  rw [he] at hl
  linarith

lemma terminal_size_comparison {p₀ p₁ q₀ q₁ ρ : ℝ} (hρ : 0<ρ)
    (hl : ρ< |(p₁-p₀)| ∨ ρ< |(q₁-q₀)|)
    (hpair₀ : |p₀-q₀|≤ρ/4) (hpair₁ : |p₁-q₁|≤ρ/4) :
    |q₁-q₀|≤2* |p₁-p₀| ∧ |p₁-p₀|≤2* |q₁-q₀| := by
  have he : (p₁-p₀)-(q₁-q₀)=(p₁-q₁)-(p₀-q₀) := by ring
  have hh : abs (abs (p₁-p₀)-abs (q₁-q₀))≤ρ/2 :=
    (abs_abs_sub_abs_le_abs_sub _ _).trans (by
      rw [he]
      exact (abs_sub _ _).trans (by linarith))
  have hb := abs_le.mp hh
  rcases hl with hl|hl <;> constructor <;> linarith

end StandardMapEntropy.NonlinearStable

end
section
namespace StandardMapEntropy.NonlinearStable
open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal
variable {ℓ δ : ℝ≥0}

lemma LocalRecurrence.affine_interval_abs_distortion (r : LocalRecurrence ℓ δ) (h : ℓ+δ<1)
    (hδ : (δ : ℝ)≤1/2) (D : ℕ → Plane → Plane →L[ℝ] Plane)
    (hd : ∀ n v, HasFDerivAt (r.remainder n) (D n v) v)
    (hsmall : ∀ n v, ‖v‖≤1 → ‖D n v‖≤(δ : ℝ)*‖v‖)
    (p V : Plane) (hc : |V.1|≤|V.2|) (hV : V.2≠0)
    {t u : ℝ} {N : ℕ}
    (ht : ∀ n : ℕ,n≤N → ‖r.extend.orbit (p+t•V) n‖≤1/3)
    (hu : ∀ n : ℕ,n≤N → ‖r.extend.orbit (p+u•V) n‖≤1/3) :
    let A := Real.log |V.2|+∑ j ∈ Finset.range N,Real.log |r.b j|
    let C := 4*(δ : ℝ)/(1-((ℓ+δ : ℝ≥0) : ℝ))
    Real.exp (A-C)* |u-t|≤|(r.extend.orbit (p+u•V) N).2-(r.extend.orbit (p+t•V) N).2| ∧
      |(r.extend.orbit (p+u•V) N).2-(r.extend.orbit (p+t•V) N).2|≤Real.exp (A+C)* |u-t| := by
  dsimp only
  have ht' : p+t•V∈r.extend.trappedBox N := fun n hn => (ht n hn).trans (by norm_num)
  have hu' : p+u•V∈r.extend.trappedBox N := fun n hn => (hu n hn).trans (by norm_num)
  rcases le_total t u with htu|hut
  · have hh := r.affine_interval_distortion h hδ D hd hsmall p V hc hV htu ht hu
    rw [r.trueOrbit_eq_extend ht' le_rfl,r.trueOrbit_eq_extend hu' le_rfl] at hh
    simpa only [abs_of_nonneg (sub_nonneg.mpr htu)] using hh
  · have hh := r.affine_interval_distortion h hδ D hd hsmall p V hc hV hut hu ht
    rw [r.trueOrbit_eq_extend ht' le_rfl,r.trueOrbit_eq_extend hu' le_rfl] at hh
    rw [abs_sub_comm u t,abs_sub_comm ((r.extend.orbit (p+u•V) N).2)]
    simpa only [abs_of_nonneg (sub_nonneg.mpr hut)] using hh

lemma relative_interval_ratio {A C p q P Q : ℝ}
    (hp : P≤Real.exp (A+C)*p) (hq : Real.exp (A-C)*q≤Q) (h : Q≤2*P) :
    q≤2*Real.exp (2*C)*p := by
  have he : Real.exp (A+C)=Real.exp (A-C)*Real.exp (2*C) := by
    rw [←Real.exp_add]; congr 1; ring
  rw [he] at hp
  have hh : Real.exp (A-C)*q≤Real.exp (A-C)*(2*Real.exp (2*C)*p) := by nlinarith
  exact (mul_le_mul_iff_right₀ (Real.exp_pos (A-C))).mp hh

theorem LocalRecurrence.finite_holonomy_ratio (r : LocalRecurrence ℓ δ) (h : ℓ+δ<1)
    (hδ : (δ : ℝ)≤1/2) (D : ℕ → Plane → Plane →L[ℝ] Plane)
    (hd : ∀ n v, HasFDerivAt (r.remainder n) (D n v) v)
    (hsmall : ∀ n v, ‖v‖≤1 → ‖D n v‖≤(δ : ℝ)*‖v‖)
    (p q V : Plane) (hc : |V.1|≤|V.2|) (hV : V.2≠0)
    {t₀ t₁ u₀ u₁ : ℝ} {N : ℕ}
    (hp₀ : ∀ n : ℕ,n≤N → ‖r.extend.orbit (p+t₀•V) n‖≤1/3)
    (hp₁ : ∀ n : ℕ,n≤N → ‖r.extend.orbit (p+t₁•V) n‖≤1/3)
    (hq₀ : ∀ n : ℕ,n≤N → ‖r.extend.orbit (q+u₀•V) n‖≤1/3)
    (hq₁ : ∀ n : ℕ,n≤N → ‖r.extend.orbit (q+u₁•V) n‖≤1/3)
    (hterminal : |(r.extend.orbit (q+u₁•V) N).2-(r.extend.orbit (q+u₀•V) N).2|≤
      2* |(r.extend.orbit (p+t₁•V) N).2-(r.extend.orbit (p+t₀•V) N).2|) :
    |u₁-u₀|≤(2*Real.exp (8*(δ : ℝ)/(1-((ℓ+δ : ℝ≥0) : ℝ))))* |t₁-t₀| := by
  have hp := r.affine_interval_abs_distortion h hδ D hd hsmall p V hc hV hp₀ hp₁
  have hq := r.affine_interval_abs_distortion h hδ D hd hsmall q V hc hV hq₀ hq₁
  have hh := relative_interval_ratio hp.2 hq.1 hterminal
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  congr 2
  ring_nf

end StandardMapEntropy.NonlinearStable

end
section
namespace StandardMapEntropy.NonlinearStable
open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal
variable {ℓ δ : ℝ≥0}

lemma eventually_scaled_power_small {a b C d : ℝ} (ha : 0<a) (hb : 0≤b)
    (hab : a*b<1) (hd : 0<d) :
    ∀ᶠ n : ℕ in atTop, C*b^n≤d/a^n := by
  have ht : Tendsto (fun n : ℕ => C*(a*b)^n) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (mul_nonneg ha.le hb) hab).const_mul C
  filter_upwards [ht.eventually (gt_mem_nhds hd)] with n hn
  apply (le_div_iff₀ (pow_pos ha n)).mpr
  rw [mul_pow] at hn
  nlinarith

theorem LocalRecurrence.holonomy_local_bound (r : LocalRecurrence ℓ δ) (h : ℓ+δ<1)
    (hδ : (δ : ℝ)≤1/2) (D : ℕ → Plane → Plane →L[ℝ] Plane)
    (hd : ∀ n v, HasFDerivAt (r.remainder n) (D n v) v)
    (hsmall : ∀ n v, ‖v‖≤1 → ‖D n v‖≤(δ : ℝ)*‖v‖)
    (p q V : Plane) (hc : |V.1|≤|V.2|) (hV : V.2≠0)
    (S : Set ℝ) (H : ℝ → ℝ) {t₀ : ℝ} (ht₀ : t₀∈S)
    (hH : ContinuousWithinAt H S t₀)
    {M a b B ρ : ℝ} (hM : 0<M) (ha : 0<a) (hb : 0≤b) (hb1 : b≤1)
    (hρ : 0≤ρ) (hab : a*b<1) (haρ : a*ρ<1)
    (hstep : ∀ n u, ‖r.extend.step n u‖≤M*a^n*‖u‖)
    (hp₀ : ∀ n, ‖r.extend.orbit (p+t₀•V) n‖≤b^n/12)
    (hq₀ : ∀ n, ‖r.extend.orbit (q+H t₀•V) n‖≤b^n/12)
    (htrack : ∀ t∈S, ∀ N : ℕ,
      (∀ n : ℕ,n≤N → ‖r.extend.orbit (p+t•V) n‖≤1/3) →
      (∀ n : ℕ,n≤N → ‖r.extend.orbit (q+H t•V) n‖≤1/3) →
      ‖r.extend.orbit (p+t•V) N-r.extend.orbit (q+H t•V) N‖≤B*ρ^N) :
    ∀ᶠ t in 𝓝[S] t₀,
      |H t-H t₀|≤(2*Real.exp (8*(δ : ℝ)/(1-((ℓ+δ : ℝ≥0) : ℝ))))* |t-t₀| := by
  classical
  have hcentralP (n : ℕ) : ‖r.extend.orbit (p+t₀•V) n‖≤1/12 :=
    (hp₀ n).trans (div_le_div_of_nonneg_right (pow_le_one₀ hb hb1) (by norm_num))
  have hcentralQ (n : ℕ) : ‖r.extend.orbit (q+H t₀•V) n‖≤1/12 :=
    (hq₀ n).trans (div_le_div_of_nonneg_right (pow_le_one₀ hb hb1) (by norm_num))
  have hcentralP' (n : ℕ) : ‖r.extend.orbit (p+t₀•V) n‖≤1/3 := (hcentralP n).trans (by norm_num)
  have hcentralQ' (n : ℕ) : ‖r.extend.orbit (q+H t₀•V) n‖≤1/3 := (hcentralQ n).trans (by norm_num)
  have hdecay := eventually_scaled_power_small (C := (1:ℝ)/12) (d := 1/(6*M)) ha hb hab (by positivity)
  have hpair := eventually_scaled_power_small (C := B) (d := 1/(24*M)) ha hρ haρ (by positivity)
  obtain ⟨N₀,hN₀⟩ := eventually_atTop.mp (hdecay.and hpair)
  have hpre (n : ℕ) : ∀ᶠ t in 𝓝[S] t₀,
      ‖r.extend.orbit (p+t•V) n‖≤1/3 ∧ ‖r.extend.orbit (q+H t•V) n‖≤1/3 := by
    have hp : ContinuousAt (fun t : ℝ => ‖r.extend.orbit (p+t•V) n‖) t₀ :=
      ((r.extend.orbit_continuous n).comp (continuous_const.add (continuous_id.smul continuous_const))).norm.continuousAt
    have hq : ContinuousWithinAt (fun t : ℝ => ‖r.extend.orbit (q+H t•V) n‖) S t₀ :=
      (r.extend.orbit_continuous n).continuousAt.continuousWithinAt.comp
        (continuousWithinAt_const.add (hH.smul continuousWithinAt_const)) (mapsTo_univ _ _) |>.norm
    exact ((hp.eventually (gt_mem_nhds ((hcentralP n).trans_lt (by norm_num)))).filter_mono
      inf_le_left).and (hq.eventually (gt_mem_nhds ((hcentralQ n).trans_lt (by norm_num)))) |>.mono
        (fun t ht => ⟨ht.1.le,ht.2.le⟩)
  have hprefix : ∀ᶠ t in 𝓝[S] t₀, ∀ n∈Finset.range (N₀+1),
      ‖r.extend.orbit (p+t•V) n‖≤1/3 ∧ ‖r.extend.orbit (q+H t•V) n‖≤1/3 := by
    exact (Finset.eventually_all _).mpr (fun n hn => hpre n)
  filter_upwards [hprefix,self_mem_nhdsWithin] with t ht htS
  by_cases he : t=t₀
  · simp [he]
  have hcone (x y : ℝ) : |(p+x•V).1-(p+y•V).1|≤|(p+x•V).2-(p+y•V).2| := by
    change |p.1+x*V.1-(p.1+y*V.1)|≤|p.2+x*V.2-(p.2+y*V.2)|
    have h₁ : p.1+x*V.1-(p.1+y*V.1)=(x-y)*V.1 := by ring
    have h₂ : p.2+x*V.2-(p.2+y*V.2)=(x-y)*V.2 := by ring
    rw [h₁,h₂,abs_mul,abs_mul]
    exact mul_le_mul_of_nonneg_left hc (abs_nonneg _)
  have hconeQ (x y : ℝ) : |(q+x•V).1-(q+y•V).1|≤|(q+x•V).2-(q+y•V).2| := by
    change |q.1+x*V.1-(q.1+y*V.1)|≤|q.2+x*V.2-(q.2+y*V.2)|
    have h₁ : q.1+x*V.1-(q.1+y*V.1)=(x-y)*V.1 := by ring
    have h₂ : q.2+x*V.2-(q.2+y*V.2)=(x-y)*V.2 := by ring
    rw [h₁,h₂,abs_mul,abs_mul]
    exact mul_le_mul_of_nonneg_left hc (abs_nonneg _)
  have hne : (p+t•V).2≠(p+t₀•V).2 := by
    intro hh
    change p.2+t*V.2=p.2+t₀*V.2 at hh
    exact he (mul_right_cancel₀ hV (add_left_cancel hh))
  obtain ⟨j,hj⟩ := r.extend.exists_orbit_escape h (hcone t t₀) hne hcentralP'
  have hbad : ∃ n : ℕ, ¬(‖r.extend.orbit (p+t•V) n‖≤1/3 ∧
      ‖r.extend.orbit (q+H t•V) n‖≤1/3) := ⟨j,fun hh => hj.not_ge hh.1⟩
  obtain ⟨N,hN,htr,hout⟩ := last_trapped_time hbad (N₀ := N₀)
    (fun n hn => ht n (Finset.mem_range.mpr (by omega)))
  have hcentral (n : ℕ) (hn : N₀≤n) : b^n/12≤1/(6*M*a^n) := by
    have hh := (hN₀ n hn).1
    convert hh using 1 <;> ring
  have hpairbound : B*ρ^N≤(1/(6*M*a^N))/4 := by
    have hh := (hN₀ N hN).2
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    ring
  have hesc : 1/(6*M*a^N)< |(r.extend.orbit (p+t•V) N).2-(r.extend.orbit (p+t₀•V) N).2| ∨
      1/(6*M*a^N)< |(r.extend.orbit (q+H t•V) N).2-(r.extend.orbit (q+H t₀•V) N).2| := by
    push Not at hout
    by_cases hp : 1/3<‖r.extend.orbit (p+t•V) (N+1)‖
    · exact Or.inl (r.extend.escape_vertical_lower h (hcone t t₀) hM ha hstep hp
        ((hp₀ N).trans (hcentral N hN)))
    · exact Or.inr (r.extend.escape_vertical_lower h (hconeQ (H t) (H t₀)) hM ha hstep
        (hout (le_of_not_gt hp)) ((hq₀ N).trans (hcentral N hN)))
  have hpairs₀ : |(r.extend.orbit (p+t₀•V) N).2-(r.extend.orbit (q+H t₀•V) N).2|≤(1/(6*M*a^N))/4 := by
    exact (norm_snd_le _).trans ((htrack t₀ ht₀ N (fun n _ => hcentralP' n)
      (fun n _ => hcentralQ' n)).trans hpairbound)
  have hpairs₁ : |(r.extend.orbit (p+t•V) N).2-(r.extend.orbit (q+H t•V) N).2|≤(1/(6*M*a^N))/4 := by
    exact (norm_snd_le _).trans ((htrack t htS N (fun n hn => (htr n hn).1)
      (fun n hn => (htr n hn).2)).trans hpairbound)
  have hterminal := (terminal_size_comparison (by positivity : 0<(1/(6*M*a^N)))
    hesc hpairs₀ hpairs₁).1
  exact r.finite_holonomy_ratio h hδ D hd hsmall p q V hc hV
    (fun n _ => hcentralP' n) (fun n hn => (htr n hn).1)
    (fun n _ => hcentralQ' n) (fun n hn => (htr n hn).2) hterminal

end StandardMapEntropy.NonlinearStable

end
section
namespace StandardMapEntropy
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
open NonlinearStable

lemma fine_trueOrbit (k χ ε δ : ℝ) (hδ : 0<δ) (w : ℂ)
    (hw : ∀ n : ℕ, FineRegular k χ ε (complexProjection ((standardLift k)^[n] w)))
    (v : RealPlane) (n : ℕ) :
    (fineLocalRecurrence k χ ε δ hδ w hw).trueOrbit v n=
      fineCoordinate k χ ε δ w (w+fineFrame k χ ε δ (complexProjection w) v) n := by
  induction n with
  | zero => exact (fineCoordinate_initial k χ ε hδ w (hw 0) v).symm
  | succ n ih => rw [LocalRecurrence.trueOrbit,ih,fineCoordinate_step]

end StandardMapEntropy

end
section
namespace StandardMapEntropy
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
open NonlinearStable

lemma fineInverse_forward_bound (k χ ε δ : ℝ) (hδ : 0<δ) (w : ℂ)
    (hw : ∀ n : ℕ, FineRegular k χ ε (complexProjection ((standardLift k)^[n] w))) (n : ℕ) :
    ‖fineInverse k χ ε δ (complexProjection ((standardLift k)^[n] w))‖≤
      (Real.exp (2*ε))^n/(100*codingRadius k χ ε δ (complexProjection w)) := by
  have hr := codingRadius_pos k χ ε hδ (complexProjection w)
  have hh := fineInverse_forward_radius_bound k χ ε δ hδ w hw n
  apply (le_div_iff₀ (by positivity)).mpr
  nlinarith

lemma fineCoordinate_tracking_rate (k χ ε δ : ℝ) (hδ : 0<δ) (w p p' : ℂ)
    (hw : ∀ n : ℕ, FineRegular k χ ε (complexProjection ((standardLift k)^[n] w)))
    {D b : ℝ} (hD : 0≤D) (hb : 0≤b)
    (htrack : ∀ n : ℕ, ‖(standardLift k)^[n] p-(standardLift k)^[n] p'‖≤D*b^n) (n : ℕ) :
    ‖fineCoordinate k χ ε δ w p n-fineCoordinate k χ ε δ w p' n‖≤
      (D/(100*codingRadius k χ ε δ (complexProjection w)))*(Real.exp (2*ε)*b)^n := by
  have he : fineCoordinate k χ ε δ w p n-fineCoordinate k χ ε δ w p' n=
      fineInverse k χ ε δ (complexProjection ((standardLift k)^[n] w))
        ((standardLift k)^[n] p-(standardLift k)^[n] p') := by
    dsimp only [fineCoordinate]
    rw [←map_sub,sub_sub_sub_cancel_right]
  rw [he]
  calc
    _ ≤ ‖fineInverse k χ ε δ (complexProjection ((standardLift k)^[n] w))‖*
        ‖(standardLift k)^[n] p-(standardLift k)^[n] p'‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ ((Real.exp (2*ε))^n/(100*codingRadius k χ ε δ (complexProjection w)))*(D*b^n) :=
      (mul_le_mul_of_nonneg_left (htrack n) (norm_nonneg _)).trans
        (mul_le_mul_of_nonneg_right (fineInverse_forward_bound k χ ε δ hδ w hw n)
          (mul_nonneg hD (pow_nonneg hb n)))
    _ = _ := by rw [mul_pow]; ring

theorem fine_extended_step_bound (k : ℝ) (hk : 0≤k) (χ ε δ : ℝ) (hε : 0≤ε) (hδ : 0<δ)
    (w : ℂ) (hw : ∀ n : ℕ, FineRegular k χ ε (complexProjection ((standardLift k)^[n] w))) :
    ∃ M : ℝ, 0<M ∧ ∀ n u, ‖(fineLocalRecurrence k χ ε δ hδ w hw).extend.step n u‖≤
      M*(Real.exp (2*ε))^n*‖u‖ := by
  let a := Real.exp (2*ε)
  let R := codingRadius k χ ε δ (complexProjection w)
  let C := (a*(9*growthBase k)*(2*fineScale k ε δ))/(100*R)
  let r := fineLocalRecurrence k χ ε δ hδ w hw
  have ha : 1≤a := Real.one_le_exp_iff.mpr (by positivity)
  have hR : 0<R := codingRadius_pos k χ ε hδ _
  have hG : 0<growthBase k := by unfold growthBase; positivity
  have hC : 0<C := by dsimp [C,a]; positivity [fineScale_pos k ε hδ]
  refine ⟨C+δ,by positivity,fun n u => ?_⟩
  let z := complexProjection ((standardLift k)^[n] w)
  have hI : ‖fineInverse k χ ε δ (standardMap k z)‖≤a^(n+1)/(100*R) := by
    simpa only [z,Function.iterate_succ_apply',complexProjection_standardLift] using
      fineInverse_forward_bound k χ ε δ hδ w hw (n+1)
  have hF : ‖fineFrame k χ ε δ z‖≤2*fineScale k ε δ :=
    (fineFrame_norm_le k χ ε hδ z).trans (mul_le_mul_of_nonneg_left (fineSize_le_scale k χ ε hδ z) (by norm_num))
  have hdiag : ‖((r.a n*u.1,r.b n*u.2) : Plane)‖≤C*a^n*‖u‖ := by
    rw [show ((r.a n*u.1,r.b n*u.2) : Plane)=
      fineInverse k χ ε δ (standardMap k z) (standardDerivative k z (fineFrame k χ ε δ z u)) from
        (fine_derivative_diagonal k χ ε δ z (hw n) u).symm]
    calc
      _ ≤ ‖fineInverse k χ ε δ (standardMap k z)‖*
          (‖standardDerivative k z‖*(‖fineFrame k χ ε δ z‖*‖u‖)) :=
        (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_left
          ((ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_left
            (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _))) (norm_nonneg _))
      _ ≤ (a^(n+1)/(100*R))*((9*growthBase k)*((2*fineScale k ε δ)*‖u‖)) :=
        mul_le_mul hI (mul_le_mul (standardDerivative_norm_bound k hk z)
          (mul_le_mul_of_nonneg_right hF (norm_nonneg _)) (by positivity) (by positivity))
          (by positivity) (by positivity)
      _ = _ := by dsimp only [C]; rw [pow_succ]; ring
  have hrem : ‖r.extend.remainder n u‖≤δ*‖u‖ := by
    have ht := (r.extend.lipschitz n).dist_le_mul u 0
    change ‖r.extend.remainder n u-r.extend.remainder n 0‖≤δ*‖u-0‖ at ht
    rw [r.extend.zero,sub_zero,sub_zero] at ht
    exact ht
  have he : r.extend.step n u=((r.a n*u.1,r.b n*u.2) : Plane)+r.extend.remainder n u := rfl
  change ‖r.extend.step n u‖≤_
  rw [he]
  have hap : 1≤a^n := one_le_pow₀ ha
  have hh := (norm_add_le _ _).trans (add_le_add hdiag hrem)
  have hrem' : δ*‖u‖≤δ*a^n*‖u‖ := by
    have hh := mul_le_mul_of_nonneg_left hap hδ.le
    simpa only [mul_one] using mul_le_mul_of_nonneg_right hh (norm_nonneg u)
  exact hh.trans (by nlinarith)

end StandardMapEntropy

end
end

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_Holonomy_FinePlaqueParameters
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace StandardMapEntropy
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
open NonlinearStable

lemma fineStableGraph_slope (k χ ε δ : ℝ) (hδ : 0<δ) (hq : Real.exp (-χ+ε)+δ<1)
    (w : ℂ) (hw : ∀ n : ℕ, FineRegular k χ ε (complexProjection ((standardLift k)^[n] w)))
    (s t : ℝ) :
    |fineStableGraph k χ ε δ hδ hq w hw s-fineStableGraph k χ ε δ hδ hq w hw t|≤
      (Real.exp (-χ+ε)*δ/(1-Real.exp (-χ+ε)))*|s-t| :=
  graph_slope_bound (fineLocalRecurrence k χ ε δ hδ w hw).extend hq s t

end StandardMapEntropy

end
section
namespace StandardMapEntropy
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
open NonlinearStable

lemma NonlinearStable.Recurrence.orbit_solution {ℓ δ : ℝ≥0} (r : Recurrence ℓ δ)
    (h : ℓ+δ<1) (s : ℝ) (n : ℕ) : r.orbit (r.solution h s 0) n=r.solution h s n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Recurrence.orbit,ih,solution_orbit]

lemma fine_central_orbit_decay (k χ ε δ : ℝ) (hδ : 0<δ) (hq : Real.exp (-χ+ε)+δ<1)
    (w : ℂ) (hw : ∀ n : ℕ, FineRegular k χ ε (complexProjection ((standardLift k)^[n] w)))
    {v : Plane} {s : ℝ} (hs : |s|≤1/12)
    (he : w+fineFrame k χ ε δ (complexProjection w) v=fineStableCurve k χ ε δ hδ hq w hw s)
    (n : ℕ) : ‖(fineLocalRecurrence k χ ε δ hδ w hw).extend.orbit v n‖≤
      (Real.exp (-χ+ε)+δ)^n/12 := by
  let r := fineLocalRecurrence k χ ε δ hδ w hw
  have hs' : |s|≤1 := hs.trans (by norm_num)
  have hv : v=r.extend.solution hq s 0 := by
    have hh := congrArg (fun p => fineCoordinate k χ ε δ w p 0) he
    rw [fineCoordinate_initial k χ ε hδ w (hw 0),fineStableCoordinate k χ ε δ hδ hq w hw hs'] at hh
    exact hh
  rw [hv,r.extend.orbit_solution hq]
  have hdec : ‖r.extend.solution hq s n‖≤(Real.exp (-χ+ε)+δ)^n*|s| := by
    have hh := solution_exponential_contraction r.extend hq s 0 n
    rw [solution_zero r.extend hq] at hh
    change ‖r.extend.solution hq s n-0‖≤(Real.exp (-χ+ε)+δ)^n*|s-0| at hh
    simpa only [sub_zero] using hh
  exact hdec.trans ((mul_le_mul_of_nonneg_left hs (by positivity)).trans_eq (by ring))

theorem fine_stable_matching_local_bound (k : ℝ) (hk : 0≤k) (χ ε δ : ℝ)
    (hε : 0≤ε) (hδ : 0<δ) (hδ' : δ≤1/2) (hq : Real.exp (-χ+ε)+δ<1)
    (hslow : Real.exp (4*ε)*(Real.exp (-χ+ε)+δ)<1)
    (w : ℂ) (hw : ∀ n : ℕ, FineRegular k χ ε (complexProjection ((standardLift k)^[n] w)))
    (p q V : Plane) (hc : |V.1|≤|V.2|) (hV : V.2≠0)
    (S : Set ℝ) (H : ℝ → ℝ) {t₀ : ℝ} (ht₀ : t₀∈S) (hH : ContinuousWithinAt H S t₀)
    {s₀ s₁ : ℝ} (hs₀ : |s₀|≤1/12) (hs₁ : |s₁|≤1/12)
    (hp₀ : w+fineFrame k χ ε δ (complexProjection w) (p+t₀•V)=fineStableCurve k χ ε δ hδ hq w hw s₀)
    (hq₀ : w+fineFrame k χ ε δ (complexProjection w) (q+H t₀•V)=fineStableCurve k χ ε δ hδ hq w hw s₁)
    (hmatch : ∀ t∈S, ∃ (v : ℂ)
      (hv : ∀ n : ℕ, FineRegular k χ ε (complexProjection ((standardLift k)^[n] v))) (s u : ℝ),
      |s|≤1 ∧ |u|≤1 ∧
      w+fineFrame k χ ε δ (complexProjection w) (p+t•V)=fineStableCurve k χ ε δ hδ hq v hv s ∧
      w+fineFrame k χ ε δ (complexProjection w) (q+H t•V)=fineStableCurve k χ ε δ hδ hq v hv u) :
    ∀ᶠ t in 𝓝[S] t₀, |H t-H t₀|≤(2*Real.exp (8*δ/(1-(Real.exp (-χ+ε)+δ))))* |t-t₀| := by
  let r := fineLocalRecurrence k χ ε δ hδ w hw
  let D (n : ℕ) := fineRemainderDerivative k χ ε δ ((standardLift k)^[n] w)
  let a := Real.exp (2*ε)
  let b := Real.exp (-χ+ε)+δ
  have hb : 0<b := add_pos (Real.exp_pos _) hδ
  have hscale := fineScale_pos k ε hδ
  have hab : a*b<1 := (mul_le_mul_of_nonneg_right
    (Real.exp_le_exp.mpr (by linarith : 2*ε≤4*ε)) hb.le).trans_lt hslow
  have haρ : a*(a*b)<1 := by
    have he : a*(a*b)=Real.exp (4*ε)*b := by
      dsimp only [a]
      rw [←mul_assoc,←Real.exp_add]
      congr 2
      ring
    rwa [he]
  obtain ⟨M,hM,hstep⟩ := fine_extended_step_bound k hk χ ε δ hε hδ w hw
  have hsmall (n : ℕ) (v : Plane) (_ : ‖v‖≤1) : ‖D n v‖≤δ*‖v‖ := by
    have hh := fineRemainderDerivative_lipschitz k χ ε hδ ((standardLift k)^[n] w)
      (hw n) (fine_regular_lift_next k χ ε w hw n) v 0
    simpa only [fineRemainderDerivative_zero,sub_zero] using hh
  have htrack (t : ℝ) (ht : t∈S) (N : ℕ)
      (hP : ∀ n : ℕ,n≤N → ‖r.extend.orbit (p+t•V) n‖≤1/3)
      (hQ : ∀ n : ℕ,n≤N → ‖r.extend.orbit (q+H t•V) n‖≤1/3) :
      ‖r.extend.orbit (p+t•V) N-r.extend.orbit (q+H t•V) N‖≤
        ((4*fineScale k ε δ)/(100*codingRadius k χ ε δ (complexProjection w)))*(a*b)^N := by
    have htp : p+t•V∈r.extend.trappedBox N := fun n hn => (hP n hn).trans (by norm_num)
    have htq : q+H t•V∈r.extend.trappedBox N := fun n hn => (hQ n hn).trans (by norm_num)
    rw [←r.trueOrbit_eq_extend htp le_rfl,←r.trueOrbit_eq_extend htq le_rfl]
    rw [fine_trueOrbit,fine_trueOrbit]
    obtain ⟨v,hv,s,u,hs,hu,hps,hqu⟩ := hmatch t ht
    have hd (n : ℕ) :
        ‖(standardLift k)^[n] (w+fineFrame k χ ε δ (complexProjection w) (p+t•V))-
          (standardLift k)^[n] (w+fineFrame k χ ε δ (complexProjection w) (q+H t•V))‖≤
          (4*fineScale k ε δ)*b^n := by
      rw [hps,hqu]
      have hh := fineStableCurve_contraction k χ ε δ hδ hq v hv hs hu n
      have hsu : |s-u|≤2 := (abs_sub _ _).trans (by linarith)
      have hm := mul_le_mul_of_nonneg_left hsu (by positivity : 0≤(2*fineScale k ε δ)*b^n)
      exact hh.trans (hm.trans_eq (by ring))
    exact fineCoordinate_tracking_rate k χ ε δ hδ w _ _ hw
      (by positivity [fineScale_pos k ε hδ]) hb.le hd N
  exact r.holonomy_local_bound hq hδ' D (fun n v => hasFDerivAt_fineRemainder k χ ε δ _ v)
    hsmall p q V hc hV S H ht₀ hH hM (Real.exp_pos _) hb.le hq.le
    (mul_nonneg (Real.exp_pos _).le hb.le) hab haρ hstep
    (fine_central_orbit_decay k χ ε δ hδ hq w hw hs₀ hp₀)
    (fine_central_orbit_decay k χ ε δ hδ hq w hw hs₁ hq₀) htrack

end StandardMapEntropy

end
section
namespace StandardMapEntropy
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal

theorem null_image_of_pointwise_local_bound {S : Set ℝ} {H : ℝ → ℝ} {K : ℝ} (hK : 0≤K)
    (h : ∀ x∈S, ∀ᶠ y in 𝓝[S] x, |H y-H x| ≤ K*|y-x|)
    {Z : Set ℝ} (hZS : Z⊆S) (hZ : volume Z=0) : volume (H '' Z)=0 := by
  classical
  let A (n : ℕ) : Set ℝ := {x | x∈S ∧ |H x| ≤ (n : ℝ) ∧
    ∀ y∈S, |y-x| < 1/((n : ℝ)+1) → |H y-H x| ≤ K*|y-x|}
  have hcover : S⊆⋃ n : ℕ,A n := by
    intro x hx
    obtain ⟨ε,hε,hball⟩ := Metric.mem_nhdsWithin_iff.mp (h x hx)
    obtain ⟨n,hn⟩ := exists_nat_gt (max |H x| (1/ε))
    have hbn : |H x| ≤ (n : ℝ) := ((le_max_left _ _).trans_lt hn).le
    have hεn : 1/((n : ℝ)+1)<ε := by
      have he : 1/ε<(n : ℝ) := (le_max_right _ _).trans_lt hn
      have hh : 1<(n : ℝ)*ε := (div_lt_iff₀ hε).mp he
      apply (div_lt_iff₀ (by positivity : 0<(n : ℝ)+1)).mpr
      nlinarith
    refine mem_iUnion.mpr ⟨n,hx,hbn,fun y hy hxy => ?_⟩
    exact hball ⟨by simpa only [Metric.mem_ball,Real.dist_eq] using hxy.trans hεn,hy⟩
  have hLip (n : ℕ) : LipschitzOnWith
      ⟨max K (2*(n : ℝ)*((n : ℝ)+1)), hK.trans (le_max_left _ _)⟩ H (A n) := by
    refine LipschitzOnWith.of_dist_le_mul fun x hx y hy => ?_
    change |H x-H y| ≤ max K (2*(n : ℝ)*((n : ℝ)+1))*|x-y|
    by_cases hxy : |x-y| < 1/((n : ℝ)+1)
    · exact (hy.2.2 x hx.1 hxy).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (abs_nonneg _))
    · have hd : 1/((n : ℝ)+1)≤|x-y| := le_of_not_gt hxy
      have hprod : 1≤|x-y| *((n : ℝ)+1) := (div_le_iff₀ (by positivity)).mp hd
      have hleft : |H x-H y| ≤ 2*(n : ℝ) := (abs_sub _ _).trans (by linarith [hx.2.1,hy.2.1])
      have hm := mul_le_mul_of_nonneg_left hprod (by positivity : 0≤2*(n : ℝ))
      apply hleft.trans
      apply le_trans _ (mul_le_mul_of_nonneg_right (le_max_right _ _) (abs_nonneg _))
      nlinarith
  have hpieces (n : ℕ) : volume (H '' (Z∩A n))=0 := by
    have hz : volume (Z∩A n)=0 := measure_mono_null inter_subset_left hZ
    have hl := ((hLip n).mono (show Z∩A n⊆A n from inter_subset_right)).hausdorffMeasure_image_le (by norm_num : (0:ℝ)≤1)
    rw [hausdorffMeasure_real,hz,mul_zero] at hl
    exact bot_unique hl
  have hsub : H '' Z⊆⋃ n : ℕ,H '' (Z∩A n) := by
    rintro _ ⟨x,hx,rfl⟩
    obtain ⟨n,hn⟩ := mem_iUnion.mp (hcover (hZS hx))
    exact mem_iUnion.mpr ⟨n,x,⟨hx,hn⟩,rfl⟩
  exact measure_mono_null hsub (measure_iUnion_null hpieces)

end StandardMapEntropy

end
section
namespace StandardMapEntropy
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
open NonlinearStable

lemma fine_affine_coordinates (k χ ε δ : ℝ) (hδ : 0<δ) (w p V : ℂ)
    (hw : FineRegular k χ ε (complexProjection w)) (t : ℝ) :
    w+fineFrame k χ ε δ (complexProjection w)
      (fineInverse k χ ε δ (complexProjection w) (p-w)+t•fineInverse k χ ε δ (complexProjection w) V)=
      p+t•V := by
  rw [map_add,map_smul,fineFrame_inverse k χ ε hδ _ hw.1,
    fineFrame_inverse k χ ε hδ _ hw.1]
  abel

end StandardMapEntropy

end
section
namespace StandardMapEntropy
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
open NonlinearStable

lemma strictMono_of_linear_error {f : ℝ → ℝ} {κ : ℝ} (hκ : κ<1)
    (h : ∀ s t : ℝ, |f s-f t-(s-t)|≤κ*|s-t|) : StrictMono f := by
  intro s t hst
  have hh := (abs_le.mp (h t s)).1
  rw [abs_of_pos (sub_pos.mpr hst)] at hh
  nlinarith

theorem compact_graph_crossing {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (r : ℝ) (hr : 0 < r) (F : X → ℝ → Plane)
    (hF : Continuous (fun p : X×Icc (-r) r => F p.1 p.2))
    (he : ∀ x s t, |(F x s).1-(F x t).1-(s-t)|≤(1/4)*|s-t|)
    (hzero : ∀ x, |(F x 0).1| ≤ r/4) :
    ∃ σ : (X×Icc (-r/2) (r/2)) → Icc (-r) r, Continuous σ ∧
      ∀ v, (F v.1 (σ v)).1=(v.2 : ℝ) := by
  classical
  have hm (x : X) : StrictMono (fun s => (F x s).1) := strictMono_of_linear_error (by norm_num) (he x)
  have hf (x : X) : ContinuousOn (fun s => (F x s).1) (Icc (-r) r) := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    exact (hF.comp (continuous_const.prodMk continuous_id)).fst
  have hend (x : X) : (F x (-r)).1≤-r/2 ∧ r/2≤(F x r).1 := by
    have hl := (abs_le.mp (he x (-r) 0)).2
    have hu := (abs_le.mp (he x r 0)).1
    have hz := abs_le.mp (hzero x)
    simp only [sub_zero,abs_neg,abs_of_pos hr] at hl hu
    constructor <;> linarith
  have hex (v : X×Icc (-r/2) (r/2)) : ∃ s : Icc (-r) r, (F v.1 s).1=(v.2 : ℝ) := by
    obtain ⟨s,hs,hs'⟩ := intermediate_value_Icc (by linarith : -r ≤ r) (hf v.1)
      ⟨(hend v.1).1.trans v.2.property.1,v.2.property.2.trans (hend v.1).2⟩
    exact ⟨⟨s,hs⟩,hs'⟩
  choose σ hσ using hex
  let G : X×Icc (-r) r → X×ℝ := fun p => (p.1,(F p.1 p.2).1)
  have hGc : Continuous G := continuous_fst.prodMk hF.fst
  have hGi : Function.Injective G := by
    rintro ⟨x,s⟩ ⟨y,t⟩ heq
    have hxy : x=y := congrArg Prod.fst heq
    subst y
    have hst : (s : ℝ)=(t : ℝ) := (hm x).injective (congrArg Prod.snd heq)
    exact Prod.ext rfl (Subtype.ext hst)
  have hemb := hGc.isClosedEmbedding hGi |>.isEmbedding
  have hpair : Continuous (fun v : X×Icc (-r/2) (r/2) => (v.1,σ v)) := by
    apply hemb.continuous_iff.mpr
    have heq : G ∘ (fun v : X×Icc (-r/2) (r/2) => (v.1,σ v))=
        (fun v => (v.1,(v.2 : ℝ))) := by
      funext v; exact Prod.ext rfl (hσ v)
    rw [heq]
    exact continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)
  exact ⟨σ,hpair.snd,hσ⟩

end StandardMapEntropy

end
section
namespace StandardMapEntropy
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
open NonlinearStable

lemma fine_graph_pair_bound (k χ ε δ : ℝ) (hδ : 0<δ) (hq : Real.exp (-χ+ε)+δ<1)
    (v : ℂ) (hv : ∀ n : ℕ, FineRegular k χ ε (complexProjection ((standardLift k)^[n] v))) (s t : ℝ) :
    ‖((s,fineStableGraph k χ ε δ hδ hq v hv s) : Plane)-
      (t,fineStableGraph k χ ε δ hδ hq v hv t)‖≤|s-t| := by
  have hg := (graph_lipschitz (fineLocalRecurrence k χ ε δ hδ v hv).extend hq).dist_le_mul s t
  change max |s-t| |fineStableGraph k χ ε δ hδ hq v hv s-fineStableGraph k χ ε δ hδ hq v hv t|≤|s-t|
  exact max_le le_rfl (by simpa only [Real.dist_eq,NNReal.coe_one,one_mul,fineStableGraph] using hg)

lemma fine_plaque_linear_error (k χ ε δ : ℝ) (hδ : 0<δ) (hq : Real.exp (-χ+ε)+δ<1)
    (w v : ℂ) (hv : ∀ n : ℕ, FineRegular k χ ε (complexProjection ((standardLift k)^[n] v)))
    (hclose : ‖(fineInverse k χ ε δ (complexProjection w)).comp (fineFrame k χ ε δ (complexProjection v))-
      ContinuousLinearMap.id ℝ Plane‖≤1/4) (s t : ℝ) :
    |(finePlaqueInChart k χ ε δ hδ hq w v hv s).1-
      (finePlaqueInChart k χ ε δ hδ hq w v hv t).1-(s-t)|≤(1/4)*|s-t| := by
  let I := fineInverse k χ ε δ (complexProjection w)
  let F := fineFrame k χ ε δ (complexProjection v)
  let u : Plane := (s,fineStableGraph k χ ε δ hδ hq v hv s)-(t,fineStableGraph k χ ε δ hδ hq v hv t)
  have he : (finePlaqueInChart k χ ε δ hδ hq w v hv s).1-
      (finePlaqueInChart k χ ε δ hδ hq w v hv t).1-(s-t)=
      (((I.comp F)-ContinuousLinearMap.id ℝ Plane) u).1 := by
    change (I (v+F (s,fineStableGraph k χ ε δ hδ hq v hv s)-w)).1-
      (I (v+F (t,fineStableGraph k χ ε δ hδ hq v hv t)-w)).1-(s-t)=_
    simp only [map_sub,map_add,Prod.fst_add,Prod.fst_sub,sub_apply,
      ContinuousLinearMap.comp_apply,ContinuousLinearMap.id_apply,u]
    ring
  rw [he]
  exact (norm_fst_le _).trans ((ContinuousLinearMap.le_opNorm _ _).trans
    ((mul_le_mul_of_nonneg_right hclose (norm_nonneg u)).trans
      (mul_le_mul_of_nonneg_left (fine_graph_pair_bound k χ ε δ hδ hq v hv s t) (by norm_num))))

lemma fine_plaque_crossing_unique (k χ ε δ : ℝ) (hδ : 0<δ) (hq : Real.exp (-χ+ε)+δ<1)
    (w v : ℂ) (hv : ∀ n : ℕ, FineRegular k χ ε (complexProjection ((standardLift k)^[n] v)))
    (hclose : ‖(fineInverse k χ ε δ (complexProjection w)).comp (fineFrame k χ ε δ (complexProjection v))-
      ContinuousLinearMap.id ℝ Plane‖≤1/4) :
    Function.Injective (fun s => (finePlaqueInChart k χ ε δ hδ hq w v hv s).1) :=
  (strictMono_of_linear_error (by norm_num) (fine_plaque_linear_error k χ ε δ hδ hq w v hv hclose)).injective

theorem fine_compact_graph_crossing {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (k χ ε δ : ℝ) (hδ : 0<δ) (hq : Real.exp (-χ+ε)+δ<1)
    (w : ℂ) (v : X → ℂ) (hvc : Continuous v)
    (hv : ∀ x, ∀ n : ℕ, FineRegular k χ ε (complexProjection ((standardLift k)^[n] (v x))))
    (hdata : ∀ n : ℕ, Continuous (fun x => lyapunovChartData k χ ε
      (complexProjection ((standardLift k)^[n] (v x)))))
    {r : ℝ} (hr : 0 < r) (hr1 : r≤1)
    (hclose : ∀ x, ‖(fineInverse k χ ε δ (complexProjection w)).comp (fineFrame k χ ε δ (complexProjection (v x)))-
      ContinuousLinearMap.id ℝ Plane‖≤1/4)
    (hcentre : ∀ x, |(fineInverse k χ ε δ (complexProjection w) (v x-w)).1| ≤ r/4) :
    ∃ σ : (X×Icc (-r/2) (r/2)) → Icc (-r) r, Continuous σ ∧ ∀ p : X×Icc (-r/2) (r/2),
      (finePlaqueInChart k χ ε δ hδ hq w (v p.1) (hv p.1) (σ p)).1=(p.2 : ℝ) := by
  let F (x : X) (s : ℝ) := finePlaqueInChart k χ ε δ hδ hq w (v x) (hv x) s
  have hc0 := continuous_fineStableCurve_family k χ ε δ hδ hq v hvc hv hdata
  let ι : Icc (-r) r → Icc (-1 : ℝ) 1 := fun s => ⟨s,⟨by linarith [s.property.1],s.property.2.trans hr1⟩⟩
  have hι : Continuous ι := continuous_subtype_val.subtype_mk _
  have hc : Continuous (fun p : X×Icc (-r) r => F p.1 p.2) := by
    exact (fineInverse k χ ε δ (complexProjection w)).continuous.comp
      ((hc0.comp (continuous_fst.prodMk (hι.comp continuous_snd))).sub continuous_const)
  apply compact_graph_crossing r hr F hc (fun x => fine_plaque_linear_error k χ ε δ hδ hq w (v x) (hv x) (hclose x))
  intro x
  simpa only [F,finePlaqueInChart,fineStableCurve_zero] using hcentre x

end StandardMapEntropy

end
section
namespace StandardMapEntropy
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
open NonlinearStable

theorem fine_small_crossings_coincide (k χ ε δ : ℝ) (hδ : 0<δ)
    (hq : Real.exp (-χ+ε)+δ<1) (hslow : Real.exp (2*ε)*(Real.exp (-χ+ε)+δ)≤1)
    (w v v' : ℂ)
    (hv : ∀ n : ℕ, FineRegular k χ ε (complexProjection ((standardLift k)^[n] v)))
    (hv' : ∀ n : ℕ, FineRegular k χ ε (complexProjection ((standardLift k)^[n] v')))
    {r R : ℝ} (hr : 0 < r) (hr1 : r≤1) (hR : 0<R)
    (hRv : R ≤ codingRadius k χ ε δ (complexProjection v))
    (hsize : (4*fineScale k ε δ*r)/(100*R)+r≤1)
    (hclose : ‖(fineInverse k χ ε δ (complexProjection w)).comp (fineFrame k χ ε δ (complexProjection v))-
      ContinuousLinearMap.id ℝ Plane‖≤1/4)
    {s t s' t' : ℝ} (hs : |s| ≤ r) (ht : |t| ≤ r) (hs' : |s'| ≤ r) (ht' : |t'| ≤ r)
    (hmeet : fineStableCurve k χ ε δ hδ hq v hv s=fineStableCurve k χ ε δ hδ hq v' hv' s')
    (hcross : (finePlaqueInChart k χ ε δ hδ hq w v hv t).1=
      (finePlaqueInChart k χ ε δ hδ hq w v' hv' t').1) :
    fineStableCurve k χ ε δ hδ hq v hv t=fineStableCurve k χ ε δ hδ hq v' hv' t' := by
  let p := fineStableCurve k χ ε δ hδ hq v' hv' t'
  let p₀ := fineStableCurve k χ ε δ hδ hq v hv s
  have hscale := fineScale_pos k ε hδ
  have hq0 : 0≤Real.exp (-χ+ε)+δ := by positivity
  have htrack (n : ℕ) : ‖(standardLift k)^[n] p-(standardLift k)^[n] p₀‖≤
      ((2*fineScale k ε δ)*|t'-s'|)*(Real.exp (-χ+ε)+δ)^n := by
    dsimp only [p,p₀]
    rw [hmeet]
    exact (fineStableCurve_contraction k χ ε δ hδ hq v' hv' (ht'.trans hr1) (hs'.trans hr1) n).trans_eq (by ring)
  have hdiff : |t'-s'|≤2*r := (abs_sub _ _).trans (by linarith)
  have hdist (n : ℕ) : ‖fineCoordinate k χ ε δ v p n-fineCoordinate k χ ε δ v p₀ n‖≤
      (4*fineScale k ε δ*r)/(100*R) := by
    have hd := fineCoordinate_tracking_difference k χ ε δ hδ v p p₀ hv (by positivity) hq0 hslow htrack n
    apply hd.trans
    calc
      _ ≤ (4*fineScale k ε δ*r)/(100*codingRadius k χ ε δ (complexProjection v)) :=
        div_le_div_of_nonneg_right (by nlinarith only [hdiff,hscale])
          (by positivity [codingRadius_pos k χ ε hδ (complexProjection v)])
      _ ≤ _ := div_le_div_of_nonneg_left
        (mul_nonneg (mul_nonneg (by norm_num) hscale.le) hr.le) (by positivity : 0<100*R)
        (mul_le_mul_of_nonneg_left hRv (by norm_num))
  have hp (n : ℕ) : ‖fineCoordinate k χ ε δ v p n‖≤1 := by
    have hc : ‖fineCoordinate k χ ε δ v p₀ n‖ ≤ r :=
      (fineStableCoordinate_bound k χ ε δ hδ hq v hv (hs.trans hr1) n).trans hs
    have hh := norm_add_le (fineCoordinate k χ ε δ v p n-fineCoordinate k χ ε δ v p₀ n)
      (fineCoordinate k χ ε δ v p₀ n)
    rw [sub_add_cancel] at hh
    exact hh.trans ((add_le_add (hdist n) hc).trans hsize)
  have hu := fineStableCurve_unique k χ ε δ hδ hq v p hv hp
  let a := (fineCoordinate k χ ε δ v p 0).1
  have hca : (finePlaqueInChart k χ ε δ hδ hq w v hv t).1=
      (finePlaqueInChart k χ ε δ hδ hq w v hv a).1 := by
    apply hcross.trans
    change (fineInverse k χ ε δ (complexProjection w) (p-w)).1=_
    rw [hu]
    rfl
  have hta : t=a := (fine_plaque_crossing_unique k χ ε δ hδ hq w v hv hclose).injOn
    (s := Icc (-1) 1) (abs_le.mp (ht.trans hr1))
    (abs_le.mp ((norm_fst_le _).trans (hp 0))) hca
  rw [hta]
  exact hu.symm

end StandardMapEntropy

end
end

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_Holonomy_CompactHolonomy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace StandardMapEntropy
open MeasureTheory Set Filter Topology
open scoped Topology NNReal ENNReal

lemma compact_fibre_descent {X : Type*} [TopologicalSpace X] [CompactSpace X]
    {f g : X → ℝ} (hf : Continuous f) (hg : Continuous g)
    (hfg : ∀ x y, f x=f y → g x=g y) :
    ∃ H : ℝ → ℝ, ContinuousOn H (range f) ∧ ∀ x, H (f x)=g x := by
  classical
  let H : ℝ → ℝ := fun y => if hy : y∈range f then g (Classical.choose hy) else 0
  have hH (x : X) : H (f x)=g x := by
    dsimp only [H]
    rw [dite_eq_left (mem_range_self x)]
    exact hfg _ x (Classical.choose_spec (mem_range_self x))
  refine ⟨H,?_,hH⟩
  let q : X → range f := fun x => ⟨f x,mem_range_self x⟩
  have hq : Continuous q := hf.subtype_mk _
  have hqs : Function.Surjective q := by
    rintro ⟨y,x,rfl⟩
    exact ⟨x,rfl⟩
  have hquot := IsQuotientMap.of_surjective_continuous hqs hq
  apply continuousOn_iff_continuous_domRestrict.mpr
  apply hquot.continuous_iff.mpr
  have he : (fun y : range f => H y) ∘ q=g := by funext x; exact hH x
  change Continuous ((fun y : range f => H y) ∘ q)
  rw [he]
  exact hg

end StandardMapEntropy

end
section
namespace StandardMapEntropy
open MeasureTheory Set Filter Topology
open scoped Topology NNReal ENNReal
open NonlinearStable

lemma fine_transverse_cone (k χ ε δ : ℝ) (w v : ℂ)
    (hc : ‖(fineInverse k χ ε δ (complexProjection v)).comp (fineFrame k χ ε δ (complexProjection w))-
      ContinuousLinearMap.id ℝ Plane‖≤1/4) :
    let W := fineFrame k χ ε δ (complexProjection w) (0,1)
    |(fineInverse k χ ε δ (complexProjection v) W).1|≤
      |(fineInverse k χ ε δ (complexProjection v) W).2| ∧
      (fineInverse k χ ε δ (complexProjection v) W).2≠0 := by
  dsimp only
  let A := (fineInverse k χ ε δ (complexProjection v)).comp (fineFrame k χ ε δ (complexProjection w))
  have h := (ContinuousLinearMap.le_opNorm (A-ContinuousLinearMap.id ℝ Plane) ((0,1) : Plane)).trans
    (mul_le_mul_of_nonneg_right hc (norm_nonneg _))
  have hnorm : ‖((0,1) : Plane)‖=1 := by simp [Prod.norm_def]
  rw [hnorm,mul_one] at h
  have he : ((A-ContinuousLinearMap.id ℝ Plane) (0,1))=A (0,1)-(0,1) := rfl
  rw [he] at h
  have h1 : |(A (0,1)).1|≤1/4 := by simpa using (norm_fst_le _).trans h
  have h2 : |(A (0,1)).2-1|≤1/4 := (norm_snd_le _).trans h
  have h2' : 3/4≤(A (0,1)).2 := by linarith [(abs_le.mp h2).1]
  change |(A (0,1)).1|≤|(A (0,1)).2| ∧ (A (0,1)).2≠0
  exact ⟨h1.trans (by linarith [le_abs_self ((A (0,1)).2)]),ne_of_gt (by linarith)⟩

end StandardMapEntropy

end
end

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_Components_BoundedBirkhoff
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Filter Set
open scoped Topology ENNReal BigOperators

namespace BoundedSubadditive
variable {X : Type*} [MeasurableSpace X] {T : X → X}

lemma observation_integral_rate {μ : Measure X} [IsFiniteMeasure μ]
    (hT : MeasurePreserving T μ μ) {g : X → ℝ} (hg : Measurable g)
    (h0 : ∀ x,0≤g x) (h1 : ∀ x,g x≤1) :
    ∫ x, (observationCocycle g hT.measurable hg h0 h1).lowerRate x ∂μ = ∫ x,g x ∂μ := by
  let f := observationCocycle g hT.measurable hg h0 h1
  have hi : Integrable g μ := (integrable_const (1 : ℝ)).mono' hg.aestronglyMeasurable
    (Eventually.of_forall fun x => by rw [Real.norm_eq_abs,abs_of_nonneg (h0 x)]; exact h1 x)
  have him (i : ℕ) : Integrable (fun x => g (T^[i] x)) μ := (hT.iterate i).integrable_comp_of_integrable hi
  have he (n : ℕ) (hn : n≠0) : (∫ x,f.average n x ∂μ)=∫ x,g x ∂μ := by
    change (∫ x,birkhoffSum T g n x/(n : ℝ) ∂μ)=_
    rw [integral_div]
    have hs : (∫ x,birkhoffSum T g n x ∂μ)=(n : ℝ)*(∫ x,g x ∂μ) := by
      unfold birkhoffSum
      rw [integral_finsetSum _ (fun i _ => him i)]
      simp only [BoundedSubadditive.integral_comp (hT.iterate _) hi.aestronglyMeasurable,
        Finset.sum_const,Finset.card_range,nsmul_eq_mul]
    rw [hs,mul_div_cancel_left₀ _ (by exact_mod_cast hn)]
  have ht := f.tendsto_integral_average hT
  have hc : Tendsto (fun n => ∫ x,f.average n x ∂μ) atTop (𝓝 (∫ x,g x ∂μ)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ne_atTop 0] with n hn
    exact (he n hn).symm
  exact tendsto_nhds_unique ht hc

theorem exists_bounded_birkhoff_limit {μ : Measure X} [IsFiniteMeasure μ]
    (hT : MeasurePreserving T μ μ) {g : X → ℝ} (hg : Measurable g)
    (h0 : ∀ x,0≤g x) (h1 : ∀ x,g x≤1) :
    ∃ G : X → ℝ, Measurable G ∧ (∀ x,0≤G x ∧ G x≤1) ∧ (∀ x,G (T x)=G x) ∧
      (∀ᵐ x ∂μ,Tendsto (fun n : ℕ => birkhoffSum T g n x/(n : ℝ)) atTop (𝓝 (G x))) ∧
      ∀ A : Set X, MeasurableSet A → T ⁻¹' A=A → ∫ x in A,G x ∂μ=∫ x in A,g x ∂μ := by
  let f := observationCocycle g hT.measurable hg h0 h1
  refine ⟨f.lowerRate,f.measurable_lowerRate,f.lowerRate_bounds,f.lowerRate_shift,f.ae_tendsto_average hT,?_⟩
  intro A hA hTA
  have hm : MeasurePreserving T (μ.restrict A) (μ.restrict A) := by
    simpa only [hTA] using hT.restrict_preimage hA
  exact observation_integral_rate hm hg h0 h1

theorem forward_backward_birkhoff {μ : Measure X} [IsFiniteMeasure μ]
    {S : X → X} (hT : MeasurePreserving T μ μ) (hS : MeasurePreserving S μ μ)
    (hST : ∀ x,S (T x)=x) (hTS : ∀ x,T (S x)=x)
    {g : X → ℝ} (hg : Measurable g) (h0 : ∀ x,0≤g x) (h1 : ∀ x,g x≤1) :
    ∃ G : X → ℝ, Measurable G ∧ (∀ x,0≤G x ∧ G x≤1) ∧ (∀ x,G (T x)=G x) ∧
      ∀ᵐ x ∂μ,
        Tendsto (fun n : ℕ => birkhoffSum T g n x/(n : ℝ)) atTop (𝓝 (G x)) ∧
        Tendsto (fun n : ℕ => birkhoffSum S g n x/(n : ℝ)) atTop (𝓝 (G x)) := by
  obtain ⟨F,hFm,hFb,hFT,hFconv,hFint⟩ := exists_bounded_birkhoff_limit hT hg h0 h1
  obtain ⟨B,hBm,hBb,hBS,hBconv,hBint⟩ := exists_bounded_birkhoff_limit hS hg h0 h1
  have hFS (x : X) : F (S x)=F x := by simpa only [hTS] using (hFT (S x)).symm
  have hBT (x : X) : B (T x)=B x := by simpa only [hST] using (hBS (T x)).symm
  have hFi : Integrable F μ := (integrable_const (1 : ℝ)).mono' hFm.aestronglyMeasurable
    (Eventually.of_forall fun x => by rw [Real.norm_eq_abs,abs_of_nonneg (hFb x).1]; exact (hFb x).2)
  have hBi : Integrable B μ := (integrable_const (1 : ℝ)).mono' hBm.aestronglyMeasurable
    (Eventually.of_forall fun x => by rw [Real.norm_eq_abs,abs_of_nonneg (hBb x).1]; exact (hBb x).2)
  have hle : F≤ᵐ[μ] B := by
    let A := {x | B x<F x}
    have hA : MeasurableSet A := measurableSet_lt hBm hFm
    have hAT : T ⁻¹' A=A := by ext x; simp only [A,mem_preimage,mem_ofPred_eq,hBT,hFT]
    have hAS : S ⁻¹' A=A := by ext x; simp only [A,mem_preimage,mem_ofPred_eq,hBS,hFS]
    have he : (∫ x in A,F x-B x ∂μ)=0 := by
      rw [integral_sub hFi.integrableOn hBi.integrableOn,hFint A hA hAT,hBint A hA hAS,sub_self]
    have hn : 0≤ᵐ[μ.restrict A] (fun x => F x-B x) :=
      (ae_restrict_mem hA).mono fun x hx => sub_nonneg.mpr (le_of_lt hx)
    have hz := (integral_eq_zero_iff_of_nonneg_ae hn (hFi.sub hBi).integrableOn).mp he
    filter_upwards [(ae_restrict_iff' hA).mp hz] with x hx
    by_contra he'
    have hh := hx (not_le.mp he')
    change F x-B x=0 at hh
    linarith
  have hge : B≤ᵐ[μ] F := by
    let A := {x | F x<B x}
    have hA : MeasurableSet A := measurableSet_lt hFm hBm
    have hAT : T ⁻¹' A=A := by ext x; simp only [A,mem_preimage,mem_ofPred_eq,hBT,hFT]
    have hAS : S ⁻¹' A=A := by ext x; simp only [A,mem_preimage,mem_ofPred_eq,hBS,hFS]
    have he : (∫ x in A,B x-F x ∂μ)=0 := by
      rw [integral_sub hBi.integrableOn hFi.integrableOn,hFint A hA hAT,hBint A hA hAS,sub_self]
    have hn : 0≤ᵐ[μ.restrict A] (fun x => B x-F x) :=
      (ae_restrict_mem hA).mono fun x hx => sub_nonneg.mpr (le_of_lt hx)
    have hz := (integral_eq_zero_iff_of_nonneg_ae hn (hBi.sub hFi).integrableOn).mp he
    filter_upwards [(ae_restrict_iff' hA).mp hz] with x hx
    by_contra he'
    have hh := hx (not_le.mp he')
    change B x-F x=0 at hh
    linarith
  refine ⟨F,hFm,hFb,hFT,?_⟩
  filter_upwards [hFconv,hBconv,hle,hge] with x hx hy hxy hyx
  exact ⟨hx,by simpa only [le_antisymm hyx hxy] using hy⟩

end BoundedSubadditive

end
section
open MeasureTheory Filter Set Topology
open scoped Topology ENNReal BigOperators

lemma birkhoff_difference_tendsto_zero {X : Type*} [PseudoMetricSpace X]
    {T : X → X} {g : X → ℝ} (hg : UniformContinuous g) {x y : X}
    (hxy : Tendsto (fun n : ℕ => dist (T^[n] x) (T^[n] y)) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => birkhoffSum T g n x/(n : ℝ)-birkhoffSum T g n y/(n : ℝ)) atTop (𝓝 0) := by
  have hdiff : Tendsto (fun n : ℕ => g (T^[n] x)-g (T^[n] y)) atTop (𝓝 0) := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    obtain ⟨δ,hδ,hδg⟩ := Metric.uniformContinuous_iff.mp hg ε hε
    filter_upwards [hxy.eventually (eventually_lt_nhds hδ)] with n hn
    simpa only [Real.dist_eq,sub_zero] using hδg hn
  have hc := hdiff.cesaro
  convert hc using 1
  all_goals try with_reducible_and_instances rfl
  funext n
  simp only [birkhoffSum,Finset.sum_sub_distrib,div_eq_mul_inv]
  ring

lemma birkhoff_limit_eq_of_asymptotic {X : Type*} [PseudoMetricSpace X]
    {T : X → X} {g : X → ℝ} (hg : UniformContinuous g) {x y : X}
    (hxy : Tendsto (fun n : ℕ => dist (T^[n] x) (T^[n] y)) atTop (𝓝 0))
    {a b : ℝ} (hx : Tendsto (fun n : ℕ => birkhoffSum T g n x/(n : ℝ)) atTop (𝓝 a))
    (hy : Tendsto (fun n : ℕ => birkhoffSum T g n y/(n : ℝ)) atTop (𝓝 b)) : a=b :=
  sub_eq_zero.mp (tendsto_nhds_unique (hx.sub hy) (birkhoff_difference_tendsto_zero hg hxy))

namespace StandardMapEntropy

lemma complexProjection_dist_le (z w : ℂ) : dist (complexProjection z) (complexProjection w)≤‖z-w‖ := by
  change max (dist (z.re : Circle) (w.re : Circle)) (dist (z.im : Circle) (w.im : Circle))≤‖z-w‖
  apply max_le
  · calc
      dist (z.re : Circle) (w.re : Circle)=‖((z.re-w.re : ℝ) : Circle)‖ := by
        rw [dist_eq_norm,←QuotientAddGroup.mk_sub]
      _ ≤ |z.re-w.re| := QuotientAddGroup.norm_mk_le_norm
      _ ≤ ‖z-w‖ := Complex.abs_re_le_norm (z-w)
  · calc
      dist (z.im : Circle) (w.im : Circle)=‖((z.im-w.im : ℝ) : Circle)‖ := by
        rw [dist_eq_norm,←QuotientAddGroup.mk_sub]
      _ ≤ |z.im-w.im| := QuotientAddGroup.norm_mk_le_norm
      _ ≤ ‖z-w‖ := Complex.abs_im_le_norm (z-w)

lemma fineStableCurve_asymptotic (k χ ε δ : ℝ) (hδ : 0<δ) (hq : Real.exp (-χ+ε)+δ<1)
    (w : ℂ) (hw : ∀ n : ℕ, FineRegular k χ ε (complexProjection ((standardLift k)^[n] w)))
    {s t : ℝ} (hs : |s|≤1) (ht : |t|≤1) :
    Tendsto (fun n : ℕ => dist ((standardMap k)^[n] (complexProjection (fineStableCurve k χ ε δ hδ hq w hw s)))
      ((standardMap k)^[n] (complexProjection (fineStableCurve k χ ε δ hδ hq w hw t)))) atTop (𝓝 0) := by
  have hq0 : 0≤Real.exp (-χ+ε)+δ := by positivity
  have hc := ((tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq).const_mul (2*fineScale k ε δ)).mul_const |s-t|
  simp only [mul_zero,zero_mul] at hc
  simpa only [complexProjection_iterate] using squeeze_zero (fun _ => dist_nonneg)
    (fun n => (complexProjection_dist_le _ _).trans (fineStableCurve_contraction k χ ε δ hδ hq w hw hs ht n)) hc

end StandardMapEntropy

end
section
namespace StandardMapEntropy
open MeasureTheory Set Filter Topology
open scoped Topology NNReal ENNReal
open NonlinearStable

@[simp] lemma fineUnstableCurve_zero (k χ ε δ : ℝ) (hδ : 0<δ) (hq : Real.exp (-χ+ε)+δ<1)
    (w : ℂ) (hw : ∀ n : ℕ, FineRegular k χ ε (complexProjection ((standardLift k)^[n] (tangentReversal w)))) :
    fineUnstableCurve k χ ε δ hδ hq w hw 0=w := by
  simp only [fineUnstableCurve,fineStableCurve_zero,tangentReversal_involutive]
lemma fineUnstableCurve_contraction (k χ ε δ : ℝ) (hδ : 0<δ) (hq : Real.exp (-χ+ε)+δ<1)
    (w : ℂ) (hw : ∀ n : ℕ, FineRegular k χ ε (complexProjection ((standardLift k)^[n] (tangentReversal w))))
    {s t : ℝ} (hs : |s|≤1) (ht : |t|≤1) (n : ℕ) :
    ‖(standardInverseLift k)^[n] (fineUnstableCurve k χ ε δ hδ hq w hw s)-
      (standardInverseLift k)^[n] (fineUnstableCurve k χ ε δ hδ hq w hw t)‖≤
      (6*fineScale k ε δ)*(Real.exp (-χ+ε)+δ)^n*|s-t| := by
  simp only [fineUnstableCurve,inverse_lift_iterate_reversed,←map_sub]
  exact ((tangentReversal_norm_le _).trans (mul_le_mul_of_nonneg_left
    (fineStableCurve_contraction k χ ε δ hδ hq (tangentReversal w) hw hs ht n) (by norm_num))).trans_eq (by ring)
lemma fineUnstableCurve_asymptotic (k χ ε δ : ℝ) (hδ : 0<δ) (hq : Real.exp (-χ+ε)+δ<1)
    (w : ℂ) (hw : ∀ n : ℕ, FineRegular k χ ε (complexProjection ((standardLift k)^[n] (tangentReversal w))))
    {s t : ℝ} (hs : |s|≤1) (ht : |t|≤1) :
    Tendsto (fun n : ℕ => dist ((inverseMap k)^[n] (complexProjection (fineUnstableCurve k χ ε δ hδ hq w hw s)))
      ((inverseMap k)^[n] (complexProjection (fineUnstableCurve k χ ε δ hδ hq w hw t)))) atTop (𝓝 0) := by
  have hq0 : 0≤Real.exp (-χ+ε)+δ := by positivity
  have hc := ((tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq).const_mul (6*fineScale k ε δ)).mul_const |s-t|
  simp only [mul_zero,zero_mul] at hc
  simpa only [complexProjection_inverse_iterate] using squeeze_zero (fun _ => dist_nonneg)
    (fun n => (complexProjection_dist_le _ _).trans (fineUnstableCurve_contraction k χ ε δ hδ hq w hw hs ht n)) hc

end StandardMapEntropy

end
end

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_Components_FineChartGraph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace StandardMapEntropy
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
open NonlinearStable

lemma fine_plaque_second_bound (k χ ε δ : ℝ) (hδ : 0<δ) (hq : Real.exp (-χ+ε)+δ<1)
    (w v : ℂ) (hv : ∀ n : ℕ,FineRegular k χ ε (complexProjection ((standardLift k)^[n] v)))
    {η τ : ℝ} (hη : 0≤η)
    (hclose : ‖(fineInverse k χ ε δ (complexProjection w)).comp
      (fineFrame k χ ε δ (complexProjection v))-ContinuousLinearMap.id ℝ Plane‖≤η)
    (hslope : Real.exp (-χ+ε)*δ/(1-Real.exp (-χ+ε))≤τ) (s t : ℝ) :
    |(finePlaqueInChart k χ ε δ hδ hq w v hv s).2-
      (finePlaqueInChart k χ ε δ hδ hq w v hv t).2|≤(τ+η)*|s-t| := by
  let I := fineInverse k χ ε δ (complexProjection w)
  let F := fineFrame k χ ε δ (complexProjection v)
  let g := fineStableGraph k χ ε δ hδ hq v hv
  let u : Plane := (s,g s)-(t,g t)
  have he : (finePlaqueInChart k χ ε δ hδ hq w v hv s).2-
      (finePlaqueInChart k χ ε δ hδ hq w v hv t).2=
      (((I.comp F)-ContinuousLinearMap.id ℝ Plane) u).2+(g s-g t) := by
    change (I (v+F (s,g s)-w)).2-(I (v+F (t,g t)-w)).2=_
    simp only [map_sub,map_add,Prod.snd_add,Prod.snd_sub,sub_apply,
      ContinuousLinearMap.comp_apply,ContinuousLinearMap.id_apply,u]
    ring
  rw [he]
  have herr : |(((I.comp F)-ContinuousLinearMap.id ℝ Plane) u).2|≤η*|s-t| :=
    (norm_snd_le _).trans ((ContinuousLinearMap.le_opNorm _ _).trans
      ((mul_le_mul_of_nonneg_right hclose (norm_nonneg u)).trans
        (mul_le_mul_of_nonneg_left (fine_graph_pair_bound k χ ε δ hδ hq v hv s t) hη)))
  have hg : |g s-g t|≤τ*|s-t| := (fineStableGraph_slope k χ ε δ hδ hq v hv s t).trans
    (mul_le_mul_of_nonneg_right hslope (abs_nonneg _))
  exact (abs_add_le _ _).trans ((add_le_add herr hg).trans_eq (by ring))

theorem fine_compact_chart_graph {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (k χ ε δ : ℝ) (hδ : 0<δ) (hq : Real.exp (-χ+ε)+δ<1)
    (w : ℂ) (v : X → ℂ) (hvc : Continuous v)
    (hv : ∀ x,∀ n : ℕ,FineRegular k χ ε (complexProjection ((standardLift k)^[n] (v x))))
    (hdata : ∀ n : ℕ,Continuous (fun x => lyapunovChartData k χ ε
      (complexProjection ((standardLift k)^[n] (v x)))))
    {r η τ : ℝ} (hr : 0 < r) (hr1 : r≤1) (hη : 0≤η) (hη' : η≤1/4) (hτ : 0≤τ)
    (hclose : ∀ x,‖(fineInverse k χ ε δ (complexProjection w)).comp
      (fineFrame k χ ε δ (complexProjection (v x)))-ContinuousLinearMap.id ℝ Plane‖≤η)
    (hslope : Real.exp (-χ+ε)*δ/(1-Real.exp (-χ+ε))≤τ)
    (hcentre : ∀ x,|(fineInverse k χ ε δ (complexProjection w) (v x-w)).1| ≤ r/4) :
    ∃ (G σ : X → ℝ → ℝ),
      Continuous (fun p : X×ℝ => G p.1 p.2) ∧ Continuous (fun p : X×ℝ => σ p.1 p.2) ∧
      (∀ x s t,|G x s-G x t|≤((4/3)*(τ+η))*|s-t|) ∧
      (∀ x s,|σ x s| ≤ r) ∧
      (∀ x s,s∈Icc (-r/2) (r/2) →
        finePlaqueInChart k χ ε δ hδ hq w (v x) (hv x) (σ x s)=(s,G x s)) ∧
      (∀ x,σ x ((fineInverse k χ ε δ (complexProjection w) (v x-w)).1)=0 ∧
        G x ((fineInverse k χ ε δ (complexProjection w) (v x-w)).1)=
          (fineInverse k χ ε δ (complexProjection w) (v x-w)).2) := by
  obtain ⟨s,hs,hsval⟩ := fine_compact_graph_crossing k χ ε δ hδ hq w v hvc hv hdata hr hr1
    (fun x => (hclose x).trans hη') hcentre
  let c : ℝ → Icc (-r/2) (r/2) := projIcc (-r/2) (r/2) (by linarith)
  let σ (x : X) (t : ℝ) : ℝ := s (x,c t)
  let G (x : X) (t : ℝ) := (finePlaqueInChart k χ ε δ hδ hq w (v x) (hv x) (σ x t)).2
  have hσ : Continuous (fun p : X×ℝ => σ p.1 p.2) :=
    continuous_subtype_val.comp (hs.comp (continuous_fst.prodMk (continuous_projIcc.comp continuous_snd)))
  have hσbound (x : X) (t : ℝ) : |σ x t| ≤ r := abs_le.mpr (s (x,c t)).property
  have hG : Continuous (fun p : X×ℝ => G p.1 p.2) := by
    let param : X×ℝ → Icc (-1 : ℝ) 1 := fun p => ⟨σ p.1 p.2,abs_le.mp ((hσbound _ _).trans hr1)⟩
    have hparam : Continuous param := hσ.subtype_mk _
    have hc := continuous_fineStableCurve_family k χ ε δ hδ hq v hvc hv hdata
    exact continuous_snd.comp ((fineInverse k χ ε δ (complexProjection w)).continuous.comp
      ((hc.comp (continuous_fst.prodMk hparam)).sub continuous_const))
  have hσval (x : X) (t : ℝ) :
      (finePlaqueInChart k χ ε δ hδ hq w (v x) (hv x) (σ x t)).1=(c t : ℝ) := hsval (x,c t)
  have hpoint (x : X) (t : ℝ) (ht : t∈Icc (-r/2) (r/2)) :
      finePlaqueInChart k χ ε δ hδ hq w (v x) (hv x) (σ x t)=(t,G x t) := by
    refine Prod.ext ?_ rfl
    exact (hσval x t).trans (by dsimp only [c]; rw [projIcc_of_mem _ ht])
  refine ⟨G,σ,hG,hσ,?_,hσbound,hpoint,?_⟩
  · intro x a b
    have hvab := fine_plaque_linear_error k χ ε δ hδ hq w (v x) (hv x)
      ((hclose x).trans hη') (σ x a) (σ x b)
    rw [hσval,hσval] at hvab
    have hd : |σ x a-σ x b|≤(4/3)*|(c a : ℝ)-(c b : ℝ)| := by
      have hex : σ x a-σ x b=((c a : ℝ)-(c b : ℝ))-
          ((c a : ℝ)-(c b : ℝ)-(σ x a-σ x b)) := by ring
      have hh := abs_sub ((c a : ℝ)-(c b : ℝ)) ((c a : ℝ)-(c b : ℝ)-(σ x a-σ x b))
      rw [←hex] at hh
      linarith
    have hg := fine_plaque_second_bound k χ ε δ hδ hq w (v x) (hv x) hη (hclose x) hslope (σ x a) (σ x b)
    apply hg.trans
    calc
      (τ+η)*|σ x a-σ x b|≤(τ+η)*((4/3)*|(c a : ℝ)-(c b : ℝ)|) := mul_le_mul_of_nonneg_left hd (add_nonneg hτ hη)
      _ ≤ (τ+η)*((4/3)*|a-b|) := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (abs_projIcc_sub_projIcc _) (by norm_num)) (add_nonneg hτ hη)
      _ = (4/3)*(τ+η)*|a-b| := by ring
  · intro x
    let t := (fineInverse k χ ε δ (complexProjection w) (v x-w)).1
    have ht : t∈Icc (-r/2) (r/2) := by have := abs_le.mp (hcentre x); constructor <;> linarith
    have hp := hpoint x t ht
    have hzero : finePlaqueInChart k χ ε δ hδ hq w (v x) (hv x) 0=
        fineInverse k χ ε δ (complexProjection w) (v x-w) := by rw [finePlaqueInChart,fineStableCurve_zero]
    have hz : σ x t=0 := fine_plaque_crossing_unique k χ ε δ hδ hq w (v x) (hv x)
      ((hclose x).trans hη') ((congrArg Prod.fst hp).trans (by change t=(finePlaqueInChart k χ ε δ hδ hq w (v x) (hv x) 0).1; rw [hzero]))
    refine ⟨hz,?_⟩
    change (finePlaqueInChart k χ ε δ hδ hq w (v x) (hv x) (σ x t)).2=_
    rw [hz,hzero]

end StandardMapEntropy

end
section
namespace StandardMapEntropy
open MeasureTheory Set Filter Topology
open scoped Topology ENNReal
open NonlinearStable

namespace ReversibleRectangleBlock
variable {k χ : ℝ} (B : ReversibleRectangleBlock k χ)

@[simp] lemma coordinates_chart (p : RealPlane) : B.coordinates (B.chart p)=p := by
  rw [coordinates,chart,add_sub_cancel_left,fineInverse_frame k χ B.ε B.δ_pos _ B.centre_regular]
lemma coordinates_swap (v : ℂ) : B.coordinates v=(B.β*(B.reverseCoordinates v).2,B.α*(B.reverseCoordinates v).1) := by
  have h := B.swap (B.reverseCoordinates v)
  rw [reverseCoordinates,fineFrame_inverse k χ B.ε B.δ_pos _ B.reverse_regular,map_sub,tangentReversal_involutive,
    tangentReversal_involutive] at h
  exact h
lemma continuous_chart : Continuous B.chart := by unfold chart; fun_prop
lemma continuous_coordinates : Continuous B.coordinates := by unfold coordinates; fun_prop

end ReversibleRectangleBlock

theorem reversible_graph_families {k χ : ℝ} (B : ReversibleRectangleBlock k χ) :
    Nonempty (ReversibleGraphFamilies B) := by
  let : CompactSpace B.carrier := isCompact_iff_compactSpace.mp B.compact
  have hd : Continuous (fun v : B.carrier => (orbitChartData k χ B.ε (complexProjection v),
      orbitChartData k χ B.ε (complexProjection (tangentReversal v)))) :=
    continuousOn_iff_continuous_domRestrict.mp B.data
  have hdata (n : ℕ) : Continuous (fun v : B.carrier => lyapunovChartData k χ B.ε
      (complexProjection ((standardLift k)^[n] v))) := by
    simpa only [Function.comp_def,orbitChartData,complexProjection_iterate] using ((continuous_apply n).comp hd.fst).fst
  have hdataR (n : ℕ) : Continuous (fun v : B.carrier => lyapunovChartData k χ B.ε
      (complexProjection ((standardLift k)^[n] (tangentReversal v)))) := by
    simpa only [Function.comp_def,orbitChartData,complexProjection_iterate] using ((continuous_apply n).comp hd.snd).fst
  have hη : B.η≤1/4 := B.η_small.trans (by norm_num)
  have hcent (v : B.carrier) : |(B.coordinates v).1|≤B.r/4 := by
    have hh := (norm_fst_le (B.coordinates v)).trans (B.central v v.property)
    simpa only [Real.norm_eq_abs] using hh.trans (by linarith [B.ρ_small,B.r_pos])
  have hcentR (v : B.carrier) : |(B.reverseCoordinates v).1|≤B.r'/4 :=
    (norm_fst_le _).trans (B.reverse_central v v.property)
  obtain ⟨G,σ,hG,hσ,hsG,hσb,hrep,hG0⟩ := fine_compact_chart_graph k χ B.ε B.δ B.δ_pos B.contraction
    B.centre (fun v : B.carrier => (v : ℂ)) continuous_subtype_val (fun v => B.regular v v.property)
    hdata B.r_pos (by linarith [B.r_small]) B.η_pos.le hη B.η_pos.le
    (fun v => B.frames v v.property) B.slope hcent
  obtain ⟨GR,σR,hGR,hσR,hsGR,hσRb,hrepR,hGR0⟩ := fine_compact_chart_graph k χ B.ε B.δ B.δ_pos B.contraction
    (tangentReversal B.centre) (fun v : B.carrier => tangentReversal v)
    (tangentReversal.continuous.comp continuous_subtype_val) (fun v => B.reversed v v.property)
    hdataR B.r'_pos (by linarith [B.r'_small]) B.η_pos.le hη B.η_pos.le
    (fun v => B.reverse_frames v v.property) B.slope hcentR
  let U (a : B.carrier) (s : ℝ) := B.β*GR a (s/B.α)
  let τ (a : B.carrier) (s : ℝ) := σR a (s/B.α)
  have hUc : Continuous (fun p : B.carrier×ℝ => U p.1 p.2) :=
    continuous_const.mul (hGR.comp (continuous_fst.prodMk (continuous_snd.div_const B.α)))
  have hτc : Continuous (fun p : B.carrier×ℝ => τ p.1 p.2) :=
    hσR.comp (continuous_fst.prodMk (continuous_snd.div_const B.α))
  have hUslope (a : B.carrier) (s t : ℝ) : |U a s-U a t|≤(1/2)*|s-t| := by
    have hh := mul_le_mul_of_nonneg_left (hsGR a (s/B.α) (t/B.α)) (abs_nonneg B.β)
    have he : |U a s-U a t|=|B.β| * |GR a (s/B.α)-GR a (t/B.α)| := by
      dsimp only [U]; rw [←mul_sub,abs_mul]
    rw [he]
    apply hh.trans
    rw [←sub_div,abs_div]
    have he' : |B.β| * ((4/3)*(B.η+B.η)*(|s-t|/|B.α|))=
        ((|B.β|/|B.α|)*((8/3)*B.η))*|s-t| := by ring
    rw [he']
    exact mul_le_mul_of_nonneg_right B.reverse_slope (abs_nonneg _)
  have hU0 (a : B.carrier) : U a (B.coordinates a).2=(B.coordinates a).1 := by
    have he := B.coordinates_swap a
    have he1 := congrArg Prod.fst he
    have he2 := congrArg Prod.snd he
    change (B.coordinates a).1=B.β*(B.reverseCoordinates a).2 at he1
    change (B.coordinates a).2=B.α*(B.reverseCoordinates a).1 at he2
    dsimp only [U]
    rw [he2,mul_div_cancel_left₀ _ B.α_ne]
    have hGR0' : GR a (B.reverseCoordinates a).1=(B.reverseCoordinates a).2 := (hGR0 a).2
    rw [hGR0']
    exact he1.symm
  refine ⟨{
    G := G,U := U,stableParameter := σ,unstableParameter := τ,
    continuous_G := hG,continuous_U := hUc,continuous_stableParameter := hσ,continuous_unstableParameter := hτc,
    slope_G := fun a s t => (hsG a s t).trans (mul_le_mul_of_nonneg_right (by linarith [B.η_small]) (abs_nonneg _)),
    slope_U := hUslope,stable_bound := hσb,unstable_bound := fun a s => hσRb a (s/B.α),
    stable_representation := ?_,unstable_representation := ?_,G_centre := fun a => (hG0 a).2,U_centre := hU0 }⟩
  · intro a s hs
    have hh := hrep a s (by exact ⟨by linarith [(abs_le.mp hs).1],(abs_le.mp hs).2⟩)
    have hh' := congrArg B.chart hh
    change B.chart (B.coordinates (fineStableCurve k χ B.ε B.δ B.δ_pos B.contraction a (B.regular a a.property) (σ a s)))=_ at hh'
    rw [B.chart_coordinates] at hh'
    exact hh'.symm
  · intro a s hs
    have hdiv : |s/B.α|≤B.r'/2 := by
      rw [abs_div]
      apply (div_le_iff₀ (abs_pos.mpr B.α_ne)).mpr
      nlinarith
    have hh := hrepR a (s/B.α) ⟨by linarith [(abs_le.mp hdiv).1],(abs_le.mp hdiv).2⟩
    let z := fineUnstableCurve k χ B.ε B.δ B.δ_pos B.contraction a (B.reversed a a.property) (τ a s)
    have hzR : B.reverseCoordinates z=(s/B.α,GR a (s/B.α)) := by
      simpa only [ReversibleRectangleBlock.reverseCoordinates,z,fineUnstableCurve,tangentReversal_involutive,τ,
        finePlaqueInChart] using hh
    have hz := B.coordinates_swap z
    rw [hzR] at hz
    have hαs : B.α*(s/B.α)=s := by field_simp [B.α_ne]
    change B.coordinates z=(U a s,B.α*(s/B.α)) at hz
    rw [hαs] at hz
    have he := congrArg B.chart hz
    rw [B.chart_coordinates] at he
    exact he.symm

end StandardMapEntropy

end
section
namespace StandardMapEntropy
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
open NonlinearStable

theorem actual_stable_holonomy_local_bound (k : ℝ) (hk : 0≤k) (χ ε δ : ℝ)
    (hε : 0≤ε) (hδ : 0<δ) (hδ' : δ≤1/2) (hq : Real.exp (-χ+ε)+δ<1)
    (hslow : Real.exp (4*ε)*(Real.exp (-χ+ε)+δ)<1)
    (P Q W : ℂ) (S : Set ℝ) (H : ℝ → ℝ) (hH : ContinuousOn H S)
    (hmatch : ∀ t∈S, ∃ (v : ℂ)
      (hv : ∀ n : ℕ, FineRegular k χ ε (complexProjection ((standardLift k)^[n] v))) (s u : ℝ),
      |s|≤1/12 ∧ |u|≤1/12 ∧
      |(fineInverse k χ ε δ (complexProjection v) W).1|≤
        |(fineInverse k χ ε δ (complexProjection v) W).2| ∧
      (fineInverse k χ ε δ (complexProjection v) W).2≠0 ∧
      P+t•W=fineStableCurve k χ ε δ hδ hq v hv s ∧
      Q+H t•W=fineStableCurve k χ ε δ hδ hq v hv u) :
    ∀ t∈S,∀ᶠ t' in 𝓝[S] t,
      |H t'-H t|≤(2*Real.exp (8*δ/(1-(Real.exp (-χ+ε)+δ))))*|t'-t| := by
  intro t ht
  obtain ⟨v,hv,s,u,hs,hu,hcone,hnonzero,hleft,hright⟩ := hmatch t ht
  let I := fineInverse k χ ε δ (complexProjection v)
  have he (p : ℂ) (t : ℝ) : v+fineFrame k χ ε δ (complexProjection v) (I (p-v)+t•I W)=p+t•W :=
    fine_affine_coordinates k χ ε δ hδ v p W (hv 0) t
  have hleft' : v+fineFrame k χ ε δ (complexProjection v) (I (P-v)+t•I W)=
      fineStableCurve k χ ε δ hδ hq v hv s := (he P t).trans hleft
  have hright' : v+fineFrame k χ ε δ (complexProjection v) (I (Q-v)+H t•I W)=
      fineStableCurve k χ ε δ hδ hq v hv u := (he Q (H t)).trans hright
  apply fine_stable_matching_local_bound k hk χ ε δ hε hδ hδ' hq hslow v hv
    (I (P-v)) (I (Q-v)) (I W) hcone hnonzero S H ht (hH t ht) hs hu hleft' hright'
  intro t' ht'
  obtain ⟨v',hv',s',u',hs',hu',_,_,hleft'',hright''⟩ := hmatch t' ht'
  exact ⟨v',hv',s',u',hs'.trans (by norm_num),hu'.trans (by norm_num),
    (he P t').trans hleft'',(he Q (H t')).trans hright''⟩

end StandardMapEntropy

end
section
namespace StandardMapEntropy
open MeasureTheory Set Filter Topology
open scoped Topology NNReal ENNReal

theorem compact_actual_stable_holonomy_bounds {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (k : ℝ) (hk : 0≤k) (χ ε δ : ℝ) (hε : 0≤ε) (hδ : 0<δ) (hδ' : δ≤1/2)
    (hq : Real.exp (-χ+ε)+δ<1) (hslow : Real.exp (4*ε)*(Real.exp (-χ+ε)+δ)<1)
    (P Q W : ℂ) (f g : X → ℝ) (hf : Continuous f) (hg : Continuous g)
    (hfib : ∀ x y, f x=f y ↔ g x=g y)
    (hplaque : ∀ x, ∃ (v : ℂ)
      (hv : ∀ n : ℕ, FineRegular k χ ε (complexProjection ((standardLift k)^[n] v))) (s u : ℝ),
      |s|≤1/12 ∧ |u|≤1/12 ∧
      |(fineInverse k χ ε δ (complexProjection v) W).1|≤
        |(fineInverse k χ ε δ (complexProjection v) W).2| ∧
      (fineInverse k χ ε δ (complexProjection v) W).2≠0 ∧
      P+f x•W=fineStableCurve k χ ε δ hδ hq v hv s ∧
      Q+g x•W=fineStableCurve k χ ε δ hδ hq v hv u) :
    ∃ H J : ℝ → ℝ,
      ContinuousOn H (range f) ∧ ContinuousOn J (range g) ∧
      (∀ x, H (f x)=g x ∧ J (g x)=f x) ∧
      (∀ y∈range f, J (H y)=y) ∧ (∀ y∈range g, H (J y)=y) ∧
      (∀ t∈range f,∀ᶠ t' in 𝓝[range f] t,
        |H t'-H t|≤(2*Real.exp (8*δ/(1-(Real.exp (-χ+ε)+δ))))*|t'-t|) ∧
      (∀ t∈range g,∀ᶠ t' in 𝓝[range g] t,
        |J t'-J t|≤(2*Real.exp (8*δ/(1-(Real.exp (-χ+ε)+δ))))*|t'-t|) := by
  obtain ⟨H,hH,hHval⟩ := compact_fibre_descent hf hg (fun x y h => (hfib x y).mp h)
  obtain ⟨J,hJ,hJval⟩ := compact_fibre_descent hg hf (fun x y h => (hfib x y).mpr h)
  refine ⟨H,J,hH,hJ,fun x => ⟨hHval x,hJval x⟩,?_,?_,?_,?_⟩
  · rintro y ⟨x,rfl⟩; rw [hHval,hJval]
  · rintro y ⟨x,rfl⟩; rw [hJval,hHval]
  · apply actual_stable_holonomy_local_bound k hk χ ε δ hε hδ hδ' hq hslow P Q W (range f) H hH
    rintro t ⟨x,rfl⟩
    obtain ⟨v,hv,s,u,hs,hu,hc,hn,hp,hq'⟩ := hplaque x
    exact ⟨v,hv,s,u,hs,hu,hc,hn,hp,by rw [hHval]; exact hq'⟩
  · apply actual_stable_holonomy_local_bound k hk χ ε δ hε hδ hδ' hq hslow Q P W (range g) J hJ
    rintro t ⟨x,rfl⟩
    obtain ⟨v,hv,s,u,hs,hu,hc,hn,hp,hq'⟩ := hplaque x
    exact ⟨v,hv,u,s,hu,hs,hc,hn,hq',by rw [hJval]; exact hp⟩

end StandardMapEntropy

end
section
namespace StandardMapEntropy
open MeasureTheory Set Filter Topology
open scoped Topology ENNReal
open NonlinearStable

theorem actual_graph_holonomy_bounds {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (k : ℝ) (hk : 0≤k) (χ ε δ : ℝ) (hε : 0≤ε) (hδ : 0<δ) (hδ' : δ≤1/2)
    (hq : Real.exp (-χ+ε)+δ<1) (hslow : Real.exp (4*ε)*(Real.exp (-χ+ε)+δ)<1)
    (w : ℂ) (hw : wedge (stableVector k (complexProjection w)) (unstableVector k (complexProjection w))≠0)
    (v : X → ℂ) (hv : ∀ a,∀ n : ℕ,FineRegular k χ ε (complexProjection ((standardLift k)^[n] (v a))))
    (G σ : X → ℝ → ℝ) (hG : Continuous (fun p : X×ℝ => G p.1 p.2))
    {r R : ℝ} (hr : 0 < r) (hrsmall : r≤1/12) (hR : 0<R)
    (hRv : ∀ a,R ≤ codingRadius k χ ε δ (complexProjection (v a)))
    (hsize : (4*fineScale k ε δ*r)/(100*R)+r≤1)
    (hclose : ∀ a,‖(fineInverse k χ ε δ (complexProjection w)).comp (fineFrame k χ ε δ (complexProjection (v a)))-ContinuousLinearMap.id ℝ Plane‖≤1/4)
    (hclose' : ∀ a,‖(fineInverse k χ ε δ (complexProjection (v a))).comp (fineFrame k χ ε δ (complexProjection w))-ContinuousLinearMap.id ℝ Plane‖≤1/4)
    (I : Set ℝ) (hσ : ∀ a s,s∈I → |σ a s| ≤ r)
    (hrep : ∀ a s,s∈I → w+fineFrame k χ ε δ (complexProjection w) (s,G a s)=
      fineStableCurve k χ ε δ hδ hq (v a) (hv a) (σ a s))
    {c d : ℝ} (hc : c∈I) (hd : d∈I) :
    ∃ H J : ℝ → ℝ,
      ContinuousOn H (range (fun a => G a c)) ∧ ContinuousOn J (range (fun a => G a d)) ∧
      (∀ a,H (G a c)=G a d ∧ J (G a d)=G a c) ∧
      (∀ y∈range (fun a => G a c),J (H y)=y) ∧
      (∀ y∈range (fun a => G a d),H (J y)=y) ∧
      (∀ t∈range (fun a => G a c),∀ᶠ t' in 𝓝[range (fun a => G a c)] t,
        |H t'-H t|≤(2*Real.exp (8*δ/(1-(Real.exp (-χ+ε)+δ))))*|t'-t|) ∧
      (∀ t∈range (fun a => G a d),∀ᶠ t' in 𝓝[range (fun a => G a d)] t,
        |J t'-J t|≤(2*Real.exp (8*δ/(1-(Real.exp (-χ+ε)+δ))))*|t'-t|) := by
  have hr1 : r≤1 := by linarith
  have hslo : Real.exp (2*ε)*(Real.exp (-χ+ε)+δ)≤1 :=
    (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (by linarith)) (by positivity)).trans hslow.le
  have coord (a : X) (s : ℝ) (hs : s∈I) :
      finePlaqueInChart k χ ε δ hδ hq w (v a) (hv a) (σ a s)=(s,G a s) := by
    unfold finePlaqueInChart
    rw [←hrep a s hs,add_sub_cancel_left,fineInverse_frame k χ ε hδ _ hw]
  have one (c d : ℝ) (hc : c∈I) (hd : d∈I) (a b : X) (he : G a c=G b c) : G a d=G b d := by
    have meet : fineStableCurve k χ ε δ hδ hq (v a) (hv a) (σ a c)=
        fineStableCurve k χ ε δ hδ hq (v b) (hv b) (σ b c) := by rw [←hrep a c hc,←hrep b c hc,he]
    have hh := fine_small_crossings_coincide k χ ε δ hδ hq hslo w (v a) (v b) (hv a) (hv b)
      hr hr1 hR (hRv a) hsize (hclose a) (hσ a c hc) (hσ a d hd) (hσ b c hc) (hσ b d hd)
      meet (by rw [coord a d hd,coord b d hd])
    have hh' := congrArg (fun z => (fineInverse k χ ε δ (complexProjection w) (z-w)).2) hh
    change (finePlaqueInChart k χ ε δ hδ hq w (v a) (hv a) (σ a d)).2=_ at hh'
    rw [coord a d hd] at hh'
    change G a d=(finePlaqueInChart k χ ε δ hδ hq w (v b) (hv b) (σ b d)).2 at hh'
    simpa only [coord b d hd] using hh'
  let W := fineFrame k χ ε δ (complexProjection w) (0,1)
  have endpoint (a : X) (s : ℝ) (hs : s∈I) :
      (w+fineFrame k χ ε δ (complexProjection w) (s,0))+G a s•W=
      fineStableCurve k χ ε δ hδ hq (v a) (hv a) (σ a s) := by
    dsimp only [W]
    rw [←map_smul,add_assoc,←map_add]
    have he : (s,0)+(G a s)•((0,1) : Plane)=(s,G a s) := by ext <;> simp
    rw [he,hrep a s hs]
  apply compact_actual_stable_holonomy_bounds k hk χ ε δ hε hδ hδ' hq hslow
    (w+fineFrame k χ ε δ (complexProjection w) (c,0))
    (w+fineFrame k χ ε δ (complexProjection w) (d,0)) W
    (fun a => G a c) (fun a => G a d)
    (hG.comp (continuous_id.prodMk continuous_const)) (hG.comp (continuous_id.prodMk continuous_const))
    (fun a b => ⟨one c d hc hd a b,one d c hd hc a b⟩)
  intro a
  exact ⟨v a,hv a,σ a c,σ a d,(hσ a c hc).trans hrsmall,(hσ a d hd).trans hrsmall,
    (fine_transverse_cone k χ ε δ w (v a) (hclose' a)).1,
    (fine_transverse_cone k χ ε δ w (v a) (hclose' a)).2,endpoint a c hc,endpoint a d hd⟩

end StandardMapEntropy

end
end

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_Components_CurvedHolonomy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace StandardMapEntropy
open MeasureTheory Set Filter Topology
open scoped Topology ENNReal

lemma AffineGraphControl.fibres {X : Type*} {G : X → ℝ → ℝ} {I : Set ℝ} {K : ℝ}
    (h : AffineGraphControl G I K) {c d : ℝ} (hc : c∈I) (hd : d∈I) (a b : X) :
    G a c=G b c ↔ G a d=G b d := by
  obtain ⟨H,_,hH,_⟩ := h c hc d hd
  obtain ⟨J,_,hJ,_⟩ := h d hd c hc
  constructor
  · intro he; rw [←hH a,←hH b,he]
  · intro he; rw [←hJ a,←hJ b,he]

theorem compact_curved_inverse_control {X : Type*} [TopologicalSpace X] [CompactSpace X]
    {G : X → ℝ → ℝ} (hGc : Continuous (fun p : X×ℝ => G p.1 p.2))
    {I : Set ℝ} {K κ ℓ : ℝ} (hK : 0≤K) (hκ : 0≤κ) (hℓ : 0≤ℓ) (hcone : κ*ℓ<1)
    (hG : ∀ a s t,|G a s-G a t|≤κ*|s-t|) (hh : AffineGraphControl G I K)
    (u : ℝ → ℝ) (hu : ∀ s t,|u s-u t|≤ℓ*|s-t|)
    (g : X → ℝ) (hg : Continuous g) (hmatch : ∀ a,g a=G a (u (g a)))
    (hwithin : ∀ a,u (g a)∈I)
    {c : ℝ} (hc : c∈I) :
    ∃ J : ℝ → ℝ,ContinuousOn J (range g) ∧ (∀ a,J (g a)=G a c) ∧
      ∀ t∈range g,∀ᶠ t' in 𝓝[range g] t,|J t'-J t|≤(K*(1+κ*ℓ))*|t'-t| := by
  have fibre (a b : X) (d : ℝ) (hd : d∈I) : g a=g b ↔ G a d=G b d := by
    constructor
    · intro he
      apply (hh.fibres (hwithin a) hd a b).mp
      rw [←hmatch a,he,←he,he,←hmatch b]
    · intro he
      have hsame := (hh.fibres (hwithin b) hd a b).mpr he
      have hdist : |g a-g b|≤κ*(ℓ*|g a-g b|) := by
        calc
          |g a-g b| = |G a (u (g a))-G a (u (g b))| := by rw [hsame,←hmatch a,←hmatch b]
          _ ≤ κ*(ℓ*|g a-g b|) := (hG a _ _).trans (mul_le_mul_of_nonneg_left (hu _ _) hκ)
      apply sub_eq_zero.mp
      apply abs_eq_zero.mp
      exact le_antisymm (by nlinarith [mul_nonneg (sub_pos.mpr hcone).le (abs_nonneg (g a-g b))]) (abs_nonneg _)
  obtain ⟨J,hJ,hJval⟩ := compact_fibre_descent hg
    (hGc.comp (continuous_id.prodMk continuous_const)) (fun a b he => (fibre a b c hc).mp he)
  change ∀ a,J (g a)=G a c at hJval
  refine ⟨J,hJ,hJval,?_⟩
  rintro t ⟨a,rfl⟩
  let d := u (g a)
  have hd : d∈I := hwithin a
  obtain ⟨H,hH,hHval,hHbound⟩ := hh d hd c hc
  obtain ⟨V,hV,hVval⟩ := compact_fibre_descent hg
    (show Continuous (fun b => G b d) from hGc.comp (continuous_id.prodMk continuous_const)) (fun a b he => (fibre a b d hd).mp he)
  change ∀ b,V (g b)=G b d at hVval
  have hmaps : MapsTo V (range g) (range (fun b => G b d)) := by
    rintro _ ⟨b,rfl⟩; exact ⟨b,(hVval b).symm⟩
  have hv : Tendsto V (𝓝[range g] (g a)) (𝓝[range (fun b => G b d)] (G a d)) := by
    rw [←hVval a]
    exact tendsto_nhdsWithin_iff.mpr ⟨hV (g a) ⟨a,rfl⟩,Eventually.mono self_mem_nhdsWithin hmaps⟩
  filter_upwards [hv.eventually (hHbound (G a d) ⟨a,rfl⟩),self_mem_nhdsWithin] with t ht htS
  obtain ⟨b,rfl⟩ := htS
  rw [hVval b,hHval b,hHval a] at ht
  rw [hJval b,hJval a]
  apply ht.trans
  have hm : |G b d-G a d|≤(1+κ*ℓ)*|g b-g a| := by
    have hea : G a d=g a := (hmatch a).symm
    calc
      |G b d-G a d| = |G b (u (g a))-g a| := by rw [hea]
      _ ≤ |G b (u (g a))-G b (u (g b))|+|G b (u (g b))-g a| := abs_sub_le _ _ _
      _ ≤ κ*(ℓ*|g a-g b|)+|g b-g a| := add_le_add
        ((hG b _ _).trans (by
          simpa only [mul_comm] using mul_le_mul (hu _ _) le_rfl hκ (mul_nonneg hℓ (abs_nonneg _)))) (by rw [←hmatch b])
      _ = (1+κ*ℓ)*|g b-g a| := by rw [abs_sub_comm (g a) (g b)]; ring
  exact (mul_le_mul_of_nonneg_left hm hK).trans_eq (by ring)

end StandardMapEntropy

namespace StandardMapEntropy
open Set Filter Topology
open scoped Topology
lemma AffineGraphControl.comp {X Y : Type*} {G : Y → ℝ → ℝ} {I : Set ℝ} {K : ℝ}
    (h : AffineGraphControl G I K) (f : X → Y) : AffineGraphControl (fun a s => G (f a) s) I K := by
  intro c hc d hd
  obtain ⟨H,hH,hval,hb⟩ := h c hc d hd
  have hsub : range (fun a : X => G (f a) c)⊆range (fun a : Y => G a c) := by
    rintro _ ⟨a,rfl⟩; exact ⟨f a,rfl⟩
  exact ⟨H,hH.mono hsub,fun a => hval (f a),fun z hz => (hb z (hsub hz)).filter_mono (nhdsWithin_mono z hsub)⟩
end StandardMapEntropy
end
section
namespace StandardMapEntropy
open MeasureTheory Set Filter Topology
open scoped Topology ENNReal

lemma AffineGraphControl.scale {X : Type*} {G : X → ℝ → ℝ} {I J : Set ℝ} {K α β : ℝ}
    (h : AffineGraphControl G I K) (hβ : β≠0) (hJ : ∀ t∈J,t/α∈I) :
    AffineGraphControl (fun a s => β*G a (s/α)) J K := by
  intro c hc d hd
  obtain ⟨H,hH,hHval,hHbound⟩ := h (c/α) (hJ c hc) (d/α) (hJ d hd)
  let S := range (fun a => β*G a (c/α))
  have hmaps : MapsTo (fun t : ℝ => t/β) S (range (fun a => G a (c/α))) := by
    rintro _ ⟨a,rfl⟩
    exact ⟨a,(mul_div_cancel_left₀ _ hβ).symm⟩
  have hcont : ContinuousOn (fun t : ℝ => H (t/β)) S :=
    hH.comp (continuous_id.div_const β).continuousOn hmaps
  refine ⟨(fun t => β*H (t/β)),continuousOn_const.mul hcont,?_,?_⟩
  · intro a
    dsimp only
    rw [mul_div_cancel_left₀ _ hβ,hHval]
  · intro t ht
    have hv : Tendsto (fun t : ℝ => t/β) (𝓝[S] t) (𝓝[range (fun a => G a (c/α))] (t/β)) :=
      tendsto_nhdsWithin_iff.mpr ⟨(continuous_id.div_const β).continuousAt.continuousWithinAt,
        Eventually.mono self_mem_nhdsWithin hmaps⟩
    filter_upwards [hv.eventually (hHbound (t/β) (hmaps ht))] with t' hh
    rw [←mul_sub,abs_mul]
    apply (mul_le_mul_of_nonneg_left hh (abs_nonneg β)).trans_eq
    rw [←sub_div,abs_div]
    field_simp

end StandardMapEntropy

end
section
namespace StandardMapEntropy
open MeasureTheory Set Filter Topology
open scoped Topology ENNReal
open NonlinearStable

namespace ReversibleRectangleBlock
variable {k χ : ℝ} (B : ReversibleRectangleBlock k χ)
lemma holonomyConstant_pos : 0<B.holonomyConstant := by unfold holonomyConstant; positivity
lemma mem_stableInterval {s : ℝ} : s∈B.stableInterval ↔ |s|≤B.r/2 := by
  change -B.r/2 ≤ s ∧ s ≤ B.r/2 ↔ _
  rw [abs_le]
  constructor <;> intro h <;> constructor <;> linarith [h.1,h.2]
lemma mem_unstableInterval {s : ℝ} : s∈B.unstableInterval ↔ |s|≤|B.α| * B.r'/2 := by
  change -|B.α| * B.r'/2 ≤ s ∧ s ≤ |B.α| * B.r'/2 ↔ _
  rw [abs_le]
  constructor <;> intro h <;> constructor <;> linarith [h.1,h.2]
lemma reverseCoordinates_chart (p : RealPlane) : B.reverseCoordinates (B.chart p)=(p.2/B.α,p.1/B.β) := by
  have he := B.coordinates_swap (B.chart p)
  rw [B.coordinates_chart] at he
  have he1 := congrArg Prod.fst he
  have he2 := congrArg Prod.snd he
  change p.1=B.β*(B.reverseCoordinates (B.chart p)).2 at he1
  change p.2=B.α*(B.reverseCoordinates (B.chart p)).1 at he2
  apply Prod.ext
  · apply (eq_div_iff B.α_ne).mpr
    nlinarith [he2]
  · apply (eq_div_iff B.β_ne).mpr
    nlinarith [he1]
lemma reverse_chart_coordinates (v : ℂ) : tangentReversal B.centre+
    fineFrame k χ B.ε B.δ (complexProjection (tangentReversal B.centre)) (B.reverseCoordinates v)=tangentReversal v := by
  rw [reverseCoordinates,fineFrame_inverse k χ B.ε B.δ_pos _ B.reverse_regular]
  abel
end ReversibleRectangleBlock

namespace ReversibleGraphFamilies
variable {k χ : ℝ} {B : ReversibleRectangleBlock k χ} (F : ReversibleGraphFamilies B)

lemma stable_control (hk : 0≤k) : AffineGraphControl F.G B.stableInterval B.holonomyConstant := by
  let _ : CompactSpace B.carrier := isCompact_iff_compactSpace.mp B.compact
  intro c hc d hd
  obtain ⟨H,J,hH,hJ,hval,_,_,hHb,_⟩ := actual_graph_holonomy_bounds k hk χ B.ε B.δ B.ε_pos.le
    B.δ_pos B.δ_small B.contraction B.slow B.centre B.centre_regular
    (fun a : B.carrier => (a : ℂ)) (fun a => B.regular a a.property) F.G F.stableParameter F.continuous_G
    B.r_pos B.r_small B.R_pos (fun a => B.radius a a.property) B.size
    (fun a => (B.frames a a.property).trans (by linarith [B.η_small]))
    (fun a => B.coframes a a.property) B.stableInterval
    (fun a s _ => F.stable_bound a s)
    (fun a s hs => F.stable_representation a s (B.mem_stableInterval.mp hs)) hc hd
  exact ⟨H,hH,fun a => (hval a).1,hHb⟩

lemma reverse_representation (a : B.carrier) {s : ℝ} (hs : |s|≤B.r'/2) :
    tangentReversal B.centre+fineFrame k χ B.ε B.δ (complexProjection (tangentReversal B.centre))
      (s,F.U a (B.α*s)/B.β)=
    fineStableCurve k χ B.ε B.δ B.δ_pos B.contraction (tangentReversal a)
      (B.reversed a a.property) (F.unstableParameter a (B.α*s)) := by
  have has : |B.α*s|≤|B.α| * B.r'/2 := by rw [abs_mul]; nlinarith [abs_nonneg B.α]
  have he := F.unstable_representation a (B.α*s) has
  have hc := congrArg B.reverseCoordinates he
  rw [B.reverseCoordinates_chart] at hc
  have heα : B.α*s/B.α=s := mul_div_cancel_left₀ s B.α_ne
  rw [heα] at hc
  have hz := congrArg (fun p => tangentReversal B.centre+
    fineFrame k χ B.ε B.δ (complexProjection (tangentReversal B.centre)) p) hc
  rw [B.reverse_chart_coordinates] at hz
  simpa only [fineUnstableCurve,tangentReversal_involutive] using hz

lemma unstable_control (hk : 0≤k) : AffineGraphControl F.U B.unstableInterval B.holonomyConstant := by
  let _ : CompactSpace B.carrier := isCompact_iff_compactSpace.mp B.compact
  let GR (a : B.carrier) (s : ℝ) := F.U a (B.α*s)/B.β
  let σ (a : B.carrier) (s : ℝ) := F.unstableParameter a (B.α*s)
  let I : Set ℝ := Icc (-B.r'/2) (B.r'/2)
  have hGR : Continuous (fun p : B.carrier×ℝ => GR p.1 p.2) :=
    (F.continuous_U.comp (continuous_fst.prodMk (continuous_const.mul continuous_snd))).div_const B.β
  have hcontrol : AffineGraphControl GR I B.holonomyConstant := by
    intro c hc d hd
    obtain ⟨H,J,hH,hJ,hval,_,_,hHb,_⟩ := actual_graph_holonomy_bounds k hk χ B.ε B.δ B.ε_pos.le
      B.δ_pos B.δ_small B.contraction B.slow (tangentReversal B.centre) B.reverse_regular
      (fun a : B.carrier => tangentReversal a) (fun a => B.reversed a a.property) GR σ hGR
      B.r'_pos B.r'_small B.R'_pos (fun a => B.reverse_radius a a.property) B.reverse_size
      (fun a => (B.reverse_frames a a.property).trans (by linarith [B.η_small]))
      (fun a => B.reverse_coframes a a.property) I
      (fun a s _ => F.unstable_bound a (B.α*s))
      (fun a s hs => F.reverse_representation a (abs_le.mpr ⟨by linarith [hs.1],hs.2⟩)) hc hd
    exact ⟨H,hH,fun a => (hval a).1,hHb⟩
  have hscaled := hcontrol.scale (α := B.α) B.β_ne (J := B.unstableInterval) (by
    intro s hs
    have hs' := B.mem_unstableInterval.mp hs
    have hab : |s/B.α|≤B.r'/2 := by
      rw [abs_div]
      exact (div_le_iff₀ (abs_pos.mpr B.α_ne)).mpr (by nlinarith)
    exact ⟨by linarith [(abs_le.mp hab).1],(abs_le.mp hab).2⟩)
  have he : (fun a s => B.β*GR a (s/B.α))=F.U := by
    funext a s
    dsimp only [GR]
    rw [mul_div_cancel₀ _ B.β_ne,mul_div_cancel₀ _ B.α_ne]
  rw [he] at hscaled
  exact hscaled

end ReversibleGraphFamilies
end StandardMapEntropy

end
section
namespace StandardMapEntropy
open MeasureTheory MeasureTheory.Measure Set Filter Topology
open scoped Topology ENNReal
attribute [local instance] Measure.Subtype.measureSpace

namespace ReversibleRectangleBlock
variable {k χ : ℝ} (B : ReversibleRectangleBlock k χ)

lemma compact_coordinateCarrier : IsCompact B.coordinateCarrier := B.compact.image B.continuous_coordinates
lemma continuous_label : Continuous B.label :=
  (B.continuous_chart.comp continuous_subtype_val).subtype_mk _
@[simp] lemma coordinates_label (p : B.coordinateCarrier) : B.coordinates (B.label p)=(p : RealPlane) :=
  B.coordinates_chart p
lemma chart_image_carrier : B.chart '' B.coordinateCarrier=B.carrier := by
  ext v
  constructor
  · rintro ⟨p,⟨v',hv',hp⟩,rfl⟩
    rw [←hp,B.chart_coordinates]
    exact hv'
  · intro hv
    exact ⟨B.coordinates v,⟨v,hv,rfl⟩,B.chart_coordinates v⟩

lemma volume_chart_image {S : Set RealPlane} (hS : MeasurableSet S) :
    volume (B.chart '' S)=ENNReal.ofReal (fineVolumeFactor k χ B.ε B.δ (complexProjection B.centre))*volume S := by
  have he : B.chart '' S=(fun z : ℂ => B.centre+z) ''
      ((fineSize k χ B.ε B.δ (complexProjection B.centre) • lyapunovFrame k χ (complexProjection B.centre)) '' (pairToComplex '' S)) := by
    rw [Set.image_image,Set.image_image]
    rfl
  rw [he,Set.image_add_left,measure_preimage_add,Measure.addHaar_image_continuousLinearMap,volume_pairToComplex_image hS]
  rfl
lemma positive_coordinateCarrier : 0<volume B.coordinateCarrier := by
  by_contra h
  have hz : volume B.coordinateCarrier=0 := le_antisymm (not_lt.mp h) (bot_le)
  have hh := B.volume_chart_image B.compact_coordinateCarrier.measurableSet
  rw [B.chart_image_carrier,hz,mul_zero] at hh
  exact B.positive.ne' hh
lemma volume_coordinate_univ : (volume : Measure B.coordinateCarrier) univ=volume B.coordinateCarrier := by
  change (Measure.comap Subtype.val volume) univ=volume B.coordinateCarrier
  rw [comap_subtype_coe_apply B.compact_coordinateCarrier.measurableSet]
  simp only [Set.image_univ,Subtype.range_coe]
lemma finite_coordinate_volume : IsFiniteMeasure (volume : Measure B.coordinateCarrier) := by
  apply (isFiniteMeasure_iff _).mpr
  rw [B.volume_coordinate_univ]
  exact B.compact_coordinateCarrier.measure_lt_top

lemma chart_quasiMeasurePreserving : QuasiMeasurePreserving B.chart volume volume := by
  let L : ℂ →L[ℝ] ℂ := fineSize k χ B.ε B.δ (complexProjection B.centre) • lyapunovFrame k χ (complexProjection B.centre)
  have hi : Function.Injective L := by
    intro z z' he
    have hh : fineFrame k χ B.ε B.δ (complexProjection B.centre) (complexToPair z)=
        fineFrame k χ B.ε B.δ (complexProjection B.centre) (complexToPair z') := by
      simpa only [fineFrame,flatFrame,ContinuousLinearMap.comp_apply,pairToComplex_complexToPair] using he
    have hh' := congrArg (fineInverse k χ B.ε B.δ (complexProjection B.centre)) hh
    rw [fineInverse_frame k χ B.ε B.δ_pos _ B.centre_regular,
      fineInverse_frame k χ B.ε B.δ_pos _ B.centre_regular] at hh'
    exact congrArg pairToComplex hh'
  have hdet : L.det≠0 := by
    intro hzero
    exact (LinearMap.det_eq_zero_iff_ker_ne_bot.mp hzero) (LinearMap.ker_eq_bot.mpr hi)
  have hp : MeasurePreserving pairToComplex volume volume := by
    exact Complex.volume_preserving_equiv_real_prod.symm Complex.measurableEquivRealProd
  exact (measurePreserving_add_left volume B.centre).quasiMeasurePreserving.comp
    ((L.quasiMeasurePreserving volume hdet).comp hp.quasiMeasurePreserving)

end ReversibleRectangleBlock
end StandardMapEntropy

end
section
namespace StandardMapEntropy
open MeasureTheory MeasureTheory.Measure Set Filter Topology
open scoped Topology ENNReal
attribute [local instance] Measure.Subtype.measureSpace

theorem label_nonsingular_of_vertical_inverse {K : Set (ℝ×ℝ)} (hK : MeasurableSet K)
    (f : K → ℝ) (hf : Measurable f) {I : Set ℝ} (hwithin : ∀ a : K,(a : ℝ×ℝ).1∈I)
    (hinv : ∀ c∈I,∃ J : ℝ → ℝ,
      (∀ a : K,(a : ℝ×ℝ).1=c → J (f a)=(a : ℝ×ℝ).2) ∧
      ∀ Z : Set ℝ,Z⊆range f → volume Z=0 → volume (J '' Z)=0) :
    QuasiMeasurePreserving f (volume : Measure K) volume := by
  refine ⟨hf,AbsolutelyContinuous.mk fun N hN hNz => ?_⟩
  rw [map_apply hf hN]
  change Measure.comap Subtype.val volume (f ⁻¹' N)=0
  rw [comap_subtype_coe_apply hK]
  let S : Set (ℝ×ℝ) := Subtype.val '' (f ⁻¹' N)
  have hS : MeasurableSet S := (MeasurableEmbedding.subtype_coe hK).measurableSet_image.mpr (hN.preimage hf)
  change volume S=0
  rw [Measure.volume_eq_prod,Measure.prod_apply hS]
  apply lintegral_eq_zero_of_ae_eq_zero
  apply Filter.Eventually.of_forall
  intro c
  by_cases hc : c∈I
  · obtain ⟨J,hJ,hJnull⟩ := hinv c hc
    apply measure_mono_null (t := J '' (N∩range f)) _ (hJnull _ inter_subset_right (measure_mono_null inter_subset_left hNz))
    rintro t ⟨a,ha,he⟩
    have h1 : (a : ℝ×ℝ).1=c := congrArg Prod.fst he
    have h2 : (a : ℝ×ℝ).2=t := congrArg Prod.snd he
    exact ⟨f a,⟨ha,⟨a,rfl⟩⟩,(hJ a h1).trans h2⟩
  · apply measure_mono_null (t := ∅) _ (measure_empty)
    rintro t ⟨a,ha,he⟩
    have he' : (a : ℝ×ℝ).1=c := congrArg Prod.fst he
    exact (hc (he' ▸ hwithin a)).elim

theorem label_nonsingular_of_horizontal_inverse {K : Set (ℝ×ℝ)} (hK : MeasurableSet K)
    (f : K → ℝ) (hf : Measurable f) {I : Set ℝ} (hwithin : ∀ a : K,(a : ℝ×ℝ).2∈I)
    (hinv : ∀ c∈I,∃ J : ℝ → ℝ,
      (∀ a : K,(a : ℝ×ℝ).2=c → J (f a)=(a : ℝ×ℝ).1) ∧
      ∀ Z : Set ℝ,Z⊆range f → volume Z=0 → volume (J '' Z)=0) :
    QuasiMeasurePreserving f (volume : Measure K) volume := by
  refine ⟨hf,AbsolutelyContinuous.mk fun N hN hNz => ?_⟩
  rw [map_apply hf hN]
  change Measure.comap Subtype.val volume (f ⁻¹' N)=0
  rw [comap_subtype_coe_apply hK]
  let S : Set (ℝ×ℝ) := Subtype.val '' (f ⁻¹' N)
  have hS : MeasurableSet S := (MeasurableEmbedding.subtype_coe hK).measurableSet_image.mpr (hN.preimage hf)
  change volume S=0
  rw [Measure.volume_eq_prod,Measure.prod_apply_symm hS]
  apply lintegral_eq_zero_of_ae_eq_zero
  apply Filter.Eventually.of_forall
  intro c
  by_cases hc : c∈I
  · obtain ⟨J,hJ,hJnull⟩ := hinv c hc
    apply measure_mono_null (t := J '' (N∩range f)) _ (hJnull _ inter_subset_right (measure_mono_null inter_subset_left hNz))
    rintro t ⟨a,ha,he⟩
    have h1 : (a : ℝ×ℝ).2=c := congrArg Prod.snd he
    have h2 : (a : ℝ×ℝ).1=t := congrArg Prod.fst he
    exact ⟨f a,⟨ha,⟨a,rfl⟩⟩,(hJ a h1).trans h2⟩
  · apply measure_mono_null (t := ∅) _ (measure_empty)
    rintro t ⟨a,ha,he⟩
    have he' : (a : ℝ×ℝ).2=c := congrArg Prod.snd he
    exact (hc (he' ▸ hwithin a)).elim

end StandardMapEntropy

end
section
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal Topology

theorem ae_constant_of_product_rows_columns {A B Y : Type*}
    [MeasurableSpace A] [MeasurableSpace B] {α : Measure A} {β : Measure B}
    [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    {P : A×B → Prop} (hP : ∀ᵐ p ∂α.prod β,P p) {F : A×B → Y}
    (hrow : ∀ a b b',P (a,b) → P (a,b') → F (a,b)=F (a,b'))
    (hcol : ∀ a a' b,P (a,b) → P (a',b) → F (a,b)=F (a',b)) :
    ∃ c : Y, ∀ᵐ p ∂α.prod β,F p=c := by
  have hp : ∀ᵐ a ∂α,∀ᵐ b ∂β,P (a,b) := ae_ae_of_ae_prod hP
  obtain ⟨a₀,ha₀⟩ := hp.exists
  obtain ⟨b₀,hb₀⟩ := ha₀.exists
  refine ⟨F (a₀,b₀),?_⟩
  have hrowc : ∀ᵐ a ∂α,∀ b,P (a,b) → F (a,b)=F (a₀,b₀) := by
    filter_upwards [hp] with a ha
    obtain ⟨b',hab',ha₀b'⟩ := (ha.and ha₀).exists
    intro b hab
    exact (hrow a b b' hab hab').trans ((hcol a a₀ b' hab' ha₀b').trans (hrow a₀ b' b₀ ha₀b' hb₀))
  have hr : ∀ᵐ p ∂α.prod β,∀ b,P (p.1,b) → F (p.1,b)=F (a₀,b₀) :=
    (measurePreserving_fst (μ := α) (ν := β)).quasiMeasurePreserving.ae hrowc
  filter_upwards [hP,hr] with p hp' hr'
  exact hr' p.2 hp'

end
end

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_Components_SliceRectangleNonsingular
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal Topology

theorem rectangle_quasiMeasurePreserving {A B : Type*}
    [MeasurableSpace A] [MeasurableSpace B]
    (α : Measure A) (β : Measure B) [SFinite α] [SFinite β]
    {I : Set ℝ} (hI : MeasurableSet I)
    (G : A → ℝ → ℝ) (hG : Measurable (fun p : A×ℝ => G p.1 p.2))
    (π : A×B → ℝ×ℝ) (hπ : Measurable π)
    (hgraph : ∀ p,(π p).2=G p.1 (π p).1)
    (haffine : ∀ x∈I,QuasiMeasurePreserving (fun a => G a x) α volume)
    (hcurved : ∀ a,QuasiMeasurePreserving (fun b => (π (a,b)).1) β (volume.restrict I)) :
    QuasiMeasurePreserving π (α.prod β) (volume : Measure (ℝ×ℝ)) := by
  refine ⟨hπ,AbsolutelyContinuous.mk fun N hN hNzero => ?_⟩
  rw [map_apply hπ hN]
  have hslice : ∀ᵐ x ∂volume.restrict I,∀ᵐ y ∂(volume : Measure ℝ),(x,y)∉N := by
    apply ae_restrict_of_ae
    apply ae_ae_of_ae_prod (p := fun p : ℝ×ℝ => p∉N)
    rw [ae_iff]
    simpa only [not_not,Set.ofPred_mem_eq,Measure.volume_eq_prod] using hNzero
  have hGEN : ∀ᵐ x ∂volume.restrict I,∀ᵐ a ∂α,(x,G a x)∉N := by
    filter_upwards [hslice,ae_restrict_mem hI] with x hx hxI
    exact (haffine x hxI).ae hx
  have hprod : ∀ᵐ p ∂(volume.restrict I).prod α,(p.1,G p.2 p.1)∉N := by
    apply (ae_prod_iff_ae_ae ((hN.preimage
      (measurable_fst.prodMk (hG.comp measurable_swap))).compl)).mpr
    exact hGEN
  have hrev : ∀ᵐ a ∂α,∀ᵐ x ∂volume.restrict I,(x,G a x)∉N := by
    exact ae_ae_of_ae_prod ((measurePreserving_swap (μ := α) (ν := volume.restrict I)).quasiMeasurePreserving.ae hprod)
  have hout : ∀ᵐ a ∂α,∀ᵐ b ∂β,π (a,b)∉N := by
    filter_upwards [hrev] with a ha
    filter_upwards [(hcurved a).ae ha] with b hb
    simpa only [←hgraph (a,b),Prod.mk.eta] using hb
  have hall := (ae_prod_iff_ae_ae ((hN.preimage hπ).compl)).mpr hout
  simpa only [ae_iff,not_not,Set.ofPred_mem_eq] using hall

end
section
namespace StandardMapEntropy
open MeasureTheory MeasureTheory.Measure Set Filter Topology
open scoped Topology ENNReal
attribute [local instance] Measure.Subtype.measureSpace

theorem compact_graph_product_nonsingular {K : Set (ℝ×ℝ)} (hK : IsCompact K)
    [SFinite (volume : Measure K)]
    (G U : K → ℝ → ℝ)
    (hG : Continuous (fun p : K×ℝ => G p.1 p.2))
    (hU : Continuous (fun p : K×ℝ => U p.1 p.2))
    (hsG : ∀ a s t,|G a s-G a t|≤(1/2)*|s-t|)
    (hsU : ∀ a s t,|U a s-U a t|≤(1/2)*|s-t|)
    {I J : Set ℝ} (hI : MeasurableSet I)
    (hIc : ∀ a : K,(a : ℝ×ℝ).1∈I) (hJc : ∀ a : K,(a : ℝ×ℝ).2∈J)
    (hcentreG : ∀ a : K,G a (a : ℝ×ℝ).1=(a : ℝ×ℝ).2)
    (hcentreU : ∀ a : K,U a (a : ℝ×ℝ).2=(a : ℝ×ℝ).1)
    {C : ℝ} (hC : 0≤C) (hGcontrol : AffineGraphControl G I C) (hUcontrol : AffineGraphControl U J C)
    (π : K×K → ℝ×ℝ) (hπ : Continuous π)
    (hπG : ∀ p,(π p).2=G p.1 (π p).1) (hπU : ∀ p,(π p).1=U p.2 (π p).2)
    (hπI : ∀ p,(π p).1∈I) (hπJ : ∀ p,(π p).2∈J) :
    QuasiMeasurePreserving π ((volume : Measure K).prod volume) (volume : Measure (ℝ×ℝ)) := by
  let _ : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have haff (x : ℝ) (hx : x∈I) : QuasiMeasurePreserving (fun a => G a x) (volume : Measure K) volume := by
    apply label_nonsingular_of_vertical_inverse hK.measurableSet _
      (hG.comp (continuous_id.prodMk continuous_const)).measurable hIc
    intro c hc
    obtain ⟨H,hH,hHval,hHbound⟩ := hGcontrol x hx c hc
    refine ⟨H,?_,fun Z hZ hZ0 => null_image_of_pointwise_local_bound hC hHbound hZ hZ0⟩
    intro a he
    change H (G a x)=(a : ℝ×ℝ).2
    rw [hHval,←he,hcentreG]
  have hcurved (a : K) : QuasiMeasurePreserving (fun b => (π (a,b)).1)
      (volume : Measure K) (volume.restrict I) := by
    have hbase : QuasiMeasurePreserving (fun b => (π (a,b)).1) (volume : Measure K) volume := by
      apply label_nonsingular_of_horizontal_inverse hK.measurableSet _
        (continuous_fst.comp (hπ.comp (continuous_const.prodMk continuous_id))).measurable hJc
      intro c hc
      obtain ⟨H,hH,hHval,hHbound⟩ := compact_curved_inverse_control hU hC (by norm_num : (0:ℝ)≤1/2)
        (by norm_num : (0:ℝ)≤1/2) (by norm_num : (1/2:ℝ)*(1/2)<1) hsU hUcontrol
        (G a) (hsG a) (fun b => (π (a,b)).1)
        (continuous_fst.comp (hπ.comp (continuous_const.prodMk continuous_id)))
        (fun b => by rw [←hπG (a,b)]; exact hπU (a,b))
        (fun b => by rw [←hπG (a,b)]; exact hπJ (a,b)) hc
      refine ⟨H,?_,fun Z hZ hZ0 => null_image_of_pointwise_local_bound (by positivity) hHbound hZ hZ0⟩
      intro b he
      change H (π (a,b)).1=(b : ℝ×ℝ).1
      rw [hHval,←he,hcentreU]
    simpa only [Measure.restrict_univ] using hbase.restrict
      (s := univ) (t := I) (fun b _ => hπI (a,b))
  exact rectangle_quasiMeasurePreserving volume volume hI G hG.measurable π hπ.measurable hπG haff hcurved

end StandardMapEntropy

end
section
namespace StandardMapEntropy
open MeasureTheory Set Filter
open scoped Topology
open NonlinearStable

theorem compact_graph_rectangle {A B : Type*}
    [TopologicalSpace A] [CompactSpace A] [T2Space A]
    [TopologicalSpace B] [CompactSpace B] [T2Space B]
    (G : A → ℝ → ℝ) (U : B → ℝ → ℝ)
    (hG : Continuous (fun p : A×ℝ => G p.1 p.2))
    (hU : Continuous (fun p : B×ℝ => U p.1 p.2))
    (hsG : ∀ a s t,|G a s-G a t|≤(1/2)*|s-t|)
    (hsU : ∀ b s t,|U b s-U b t|≤(1/2)*|s-t|)
    {r : ℝ} (hr : 0 < r) (hsmall : ∀ a b,|G a (U b 0)| ≤ r/4) :
    ∃ π : A×B → Plane, Continuous π ∧
      (∀ p, (π p).1=U p.2 (π p).2 ∧ (π p).2=G p.1 (π p).1 ∧ |(π p).2| ≤ r) ∧
      ∀ p q : A×B, ∀ z : Plane,
        z.1=U p.2 z.2 → z.2=G q.1 z.1 → z=π (q.1,p.2) := by
  let F (p : A×B) (s : ℝ) : Plane := (s-G p.1 (U p.2 s),0)
  have hFc : Continuous (fun p : (A×B)×Icc (-r) r => F p.1 p.2) := by
    apply Continuous.prodMk _ continuous_const
    exact (continuous_subtype_val.comp continuous_snd).sub
      (hG.comp ((continuous_fst.comp continuous_fst).prodMk
        (hU.comp ((continuous_snd.comp continuous_fst).prodMk (continuous_subtype_val.comp continuous_snd)))))
  have herr (p : A×B) (s t : ℝ) : |(F p s).1-(F p t).1-(s-t)|≤(1/4)*|s-t| := by
    have he : (F p s).1-(F p t).1-(s-t)=G p.1 (U p.2 t)-G p.1 (U p.2 s) := by dsimp only [F]; ring
    rw [he,abs_sub_comm]
    exact ((hsG p.1 _ _).trans (mul_le_mul_of_nonneg_left (hsU p.2 s t) (by norm_num))).trans_eq (by ring)
  obtain ⟨σ,hσ,hσval⟩ := compact_graph_crossing r hr F hFc herr (fun p => by
    simpa only [F,zero_sub,abs_neg] using hsmall p.1 p.2)
  let z₀ : Icc (-r/2) (r/2) := ⟨0,by constructor <;> linarith⟩
  let t : A×B → ℝ := fun p => σ (p,z₀)
  have ht : Continuous t := continuous_subtype_val.comp (hσ.comp (continuous_id.prodMk continuous_const))
  have he (p : A×B) : t p=G p.1 (U p.2 (t p)) := by
    have hh := hσval (p,z₀)
    change t p-G p.1 (U p.2 (t p))=0 at hh
    exact sub_eq_zero.mp hh
  refine ⟨(fun p => (U p.2 (t p),t p)),(hU.comp (continuous_snd.prodMk ht)).prodMk ht,?_,?_⟩
  · intro p
    exact ⟨rfl,he p,abs_le.mpr (σ (p,z₀)).property⟩
  · intro p q z hzU hzG
    have hm := strictMono_of_linear_error (by norm_num : (1/4 : ℝ)<1) (herr (q.1,p.2))
    have hzero : (F (q.1,p.2) z.2).1=0 := by
      change z.2-G q.1 (U p.2 z.2)=0
      rw [←hzU,←hzG,sub_self]
    have hz : z.2=t (q.1,p.2) := hm.injective (hzero.trans (by
      change 0=t (q.1,p.2)-G q.1 (U p.2 (t (q.1,p.2)))
      exact (sub_eq_zero.mpr (he (q.1,p.2))).symm))
    exact Prod.ext (hzU.trans (congrArg (U p.2) hz)) hz

end StandardMapEntropy

end
section
namespace StandardMapEntropy
open MeasureTheory MeasureTheory.Measure Set Filter Topology
open scoped Topology ENNReal
open NonlinearStable
attribute [local instance] Measure.Subtype.measureSpace

theorem reversible_graph_rectangle {k χ : ℝ} {B : ReversibleRectangleBlock k χ}
    (F : ReversibleGraphFamilies B) (hk : 0≤k) : Nonempty (ReversibleGraphRectangle F) := by
  let _ : CompactSpace B.coordinateCarrier := isCompact_iff_compactSpace.mp B.compact_coordinateCarrier
  let _ : IsFiniteMeasure (volume : Measure B.coordinateCarrier) := B.finite_coordinate_volume
  let G (a : B.coordinateCarrier) (s : ℝ) := F.G (B.label a) s
  let U (a : B.coordinateCarrier) (s : ℝ) := F.U (B.label a) s
  have hG : Continuous (fun p : B.coordinateCarrier×ℝ => G p.1 p.2) :=
    F.continuous_G.comp ((B.continuous_label.comp continuous_fst).prodMk continuous_snd)
  have hU : Continuous (fun p : B.coordinateCarrier×ℝ => U p.1 p.2) :=
    F.continuous_U.comp ((B.continuous_label.comp continuous_fst).prodMk continuous_snd)
  have hx (a : B.coordinateCarrier) : |(a : RealPlane).1|≤B.ρ/100 := by
    have hh := (norm_fst_le (B.coordinates (B.label a))).trans (B.central (B.label a) (B.label a).property)
    simpa only [B.coordinates_label,Real.norm_eq_abs] using hh
  have hy (a : B.coordinateCarrier) : |(a : RealPlane).2|≤B.ρ/100 := by
    have hh := (norm_snd_le (B.coordinates (B.label a))).trans (B.central (B.label a) (B.label a).property)
    simpa only [B.coordinates_label,Real.norm_eq_abs] using hh
  have hGc (a : B.coordinateCarrier) : G a (a : RealPlane).1=(a : RealPlane).2 := by
    simpa only [B.coordinates_label] using F.G_centre (B.label a)
  have hUc (a : B.coordinateCarrier) : U a (a : RealPlane).2=(a : RealPlane).1 := by
    simpa only [B.coordinates_label] using F.U_centre (B.label a)
  have hG0 (a : B.coordinateCarrier) : |G a 0|≤3*B.ρ/200 := by
    have hh := F.slope_G (B.label a) 0 (a : RealPlane).1
    change |G a 0-G a (a : RealPlane).1|≤_ at hh
    rw [hGc,zero_sub,abs_neg] at hh
    have htri := abs_sub_le (G a 0) (a : RealPlane).2 0
    simp only [sub_zero] at htri
    nlinarith [hx a,hy a]
  have hU0 (a : B.coordinateCarrier) : |U a 0|≤3*B.ρ/200 := by
    have hh := F.slope_U (B.label a) 0 (a : RealPlane).2
    change |U a 0-U a (a : RealPlane).2|≤_ at hh
    rw [hUc,zero_sub,abs_neg] at hh
    have htri := abs_sub_le (U a 0) (a : RealPlane).1 0
    simp only [sub_zero] at htri
    nlinarith [hx a,hy a]
  have hsmall (a b : B.coordinateCarrier) : |G a (U b 0)|≤B.ρ/4 := by
    have hh := F.slope_G (B.label a) (U b 0) 0
    change |G a (U b 0)-G a 0|≤_ at hh
    simp only [sub_zero] at hh
    have htri := abs_sub_le (G a (U b 0)) (G a 0) 0
    simp only [sub_zero] at htri
    nlinarith [hG0 a,hU0 b,B.ρ_pos]
  obtain ⟨π,hπ,hgraph,hunique⟩ := compact_graph_rectangle G U hG hU
    (fun a => F.slope_G (B.label a)) (fun a => F.slope_U (B.label a)) B.ρ_pos hsmall
  have hπx (p : B.coordinateCarrier×B.coordinateCarrier) : |(π p).1|≤B.ρ := by
    rw [(hgraph p).1]
    have hh := F.slope_U (B.label p.2) (π p).2 0
    change |U p.2 (π p).2-U p.2 0|≤_ at hh
    simp only [sub_zero] at hh
    have htri := abs_sub_le (U p.2 (π p).2) (U p.2 0) 0
    simp only [sub_zero] at htri
    nlinarith [(hgraph p).2.2,hU0 p.2,B.ρ_pos]
  have hπI (p : B.coordinateCarrier×B.coordinateCarrier) : (π p).1∈B.stableInterval :=
    B.mem_stableInterval.mpr ((hπx p).trans (by linarith [B.ρ_small,B.r_pos]))
  have hπJ (p : B.coordinateCarrier×B.coordinateCarrier) : (π p).2∈B.unstableInterval :=
    B.mem_unstableInterval.mpr ((hgraph p).2.2.trans (by linarith [B.ρ_reverse,B.ρ_pos]))
  have hNS := compact_graph_product_nonsingular B.compact_coordinateCarrier G U hG hU
    (fun a => F.slope_G (B.label a)) (fun a => F.slope_U (B.label a))
    (I := B.stableInterval) (J := B.unstableInterval) measurableSet_Icc
    (fun a => B.mem_stableInterval.mpr ((hx a).trans (by linarith [B.ρ_small,B.ρ_pos])))
    (fun a => B.mem_unstableInterval.mpr ((hy a).trans (by linarith [B.ρ_reverse,B.ρ_pos])))
    hGc hUc B.holonomyConstant_pos.le ((F.stable_control hk).comp B.label) ((F.unstable_control hk).comp B.label)
    π hπ (fun p => (hgraph p).2.1) (fun p => (hgraph p).1) hπI hπJ
  exact ⟨⟨π,hπ,hNS,fun p => (hgraph p).2.1,fun p => (hgraph p).1,hπx,fun p => (hgraph p).2.2⟩⟩

end StandardMapEntropy

end
section
namespace StandardMapEntropy
open MeasureTheory MeasureTheory.Measure Set Filter Topology
open scoped Topology ENNReal

theorem complexProjection_quasiMeasurePreserving : QuasiMeasurePreserving complexProjection volume area := by
  refine ⟨continuous_complexProjection.measurable,AbsolutelyContinuous.mk fun N hN hNz => ?_⟩
  rw [Measure.map_apply continuous_complexProjection.measurable hN]
  let C (m n : ℤ) : Set ℂ := {z | z.re∈Ico (m : ℝ) ((m : ℝ)+1) ∧ z.im∈Ico (n : ℝ) ((n : ℝ)+1)}
  have hmp (m n : ℤ) : MeasurePreserving complexProjection (volume.restrict (C m n)) area := by
    have hp := (AddCircle.measurePreserving_mk (1 : ℝ) (m : ℝ)).prod (AddCircle.measurePreserving_mk (1 : ℝ) (n : ℝ))
    simp only [←restrict_Ico_eq_restrict_Ioc,Measure.prod_restrict] at hp
    have hc := Complex.volume_preserving_equiv_real_prod.restrict_preimage
      (measurableSet_Ico.prod measurableSet_Ico : MeasurableSet
        (Ico (m : ℝ) ((m : ℝ)+1) ×ˢ Ico (n : ℝ) ((n : ℝ)+1)))
    exact hp.comp hc
  have hz (m n : ℤ) : volume (complexProjection ⁻¹' N∩C m n)=0 := by
    have hh := (hmp m n).measure_preimage hN.nullMeasurableSet
    rw [Measure.restrict_apply (hN.preimage continuous_complexProjection.measurable),hNz] at hh
    exact hh
  apply measure_mono_null (t := ⋃ m : ℤ,⋃ n : ℤ,complexProjection ⁻¹' N∩C m n) _
    (measure_iUnion_null fun m => measure_iUnion_null fun n => hz m n)
  intro z hzN
  exact mem_iUnion.mpr ⟨⌊z.re⌋,mem_iUnion.mpr ⟨⌊z.im⌋,hzN,
    ⟨Int.floor_le _,Int.lt_floor_add_one _⟩,⟨Int.floor_le _,Int.lt_floor_add_one _⟩⟩⟩

end StandardMapEntropy

end
section
namespace StandardMapEntropy
open MeasureTheory Set Filter
open scoped Topology
open NonlinearStable

theorem fineStableCurve_contracting_tangent (k χ ε δ : ℝ) (hδ : 0<δ)
    (hq : Real.exp (-χ+ε)+δ<1) (w : ℂ)
    (hw : ∀ n : ℕ, FineRegular k χ ε (complexProjection ((standardLift k)^[n] w)))
    {s : ℝ} (hs : |s|<1) :
    ∃ v : ℂ,v≠0 ∧ ∀ n : ℕ,
      ‖standardDerivativeProduct k (complexProjection (fineStableCurve k χ ε δ hδ hq w hw s)) n v‖≤
        (2*fineScale k ε δ)*(Real.exp (-χ+ε)+δ)^n := by
  let f := fineStableCurve k χ ε δ hδ hq w hw
  have hsI : Ioo (-1 : ℝ) 1∈𝓝 s := isOpen_Ioo.mem_nhds (abs_lt.mp hs)
  have hf : DifferentiableAt ℝ f s :=
    (fineStableCurve_contDiffOn k χ ε δ hδ hq w hw).differentiableOn (by norm_num) |>.differentiableAt hsI
  let I := fineInverse k χ ε δ (complexProjection w)
  let L := (ContinuousLinearMap.fst ℝ ℝ ℝ).comp I
  have he : (fun t : ℝ => L (f t-w))=id := by
    funext t
    change (I (w+fineFrame k χ ε δ (complexProjection w) (t,fineStableGraph k χ ε δ hδ hq w hw t)-w)).1=t
    rw [add_sub_cancel_left]
    dsimp [I]
    rw [fineInverse_frame k χ ε hδ _ (by simpa using (hw 0).1)]
  have hder := L.hasFDerivAt.comp_hasDerivAt s (hf.hasDerivAt.sub_const w)
  have hfirst : L (deriv f s)=1 := by
    have hder' : HasDerivAt (fun t : ℝ => L (f t-w)) (L (deriv f s)) s := hder
    rw [he] at hder'
    exact hder'.unique (hasDerivAt_id s)
  refine ⟨deriv f s,?_,?_⟩
  · intro hz
    rw [hz,map_zero] at hfirst
    norm_num at hfirst
  · intro n
    have hd := (hasFDerivAt_standardLift_iterate k n (f s)).comp_hasDerivAt s hf.hasDerivAt
    apply hd.le_of_lip' (by positivity [fineScale_pos k ε hδ])
    filter_upwards [hsI] with t ht
    exact fineStableCurve_contraction k χ ε δ hδ hq w hw (abs_lt.mpr ht).le hs.le n

lemma vectorGrowth_le_log_of_bound (k : ℝ) (z : Torus) {v : ℂ} {l C q : ℝ}
    (hg : VectorGrowth k z v l) (hC : 0<C) (hq : 0<q)
    (hb : ∀ n : ℕ,‖standardDerivativeProduct k z n v‖≤C*q^n) : l≤Real.log q := by
  have ht : Tendsto (fun n : ℕ => Real.log C/(n : ℝ)+Real.log q) atTop (𝓝 (Real.log q)) := by
    simpa only [zero_add] using
      (tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop :
        Tendsto (fun n : ℕ => Real.log C/(n : ℝ)) atTop (𝓝 0)).add_const (Real.log q)
  apply le_of_tendsto_of_tendsto hg.2 ht
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hn' : (0 : ℝ)<n := by exact_mod_cast hn
  have hp : 0<‖standardDerivativeProduct k z n v‖ :=
    PlaneLyapunov.image_norm_pos _ (standardDerivativeProduct_area k z) hg.1 n
  have hh := Real.log_le_log hp (hb n)
  rw [Real.log_mul hC.ne' (pow_pos hq n).ne',Real.log_pow] at hh
  exact (div_le_div_of_nonneg_right hh hn'.le).trans_eq (by field_simp)

theorem fineStableCurve_spectrum_positive (k χ ε δ : ℝ) (hδ : 0<δ)
    (hq : Real.exp (-χ+ε)+δ<1) (w : ℂ)
    (hw : ∀ n : ℕ, FineRegular k χ ε (complexProjection ((standardLift k)^[n] w)))
    {s l : ℝ} (hs : |s|<1)
    (hl : LyapunovSpectrumAt k (complexProjection (fineStableCurve k χ ε δ hδ hq w hw s)) l) : 0<l := by
  rcases hl.2 with ⟨he,hzero⟩|⟨hpos,_⟩
  · obtain ⟨v,hv,hbound⟩ := fineStableCurve_contracting_tangent k χ ε δ hδ hq w hw hs
    have hh := vectorGrowth_le_log_of_bound k _ (hzero v hv) (by positivity [fineScale_pos k ε hδ])
      (show 0<Real.exp (-χ+ε)+δ by positivity) hbound
    have hneg : Real.log (Real.exp (-χ+ε)+δ)<0 := Real.log_neg (by positivity) hq
    linarith
  · exact hpos

end StandardMapEntropy

end
section
open MeasureTheory Filter Set
open scoped Topology ENNReal BigOperators

namespace BoundedSubadditive
variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]

theorem continuous_birkhoff_limit {μ : Measure X} [IsFiniteMeasure μ]
    {T S : X → X} (hT : MeasurePreserving T μ μ) (hS : MeasurePreserving S μ μ)
    (hST : ∀ x,S (T x)=x) (hTS : ∀ x,T (S x)=x) (f : C(X,ℝ)) :
    ∃ F : X → ℝ, Measurable F ∧ (∀ x,F (T x)=F x) ∧
      (∀ᵐ x ∂μ,
        Tendsto (fun n : ℕ => birkhoffSum T f n x/(n : ℝ)) atTop (𝓝 (F x)) ∧
        Tendsto (fun n : ℕ => birkhoffSum S f n x/(n : ℝ)) atTop (𝓝 (F x))) ∧
      ∀ A : Set X, MeasurableSet A → T ⁻¹' A=A → ∫ x in A,F x ∂μ=∫ x in A,f x ∂μ := by
  let C := ‖f‖
  let d := 2*C+1
  have hC : 0≤C := norm_nonneg f
  have hd : 0<d := by dsimp only [d]; positivity
  let g : X → ℝ := fun x => (f x+C)/d
  have hg : Measurable g := (f.continuous.measurable.add_const C).div_const d
  have hbound (x : X) : |f x|≤C := f.norm_coe_le_norm x
  have h0 (x : X) : 0≤g x := div_nonneg (by linarith [(abs_le.mp (hbound x)).1]) hd.le
  have h1 (x : X) : g x≤1 := by
    apply (div_le_one hd).mpr
    dsimp only [d]
    linarith [(abs_le.mp (hbound x)).2]
  obtain ⟨G,hGm,hGb,hGT,hGconv⟩ := forward_backward_birkhoff hT hS hST hTS hg h0 h1
  obtain ⟨H,hHm,hHb,hHT,hHconv,hHint⟩ := exists_bounded_birkhoff_limit hT hg h0 h1
  have hGH : G=ᵐ[μ] H := by
    filter_upwards [hGconv,hHconv] with x hx hy
    exact tendsto_nhds_unique hx.1 hy
  let F : X → ℝ := fun x => d*G x-C
  have hFi : Integrable F μ := by
    apply (integrable_const (d+C)).mono' ((measurable_const.mul hGm).sub_const C).aestronglyMeasurable
    apply Eventually.of_forall
    intro x
    change |d*G x-C|≤d+C
    rw [abs_le]
    constructor <;> nlinarith [(hGb x).1,(hGb x).2]
  have hconv {U : X → X} {x : X}
      (hu : Tendsto (fun n : ℕ => birkhoffSum U g n x/(n : ℝ)) atTop (𝓝 (G x))) :
      Tendsto (fun n : ℕ => birkhoffSum U f n x/(n : ℝ)) atTop (𝓝 (F x)) := by
    apply ((hu.const_mul d).sub_const C).congr'
    filter_upwards [eventually_ne_atTop 0] with n hn
    have hn' : (n : ℝ)≠0 := by exact_mod_cast hn
    have he : birkhoffSum U g n x=(birkhoffSum U f n x+(n : ℝ)*C)/d := by
      simp only [birkhoffSum,g]
      rw [←Finset.sum_div,Finset.sum_add_distrib]
      simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul]
    rw [he]
    field_simp
    ring
  refine ⟨F,(measurable_const.mul hGm).sub_const C,fun x => by simp only [F,hGT],?_,?_⟩
  · exact hGconv.mono fun x hx => ⟨hconv hx.1,hconv hx.2⟩
  · intro A hA hTA
    have hHi : Integrable H μ := (integrable_const (1 : ℝ)).mono' hHm.aestronglyMeasurable
      (Eventually.of_forall fun x => by rw [Real.norm_eq_abs,abs_of_nonneg (hHb x).1]; exact (hHb x).2)
    have hf : Integrable (fun x => f x) μ := (integrable_const C).mono' f.continuous.measurable.aestronglyMeasurable
      (Eventually.of_forall hbound)
    have he : (fun x => F x)=ᵐ[μ.restrict A] (fun x => d*H x-C) :=
      (ae_restrict_of_ae hGH).mono fun x hx => by simp only [F,hx]
    rw [integral_congr_ae he,integral_sub (hHi.const_mul d).integrableOn (integrable_const C),
      integral_const_mul,hHint A hA hTA]
    have hge : (∫ x in A,g x ∂μ)=((∫ x in A,f x ∂μ)+(∫ x in A,C ∂μ))/d := by
      dsimp only [g]
      rw [integral_div,integral_add hf.integrableOn (integrable_const C)]
    rw [hge]
    field_simp
    ring

end BoundedSubadditive

end
section
open MeasureTheory Filter Set
open scoped Topology ENNReal

namespace BoundedSubadditive
variable {X : Type*} [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]

theorem exists_continuousBirkhoffCode {μ : Measure X} [IsFiniteMeasure μ]
    {T S : X → X} (hT : MeasurePreserving T μ μ) (hS : MeasurePreserving S μ μ)
    (hST : ∀ x,S (T x)=x) (hTS : ∀ x,T (S x)=x) :
    Nonempty (ContinuousBirkhoffCode T S μ) := by
  obtain ⟨f,hf⟩ := TopologicalSpace.exists_dense_seq C(X,ℝ)
  choose F hFm hFT hFconv hFint using fun j => continuous_birkhoff_limit hT hS hST hTS (f j)
  exact ⟨{
    observation := f, dense := hf, value := fun x j => F j x,
    measurable := Measurable.of_eval hFm,
    invariant := fun x => funext fun j => hFT j x,
    generic := ae_all_iff.mpr hFconv,
    integral := fun A hA hTA j => hFint j A hA hTA }⟩

lemma continuousMap_integrable (μ : Measure X) [IsFiniteMeasure μ] (f : C(X,ℝ)) : Integrable f μ :=
  f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)

lemma continuous_integral_continuousMap (μ : Measure X) [IsFiniteMeasure μ] :
    Continuous (fun f : C(X,ℝ) => ∫ x,f x ∂μ) := by
  apply (LipschitzWith.of_dist_le_mul (K := ⟨μ.real univ,ENNReal.toReal_nonneg⟩) ?_).continuous
  intro f g
  rw [dist_eq_norm,←integral_sub (continuousMap_integrable μ f) (continuousMap_integrable μ g),dist_eq_norm]
  exact (norm_integral_le_of_norm_le_const (Eventually.of_forall fun x => (f-g).norm_coe_le_norm x)).trans_eq (mul_comm _ _)

lemma measure_eq_of_dense_continuous_integrals {μ ν : Measure X} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {f : ℕ → C(X,ℝ)} (hf : DenseRange f)
    (he : ∀ j,∫ x,f j x ∂μ=∫ x,f j x ∂ν) : μ=ν := by
  have hfun := hf.equalizer (continuous_integral_continuousMap μ) (continuous_integral_continuousMap ν) (funext he)
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro g
  exact congrFun hfun g.toContinuousMap

end BoundedSubadditive

end
end

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_Components_BirkhoffAtoms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Filter Set
open scoped Topology ENNReal

namespace BoundedSubadditive

namespace ContinuousBirkhoffCode

lemma measurableSet_atom {X : Type*} [MetricSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X] {T S : X → X} {μ : Measure X} [IsFiniteMeasure μ]
    (C : ContinuousBirkhoffCode T S μ) (c : ℕ → ℝ) :
    MeasurableSet {x | C.value x=c} := measurableSet_eq_fun C.measurable measurable_const
lemma invariant_atom {X : Type*} [MetricSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X] {T S : X → X} {μ : Measure X} [IsFiniteMeasure μ]
    (C : ContinuousBirkhoffCode T S μ) (c : ℕ → ℝ) :
    T ⁻¹' {x | C.value x=c}={x | C.value x=c} := by
  ext x
  simp only [mem_preimage,mem_ofPred_eq,C.invariant]

lemma integral_on_subset_atom {X : Type*} [MetricSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X] {T S : X → X} {μ : Measure X} [IsFiniteMeasure μ]
    (C : ContinuousBirkhoffCode T S μ) (c : ℕ → ℝ)
    {A : Set X} (hA : MeasurableSet A) (hTA : T ⁻¹' A=A) (hAc : A⊆{x | C.value x=c}) (j : ℕ) :
    ∫ x in A,C.observation j x ∂μ=(μ A).toReal*c j := by
  rw [←C.integral A hA hTA j]
  have he : (fun x => C.value x j)=ᵐ[μ.restrict A] (fun _ => c j) :=
    (ae_restrict_mem hA).mono fun x hx => congrFun (hAc hx) j
  rw [integral_congr_ae he,integral_const]
  simp only [Measure.real,Measure.restrict_apply_univ,smul_eq_mul]

variable {X : Type*} [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable {T S : X → X} {μ : Measure X} [IsFiniteMeasure μ]

theorem ergodic_atom (C : ContinuousBirkhoffCode T S μ) (hT : MeasurePreserving T μ μ)
    {c : ℕ → ℝ} (hc : 0<μ {x | C.value x=c}) :
    Ergodic T ((μ {x | C.value x=c})⁻¹ • μ.restrict {x | C.value x=c}) := by
  let E := {x | C.value x=c}
  have hE : MeasurableSet E := C.measurableSet_atom c
  have hTE : T ⁻¹' E=E := C.invariant_atom c
  have hET : MeasurePreserving T (μ.restrict E) (μ.restrict E) := by
    simpa only [hTE] using hT.restrict_preimage hE
  have hEr : (μ E).toReal≠0 := ne_of_gt (ENNReal.toReal_pos hc.ne' (measure_ne_top μ E))
  let ν := (μ E)⁻¹ • μ.restrict E
  have hν : IsProbabilityMeasure ν := ⟨by
    dsimp only [ν]
    rw [Measure.smul_apply,Measure.restrict_apply_univ,smul_eq_mul]
    exact ENNReal.inv_mul_cancel hc.ne' (measure_ne_top μ E)⟩
  let := hν
  refine ⟨hET.smul_measure _,?_⟩
  constructor
  intro A hA hTA
  by_cases hzero : μ (A∩E)=0
  · apply eventuallyConst_set'.mpr
    left
    have hz : ν A=0 := by
      dsimp only [ν]
      rw [Measure.smul_apply,Measure.restrict_apply hA,hzero,smul_zero]
    change A =ᵐ[ν] (∅ : Set X)
    simpa only [ae_eq_empty] using hz
  · have hAE : MeasurableSet (A∩E) := hA.inter hE
    have hTAE : T ⁻¹' (A∩E)=A∩E := by rw [preimage_inter,hTA,hTE]
    let η := (μ (A∩E))⁻¹ • μ.restrict (A∩E)
    have hη : IsProbabilityMeasure η := ⟨by
      dsimp only [η]
      rw [Measure.smul_apply,Measure.restrict_apply_univ,smul_eq_mul]
      exact ENNReal.inv_mul_cancel hzero (measure_ne_top μ _)⟩
    let := hη
    have hiE (j : ℕ) : (∫ x,C.observation j x ∂ν)=c j := by
      dsimp only [ν]
      rw [integral_smul_measure,C.integral_on_subset_atom c hE hTE Subset.rfl j,
        ENNReal.toReal_inv,smul_eq_mul,←mul_assoc,inv_mul_cancel₀ hEr,one_mul]
    have hiAE (j : ℕ) : (∫ x,C.observation j x ∂η)=c j := by
      dsimp only [η]
      have hr : (μ (A∩E)).toReal≠0 := ne_of_gt (ENNReal.toReal_pos hzero (measure_ne_top μ _))
      rw [integral_smul_measure,C.integral_on_subset_atom c hAE hTAE inter_subset_right j,
        ENNReal.toReal_inv,smul_eq_mul,←mul_assoc,inv_mul_cancel₀ hr,one_mul]
    have hην : η=ν := measure_eq_of_dense_continuous_integrals C.dense (fun j => (hiAE j).trans (hiE j).symm)
    have hz : ν Aᶜ=0 := by
      rw [←hην]
      dsimp only [η]
      rw [Measure.smul_apply,Measure.restrict_apply hA.compl]
      have he : Aᶜ∩(A∩E)=∅ := by ext x; simp only [mem_inter_iff,mem_compl_iff,mem_empty_iff_false]; tauto
      rw [he,measure_empty,smul_zero]
    apply eventuallyConst_set'.mpr
    right
    change A =ᵐ[ν] univ
    simpa only [ae_eq_univ] using hz

end ContinuousBirkhoffCode
end BoundedSubadditive

end
section
namespace StandardMapEntropy
open MeasureTheory MeasureTheory.Measure Set Filter Topology
open scoped Topology ENNReal
open NonlinearStable BoundedSubadditive
attribute [local instance] Measure.Subtype.measureSpace

namespace ReversibleGraphRectangle
variable {k χ : ℝ} {B : ReversibleRectangleBlock k χ} {F : ReversibleGraphFamilies B} (R : ReversibleGraphRectangle F)
lemma stable_representation (p : B.coordinateCarrier×B.coordinateCarrier) :
    B.chart (R.point p)=fineStableCurve k χ B.ε B.δ B.δ_pos B.contraction (B.label p.1)
      (B.regular (B.label p.1) (B.label p.1).property) (F.stableParameter (B.label p.1) (R.point p).1) := by
  calc
    B.chart (R.point p)=B.chart ((R.point p).1,F.G (B.label p.1) (R.point p).1) := congrArg B.chart (Prod.ext rfl (R.stable p))
    _ = _ := F.stable_representation _ _ ((R.x_bound p).trans (by linarith [B.ρ_small,B.r_pos]))
lemma unstable_representation (p : B.coordinateCarrier×B.coordinateCarrier) :
    B.chart (R.point p)=fineUnstableCurve k χ B.ε B.δ B.δ_pos B.contraction (B.label p.2)
      (B.reversed (B.label p.2) (B.label p.2).property) (F.unstableParameter (B.label p.2) (R.point p).2) := by
  calc
    B.chart (R.point p)=B.chart (F.U (B.label p.2) (R.point p).2,(R.point p).2) := congrArg B.chart (Prod.ext (R.unstable p) rfl)
    _ = _ := F.unstable_representation _ _ ((R.y_bound p).trans (by linarith [B.ρ_reverse,B.ρ_pos]))
lemma torus_nonsingular : QuasiMeasurePreserving R.torusPoint ((volume : Measure B.coordinateCarrier).prod volume) area :=
  complexProjection_quasiMeasurePreserving.comp (B.chart_quasiMeasurePreserving.comp R.nonsingular)
lemma spectrum_positive {p : B.coordinateCarrier×B.coordinateCarrier} {l : ℝ}
    (hl : LyapunovSpectrumAt k (R.torusPoint p) l) : 0<l := by
  apply fineStableCurve_spectrum_positive k χ B.ε B.δ B.δ_pos B.contraction (B.label p.1)
    (B.regular (B.label p.1) (B.label p.1).property)
    (s := F.stableParameter (B.label p.1) (R.point p).1)
    (lt_of_le_of_lt (F.stable_bound _ _) (by linarith [B.r_small]))
  simpa only [torusPoint,R.stable_representation] using hl
end ReversibleGraphRectangle

end StandardMapEntropy

end
section
namespace StandardMapEntropy
open MeasureTheory MeasureTheory.Measure Set Filter Topology
open scoped Topology ENNReal
open BoundedSubadditive
attribute [local instance] Measure.Subtype.measureSpace

namespace ReversibleGraphRectangle
variable {k χ : ℝ} {B : ReversibleRectangleBlock k χ} {F : ReversibleGraphFamilies B}
    (R : ReversibleGraphRectangle F)

lemma row_asymptotic (a b b' : B.coordinateCarrier) :
    Tendsto (fun n : ℕ => dist ((standardMap k)^[n] (R.torusPoint (a,b)))
      ((standardMap k)^[n] (R.torusPoint (a,b')))) atTop (𝓝 0) := by
  have h := fineStableCurve_asymptotic k χ B.ε B.δ B.δ_pos B.contraction (B.label a)
    (B.regular (B.label a) (B.label a).property)
    ((F.stable_bound (B.label a) (R.point (a,b)).1).trans (by linarith [B.r_small]))
    ((F.stable_bound (B.label a) (R.point (a,b')).1).trans (by linarith [B.r_small]))
  simpa only [torusPoint,R.stable_representation] using h

lemma column_asymptotic (a a' b : B.coordinateCarrier) :
    Tendsto (fun n : ℕ => dist ((inverseMap k)^[n] (R.torusPoint (a,b)))
      ((inverseMap k)^[n] (R.torusPoint (a',b)))) atTop (𝓝 0) := by
  have h := fineUnstableCurve_asymptotic k χ B.ε B.δ B.δ_pos B.contraction (B.label b)
    (B.reversed (B.label b) (B.label b).property)
    ((F.unstable_bound (B.label b) (R.point (a,b)).2).trans (by linarith [B.r'_small]))
    ((F.unstable_bound (B.label b) (R.point (a',b)).2).trans (by linarith [B.r'_small]))
  simpa only [torusPoint,R.unstable_representation] using h
end ReversibleGraphRectangle

lemma asymptotic_iterate {X : Type*} [PseudoMetricSpace X] {T : X → X} {x y : X}
    (h : Tendsto (fun n : ℕ => dist (T^[n] x) (T^[n] y)) atTop (𝓝 0))
    {m : ℕ} (hm : 0 < m) :
    Tendsto (fun n : ℕ => dist ((T^[m])^[n] x) ((T^[m])^[n] y)) atTop (𝓝 0) := by
  have ht : Tendsto (fun n : ℕ => m*n) atTop atTop :=
    tendsto_atTop_mono (fun n => by change n ≤ m*n; nlinarith) tendsto_id
  simpa only [Function.comp_def,Function.iterate_mul] using h.comp ht

theorem exists_powerBirkhoffCodes (k : ℝ) :
    Nonempty (∀ m : ℕ,ContinuousBirkhoffCode ((standardMap k)^[m+1]) ((inverseMap k)^[m+1]) area) := by
  have h (m : ℕ) := exists_continuousBirkhoffCode ((measurePreserving_standardMap k).iterate (m+1))
    ((measurePreserving_inverseMap k).iterate (m+1))
    ((show Function.LeftInverse (inverseMap k) (standardMap k) from inverseMap_standardMap k).iterate (m+1))
    ((show Function.LeftInverse (standardMap k) (inverseMap k) from standardMap_inverseMap k).iterate (m+1))
  exact ⟨fun m => Classical.choice (h m)⟩

end StandardMapEntropy

end
section
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal

namespace BoundedSubadditive
variable {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {T : X → X} {A B : Set X}

lemma ergodic_restrict_of_normalized [IsFiniteMeasure μ] (hA : 0<μ A)
    (h : Ergodic T ((μ A)⁻¹ • μ.restrict A)) : Ergodic T (μ.restrict A) := by
  have hh := h.smul_measure (μ A)
  simpa only [smul_smul,ENNReal.mul_inv_cancel hA.ne' (measure_ne_top μ A),one_smul] using hh

lemma ergodic_restrict_congr [IsFiniteMeasure μ] {V : X → X} (h : Ergodic V (μ.restrict A)) (hAB : A =ᵐ[μ] B) :
    Ergodic V (μ.restrict B) := by
  rwa [Measure.restrict_congr_set hAB] at h

end BoundedSubadditive

end
end

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_Bernoulli_ErgodicAverages
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace StandardMapEntropy
open MeasureTheory MeasureTheory.Measure Set Filter Topology
open scoped Topology ENNReal
open BoundedSubadditive HyperbolicCoding
attribute [local instance] Measure.Subtype.measureSpace

namespace ReversibleRectangleBlock
variable {k χ : ℝ} (B : ReversibleRectangleBlock k χ)

instance carrierProbability_probability : IsProbabilityMeasure B.carrierProbability := by
  let _ : IsFiniteMeasure (volume : Measure B.coordinateCarrier) := B.finite_coordinate_volume
  have hp : 0<(volume : Measure B.coordinateCarrier) univ := by
    rw [B.volume_coordinate_univ]
    exact B.positive_coordinateCarrier
  constructor
  simp only [carrierProbability,Measure.smul_apply,smul_eq_mul]
  exact ENNReal.inv_mul_cancel hp.ne' (measure_ne_top _ _)

lemma carrierProbability_ac : B.carrierProbability≪(volume : Measure B.coordinateCarrier) :=
  smul_absolutelyContinuous
end ReversibleRectangleBlock

lemma quasiMeasurePreserving_normalizedArea {Ω : Type*} [MeasurableSpace Ω]
    {ν : Measure Ω} {p : Ω → Torus} (hp : QuasiMeasurePreserving p ν area)
    {E : Set Torus} (hE : MeasurableSet E) (hmem : ∀ᵐ w ∂ν,p w∈E) :
    QuasiMeasurePreserving p ν (normalizedArea E) := by
  have hae : ∀ᵐ z ∂ν.map p,z∈E := (ae_map_iff hp.measurable.aemeasurable hE).mpr hmem
  have hac := hp.absolutelyContinuous.restrict E
  rw [Measure.restrict_eq_self_of_ae_mem hae] at hac
  exact ⟨hp.measurable,hac.trans (absolutelyContinuous_smul (ENNReal.inv_ne_zero.mpr (measure_ne_top area E)))⟩

namespace ReversibleGraphRectangle
variable {k χ : ℝ} {B : ReversibleRectangleBlock k χ} {F : ReversibleGraphFamilies B}
    (R : ReversibleGraphRectangle F)

lemma carrier_nonsingular :
    QuasiMeasurePreserving R.torusPoint (B.carrierProbability.prod B.carrierProbability) area := by
  let _ : IsFiniteMeasure (volume : Measure B.coordinateCarrier) := B.finite_coordinate_volume
  exact R.torus_nonsingular.mono_left (B.carrierProbability_ac.prod B.carrierProbability_ac)

lemma component_for_power {N : ℕ} (hN : 0<N)
    (C : ContinuousBirkhoffCode ((standardMap k)^[N]) ((inverseMap k)^[N]) area) :
    ∃ E : Set Torus,MeasurableSet E ∧ 0<area E ∧ ((standardMap k)^[N] ⁻¹' E=E) ∧
      Ergodic ((standardMap k)^[N]) (normalizedArea E) ∧
      QuasiMeasurePreserving R.torusPoint (B.carrierProbability.prod B.carrierProbability) (normalizedArea E) := by
  have hrow (a b b' : B.coordinateCarrier)
      (ha : ∀ j : ℕ,
        Tendsto (fun n : ℕ => birkhoffSum ((standardMap k)^[N]) (C.observation j) n (R.torusPoint (a,b))/(n : ℝ)) atTop (𝓝 (C.value (R.torusPoint (a,b)) j)) ∧
        Tendsto (fun n : ℕ => birkhoffSum ((inverseMap k)^[N]) (C.observation j) n (R.torusPoint (a,b))/(n : ℝ)) atTop (𝓝 (C.value (R.torusPoint (a,b)) j)))
      (hb : ∀ j : ℕ,
        Tendsto (fun n : ℕ => birkhoffSum ((standardMap k)^[N]) (C.observation j) n (R.torusPoint (a,b'))/(n : ℝ)) atTop (𝓝 (C.value (R.torusPoint (a,b')) j)) ∧
        Tendsto (fun n : ℕ => birkhoffSum ((inverseMap k)^[N]) (C.observation j) n (R.torusPoint (a,b'))/(n : ℝ)) atTop (𝓝 (C.value (R.torusPoint (a,b')) j))) :
      C.value (R.torusPoint (a,b))=C.value (R.torusPoint (a,b')) := by
    funext j
    exact birkhoff_limit_eq_of_asymptotic (CompactSpace.uniformContinuous_of_continuous (C.observation j).continuous)
      (asymptotic_iterate (R.row_asymptotic a b b') hN) (ha j).1 (hb j).1
  have hcol (a a' b : B.coordinateCarrier)
      (ha : ∀ j : ℕ,
        Tendsto (fun n : ℕ => birkhoffSum ((standardMap k)^[N]) (C.observation j) n (R.torusPoint (a,b))/(n : ℝ)) atTop (𝓝 (C.value (R.torusPoint (a,b)) j)) ∧
        Tendsto (fun n : ℕ => birkhoffSum ((inverseMap k)^[N]) (C.observation j) n (R.torusPoint (a,b))/(n : ℝ)) atTop (𝓝 (C.value (R.torusPoint (a,b)) j)))
      (hb : ∀ j : ℕ,
        Tendsto (fun n : ℕ => birkhoffSum ((standardMap k)^[N]) (C.observation j) n (R.torusPoint (a',b))/(n : ℝ)) atTop (𝓝 (C.value (R.torusPoint (a',b)) j)) ∧
        Tendsto (fun n : ℕ => birkhoffSum ((inverseMap k)^[N]) (C.observation j) n (R.torusPoint (a',b))/(n : ℝ)) atTop (𝓝 (C.value (R.torusPoint (a',b)) j))) :
      C.value (R.torusPoint (a,b))=C.value (R.torusPoint (a',b)) := by
    funext j
    exact birkhoff_limit_eq_of_asymptotic (CompactSpace.uniformContinuous_of_continuous (C.observation j).continuous)
      (asymptotic_iterate (R.column_asymptotic a a' b) hN) (ha j).2 (hb j).2
  obtain ⟨c,hc⟩ := ae_constant_of_product_rows_columns (F := fun p => C.value (R.torusPoint p)) (R.carrier_nonsingular.ae C.generic) hrow hcol
  let E := {z | C.value z=c}
  have hE : MeasurableSet E := C.measurableSet_atom c
  have hEpos : 0<area E := by
    by_contra hn
    have hz : area E=0 := le_antisymm (not_lt.mp hn) bot_le
    have ha : ∀ᵐ z ∂area,z∉E := by simpa only [ae_iff,not_not,Set.ofPred_mem_eq] using hz
    obtain ⟨p,hp,hp'⟩ := (hc.and (R.carrier_nonsingular.ae ha)).exists
    exact hp' hp
  exact ⟨E,hE,hEpos,C.invariant_atom c,C.ergodic_atom ((measurePreserving_standardMap k).iterate N) hEpos,
    quasiMeasurePreserving_normalizedArea R.carrier_nonsingular hE hc⟩

end ReversibleGraphRectangle
end StandardMapEntropy

end
section
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped Topology NNReal ENNReal

namespace HyperbolicCoding

lemma measurable_joinedBinary {X : Type*} [MeasurableSpace X]
    {α : ℕ → ℕ → X → Bool} (hα : ∀ i j,Measurable (α i j)) (N : ℕ) :
    Measurable (joinedBinary α N) :=
  Measurable.of_eval (fun p => hα p.1 p.2)

end HyperbolicCoding

end
end

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_Components_PowerAtomCycles
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal

namespace BoundedSubadditive
variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]

namespace PowerAtomFamily
variable {e : X ≃ᵐ X} (F : PowerAtomFamily e μ) (he : MeasurePreserving e μ μ)

lemma periods_bounded : BddAbove (Set.range (fun n => (F.cycle he n).period)) := by
  obtain ⟨D,hD,hDA⟩ := F.common
  have hDr : 0<(μ D).toReal := ENNReal.toReal_pos hD.ne' (measure_ne_top μ D)
  obtain ⟨B,hB⟩ := exists_nat_gt ((μ (F.atom 0)).toReal/(μ D).toReal)
  refine ⟨B,?_⟩
  rintro p ⟨n,rfl⟩
  have hh : ((F.cycle he n).period : ℝ≥0∞)*μ D≤μ (F.atom 0) := by
    calc
      _ ≤ ((F.cycle he n).period : ℝ≥0∞)*μ (F.atom n) := mul_le_mul_right (measure_mono (hDA n)) _
      _ = _ := (F.cycle he n).mass
  have hr := ENNReal.toReal_mono (measure_ne_top μ (F.atom 0)) hh
  simp only [ENNReal.toReal_mul,ENNReal.toReal_natCast] at hr
  have hd : ((F.cycle he n).period : ℝ)≤(μ (F.atom 0)).toReal/(μ D).toReal :=
    (le_div_iff₀ hDr).mpr hr
  exact le_of_lt (by exact_mod_cast hd.trans_lt hB)

lemma exists_max_period : ∃ n : ℕ,∀ m,(F.cycle he m).period≤(F.cycle he n).period := by
  let S := Set.range (fun n => (F.cycle he n).period)
  have hb : BddAbove S := F.periods_bounded he
  have hf : S.Finite := Set.finite_iff_bddAbove.mpr hb
  obtain ⟨n,hn⟩ := (show S.Nonempty from ⟨(F.cycle he 0).period,mem_range_self 0⟩).csSup_mem hf
  refine ⟨n,?_⟩
  intro m
  change (F.cycle he n).period=sSup S at hn
  rw [hn]
  exact le_csSup hb (mem_range_self m)

theorem exists_totally_ergodic_cycle : ∃ n : ℕ,∀ r : ℕ,0 < r →
    ∀ j : Fin (F.cycle he n).period,
      Ergodic ((e^[(F.cycle he n).period])^[r])
        (μ.restrict ((e.symm^[j.val]) ⁻¹' F.atom n)) := by
  obtain ⟨n,hn⟩ := F.exists_max_period he
  refine ⟨n,?_⟩
  intro r hr j
  let C := F.cycle he n
  let m := (n+1)*r-1
  have hm : m+1=(n+1)*r := by
    have hpos : 0<(n+1)*r := Nat.mul_pos (Nat.succ_pos n) hr
    exact Nat.sub_add_cancel hpos
  have hmn : n+1 ∣ m+1 := ⟨r,hm⟩
  have hsub := F.refinement hmn
  have hmasses : μ (F.atom n)≤μ (F.atom m) := by
    have hmul : (C.period : ℝ≥0∞)*μ (F.atom n)≤(C.period : ℝ≥0∞)*μ (F.atom m) := by
      calc
        _ = μ (F.atom 0) := C.mass
        _ = ((F.cycle he m).period : ℝ≥0∞)*μ (F.atom m) := (F.cycle he m).mass.symm
        _ ≤ _ := mul_le_mul_left (by exact_mod_cast hn m) _
    exact (ENNReal.mul_le_mul_iff_right (by exact_mod_cast C.positive.ne') (by simp)).mp hmul
  have heq : F.atom m =ᵐ[μ] F.atom n := ae_eq_of_ae_subset_of_measure_ge hsub hmasses
    (F.measurable m).nullMeasurableSet (measure_ne_top μ (F.atom n))
  have herm : Ergodic (e^[m+1]) (μ.restrict (F.atom n)) := ergodic_restrict_congr (F.ergodic m) heq
  have hbase : Ergodic (e^[C.period]) (μ.restrict (F.atom n)) := by
    simpa only [Function.iterate_zero,preimage_id_eq,id_eq] using C.ergodic ⟨0,C.positive⟩
  have ht : Ergodic ((e^[C.period])^[r]) (μ.restrict (F.atom n)) := by
    refine ⟨hbase.toMeasurePreserving.iterate r,?_⟩
    obtain ⟨q,hq⟩ := C.divides
    apply PreErgodic.of_iterate q
    have hnum : m+1=(C.period*r)*q := by
      calc
        m+1=(n+1)*r := hm
        _ = (C.period*q)*r := congrArg (fun a : ℕ => a*r) hq
        _ = _ := by ac_rfl
    simpa only [hnum,Function.iterate_mul] using herm.toPreErgodic
  have ht' : Ergodic (e^[C.period*r]) (μ.restrict (F.atom n)) := by
    simpa only [Function.iterate_mul] using ht
  simpa only [Function.iterate_mul] using ergodic_translate e he (F.measurable n) ht' j.val

end PowerAtomFamily
end BoundedSubadditive

end
section
namespace StandardMapEntropy
open MeasureTheory MeasureTheory.Measure Set Filter Topology
open scoped Topology ENNReal
open BoundedSubadditive

lemma positive_spectrum_on_ergodic_component (k : ℝ) (hk : 0≤k) {E : Set Torus}
    (hE : MeasurableSet E) (herg : Ergodic (standardMap k) (normalizedArea E))
    (hpos : 0<area (E∩{z | 0 < standardLyapunov k hk z})) :
    ∀ᵐ z ∂normalizedArea E,∃ l : ℝ,0<l ∧ LyapunovSpectrumAt k z l := by
  let H := {z | 0 < standardLyapunov k hk z}
  have hH : MeasurableSet H := measurableSet_lt measurable_const (measurable_standardLyapunov k hk)
  have hTH : standardMap k ⁻¹' H=H := by
    ext z
    simp only [H,mem_preimage,mem_ofPred_eq,standardLyapunov_invariant]
  have hHinE : 0<normalizedArea E H := by
    unfold normalizedArea
    rw [Measure.smul_apply,Measure.restrict_apply' hE,smul_eq_mul,inter_comm H E]
    exact ENNReal.mul_pos (ENNReal.inv_ne_zero.mpr (measure_ne_top area E)) hpos.ne'
  have hAE : ∀ᵐ z ∂normalizedArea E,z∈H := by
    rcases herg.toPreErgodic.ae_mem_or_ae_notMem hH hTH with h|h
    · exact h
    · have hz : normalizedArea E H=0 := by
        simpa only [ae_iff,not_not,Set.ofPred_mem_eq] using h
      exact (hHinE.ne' hz).elim
  have hac : normalizedArea E≪area := smul_absolutelyContinuous.trans Measure.absolutelyContinuous_restrict
  filter_upwards [hAE,hac.ae_le (ae_standardLyapunov_spectrum k hk)] with z hz hs
  exact ⟨standardLyapunov k hk z,hz,hs⟩

end StandardMapEntropy

end
end

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_Bernoulli_IntegerDynamics
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Set Filter

namespace HyperbolicCoding
variable {X A : Type*} [MeasurableSpace X]

lemma iterateEquiv_apply (e : X ≃ᵐ X) (n : ℕ) (x : X) : iterateEquiv e n x=e^[n] x := by
  change ((e.toEquiv^n) x)=_
  rw [Equiv.Perm.coe_pow]
  rfl

end HyperbolicCoding

end
section
namespace HyperbolicCoding
open MeasureTheory MeasureTheory.Measure Set Filter
lemma iterateEquiv_symm_apply {X : Type*} [MeasurableSpace X] (e : X ≃ᵐ X) (N : ℕ) (x : X) :
    (iterateEquiv e N).symm x=e.symm^[N] x := by
  change ((e.toEquiv^N)⁻¹ x)=_
  rw [←inv_pow,Equiv.Perm.inv_def,Equiv.Perm.coe_pow]
  rfl
end HyperbolicCoding

end
section
namespace StandardMapEntropy
open MeasureTheory MeasureTheory.Measure Set Filter Topology BoundedSubadditive
open scoped ENNReal
namespace ReversibleGraphRectangle
variable {k χ : ℝ} {B : ReversibleRectangleBlock k χ} {F : ReversibleGraphFamilies B}
    (R : ReversibleGraphRectangle F)

theorem powerAtoms_with_rectangle (hk : 0≤k) :
    ∃ P : PowerAtomFamily (standardMap_measurableEquiv k) area,
      (∀ n,QuasiMeasurePreserving R.torusPoint (B.carrierProbability.prod B.carrierProbability)
        (normalizedArea (P.atom n))) ∧
      0<area (P.atom 0∩{z | 0 < standardLyapunov k hk z}) := by
  obtain ⟨C⟩ := exists_powerBirkhoffCodes k
  have hex (n : ℕ) := R.component_for_power (Nat.succ_pos n) (C n)
  choose E hE hp hInv hErg hπ using hex
  have hmem (n : ℕ) : ∀ᵐ p ∂B.carrierProbability.prod B.carrierProbability,R.torusPoint p∈E n :=
    (hπ n).ae (normalizedArea_ae_mem (hE n))
  let D : Set Torus := (⋂ n : ℕ,E n)∩{z | 0 < standardLyapunov k hk z}
  have hDpos : 0<area D := by
    by_contra hn
    have hz : area D=0 := le_antisymm (not_lt.mp hn) bot_le
    have ha : ∀ᵐ z ∂area,z∉D := by simpa only [ae_iff,not_not,Set.ofPred_mem_eq] using hz
    obtain ⟨p,hm,hs,hn⟩ := ((ae_all_iff.mpr hmem).and
      ((R.carrier_nonsingular.ae (ae_standardLyapunov_spectrum k hk)).and (R.carrier_nonsingular.ae ha))).exists
    exact hn ⟨mem_iInter.mpr hm,R.spectrum_positive hs⟩
  let P : PowerAtomFamily (standardMap_measurableEquiv k) area := {
    atom := E
    measurable := hE
    positive := hp
    invariant := hInv
    ergodic := fun n => ergodic_restrict_of_normalized (hp n) (hErg n)
    common := ⟨D,hDpos,fun n _ hx => (mem_iInter.mp hx.1) n⟩ }
  refine ⟨P,hπ,hDpos.trans_le (measure_mono ?_)⟩
  intro x hx
  exact ⟨(mem_iInter.mp hx.1) 0,hx.2⟩

end ReversibleGraphRectangle
end StandardMapEntropy

end
end

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_Bernoulli_ReverseTailProjection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace HyperbolicCoding
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal Topology
variable {X A : Type*} [MeasurableSpace X] [MeasurableSpace A]

lemma measurable_remotePair {T S : X → X} {α : X → A}
    (hT : Measurable T) (hS : Measurable S) (hα : Measurable α) (n : ℕ) :
    Measurable (remotePair T S α n) :=
  (measurable_tailName hS hα n).prodMk (measurable_tailName hT hα n)

end HyperbolicCoding

end
end

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_Bernoulli_ErgodicL1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace HyperbolicCoding
open MeasureTheory Set Filter
open scoped ENNReal Topology
variable {X A : Type*} [MeasurableSpace X] [MeasurableSpace A]

omit [MeasurableSpace X] [MeasurableSpace A] in
lemma tailName_commute (T d : X → X) (α : X → A) (h : Function.Commute d T) (n : ℕ) :
    tailName T (α ∘ d) n=tailName T α n ∘ d := by
  funext x i
  exact congrArg α (h.iterate_right (i+n) x)

theorem WeakBernoulliProcess.translate {μ ν : Measure X} (e : X ≃ᵐ X)
    {d : X → X} (hd : MeasurePreserving d ν μ) (hde : Function.Commute d e)
    (hde' : Function.Commute d e.symm) {α : X → A} (hα : Measurable α)
    (h : WeakBernoulliProcess μ e α) : WeakBernoulliProcess ν e (α ∘ d) := by
  have ht (T : X → X) (hT : Measurable T) (hc : Function.Commute d T) (n : ℕ) :
      ν.map (tailName T (α ∘ d) n)=μ.map (tailName T α n) := by
    rw [tailName_commute T d α hc n,←Measure.map_map
      (measurable_tailName hT hα n) hd.measurable,hd.map_eq]
  have hp (n : ℕ) : ν.map (remotePair e e.symm (α ∘ d) n)=μ.map (remotePair e e.symm α n) := by
    have heq : remotePair e e.symm (α ∘ d) n=remotePair e e.symm α n ∘ d := by
      funext x
      exact Prod.ext (congrFun (tailName_commute e.symm d α hde' n) x)
        (congrFun (tailName_commute e d α hde n) x)
    rw [heq,←Measure.map_map (measurable_remotePair e.measurable e.symm.measurable hα n)
      hd.measurable,hd.map_eq]
  have hprod : remoteProductLaw ν e e.symm (α ∘ d)=remoteProductLaw μ e e.symm α := by
    simp only [remoteProductLaw,ht e e.measurable hde 0,ht e.symm e.symm.measurable hde' 0]
  intro ε hε
  filter_upwards [h ε hε] with n hn
  simpa only [hp n,hprod] using hn

end HyperbolicCoding

end
section
namespace StandardMapEntropy
open MeasureTheory MeasureTheory.Measure Set Filter Topology HyperbolicCoding BoundedSubadditive
open scoped ENNReal

theorem actual_cyclic_weakBernoulli_component_q44_oai (k : ℝ) (hk : 0≤k) {χ : ℝ} (hχ : 0<χ)
    (hgap : 0<area (spectralGapRegion k hk χ)) :
    ∃ E : Set Torus,MeasurableSet E ∧ 0<area E ∧
      (standardMap k ⁻¹' E=E) ∧ Ergodic (standardMap k) (normalizedArea E) ∧
      (∀ᵐ z ∂normalizedArea E,∃ l : ℝ,0<l ∧ LyapunovSpectrumAt k z l) ∧
      ∃ (N : ℕ) (hN : 0<N) (P : Fin N → Set Torus),
        (∀ j,MeasurableSet (P j)) ∧ ((⋃ j,P j) =ᵐ[area] E) ∧
        (∀ i j,i≠j → area (P i∩P j)=0) ∧
        (∀ j,(standardMap k '' P j) =ᵐ[area] P ⟨(j.val+1)%N,Nat.mod_lt _ hN⟩) ∧
        (∀ j,area (P j)=area E/(N : ℝ≥0∞) ∧ 0<area (P j)) ∧
        (∀ j,∀ r : ℕ,0 < r → Ergodic (((standardMap k)^[N])^[r]) (normalizedArea (P j))) ∧
        (∀ j,∃ α : ℕ → ℕ → Torus → Bool,
          (∀ i r,Measurable (α i r)) ∧ Function.Injective (fun z => fun i r => α i r z) ∧
          ∀ M : ℕ,WeakBernoulliProcess (normalizedArea (P j))
            (iterateEquiv (standardMap_measurableEquiv k) N) (joinedBinary α M)) := by
  obtain ⟨B⟩ := exists_reversibleRectangleBlock_q44 k hk hχ hgap
  obtain ⟨G⟩ := reversible_graph_families B
  obtain ⟨R⟩ := reversible_graph_rectangle G hk
  obtain ⟨F,hπ,hFH⟩ := R.powerAtoms_with_rectangle hk
  have he : MeasurePreserving (standardMap_measurableEquiv k) area area := measurePreserving_standardMap k
  obtain ⟨n,hn⟩ := F.exists_totally_ergodic_cycle he
  let C := F.cycle he n
  let P (j : Fin C.period) : Set Torus := ((standardMap_measurableEquiv k).symm^[j.val]) ⁻¹' F.atom n
  have hP (j : Fin C.period) : MeasurableSet (P j) :=
    (F.measurable n).preimage ((standardMap_measurableEquiv k).symm.measurable.iterate j.val)
  have hPmass (j : Fin C.period) : area (P j)=area (F.atom n) :=
    ((he.symm (standardMap_measurableEquiv k)).iterate j.val).measure_preimage (F.measurable n).nullMeasurableSet
  have hEerg : Ergodic (standardMap k) (normalizedArea (F.atom 0)) := by
    have hh := (F.ergodic 0).smul_measure (area (F.atom 0))⁻¹
    simp only [zero_add,Function.iterate_one] at hh
    exact hh
  have htotal (j : Fin C.period) (r : ℕ) (hr : 0 < r) :
      Ergodic (((standardMap k)^[C.period])^[r]) (normalizedArea (P j)) :=
    (hn r hr j).smul_measure (area (P j))⁻¹
  have hbase (r : ℕ) (hr : 0 < r) :
      Ergodic (((standardMap k)^[C.period])^[r]) (normalizedArea (F.atom n)) := by
    simpa only [P,Fin.val_zero,Function.iterate_zero,preimage_id_eq,id_eq] using htotal ⟨0,C.positive⟩ r hr
  let _ := normalizedArea_probability (F.positive n)
  obtain ⟨α,hα,hsep,hwb⟩ := R.exists_weakBernoulli_partitions_q44 C.positive (normalizedArea (F.atom n)) hbase (hπ n)
  refine ⟨F.atom 0,F.measurable 0,F.positive 0,?_,hEerg,
    positive_spectrum_on_ergodic_component k hk (F.measurable 0) hEerg hFH,
    C.period,C.positive,P,hP,C.cover,C.disjoint,C.forward,?_,htotal,?_⟩
  · have hh := F.invariant 0
    simp only [zero_add,Function.iterate_one] at hh
    exact hh
  · intro j
    rw [hPmass]
    exact ⟨(ENNReal.eq_div_iff (by exact_mod_cast C.positive.ne') (by simp)).mpr C.mass,F.positive n⟩
  · intro j
    let d : Torus → Torus := (standardMap_measurableEquiv k).symm^[j.val]
    have hd : MeasurePreserving d (normalizedArea (P j)) (normalizedArea (F.atom n)) := by
      unfold normalizedArea
      rw [hPmass]
      exact (((he.symm (standardMap_measurableEquiv k)).iterate j.val).restrict_preimage
        (F.measurable n)).smul_measure (area (F.atom n))⁻¹
    have hdi : Function.Injective d := (standardMap_measurableEquiv k).symm.injective.iterate j.val
    refine ⟨fun i r => α i r ∘ d,fun i r => (hα i r).comp hd.measurable,?_,?_⟩
    · intro x y hxy
      exact hdi (hsep hxy)
    · intro M
      have hc : Function.Commute (standardMap_measurableEquiv k).symm (standardMap_measurableEquiv k) :=
        fun x => (inverseMap_standardMap k x).trans (standardMap_inverseMap k x).symm
      have hde : Function.Commute d (iterateEquiv (standardMap_measurableEquiv k) C.period) := by
        simpa only [funext (iterateEquiv_apply (standardMap_measurableEquiv k) C.period)] using
          hc.iterate_iterate j.val C.period
      have hde' : Function.Commute d (iterateEquiv (standardMap_measurableEquiv k) C.period).symm := by
        have hc' : Function.Commute (standardMap_measurableEquiv k).symm (standardMap_measurableEquiv k).symm :=
          fun _ => rfl
        simpa only [funext (iterateEquiv_symm_apply (standardMap_measurableEquiv k) C.period)] using
          hc'.iterate_iterate j.val C.period
      exact (hwb M).translate _ hd hde hde' (measurable_joinedBinary hα M)

end StandardMapEntropy

end
end

end OAI
end

theorem solution : type_of% @OAI.StandardMapEntropy.actual_cyclic_weakBernoulli_component_q44_oai := @OAI.StandardMapEntropy.actual_cyclic_weakBernoulli_component_q44_oai
