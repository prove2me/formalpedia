-- Prove2me | solution 1 for OAI.FiniteFactor.exists_source_prepared_finite
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-25T23:38:22.205168+00:00
-- url     : https://prove2.me/submissions/fbb4fd62-a853-4a89-98c4-839dcc85d320

import Mathlib
import Definitions.Def_FiniteFactor
import Definitions.Def_OAIQ3Ff001
import Definitions.Def_OAIQ3Ff002
import Theorems.Thm_OAI_FiniteFactor_sourceSamplingLambda_rectangle_limit_event
import Theorems.Thm_OAI_FiniteFactor_sourceSamplingTrimmed_marginals_event
import Theorems.Thm_OAI_FiniteFactor_sourceSampling_mass_limit_event

section
-- module Solutions.OAIQ3_FF.Compat
attribute [-instance] _root_.OAI.FiniteFactor.sourceUnitCircle_probability
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : p) :
    (if p then a else b) = a := if_pos h
theorem ite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : ¬p) :
    (if p then a else b) = b := if_neg h
theorem dite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : p) :
    dite p a b = a h := dif_pos h
theorem dite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : ¬p) :
    dite p a b = b h := dif_neg h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_Coupling_Prefix
attribute [-instance] _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter Finset
open scoped Topology ENNReal
noncomputable section

/-- Finite-coordinate factorization under the actual infinite product measure. -/
theorem integral_infinitePi_finset_prod {ι : Type*} {X : ι → Type*}
    [∀ i, MeasurableSpace (X i)] (μ : ∀ i, Measure (X i)) [∀ i, IsProbabilityMeasure (μ i)]
    (I : Finset ι) (f : ∀ i, X i → ℝ) (hf : ∀ i, Measurable (f i)) :
    (∫ x, ∏ i ∈ I, f i (x i) ∂Measure.infinitePi μ) = ∏ i ∈ I, ∫ t, f i t ∂μ i := by
  classical
  have he (x : ∀ i, X i) : (∏ i ∈ I, f i (x i)) = ∏ i : I, f i (x i) :=
    (Finset.prod_coe_sort I (fun i => f i (x i))).symm
  simp_rw [he]
  change (∫ x, (∏ i : I, f i (I.restrict x i)) ∂Measure.infinitePi μ) = _
  rw [integral_restrict_infinitePi μ
    (f := fun x : ∀ i : I, X i => ∏ i : I, f i (x i))
    ((Finset.measurable_prod _ fun (i : I) _ => (hf i).comp (measurable_pi_apply i)).aestronglyMeasurable)]
  rw [integral_fintype_prod_eq_prod]
  exact Finset.prod_coe_sort I (fun i => ∫ t, f i t ∂μ i)

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_Coupling_BlockLimit
attribute [-instance] _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter Finset
open scoped Topology ENNReal
noncomputable section
namespace CouplingParameters

theorem mem_blockPrefix (m : ℕ → ℕ) (n : ℕ) (i : BlockCoordinate m) :
    i ∈ blockPrefix m n ↔ i.1 < n := by simp [blockPrefix]

end CouplingParameters
end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_CrossedProduct_FloorSupport
attribute [-instance] _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped ENNReal
noncomputable section

/-- A uniform coordinate crosses the cut under translation by a with
probability at most |a|, valid for either sign and any size of translation. -/
theorem unitInterval_floor_exception (a : ℝ) :
    unitIntervalMeasure {t : ℝ | Int.floor (t+a) ≠ 0} ≤ ENNReal.ofReal |a| := by
  have hm : MeasurableSet {t : ℝ | Int.floor (t+a) ≠ 0} :=
    (measurableSet_eq_fun (Int.measurable_floor.comp (measurable_id.add_const a)) measurable_const).compl
  by_cases ha : |a| < 1
  · rw [unitIntervalMeasure, Measure.restrict_apply hm]
    rcases le_total 0 a with hpos | hneg
    · have hsub : {t : ℝ | Int.floor (t+a) ≠ 0} ∩ Set.Ico 0 1 ⊆ Set.Ico (1-a) 1 := by
        intro t ht
        have hn : ¬ (t+a ∈ Set.Ico (0 : ℝ) 1) := by
          exact fun h => ht.1 (Int.floor_eq_zero_iff.mpr h)
        have hlow : 0 ≤ t+a := add_nonneg ht.2.1 hpos
        exact ⟨by by_contra h; apply hn; exact ⟨hlow, by linarith⟩, ht.2.2⟩
      apply (measure_mono hsub).trans
      simp [Real.volume_Ico, abs_of_nonneg hpos]
    · have hsub : {t : ℝ | Int.floor (t+a) ≠ 0} ∩ Set.Ico 0 1 ⊆ Set.Ico 0 (-a) := by
        intro t ht
        have hn : ¬ (t+a ∈ Set.Ico (0 : ℝ) 1) := by
          exact fun h => ht.1 (Int.floor_eq_zero_iff.mpr h)
        have hupp : t+a < 1 := by linarith [ht.2.2]
        exact ⟨ht.2.1, by by_contra h; apply hn; exact ⟨by linarith, hupp⟩⟩
      apply (measure_mono hsub).trans
      simp [Real.volume_Ico, abs_of_nonpos hneg]
  · exact prob_le_one.trans (by simpa using ENNReal.ofReal_le_ofReal (le_of_not_gt ha))

/-- Borel--Cantelli proves that every integer-time floor sum has only finitely
many nonzero terms, simultaneously. This is the source's conull domain for F_k. -/
theorem ae_finiteFloorSupport {ι : Type*} [Countable ι]
    (θ : ι → ℝ) (hθ : Summable (fun i => |θ i|)) :
    ∀ᵐ x ∂Measure.infinitePi (fun _ : ι => unitIntervalMeasure), finiteFloorSupport θ x := by
  rw [show (fun x : ι → ℝ => finiteFloorSupport θ x) =
      (fun x => ∀ k : ℤ, (Function.support (coordinateFloor θ k x)).Finite) from rfl, ae_all_iff]
  intro k
  let μ := Measure.infinitePi (fun _ : ι => unitIntervalMeasure)
  let E (i : ι) : Set (ι → ℝ) := {x | coordinateFloor θ k x i ≠ 0}
  have hb (i : ι) : μ (E i) ≤ ENNReal.ofReal (|(k : ℝ)| * |θ i|) := by
    have hm : MeasurableSet {t : ℝ | Int.floor (t+(k : ℝ)*θ i) ≠ 0} :=
      (measurableSet_eq_fun (Int.measurable_floor.comp
        (measurable_id.add_const ((k : ℝ)*θ i))) measurable_const).compl
    have he := congrArg (fun ν : Measure ℝ => ν {t : ℝ | Int.floor (t+(k : ℝ)*θ i) ≠ 0})
      (Measure.infinitePi_map_eval (fun _ : ι => unitIntervalMeasure) i)
    rw [Measure.map_apply (measurable_pi_apply i) hm] at he
    change μ (E i) = _ at he
    rw [he, ← abs_mul]
    exact unitInterval_floor_exception _
  have hs : (∑' i, μ (E i)) ≠ ∞ := by
    apply ne_of_lt
    apply lt_of_le_of_lt (ENNReal.tsum_le_tsum hb)
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun i => mul_nonneg (abs_nonneg _) (abs_nonneg _))
      (hθ.mul_left |(k : ℝ)|)]
    exact ENNReal.ofReal_lt_top
  exact ae_finite_setOfPred_mem hs

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_CrossedProduct_Cocycle
attribute [-instance] _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped ENNReal
noncomputable section

theorem coordinateFloor_add {ι : Type*} (θ : ι → ℝ) (x : ι → ℝ) (k n : ℤ) (i : ι) :
    coordinateFloor θ (k+n) x i = coordinateFloor θ k x i +
      coordinateFloor θ n (coordinateRotate θ k x) i := by
  unfold coordinateFloor coordinateRotate
  have he : x i + ((k+n : ℤ) : ℝ)*θ i =
      (Int.fract (x i+(k : ℝ)*θ i)+(n : ℝ)*θ i) + (Int.floor (x i+(k : ℝ)*θ i) : ℝ) := by
    rw [Int.fract]
    push_cast
    ring
  rw [he, Int.floor_add_intCast]
  omega

theorem finiteFloorSupport_rotate {ι : Type*} (θ : ι → ℝ) {x : ι → ℝ}
    (hx : finiteFloorSupport θ x) (k : ℤ) : finiteFloorSupport θ (coordinateRotate θ k x) := by
  intro n
  apply ((hx (k+n)).union (hx k)).subset
  intro i hi
  by_contra hn
  simp only [Set.mem_union, Function.mem_support, not_or, not_not] at hn
  have he := coordinateFloor_add θ x k n i
  rw [hn.1, hn.2, zero_add] at he
  exact hi he.symm

theorem sourceLog_summable {ι : Type*} (θ c : ι → ℝ) {x : ι → ℝ}
    (hx : finiteFloorSupport θ x) (k : ℤ) :
    Summable (fun i => c i * (coordinateFloor θ k x i : ℝ)) := by
  apply summable_of_hasFiniteSupport
  apply (hx k).subset
  intro i hi
  simp only [Function.mem_support] at *
  intro hz
  apply hi
  simp [hz]

theorem sourceLog_add {ι : Type*} (θ c : ι → ℝ) {x : ι → ℝ}
    (hx : finiteFloorSupport θ x) (k n : ℤ) :
    sourceLog θ c (k+n) x = sourceLog θ c k x + sourceLog θ c n (coordinateRotate θ k x) := by
  unfold sourceLog
  simp_rw [coordinateFloor_add, Int.cast_add, mul_add]
  exact (sourceLog_summable θ c hx k).tsum_add
    (sourceLog_summable θ c (finiteFloorSupport_rotate θ hx k) n)

/-- The actual cocycle identity, proved on the conull domain supplied by
Borel--Cantelli. The rotation and sums are explicit. -/
theorem sourceCocycle_add {ι : Type*} (θ c : ι → ℝ) {x : ι → ℝ}
    (hx : finiteFloorSupport θ x) (k n : ℤ) :
    sourceCocycle θ c (k+n) x = sourceCocycle θ c n (coordinateRotate θ k x) * sourceCocycle θ c k x := by
  rw [sourceCocycle, sourceLog_add θ c hx, neg_add, Real.exp_add]
  exact mul_comm _ _

theorem sourceCocycle_zero {ι : Type*} (θ c : ι → ℝ) {x : ι → ℝ}
    (hx : ∀ i, x i ∈ Set.Ico 0 1) : sourceCocycle θ c 0 x = 1 := by
  have hzero (i : ι) : coordinateFloor θ 0 x i = 0 := by
    simpa [coordinateFloor] using Int.floor_eq_zero_iff.mpr (hx i)
  simp [sourceCocycle, sourceLog, hzero]

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_CrossedProduct_Attenuation
attribute [-instance] _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter Finset
open scoped ENNReal
noncomputable section

/-- The genuine finite-prefix bound for the source cocycle F_n. This is the
pointwise estimate needed before lifting the bound to powers of T. -/
theorem sourceCocycle_prefix_bound {ι : Type*} (θ c : ι → ℝ)
    (hθ : ∀ i, 0 ≤ θ i) (hc : ∀ i, 0 ≤ c i) {x : ι → ℝ}
    (hx : finiteFloorSupport θ x) (hx0 : ∀ i, 0 ≤ x i) (I : Finset ι) (n : ℕ) :
    sourceCocycle θ c n x ≤ Real.exp ((∑ i ∈ I, c i) - (n : ℝ)*(∑ i ∈ I, c i*θ i)) := by
  have hnon (i : ι) : 0 ≤ c i * (coordinateFloor θ n x i : ℝ) := by
    apply mul_nonneg (hc i)
    have hi : 0 ≤ coordinateFloor θ n x i :=
      Int.floor_nonneg.mpr (add_nonneg (hx0 i) (mul_nonneg (by exact_mod_cast Nat.zero_le n) (hθ i)))
    exact_mod_cast hi
  have hlo (i : ι) : c i * ((n : ℝ)*θ i-1) ≤ c i * (coordinateFloor θ n x i : ℝ) := by
    apply mul_le_mul_of_nonneg_left _ (hc i)
    have hh := Int.lt_floor_add_one (x i + (n : ℝ)*θ i)
    change (n : ℝ)*θ i-1 ≤ (Int.floor (x i+(n : ℝ)*θ i) : ℝ)
    linarith [hx0 i]
  have hsum := (Finset.sum_le_sum (fun i (_hi : i ∈ I) => hlo i)).trans
    ((sourceLog_summable θ c hx n).sum_le_tsum I (fun i _ => hnon i))
  have he : (∑ i ∈ I, c i * ((n : ℝ)*θ i-1)) =
      (n : ℝ)*(∑ i ∈ I, c i*θ i) - ∑ i ∈ I, c i := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [he] at hsum
  apply Real.exp_le_exp.mpr
  change _ ≤ sourceLog θ c n x at hsum
  linarith

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_CrossedProduct_Operator
attribute [-instance] _root_.OAI.FiniteFactor.sourceHilbert_separable _root_.OAI.FiniteFactor.sourceNormalFunctionalSpace_complete _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped ENNReal
noncomputable section

theorem sourceDiagonal_ne_zero {ι : Type*} (θ c : ι → ℝ) (z : (ι → ℝ) × ℤ) :
    sourceDiagonal θ c z ≠ 0 := by
  unfold sourceDiagonal
  exact_mod_cast (sourceCocycle_pos θ c 1 (coordinateRotate θ z.2 z.1)).ne'

theorem sourceMultiplication_apply_ae {ι : Type*} [Countable ι] (θ c : ι → ℝ)
    (hθ : ∀ i, 0 ≤ θ i) (hc : ∀ i, 0 ≤ c i) (f : SourceHilbert ι) :
    sourceMultiplication θ c hθ hc f =ᵐ[sourceMeasure ι] fun z => sourceDiagonal θ c z * f z := by
  have hh := (ContinuousLinearMap.mul ℂ ℂ).coeFn_holder
    ((sourceDiagonal_memLp θ c hθ hc).toLp (sourceDiagonal θ c)) f (r := 2)
  filter_upwards [hh, (sourceDiagonal_memLp θ c hθ hc).coeFn_toLp] with z hz hw
  simpa [sourceMultiplication, hw] using hz

theorem sourceMultiplication_injective {ι : Type*} [Countable ι] (θ c : ι → ℝ)
    (hθ : ∀ i, 0 ≤ θ i) (hc : ∀ i, 0 ≤ c i) :
    Function.Injective (sourceMultiplication θ c hθ hc) := by
  intro f g hfg
  apply Lp.ext
  filter_upwards [sourceMultiplication_apply_ae θ c hθ hc f,
    sourceMultiplication_apply_ae θ c hθ hc g] with z hf hg
  rw [hfg, hg] at hf
  exact mul_left_cancel₀ (sourceDiagonal_ne_zero θ c z) hf.symm

theorem sourceOperator_injective {ι : Type*} [Countable ι] (θ c : ι → ℝ)
    (hθ : ∀ i, 0 ≤ θ i) (hc : ∀ i, 0 ≤ c i) :
    Function.Injective (sourceOperator θ c hθ hc) := by
  intro f g h
  apply sourceMultiplication_injective θ c hθ hc
  exact (Lp.compMeasurePreservingₗᵢ ℂ sourceShiftIndex
    (sourceShiftIndex_preserving ι)).injective h

theorem sourceMultiplication_norm_le {ι : Type*} [Countable ι] (θ c : ι → ℝ)
    (hθ : ∀ i, 0 ≤ θ i) (hc : ∀ i, 0 ≤ c i) (f : SourceHilbert ι) :
    ‖sourceMultiplication θ c hθ hc f‖ ≤ ‖f‖ := by
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [sourceMultiplication_apply_ae θ c hθ hc f] with z hz
  rw [hz, norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (sourceDiagonal_norm_le θ c hθ hc z)

theorem sourceOperator_norm_le_one {ι : Type*} [Countable ι] (θ c : ι → ℝ)
    (hθ : ∀ i, 0 ≤ θ i) (hc : ∀ i, 0 ≤ c i) : ‖sourceOperator θ c hθ hc‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro f
  change ‖Lp.compMeasurePreserving sourceShiftIndex (sourceShiftIndex_preserving ι)
    (sourceMultiplication θ c hθ hc f)‖ ≤ 1 * ‖f‖
  rw [Lp.norm_compMeasurePreserving, one_mul]
  exact sourceMultiplication_norm_le θ c hθ hc f

/-- This constructs a nonzero bounded T, independently of any candidate projection. -/
theorem sourceOperator_ne_zero {ι : Type*} [Countable ι] (θ c : ι → ℝ)
    (hθ : ∀ i, 0 ≤ θ i) (hc : ∀ i, 0 ≤ c i) : sourceOperator θ c hθ hc ≠ 0 := by
  let A : Set ((ι → ℝ) × ℤ) := Set.univ ×ˢ {0}
  have hA : MeasurableSet A := MeasurableSet.univ.prod (measurableSet_singleton 0)
  have hmass : sourceMeasure ι A = 1 := by simp [A, sourceMeasure, Measure.prod_prod]
  let e : SourceHilbert ι := indicatorConstLp 2 hA (by rw [hmass]; exact ENNReal.one_ne_top) 1
  have hen : ‖e‖ = 1 := by
    rw [norm_indicatorConstLp (by norm_num) (by norm_num)]
    simp [measureReal_def, hmass]
  have he : e ≠ 0 := by intro he; rw [he, norm_zero] at hen; norm_num at hen
  intro hT
  apply he
  apply sourceOperator_injective θ c hθ hc
  simp [hT]

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_Quasinilpotence
attribute [-instance] _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open Filter
open scoped Topology

/-- Taking nth roots of the finite-prefix exponential bound, for n>0. -/
theorem root_le_prefix_exponential {a A B : ℝ} (ha : 0 ≤ a) {n : ℕ} (hn : 0 < n)
    (hbound : a ≤ Real.exp (B - (n : ℝ)*A)) :
    a ^ (1 / (n : ℝ)) ≤ Real.exp (B / (n : ℝ) - A) := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hn)
  calc
    a ^ (1 / (n : ℝ)) ≤ Real.exp (B - (n : ℝ)*A) ^ (1 / (n : ℝ)) :=
      Real.rpow_le_rpow ha hbound (by positivity)
    _ = Real.exp ((B - (n : ℝ)*A) * (1 / (n : ℝ))) := (Real.exp_mul _ _).symm
    _ = Real.exp (B / (n : ℝ) - A) := by
      congr 1
      field_simp

/-- The prefix is fixed before taking n→∞. Its additive loss B(q) may grow
arbitrarily with q; no uniform estimate on that loss is required. -/
theorem root_tendsto_zero_of_prefix_bounds (a A B : ℕ → ℝ)
    (ha : ∀ n, 0 ≤ a n) (hA : Tendsto A atTop atTop)
    (hbound : ∀ (q n : ℕ), 0 < n → a n ≤ Real.exp (B q - (n : ℝ)*A q)) :
    Tendsto (fun n => a n ^ (1 / (n : ℝ))) atTop (𝓝 0) := by
  apply tendsto_order.2
  constructor
  · intro l hl
    exact Eventually.of_forall fun n => hl.trans_le (Real.rpow_nonneg (ha n) _)
  · intro u hu
    have hdecay : Tendsto (fun q => Real.exp (-A q)) atTop (𝓝 0) :=
      Real.tendsto_exp_neg_atTop_nhds_zero.comp hA
    obtain ⟨q, hq⟩ := (hdecay.eventually (gt_mem_nhds hu)).exists
    have hlim : Tendsto (fun n : ℕ => Real.exp (B q / (n : ℝ) - A q))
        atTop (𝓝 (Real.exp (-A q))) := by
      simpa only [zero_sub, Function.comp_def] using
        (Real.continuous_exp.tendsto (0 - A q)).comp
          ((tendsto_const_div_atTop_nhds_zero_nat (B q)).sub_const (A q))
    filter_upwards [hlim.eventually (gt_mem_nhds hq), eventually_gt_atTop (0 : ℕ)] with n hn hn0
    exact (root_le_prefix_exponential (ha n) hn0 (hbound q n hn0)).trans_lt hn

/-- Operator form of the analytic reduction, using precisely the norm-root
limit in MainTarget. This theorem does not assume spectral-radius theory. -/
theorem norm_quasinilpotent_of_prefix_bounds {R : Type*} [NormedRing R]
    (T : R) (A B : ℕ → ℝ) (hA : Tendsto A atTop atTop)
    (hbound : ∀ (q n : ℕ), 0 < n → ‖T^n‖ ≤ Real.exp (B q - (n : ℝ)*A q)) :
    Tendsto (fun n : ℕ => ‖T^n‖ ^ (1 / (n : ℝ))) atTop (𝓝 0) :=
  root_tendsto_zero_of_prefix_bounds (fun n => ‖T^n‖) A B (fun n => norm_nonneg (T^n)) hA hbound

end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_CrossedProduct_Powers
attribute [-instance] _root_.OAI.FiniteFactor.sourceHilbert_separable _root_.OAI.FiniteFactor.sourceNormalFunctionalSpace_complete _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped ENNReal Topology
noncomputable section

theorem sourceShiftNIndex_preserving (ι : Type*) (n : ℕ) :
    MeasurePreserving (sourceShiftNIndex (ι := ι) n) (sourceMeasure ι) (sourceMeasure ι) := by
  induction n with
  | zero =>
    have he : sourceShiftNIndex (ι := ι) 0 = id := by funext z; simp [sourceShiftNIndex]
    rw [he]
    exact MeasurePreserving.id _
  | succ n ih =>
    convert ih.comp (sourceShiftIndex_preserving ι) using 1
    funext z
    simp [sourceShiftNIndex, sourceShiftIndex, sub_sub, add_comm]

theorem sourceOperator_apply_ae {ι : Type*} [Countable ι] (θ c : ι → ℝ)
    (hθ : ∀ i, 0 ≤ θ i) (hc : ∀ i, 0 ≤ c i) (f : SourceHilbert ι) :
    sourceOperator θ c hθ hc f =ᵐ[sourceMeasure ι] fun z =>
      sourceDiagonal θ c (sourceShiftIndex z) * f (sourceShiftIndex z) := by
  have he := Lp.coeFn_compMeasurePreserving (sourceMultiplication θ c hθ hc f)
    (sourceShiftIndex_preserving ι)
  have hm := (sourceShiftIndex_preserving ι).quasiMeasurePreserving.ae
    (sourceMultiplication_apply_ae θ c hθ hc f)
  exact he.trans hm

/-- The actual powers of the constructed weighted shift, on the conull
finite-floor-support domain. No power formula is assumed. -/
theorem sourceOperator_pow_apply_ae {ι : Type*} [Countable ι] (θ c : ι → ℝ)
    (hθ : ∀ i, 0 ≤ θ i) (hc : ∀ i, 0 ≤ c i)
    (hs : Summable (fun i => |θ i|)) (n : ℕ) (f : SourceHilbert ι) :
    (sourceOperator θ c hθ hc ^ n) f =ᵐ[sourceMeasure ι] fun z =>
      (sourceCocycle θ c n (coordinateRotate θ (z.2-(n : ℤ)) z.1) : ℂ) *
        f (sourceShiftNIndex n z) := by
  induction n with
  | zero =>
    apply Eventually.of_forall
    intro z
    have hzero : sourceCocycle θ c 0 (coordinateRotate θ z.2 z.1) = 1 :=
      sourceCocycle_zero θ c (fun i => ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩)
    simp [sourceShiftNIndex, hzero]
  | succ n ih =>
    have hfs : ∀ᵐ z ∂sourceMeasure ι, finiteFloorSupport θ z.1 :=
      Measure.quasiMeasurePreserving_fst.ae (ae_finiteFloorSupport θ hs)
    have hih := (sourceShiftIndex_preserving ι).quasiMeasurePreserving.ae ih
    have he := sourceOperator_apply_ae θ c hθ hc ((sourceOperator θ c hθ hc ^ n) f)
    have hpow : (sourceOperator θ c hθ hc ^ (n+1)) f =
        sourceOperator θ c hθ hc ((sourceOperator θ c hθ hc ^ n) f) := by
      rw [pow_succ']
      rfl
    rw [hpow]
    filter_upwards [he, hih, hfs] with z hz hi hx
    rw [hz, hi]
    have hrot : coordinateRotate θ (n : ℤ) (coordinateRotate θ (z.2-((n+1 : ℕ) : ℤ)) z.1) =
        coordinateRotate θ (z.2-1) z.1 := by
      rw [coordinateRotate_add]
      congr 1
      push_cast
      omega
    have hcoe := sourceCocycle_add θ c (finiteFloorSupport_rotate θ hx (z.2-((n+1 : ℕ) : ℤ)))
      (n : ℤ) 1
    rw [hrot] at hcoe
    have hind : sourceShiftNIndex n (sourceShiftIndex z) = sourceShiftNIndex (n+1) z := by
      simp [sourceShiftNIndex, sourceShiftIndex, sub_sub, add_comm]
    have hidx : (sourceShiftIndex z).2-(n : ℤ) = z.2-((n+1 : ℕ) : ℤ) := by
      simp [sourceShiftIndex]
      omega
    simp only [sourceDiagonal, sourceShiftIndex] at *
    rw [show z.2-1-(n : ℤ) = z.2-((n+1 : ℕ) : ℤ) from hidx, hind]
    simp only [Nat.cast_add, Nat.cast_one] at hcoe ⊢
    rw [hcoe, Complex.ofReal_mul]
    exact (mul_assoc _ _ _).symm

/-- The source's finite-prefix operator bound, now for the constructed T. -/
theorem sourceOperator_pow_norm_prefix_bound {ι : Type*} [Countable ι] (θ c : ι → ℝ)
    (hθ : ∀ i, 0 ≤ θ i) (hc : ∀ i, 0 ≤ c i)
    (hs : Summable (fun i => |θ i|)) (I : Finset ι) (n : ℕ) :
    ‖sourceOperator θ c hθ hc ^ n‖ ≤
      Real.exp ((∑ i ∈ I, c i) - (n : ℝ)*(∑ i ∈ I, c i*θ i)) := by
  apply ContinuousLinearMap.opNorm_le_bound _ (Real.exp_pos _).le
  intro f
  let g := Lp.compMeasurePreserving (sourceShiftNIndex n) (sourceShiftNIndex_preserving ι n) f
  have hg := Lp.coeFn_compMeasurePreserving f (sourceShiftNIndex_preserving ι n)
  have hfs : ∀ᵐ z ∂sourceMeasure ι, finiteFloorSupport θ z.1 :=
    Measure.quasiMeasurePreserving_fst.ae (ae_finiteFloorSupport θ hs)
  have hle : ‖(sourceOperator θ c hθ hc ^ n) f‖ ≤
      Real.exp ((∑ i ∈ I, c i) - (n : ℝ)*(∑ i ∈ I, c i*θ i)) * ‖g‖ := by
    apply Lp.norm_le_mul_norm_of_ae_le_mul
    filter_upwards [sourceOperator_pow_apply_ae θ c hθ hc hs n f, hg, hfs] with z hz hg hx
    rw [hz, hg, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg (sourceCocycle_pos _ _ _ _).le]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    exact sourceCocycle_prefix_bound θ c hθ hc
      (finiteFloorSupport_rotate θ hx _) (fun i => Int.fract_nonneg _) I n
  simpa [g, Lp.norm_compMeasurePreserving] using hle

/-- Norm quasinilpotence of this concrete operator follows from divergence of
its coordinate weighted-angle sums, not from any assumed operator property. -/
theorem sourceOperator_norm_quasinilpotent {ι : Type*} [Countable ι] (θ c : ι → ℝ)
    (hθ : ∀ i, 0 ≤ θ i) (hc : ∀ i, 0 ≤ c i)
    (hs : Summable (fun i => |θ i|)) (I : ℕ → Finset ι)
    (hdiv : Tendsto (fun q => ∑ i ∈ I q, c i*θ i) atTop atTop) :
    Tendsto (fun n : ℕ => ‖sourceOperator θ c hθ hc ^ n‖ ^ (1/(n : ℝ))) atTop (𝓝 0) :=
  norm_quasinilpotent_of_prefix_bounds _ _ _ hdiv
    (fun q n _ => sourceOperator_pow_norm_prefix_bound θ c hθ hc hs (I q) n)

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_CrossedProduct_StageOperator
attribute [-instance] _root_.OAI.FiniteFactor.sourceAngleMarginal_atomless _root_.OAI.FiniteFactor.sourceBiasedRealMeasure_probability _root_.OAI.FiniteFactor.sourceFiniteReferenceKernel_markov _root_.OAI.FiniteFactor.sourceHilbert_separable _root_.OAI.FiniteFactor.sourceNormalFunctionalSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedGroup _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedSpace _root_.OAI.FiniteFactor.sourceResamplingKernel_markov _root_.OAI.FiniteFactor.sourceSamplingLambda_finite _root_.OAI.FiniteFactor.sourceSamplingSummand_finite _root_.OAI.FiniteFactor.sourceSamplingTorus_borel _root_.OAI.FiniteFactor.sourceSamplingTorus_compact _root_.OAI.FiniteFactor.sourceSamplingTrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingUntrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingWeightedMeasure_finite _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter Finset
open scoped Topology ENNReal
noncomputable section

theorem sourceCutoff_ge_pow (s : ℕ) : 2^s ≤ (sourceStageState s).K := by
  induction s with
  | zero => exact (sourceStageState 0).K_ge
  | succ s ih =>
    rw [pow_succ]
    have hh : 2^s*2 ≤ 2*(sourceStageState s).K := by simpa [mul_comm] using Nat.mul_le_mul_left 2 ih
    exact hh.trans (sourceStage_cutoff_growth s).le

theorem sourceCutoff_reciprocal_summable : Summable (fun s => 1/((sourceStageState s).K : ℝ)) := by
  apply (summable_geometric_of_lt_one (r := (1/2 : ℝ)) (by norm_num) (by norm_num)).of_nonneg_of_le
  · intro s; positivity
  · intro s
    have hpow : (2 : ℝ)^s ≤ (sourceStageState s).K := by exact_mod_cast sourceCutoff_ge_pow s
    have hh := one_div_le_one_div_of_le (by positivity : (0 : ℝ) < (2 : ℝ)^s) hpow
    simpa [one_div_pow] using hh

/-- The source interval bounds imply actual angle summability for every
realization, with the recursively constructed sizes and cutoffs. -/
theorem SourceAngles.summable {θ : SourceCoordinate → ℝ} (hθ : SourceAngles θ) :
    Summable (fun i => |θ i|) := by
  have hs : Summable θ := by
    rw [summable_sigma_of_nonneg hθ.nonneg]
    refine ⟨fun s => (hasSum_fintype (fun t => θ ⟨s,t⟩)).summable, ?_⟩
    apply (sourceCutoff_reciprocal_summable.mul_left 2).of_nonneg_of_le
    · intro s; exact tsum_nonneg (fun t => hθ.nonneg ⟨s,t⟩)
    · intro s
      rw [tsum_fintype]
      have hh := Finset.sum_le_sum (fun (i : Fin (sourceBlockSize s)) (_ : i ∈ Finset.univ) => (hθ ⟨s,i⟩).2)
      have he : (∑ _i : Fin (sourceBlockSize s), 2/((sourceBlockSize s : ℝ)*(sourceStageState s).K)) =
          2*(1/((sourceStageState s).K : ℝ)) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        field_simp [(sourceBlockSize_pos s).ne', (sourceCutoff_pos s).ne']
      exact hh.trans_eq he
  simpa only [abs_of_nonneg (hθ.nonneg _)] using hs

/-- Each source block contributes at least one to the weighted-angle sum,
using C_s >= K_s^2 and the exact lower endpoint 1/(m_s*K_s). -/
theorem SourceAngles.block_weight_lower {θ : SourceCoordinate → ℝ} (hθ : SourceAngles θ) (s : ℕ) :
    1 ≤ ∑ t : Fin (sourceBlockSize s), sourceLogWeight ⟨s,t⟩*θ ⟨s,t⟩ := by
  have hc : ((sourceStageState s).K : ℝ)^2 ≤ (sourceStage s).C := le_max_right _ _
  have hK : (1 : ℝ) ≤ (sourceStageState s).K := by exact_mod_cast (sourceStageState s).K_ge
  have hlo : 1 ≤ (sourceStage s).C/((sourceStageState s).K : ℝ) := by
    apply (le_div_iff₀ (sourceCutoff_pos s)).mpr
    nlinarith
  have hh : (∑ t : Fin (sourceBlockSize s), sourceLogWeight ⟨s,t⟩ *
      (1/((sourceBlockSize s : ℝ)*(sourceStageState s).K))) ≤
      ∑ t : Fin (sourceBlockSize s), sourceLogWeight ⟨s,t⟩*θ ⟨s,t⟩ :=
    Finset.sum_le_sum (fun (t : Fin (sourceBlockSize s)) (_ : t ∈ Finset.univ) =>
    mul_le_mul_of_nonneg_left (hθ ⟨s,t⟩).1 (sourceLogWeight_nonneg ⟨s,t⟩))
  have he : (∑ t : Fin (sourceBlockSize s), sourceLogWeight ⟨s,t⟩ *
      (1/((sourceBlockSize s : ℝ)*(sourceStageState s).K))) =
      (sourceStage s).C/((sourceStageState s).K : ℝ) := by
    simp only [sourceLogWeight, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp [(sourceBlockSize_pos s).ne', (sourceCutoff_pos s).ne']
  rw [he] at hh
  exact hlo.trans hh

theorem SourceAngles.weighted_prefix_diverges {θ : SourceCoordinate → ℝ} (hθ : SourceAngles θ) :
    Tendsto (fun q => ∑ i ∈ CouplingParameters.blockPrefix sourceBlockSize q, sourceLogWeight i*θ i)
      atTop atTop := by
  apply tendsto_atTop_mono (f := fun q : ℕ => (q : ℝ)) _ tendsto_natCast_atTop_atTop
  intro q
  rw [CouplingParameters.blockPrefix, Finset.sum_sigma]
  calc
    (q : ℝ) = ∑ _s ∈ Finset.range q, (1 : ℝ) := by simp
    _ ≤ _ := Finset.sum_le_sum (fun s _ => hθ.block_weight_lower s)

/-- The recursively staged concrete source operator is nonzero, injective,
bounded by one, and norm-quasinilpotent for every admissible angle realization.
No factor, ergodicity, sampling, or invariant-projection conclusion is asserted. -/
theorem staged_sourceOperator_properties (θ : SourceCoordinate → ℝ) (hθ : SourceAngles θ) :
    let T := sourceOperator θ sourceLogWeight hθ.nonneg sourceLogWeight_nonneg
    T ≠ 0 ∧ Function.Injective T ∧ ‖T‖ ≤ 1 ∧
      Tendsto (fun n : ℕ => ‖T^n‖^(1/(n : ℝ))) atTop (𝓝 0) := by
  refine ⟨sourceOperator_ne_zero _ _ _ _, sourceOperator_injective _ _ _ _,
    sourceOperator_norm_le_one _ _ _ _, ?_⟩
  exact sourceOperator_norm_quasinilpotent _ _ _ _ hθ.summable
    (CouplingParameters.blockPrefix sourceBlockSize) hθ.weighted_prefix_diverges

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_CrossedProduct_AngleLaw
attribute [-instance] _root_.OAI.FiniteFactor.sourceBiasedRealMeasure_probability _root_.OAI.FiniteFactor.sourceFiniteReferenceKernel_markov _root_.OAI.FiniteFactor.sourceHilbert_separable _root_.OAI.FiniteFactor.sourceNormalFunctionalSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedGroup _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedSpace _root_.OAI.FiniteFactor.sourceResamplingKernel_markov _root_.OAI.FiniteFactor.sourceSamplingLambda_finite _root_.OAI.FiniteFactor.sourceSamplingSummand_finite _root_.OAI.FiniteFactor.sourceSamplingTorus_borel _root_.OAI.FiniteFactor.sourceSamplingTorus_compact _root_.OAI.FiniteFactor.sourceSamplingTrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingUntrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingWeightedMeasure_finite _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology
noncomputable section

theorem sourceAngleUnit_pos (i : SourceCoordinate) : 0 < sourceAngleUnit i :=
  one_div_pos.mpr (mul_pos (sourceBlockSize_pos i.1) (sourceCutoff_pos i.1))

theorem sourceAngleInterval_volume (i : SourceCoordinate) :
    volume (sourceAngleInterval i) = ENNReal.ofReal (sourceAngleUnit i) := by
  simp [sourceAngleInterval, Real.volume_Icc, show 2 * sourceAngleUnit i - sourceAngleUnit i = sourceAngleUnit i by ring]

instance sourceAngleMarginal_probability (i : SourceCoordinate) :
    IsProbabilityMeasure (sourceAngleMarginal i) := by
  unfold sourceAngleMarginal
  apply cond_isProbabilityMeasure_of_finite
  · rw [sourceAngleInterval_volume]; exact (ENNReal.ofReal_pos.mpr (sourceAngleUnit_pos i)).ne'
  · rw [sourceAngleInterval_volume]; exact ENNReal.ofReal_ne_top

instance sourceAngleLaw_probability : IsProbabilityMeasure sourceAngleLaw := by
  unfold sourceAngleLaw
  infer_instance

theorem sourceAngleLaw_coordinate (i : SourceCoordinate) :
    sourceAngleLaw.map (fun θ => θ i) = sourceAngleMarginal i :=
  Measure.infinitePi_map_eval _ _

theorem sourceAngleLaw_independent :
    iIndepFun (fun i (θ : SourceCoordinate → ℝ) => θ i) sourceAngleLaw :=
  iIndepFun_infinitePi (X := fun _ (x : ℝ) => x) (fun _ => measurable_id)

theorem sourceAngleLaw_cylinder (I : Finset SourceCoordinate)
    (S : SourceCoordinate → Set ℝ) (hS : ∀ i ∈ I, MeasurableSet (S i)) :
    sourceAngleLaw (Set.pi (I : Set SourceCoordinate) S) =
      ∏ i ∈ I, sourceAngleMarginal i (S i) :=
  Measure.infinitePi_pi _ hS

theorem sourceAngleMarginal_ae (i : SourceCoordinate) :
    ∀ᵐ t ∂sourceAngleMarginal i, t ∈ sourceAngleInterval i := by
  exact ae_cond_mem measurableSet_Icc

/-- All interval constraints hold simultaneously, not just coordinatewise. -/
theorem sourceAngleLaw_admissible : ∀ᵐ θ ∂sourceAngleLaw, SourceAngles θ := by
  have h (i : SourceCoordinate) : ∀ᵐ θ ∂sourceAngleLaw, θ i ∈ sourceAngleInterval i := by
    have hh := sourceAngleMarginal_ae i
    rw [← sourceAngleLaw_coordinate i] at hh
    exact (ae_map_iff (measurable_pi_apply i).aemeasurable measurableSet_Icc).mp hh
  filter_upwards [ae_all_iff.mpr h] with θ hθ
  intro i
  change (1 : ℝ) / ((sourceBlockSize i.1 : ℝ) * (sourceStageState i.1).K) ≤ θ i ∧
    θ i ≤ 2 / ((sourceBlockSize i.1 : ℝ) * (sourceStageState i.1).K)
  simpa [sourceAngleInterval, sourceAngleUnit, div_eq_mul_inv] using hθ i

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_CrossedProduct_AngleRelations
attribute [-instance] _root_.OAI.FiniteFactor.sourceBiasedRealMeasure_probability _root_.OAI.FiniteFactor.sourceFiniteReferenceKernel_markov _root_.OAI.FiniteFactor.sourceHilbert_separable _root_.OAI.FiniteFactor.sourceNormalFunctionalSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedGroup _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedSpace _root_.OAI.FiniteFactor.sourceResamplingKernel_markov _root_.OAI.FiniteFactor.sourceSamplingLambda_finite _root_.OAI.FiniteFactor.sourceSamplingSummand_finite _root_.OAI.FiniteFactor.sourceSamplingTorus_borel _root_.OAI.FiniteFactor.sourceSamplingTorus_compact _root_.OAI.FiniteFactor.sourceSamplingTrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingUntrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingWeightedMeasure_finite _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal
noncomputable section

/-- Independent real variables cannot satisfy a prescribed affine equation
when the second variable has no atoms. -/
theorem independent_sum_ne {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {f g : Ω → ℝ} (hf : Measurable f) (hg : Measurable g)
    (hfg : IndepFun f g μ) (hg0 : ∀ r : ℝ, μ {ω | g ω = r} = 0) (c : ℝ) :
    ∀ᵐ ω ∂μ, f ω + g ω ≠ c := by
  have hp : MeasurableSet {z : ℝ × ℝ | z.1+z.2 ≠ c} :=
    (measurableSet_eq_fun (measurable_fst.add measurable_snd) measurable_const).compl
  have ha : ∀ᵐ z ∂(μ.map f).prod (μ.map g), z.1+z.2 ≠ c := by
    apply (Measure.ae_prod_iff_ae_ae hp).mpr
    apply Eventually.of_forall
    intro x
    have he : (μ.map g) {y : ℝ | x+y = c} = 0 := by
      have hs : {y : ℝ | x+y = c} = {c-x} := by ext y; simp; constructor <;> intro h <;> linarith
      rw [hs, Measure.map_apply hg (measurableSet_singleton _)]
      exact hg0 _
    exact measure_eq_zero_iff_ae_notMem.mp he
  rw [← hfg.map_prod_eq_prod_map_map hf.aemeasurable hg.aemeasurable] at ha
  exact (ae_map_iff (hf.prodMk hg).aemeasurable hp).mp ha

theorem sourceAngleLaw_scaled_atomless (i : SourceCoordinate) (a : ℝ) (ha : a ≠ 0) (r : ℝ) :
    sourceAngleLaw {θ | a*θ i = r} = 0 := by
  have hs : {θ : SourceCoordinate → ℝ | a*θ i = r} =
      (fun θ : SourceCoordinate → ℝ => θ i) ⁻¹' {r/a} := by
    ext θ
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · intro h; apply (eq_div_iff ha).mpr; nlinarith [h]
    · intro h; rw [h, mul_div_cancel₀ _ ha]
  rw [hs, ← Measure.map_apply (measurable_pi_apply i) (measurableSet_singleton _),
    sourceAngleLaw_coordinate]
  exact measure_singleton _

/-- Every nontrivial finitely supported integer relation has probability zero. -/
theorem sourceAngleLaw_relation_ne (v : SourceCoordinate →₀ ℤ) (hv : v ≠ 0) (c : ℤ) :
    ∀ᵐ θ ∂sourceAngleLaw, v.sum (fun i n => (n : ℝ)*θ i) ≠ (c : ℝ) := by
  classical
  obtain ⟨i, hi⟩ := Finsupp.support_nonempty_iff.mpr hv
  have hvi : (v i : ℝ) ≠ 0 := by exact_mod_cast Finsupp.mem_support_iff.mp hi
  let f (j : SourceCoordinate) (θ : SourceCoordinate → ℝ) : ℝ := (v j : ℝ)*θ j
  have hm (j : SourceCoordinate) : Measurable (f j) := measurable_const.mul (measurable_pi_apply j)
  have hind : iIndepFun f sourceAngleLaw :=
    sourceAngleLaw_independent.comp (fun j (t : ℝ) => (v j : ℝ)*t)
      (fun _ => measurable_const.mul measurable_id)
  have hh := independent_sum_ne (Finset.measurable_sum (v.support.erase i) (fun j _ => hm j)) (hm i)
    (by
      convert hind.indepFun_finsetSum_of_notMem hm (Finset.notMem_erase i v.support) using 1
      funext θ
      simp only [Finset.sum_apply])
    (sourceAngleLaw_scaled_atomless i (v i : ℝ) hvi) (c : ℝ)
  filter_upwards [hh] with θ hθ
  simpa only [Finsupp.sum, ← Finset.sum_erase_add _ _ hi] using hθ

theorem sourceAngleLaw_rationalIndependent :
    ∀ᵐ θ ∂sourceAngleLaw, SourceRationalIndependent θ := by
  have h (v : SourceCoordinate →₀ ℤ) (c : ℤ) :
      ∀ᵐ θ ∂sourceAngleLaw, v.sum (fun i n => (n : ℝ)*θ i) = (c : ℝ) → v = 0 ∧ c = 0 := by
    by_cases hv : v = 0
    · subst v
      apply Eventually.of_forall
      intro θ hθ
      simp only [Finsupp.sum_zero_index] at hθ
      exact ⟨rfl, by exact_mod_cast hθ.symm⟩
    · filter_upwards [sourceAngleLaw_relation_ne v hv c] with θ hθ he
      exact (hθ he).elim
  exact ae_all_iff.mpr (fun v => ae_all_iff.mpr (h v))

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_CrossedProduct_GeneratedAlgebra
attribute [-instance] _root_.OAI.FiniteFactor.sourceAngleLaw_probability _root_.OAI.FiniteFactor.sourceAngleMarginal_atomless _root_.OAI.FiniteFactor.sourceAngleMarginal_probability _root_.OAI.FiniteFactor.sourceBiasedRealMeasure_probability _root_.OAI.FiniteFactor.sourceFiniteReferenceKernel_markov _root_.OAI.FiniteFactor.sourceHilbert_separable _root_.OAI.FiniteFactor.sourceNormalFunctionalSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedGroup _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedSpace _root_.OAI.FiniteFactor.sourceResamplingKernel_markov _root_.OAI.FiniteFactor.sourceSamplingLambda_finite _root_.OAI.FiniteFactor.sourceSamplingSummand_finite _root_.OAI.FiniteFactor.sourceSamplingTorus_borel _root_.OAI.FiniteFactor.sourceSamplingTorus_compact _root_.OAI.FiniteFactor.sourceSamplingTrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingUntrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingWeightedMeasure_finite _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped ENNReal Pointwise
noncomputable section

theorem mem_sourceGeneratedVonNeumann {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (S : Set (H →L[ℂ] H)) {T : H →L[ℂ] H} (hT : T ∈ S) :
    T ∈ sourceGeneratedVonNeumann S := by
  have he : (StarSubalgebra.centralizer ℂ (StarSubalgebra.centralizer ℂ S)).carrier =
      Set.centralizer (Set.centralizer (S ∪ star S)) :=
    StarSubalgebra.coe_centralizer_centralizer ℂ S
  change T ∈ (StarSubalgebra.centralizer ℂ (StarSubalgebra.centralizer ℂ S)).carrier
  rw [he]
  exact Set.subset_centralizer_centralizer (Or.inl hT)

theorem sourcePi_mem (θ : SourceCoordinate → ℝ) (g : SourceBaseFunction) :
    sourcePi θ g ∈ sourceAlgebra θ :=
  mem_sourceGeneratedVonNeumann _ (Or.inr ⟨g,rfl⟩)

theorem sourceShift_mem (θ : SourceCoordinate → ℝ) :
    sourceShift SourceCoordinate ∈ sourceAlgebra θ :=
  mem_sourceGeneratedVonNeumann _ (Or.inl rfl)

theorem sourceMultiplication_eq_pi (θ : SourceCoordinate → ℝ) (hθ : SourceAngles θ) :
    sourceMultiplication θ sourceLogWeight hθ.nonneg sourceLogWeight_nonneg =
      sourcePi θ (sourceWeightBase θ hθ) := rfl

/-- Actual membership of the already verified staged operator in its generated
von Neumann algebra, without an assumed operator-membership hypothesis. -/
theorem staged_sourceOperator_mem (θ : SourceCoordinate → ℝ) (hθ : SourceAngles θ) :
    sourceOperator θ sourceLogWeight hθ.nonneg sourceLogWeight_nonneg ∈ sourceAlgebra θ := by
  change sourceShift SourceCoordinate * sourceMultiplication θ sourceLogWeight hθ.nonneg sourceLogWeight_nonneg ∈ _
  rw [sourceMultiplication_eq_pi θ hθ]
  exact mul_mem (sourceShift_mem θ) (sourcePi_mem θ (sourceWeightBase θ hθ))

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_CrossedProduct_VacuumFunctional
attribute [-instance] _root_.OAI.FiniteFactor.sourceAngleLaw_probability _root_.OAI.FiniteFactor.sourceAngleMarginal_atomless _root_.OAI.FiniteFactor.sourceAngleMarginal_probability _root_.OAI.FiniteFactor.sourceBiasedRealMeasure_probability _root_.OAI.FiniteFactor.sourceFiniteReferenceKernel_markov _root_.OAI.FiniteFactor.sourceHilbert_separable _root_.OAI.FiniteFactor.sourceNormalFunctionalSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedGroup _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedSpace _root_.OAI.FiniteFactor.sourceResamplingKernel_markov _root_.OAI.FiniteFactor.sourceSamplingLambda_finite _root_.OAI.FiniteFactor.sourceSamplingSummand_finite _root_.OAI.FiniteFactor.sourceSamplingTorus_borel _root_.OAI.FiniteFactor.sourceSamplingTorus_compact _root_.OAI.FiniteFactor.sourceSamplingTrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingUntrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingWeightedMeasure_finite _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped ENNReal
noncomputable section

theorem sourceVacuumFunctional_one : sourceVacuumFunctional 1 = 1 := by
  simp [sourceVacuumFunctional,inner_self_eq_norm_sq_to_K,sourceVacuum_norm]

theorem sourceVacuumFunctional_square
    (T : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate) :
    sourceVacuumFunctional (star T*T) = inner ℂ (T sourceVacuum) (T sourceVacuum) :=
  ContinuousLinearMap.adjoint_inner_right T sourceVacuum (T sourceVacuum)

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_CrossedProduct_VacuumSeparating
attribute [-instance] _root_.OAI.FiniteFactor.sourceAngleLaw_probability _root_.OAI.FiniteFactor.sourceAngleMarginal_atomless _root_.OAI.FiniteFactor.sourceAngleMarginal_probability _root_.OAI.FiniteFactor.sourceBiasedRealMeasure_probability _root_.OAI.FiniteFactor.sourceFiniteReferenceKernel_markov _root_.OAI.FiniteFactor.sourceHilbert_separable _root_.OAI.FiniteFactor.sourceNormalFunctionalSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedGroup _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedSpace _root_.OAI.FiniteFactor.sourceResamplingKernel_markov _root_.OAI.FiniteFactor.sourceSamplingLambda_finite _root_.OAI.FiniteFactor.sourceSamplingSummand_finite _root_.OAI.FiniteFactor.sourceSamplingTorus_borel _root_.OAI.FiniteFactor.sourceSamplingTorus_compact _root_.OAI.FiniteFactor.sourceSamplingTrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingUntrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingWeightedMeasure_finite _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory
noncomputable section

/-- Faithfulness on squares of the actual normal vacuum functional. -/
theorem sourceVacuumFunctional_square_eq_zero_iff (θ : SourceCoordinate → ℝ)
    {H : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate}
    (hH : H ∈ sourceAlgebra θ) :
    sourceVacuumFunctional (star H * H) = 0 ↔ H = 0 := by
  constructor
  · intro hz
    rw [sourceVacuumFunctional_square] at hz
    exact sourceVacuum_separating θ hH (inner_self_eq_zero.mp hz)
  · rintro rfl
    simp [sourceVacuumFunctional]

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_CrossedProduct_FiniteAlgebra
attribute [-instance] _root_.OAI.FiniteFactor.sourceAngleLaw_probability _root_.OAI.FiniteFactor.sourceAngleMarginal_atomless _root_.OAI.FiniteFactor.sourceAngleMarginal_probability _root_.OAI.FiniteFactor.sourceBiasedRealMeasure_probability _root_.OAI.FiniteFactor.sourceFiniteReferenceKernel_markov _root_.OAI.FiniteFactor.sourceHilbert_separable _root_.OAI.FiniteFactor.sourceNormalFunctionalSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedGroup _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedSpace _root_.OAI.FiniteFactor.sourceResamplingKernel_markov _root_.OAI.FiniteFactor.sourceSamplingLambda_finite _root_.OAI.FiniteFactor.sourceSamplingSummand_finite _root_.OAI.FiniteFactor.sourceSamplingTorus_borel _root_.OAI.FiniteFactor.sourceSamplingTorus_compact _root_.OAI.FiniteFactor.sourceSamplingTrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingUntrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingWeightedMeasure_finite _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
noncomputable section

/-- The actual generated source algebra is finite: every isometry is unitary. -/
theorem sourceAlgebra_finite (θ : SourceCoordinate → ℝ) : IsFiniteAlgebra (sourceAlgebra θ) := by
  intro v hv hiso
  let p : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate := 1 - v * star v
  have hp : p ∈ sourceAlgebra θ := sub_mem (one_mem _) (mul_mem hv (star_mem hv))
  have hw : (v * star v) * (v * star v) = v * star v := by
    calc
      _ = v * (star v * v) * star v := by simp only [mul_assoc]
      _ = v * star v := by rw [hiso]; simp
  have hps : star p = p := by
    change star (1 - v * star v) = 1 - v * star v
    rw [star_sub, star_one, star_mul, star_star]
  have hpp : star p * p = p := by
    rw [hps]
    change (1 - v * star v) * (1 - v * star v) = 1 - v * star v
    rw [sub_mul, one_mul, mul_sub, mul_one, hw]
    abel
  have ht : sourceVacuumFunctional (v * star v) = 1 := by
    rw [sourceVacuumFunctional_tracial θ hv (star_mem hv), hiso, sourceVacuumFunctional_one]
  have hz : sourceVacuumFunctional (star p * p) = 0 := by
    rw [hpp]
    change inner ℂ sourceVacuum ((1 - v * star v) sourceVacuum) = 0
    rw [sub_apply, inner_sub_right]
    change sourceVacuumFunctional 1 - sourceVacuumFunctional (v * star v) = 0
    rw [sourceVacuumFunctional_one, ht, sub_self]
  have hp0 := (sourceVacuumFunctional_square_eq_zero_iff θ hp).mp hz
  exact (sub_eq_zero.mp hp0).symm

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_CrossedProduct_FreeRotation
attribute [-instance] _root_.OAI.FiniteFactor.sourceBiasedRealMeasure_probability _root_.OAI.FiniteFactor.sourceFiniteReferenceKernel_markov _root_.OAI.FiniteFactor.sourceHilbert_separable _root_.OAI.FiniteFactor.sourceNormalFunctionalSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedGroup _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedSpace _root_.OAI.FiniteFactor.sourceResamplingKernel_markov _root_.OAI.FiniteFactor.sourceSamplingLambda_finite _root_.OAI.FiniteFactor.sourceSamplingSummand_finite _root_.OAI.FiniteFactor.sourceSamplingTorus_borel _root_.OAI.FiniteFactor.sourceSamplingTorus_compact _root_.OAI.FiniteFactor.sourceSamplingTrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingUntrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingWeightedMeasure_finite _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped Topology
noncomputable section

theorem SourceRationalIndependent.mul_ne_integer {θ : SourceCoordinate → ℝ}
    (hθ : SourceRationalIndependent θ) (i : SourceCoordinate) (k : ℤ) (hk : k ≠ 0) (c : ℤ) :
    (k : ℝ)*θ i ≠ (c : ℝ) := by
  intro he
  have hh := (hθ (Finsupp.single i k) c (by simpa using he)).1
  have hz := congrArg (fun v : SourceCoordinate →₀ ℤ => v i) hh
  exact hk (by simpa using hz)

/-- Every nonzero integer rotation has no fixed point, using one source
coordinate. This is pointwise freeness, not merely an almost-everywhere claim. -/
theorem SourceRationalIndependent.rotation_free {θ : SourceCoordinate → ℝ}
    (hθ : SourceRationalIndependent θ) (k : ℤ) (hk : k ≠ 0) (x : SourceCoordinate → ℝ) :
    coordinateRotate θ k x ≠ x := by
  intro he
  have hh := congrFun he sourceFirstCoordinate
  change Int.fract (x sourceFirstCoordinate+(k : ℝ)*θ sourceFirstCoordinate) =
    x sourceFirstCoordinate at hh
  rw [Int.fract] at hh
  apply hθ.mul_ne_integer sourceFirstCoordinate k hk
    (Int.floor (x sourceFirstCoordinate+(k : ℝ)*θ sourceFirstCoordinate))
  linarith

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_PeriodizedUniform
attribute [-instance] _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory ProbabilityTheory
open scoped ENNReal
noncomputable section

theorem sourceFract_measurable : Measurable (Int.fract : ℝ → ℝ) := by
  have hh := sourceCircleRepresentative_measurable.comp sourceCircle_mk_preserving.measurable
  simpa only [Function.comp_def, sourceCircleRepresentative_coe] using hh

/-- Every translated interval of length one maps to the same representative
Haar measure under fractional part. -/
theorem fract_unit_interval (a : ℝ) :
    (volume.restrict (Set.Ioc a (a+1))).map Int.fract = unitIntervalMeasure := by
  have hh := sourceCircleRepresentative_preserving.comp (AddCircle.measurePreserving_mk 1 a)
  have he : sourceCircleRepresentative ∘ ((↑) : ℝ → AddCircle (1 : ℝ)) = Int.fract := by
    funext x
    exact sourceCircleRepresentative_coe x
  simpa only [he] using hh.map_eq

theorem fract_integer_interval (a : ℝ) (n : ℕ) :
    (volume.restrict (Set.Ioc a (a+n))).map Int.fract = (n : ℝ≥0∞) • unitIntervalMeasure := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hu : Set.Ioc a (a+((n+1 : ℕ) : ℝ)) =
        Set.Ioc a (a+n) ∪ Set.Ioc (a+n) (a+n+1) := by
      rw [Set.Ioc_union_Ioc_eq_Ioc (by have := Nat.cast_nonneg (α := ℝ) n; linarith) (by linarith)]
      congr 1
      push_cast
      ring
    rw [hu, Measure.restrict_union (Set.Ioc_disjoint_Ioc_of_le le_rfl) measurableSet_Ioc,
      Measure.map_add, ih, fract_unit_interval]
    · simp [add_smul]
    · exact sourceFract_measurable

/-- Periodizing normalized interval measure has density at most 1+1/length.
The bound is expressed as domination of measures on every measurable set. -/
theorem fract_interval_domination (a b : ℝ) (hab : a < b) :
    (cond volume (Set.Ioc a b)).map Int.fract ≤
      ENNReal.ofReal (1+1/(b-a)) • unitIntervalMeasure := by
  let n : ℕ := Nat.ceil (b-a)
  have hsub : Set.Ioc a b ⊆ Set.Ioc a (a+n) := by
    apply Set.Ioc_subset_Ioc le_rfl
    have hh : b-a ≤ (n : ℝ) := Nat.le_ceil _
    linarith
  have hle : (volume.restrict (Set.Ioc a b)).map Int.fract ≤
      (n : ℝ≥0∞) • unitIntervalMeasure := by
    rw [← fract_integer_interval a n]
    exact Measure.map_mono (Measure.restrict_mono hsub le_rfl) sourceFract_measurable
  have hscalar : (ENNReal.ofReal (b-a))⁻¹ * (n : ℝ≥0∞) ≤
      ENNReal.ofReal (1+1/(b-a)) := by
    have hpos : 0 < b-a := sub_pos.mpr hab
    have hn : (n : ℝ) < b-a+1 := Nat.ceil_lt_add_one hpos.le
    have hreal : (b-a)⁻¹ * (n : ℝ) ≤ 1+1/(b-a) := by
      apply (mul_le_mul_of_nonneg_left hn.le (inv_nonneg.mpr hpos.le)).trans_eq
      field_simp
    rw [← ENNReal.ofReal_inv_of_pos hpos, ← ENNReal.ofReal_natCast,
      ← ENNReal.ofReal_mul (inv_nonneg.mpr hpos.le)]
    exact ENNReal.ofReal_le_ofReal hreal
  unfold ProbabilityTheory.cond
  rw [Measure.map_smul, Real.volume_Ioc]
  calc
    _ ≤ (ENNReal.ofReal (b-a))⁻¹ • ((n : ℝ≥0∞) • unitIntervalMeasure) := by gcongr
    _ = ((ENNReal.ofReal (b-a))⁻¹ * (n : ℝ≥0∞)) • unitIntervalMeasure := smul_smul _ _ _
    _ ≤ _ := by gcongr

/-- Positive scaling carries normalized interval measure to the normalized
scaled interval; this identifies the actual phase law before periodization. -/
theorem cond_interval_mul_pos (a b c : ℝ) (hab : a < b) (hc : 0 < c) :
    (cond volume (Set.Ioc a b)).map (fun t => c*t) =
      cond volume (Set.Ioc (c*a) (c*b)) := by
  have hp : (fun t : ℝ => c*t) ⁻¹' Set.Ioc (c*a) (c*b) = Set.Ioc a b := by
    ext t
    simp only [Set.mem_preimage, Set.mem_Ioc, mul_lt_mul_iff_right₀ hc, mul_le_mul_iff_right₀ hc]
  have hlen : 0 < b-a := sub_pos.mpr hab
  have hclen : 0 < c*b-c*a := by nlinarith
  unfold ProbabilityTheory.cond
  rw [Measure.map_smul, Real.volume_Ioc, Real.volume_Ioc, ← hp,
    ← Measure.restrict_map (f := fun t : ℝ => c*t) (by fun_prop) measurableSet_Ioc,
    Real.map_volume_mul_left hc.ne', Measure.restrict_smul, smul_smul]
  congr 1
  rw [abs_of_pos (inv_pos.mpr hc), ← ENNReal.ofReal_inv_of_pos hlen,
    ← ENNReal.ofReal_mul (inv_nonneg.mpr hlen.le), ← ENNReal.ofReal_inv_of_pos hclen]
  congr 1
  field_simp

theorem cond_closed_interval_eq (a b : ℝ) :
    cond volume (Set.Icc a b) = cond volume (Set.Ioc a b) := by
  unfold ProbabilityTheory.cond
  rw [Real.volume_Icc, Real.volume_Ioc, ← restrict_Ioc_eq_restrict_Icc]

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_CrossedProduct_PhaseMarginal
attribute [-instance] _root_.OAI.FiniteFactor.sourceBiasedRealMeasure_probability _root_.OAI.FiniteFactor.sourceFiniteReferenceKernel_markov _root_.OAI.FiniteFactor.sourceHilbert_separable _root_.OAI.FiniteFactor.sourceNormalFunctionalSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedGroup _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedSpace _root_.OAI.FiniteFactor.sourceResamplingKernel_markov _root_.OAI.FiniteFactor.sourceSamplingLambda_finite _root_.OAI.FiniteFactor.sourceSamplingSummand_finite _root_.OAI.FiniteFactor.sourceSamplingTorus_borel _root_.OAI.FiniteFactor.sourceSamplingTorus_compact _root_.OAI.FiniteFactor.sourceSamplingTrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingUntrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingWeightedMeasure_finite _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory ProbabilityTheory
open scoped ENNReal
noncomputable section

theorem unitInterval_middle_compl (b : ℝ) (hb : 0 ≤ b) :
    unitIntervalMeasure (Set.Icc b (1-b))ᶜ ≤ ENNReal.ofReal (2*b) := by
  rw [unitIntervalMeasure, Measure.restrict_apply measurableSet_Icc.compl]
  have hsub : (Set.Icc b (1-b))ᶜ ∩ Set.Ico (0 : ℝ) 1 ⊆
      Set.Ico 0 b ∪ Set.Ioc (1-b) 1 := by
    intro x hx
    by_cases hxb : x < b
    · exact Or.inl ⟨hx.2.1,hxb⟩
    · exact Or.inr ⟨by by_contra hh; exact hx.1 ⟨le_of_not_gt hxb, le_of_not_gt hh⟩, hx.2.2.le⟩
  calc
    _ ≤ volume (Set.Ico 0 b ∪ Set.Ioc (1-b) 1) := measure_mono hsub
    _ ≤ volume (Set.Ico (0 : ℝ) b) + volume (Set.Ioc (1-b) 1) := measure_union_le _ _
    _ = ENNReal.ofReal (2*b) := by
      rw [Real.volume_Ico, Real.volume_Ioc]
      simp only [sub_zero, sub_sub_cancel]
      rw [← ENNReal.ofReal_add hb hb]
      congr 1
      ring

/-- The actual source-angle phase law has density at most five in the
second phase range. This is domination on all Borel sets. -/
theorem sourceAngle_positive_phase_domination (i : SourceCoordinate) (c : ℝ)
    (hc : 0 < c) (hlen : 1/4 ≤ c*sourceAngleUnit i) :
    (sourceAngleMarginal i).map (fun t => Int.fract (c*t)) ≤
      (5 : ℝ≥0∞) • unitIntervalMeasure := by
  have ha := sourceAngleUnit_pos i
  have he : (sourceAngleMarginal i).map (fun t => Int.fract (c*t)) =
      (cond volume (Set.Ioc (c*sourceAngleUnit i) (c*(2*sourceAngleUnit i)))).map Int.fract := by
    rw [← cond_interval_mul_pos (sourceAngleUnit i) (2*sourceAngleUnit i) c (by linarith) hc,
      Measure.map_map sourceFract_measurable (by fun_prop)]
    rw [sourceAngleMarginal, sourceAngleInterval, cond_closed_interval_eq]
    rfl
  rw [he]
  have hpos : c*sourceAngleUnit i < c*(2*sourceAngleUnit i) := by nlinarith
  apply (fract_interval_domination _ _ hpos).trans
  have hh : 1+1/(c*(2*sourceAngleUnit i)-c*sourceAngleUnit i) ≤ (5 : ℝ) := by
    have heq : c*(2*sourceAngleUnit i)-c*sourceAngleUnit i = c*sourceAngleUnit i := by ring
    rw [heq]
    have hh := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1/4) hlen
    have hh' : 1/(c*sourceAngleUnit i) ≤ 4 := by
      simpa [one_div, mul_inv_rev] using hh
    linarith
  have hscalar : ENNReal.ofReal (1+1/(c*(2*sourceAngleUnit i)-c*sourceAngleUnit i)) ≤ 5 := by
    exact_mod_cast ENNReal.ofReal_le_ofReal hh
  gcongr

/-- Reflection preserves the symmetric phase eligibility interval, including
integer phases at the cut. -/
theorem fract_neg_middle_iff (b t : ℝ) :
    Int.fract (-t) ∈ Set.Icc b (1-b) ↔ Int.fract t ∈ Set.Icc b (1-b) := by
  by_cases ht : Int.fract t = 0
  · rw [Int.fract_neg_eq_zero.mpr ht, ht]
  · rw [Int.fract_neg ht]
    constructor <;> intro h <;> constructor <;> linarith [h.1,h.2]

theorem threshold_middle_iff (b t : ℝ) :
    1-Int.fract t ∈ Set.Icc b (1-b) ↔ Int.fract t ∈ Set.Icc b (1-b) := by
  constructor <;> intro h <;> constructor <;> linarith [h.1,h.2]

/-- Proposition phases' one-coordinate miss bound, valid for both signs and
for every coordinate in the actual source interval. -/
theorem sourceAngle_phase_miss (i : SourceCoordinate) (k : ℤ) (b : ℝ) (hb : 0 ≤ b)
    (hk : ((sourceBlockSize i.1 : ℝ)*(sourceStageState i.1).K)/4 ≤ |(k : ℝ)|) :
    sourceAngleMarginal i {t | 1-Int.fract ((k : ℝ)*t) ∉ Set.Icc b (1-b)} ≤
      ENNReal.ofReal (10*b) := by
  have hN := mul_pos (sourceBlockSize_pos i.1) (sourceCutoff_pos i.1)
  have hkpos : 0 < |(k : ℝ)| := lt_of_lt_of_le (by positivity) hk
  have hlen : 1/4 ≤ |(k : ℝ)| *sourceAngleUnit i := by
    unfold sourceAngleUnit
    rw [mul_one_div]
    apply (le_div_iff₀ hN).mpr
    nlinarith [hk]
  have he : {t : ℝ | 1-Int.fract ((k : ℝ)*t) ∉ Set.Icc b (1-b)} =
      (fun t : ℝ => Int.fract (|(k : ℝ)| *t)) ⁻¹' (Set.Icc b (1-b))ᶜ := by
    ext t
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_compl_iff, threshold_middle_iff]
    rcases le_total 0 (k : ℝ) with hpos | hneg
    · rw [abs_of_nonneg hpos]
    · rw [abs_of_nonpos hneg, neg_mul, fract_neg_middle_iff]
  rw [he, ← Measure.map_apply (f := fun t : ℝ => Int.fract (|(k : ℝ)| *t))
    (by exact sourceFract_measurable.comp (by fun_prop)) measurableSet_Icc.compl]
  calc
    _ ≤ ((5 : ℝ≥0∞) • unitIntervalMeasure) (Set.Icc b (1-b))ᶜ :=
      sourceAngle_positive_phase_domination i |(k : ℝ)| hkpos hlen _
    _ = 5 * unitIntervalMeasure (Set.Icc b (1-b))ᶜ := rfl
    _ ≤ 5 * ENNReal.ofReal (2*b) := by
      have hh := unitInterval_middle_compl b hb
      gcongr
    _ = ENNReal.ofReal (10*b) := by
      rw [show (5 : ℝ≥0∞) = ENNReal.ofReal 5 by norm_num, ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 5)]
      congr 1
      ring

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_IndependentCount
attribute [-instance] _root_.OAI.FiniteFactor.sourceBiasedRealMeasure_probability _root_.OAI.FiniteFactor.sourceFiniteReferenceKernel_markov _root_.OAI.FiniteFactor.sourceHilbert_separable _root_.OAI.FiniteFactor.sourceNormalFunctionalSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedGroup _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedSpace _root_.OAI.FiniteFactor.sourceResamplingKernel_markov _root_.OAI.FiniteFactor.sourceSamplingLambda_finite _root_.OAI.FiniteFactor.sourceSamplingSummand_finite _root_.OAI.FiniteFactor.sourceSamplingTorus_borel _root_.OAI.FiniteFactor.sourceSamplingTorus_compact _root_.OAI.FiniteFactor.sourceSamplingTrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingUntrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingWeightedMeasure_finite _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Finset
open scoped ENNReal Classical
noncomputable section

/-- Independence and the union bound, retaining the exact natural exponent.
This lemma uses the actual source angle law. -/
theorem coordinateMissEvent_bound (I : Finset SourceCoordinate) (q : ℕ)
    (S : SourceCoordinate → Set ℝ) (hS : ∀ i, MeasurableSet (S i))
    (b : ℝ≥0∞) (hb : ∀ i ∈ I, sourceAngleMarginal i (S i) ≤ b) :
    sourceAngleLaw (coordinateMissEvent I q S) ≤ (2 : ℝ≥0∞)^I.card * b^q := by
  classical
  have hJ (J : Finset SourceCoordinate) (hJ : J ∈ I.powersetCard q) :
      sourceAngleLaw (Set.pi (J : Set SourceCoordinate) S) ≤ b^q := by
    rcases Finset.mem_powersetCard.mp hJ with ⟨hsub, hcard⟩
    rw [sourceAngleLaw_cylinder J S (fun i _ => hS i)]
    calc
      _ ≤ ∏ _i ∈ J, b := Finset.prod_le_prod' (fun i hi => hb i (hsub hi))
      _ = b^q := by simp [hcard]
  have hc : (I.powersetCard q).card ≤ 2^I.card := by
    rw [← Finset.card_powerset]
    exact Finset.card_le_card (fun J hJ => Finset.mem_powerset.mpr (Finset.mem_powersetCard.mp hJ).1)
  calc
    _ ≤ ∑ J ∈ I.powersetCard q, sourceAngleLaw (Set.pi (J : Set SourceCoordinate) S) :=
      measure_biUnion_finset_le _ _
    _ ≤ ∑ _J ∈ I.powersetCard q, b^q := Finset.sum_le_sum hJ
    _ = ((I.powersetCard q).card : ℝ≥0∞)*b^q := by simp [nsmul_eq_mul]
    _ ≤ (2 : ℝ≥0∞)^I.card*b^q := by
      have hc' : ((I.powersetCard q).card : ℝ≥0∞) ≤ (2 : ℝ≥0∞)^I.card := by exact_mod_cast hc
      gcongr

/-- Any realization with at least q misses lies in the union event. -/
theorem mem_coordinateMissEvent_of_card (I : Finset SourceCoordinate) (q : ℕ)
    (S : SourceCoordinate → Set ℝ) (θ : SourceCoordinate → ℝ)
    (h : q ≤ (I.filter (fun i => θ i ∈ S i)).card) : θ ∈ coordinateMissEvent I q S := by
  classical
  obtain ⟨J, hJ, hcard⟩ := Finset.exists_subset_card_eq h
  apply Set.mem_iUnion.mpr
  refine ⟨J, Set.mem_iUnion.mpr ⟨Finset.mem_powersetCard.mpr ⟨?_, hcard⟩, ?_⟩⟩
  · exact hJ.trans (Finset.filter_subset _ _)
  · intro i hi
    exact (Finset.mem_filter.mp (hJ hi)).2

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_CrossedProduct_PhaseCount
attribute [-instance] _root_.OAI.FiniteFactor.sourceBiasedRealMeasure_probability _root_.OAI.FiniteFactor.sourceFiniteReferenceKernel_markov _root_.OAI.FiniteFactor.sourceHilbert_separable _root_.OAI.FiniteFactor.sourceNormalFunctionalSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedGroup _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedSpace _root_.OAI.FiniteFactor.sourceResamplingKernel_markov _root_.OAI.FiniteFactor.sourceSamplingLambda_finite _root_.OAI.FiniteFactor.sourceSamplingSummand_finite _root_.OAI.FiniteFactor.sourceSamplingTorus_borel _root_.OAI.FiniteFactor.sourceSamplingTorus_compact _root_.OAI.FiniteFactor.sourceSamplingTrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingUntrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingWeightedMeasure_finite _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Finset
open scoped ENNReal Classical
noncomputable section

theorem sourcePhaseMissSet_measurable (s : ℕ) (k : ℤ) : MeasurableSet (sourcePhaseMissSet s k) := by
  exact measurableSet_Icc.compl.preimage
    (measurable_const.sub (sourceFract_measurable.comp (by fun_prop)))

theorem sourceFewPhases_subset_misses (s : ℕ) (k : ℤ) :
    sourceFewPhases s k ⊆ coordinateMissEvent (sourceBlockCoordinates s) (sourceMissCount s)
      (fun _ => sourcePhaseMissSet s k) := by
  intro θ hθ
  apply mem_coordinateMissEvent_of_card
  apply Nat.ceil_le.mpr
  have hc := Finset.card_filter_add_card_filter_not (s := sourceBlockCoordinates s)
    (p := fun i => θ i ∈ sourcePhaseMissSet s k)
  have hcR : (((sourceBlockCoordinates s).filter (fun i => θ i ∈ sourcePhaseMissSet s k)).card : ℝ) +
      (((sourceBlockCoordinates s).filter (fun i => θ i ∉ sourcePhaseMissSet s k)).card : ℝ) =
      (sourceBlockSize s : ℝ) := by
        rw [sourceBlockCoordinates_card] at hc
        exact_mod_cast hc
  change (((sourceBlockCoordinates s).filter (fun i => θ i ∉ sourcePhaseMissSet s k)).card : ℝ) <
      (sourceBlockSize s : ℝ)/20 at hθ
  nlinarith

/-- The fixed-power failure probability in Proposition phases, for the actual
angle product measure. The ceiling records the exact finite counting step. -/
theorem sourceFewPhases_probability (s : ℕ) (k : ℤ)
    (hk : ((sourceBlockSize s : ℝ)*(sourceStageState s).K)/4 ≤ |(k : ℝ)|) :
    sourceAngleLaw (sourceFewPhases s k) ≤
      (2 : ℝ≥0∞)^sourceBlockSize s *
        (ENNReal.ofReal (10*sourceWidth s 1))^sourceMissCount s := by
  apply (measure_mono (sourceFewPhases_subset_misses s k)).trans
  simpa only [sourceBlockCoordinates_card] using
    coordinateMissEvent_bound (sourceBlockCoordinates s) (sourceMissCount s)
      (fun _ => sourcePhaseMissSet s k) (fun _ => sourcePhaseMissSet_measurable s k)
      (ENNReal.ofReal (10*sourceWidth s 1)) (by
        intro i hi
        have his := mem_sourceBlockCoordinates hi
        apply sourceAngle_phase_miss i k (sourceWidth s 1)
        · exact (by positivity : (0 : ℝ) ≤ 1/(sourceBlockSize s : ℝ)).trans (sourceWidth_bounds s 1).1
        · simpa only [his] using hk)

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_CrossedProduct_PhaseDecay
attribute [-instance] _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped ENNReal Topology
noncomputable section

theorem phaseFailureMajorant_le (m q : ℕ) (hm : (100 : ℝ) ≤ m)
    (hroot : (10 : ℝ) ≤ (m : ℝ)^(1/100 : ℝ))
    (hq : (19/20 : ℝ)*(m : ℝ) ≤ q) :
    (m : ℝ)^((4/5 : ℝ)*(m : ℝ))*2^m*
      (10*(m : ℝ)^(-19/20 : ℝ))^q ≤ (m : ℝ)^(-2 : ℝ) := by
  have hm0 : (0 : ℝ) < m := by linarith
  have hm1 : (1 : ℝ) ≤ m := by linarith
  have hb : 10*(m : ℝ)^(-19/20 : ℝ) ≤ (m : ℝ)^(-47/50 : ℝ) := by
    calc
      _ ≤ (m : ℝ)^(1/100 : ℝ)*(m : ℝ)^(-19/20 : ℝ) := by gcongr
      _ = _ := by rw [← Real.rpow_add hm0]; norm_num
  have htwo : (2 : ℝ)^m ≤ ((m : ℝ)^(1/100 : ℝ))^m := by
    gcongr
    linarith
  calc
    _ ≤ (m : ℝ)^((4/5 : ℝ)*(m : ℝ))*((m : ℝ)^(1/100 : ℝ))^m*
        ((m : ℝ)^(-47/50 : ℝ))^q := by gcongr
    _ = (m : ℝ)^((4/5 : ℝ)*(m : ℝ)+(1/100 : ℝ)*(m : ℝ)+(-47/50 : ℝ)*(q : ℝ)) := by
      rw [← Real.rpow_mul_natCast hm0.le, ← Real.rpow_mul_natCast hm0.le,
        ← Real.rpow_add hm0, ← Real.rpow_add hm0]
    _ ≤ (m : ℝ)^(-2 : ℝ) := by
      apply Real.rpow_le_rpow_of_exponent_le hm1
      nlinarith

theorem sourcePhaseFailureMajorant_eventually :
    ∀ᶠ s in atTop, sourcePhaseFailureMajorant s ≤ (sourceBlockSize s : ℝ)^(-2 : ℝ) := by
  have ht : Tendsto (fun s => (sourceBlockSize s : ℝ)^(1/100 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num)).comp
      (tendsto_natCast_atTop_atTop.comp sourceBlockSize_tendsto)
  filter_upwards [ht.eventually (eventually_ge_atTop 10)] with s hs
  exact phaseFailureMajorant_le (sourceBlockSize s) (sourceMissCount s)
    (by exact_mod_cast (sourceStage s).m_ge_100) hs (Nat.le_ceil _)

/-- The reciprocal-square majorant is summable from m_s >= 2^(s+1). -/
theorem sourceBlockSize_inverseSquare_summable :
    Summable (fun s => (sourceBlockSize s : ℝ)^(-2 : ℝ)) := by
  apply (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1/2) (by norm_num)).of_nonneg_of_le
  · intro s; positivity
  · intro s
    have hm1 : (1 : ℝ) ≤ sourceBlockSize s := by exact_mod_cast (show 1 ≤ sourceBlockSize s by change 1 ≤ (sourceStage s).m; have := (sourceStage s).m_ge_100; omega)
    have hp : (2 : ℝ)^s ≤ sourceBlockSize s := by
      have hh := (sourceStage s).m_ge_pow
      have hh' : 2^s ≤ sourceBlockSize s := by change 2^(s+1) ≤ sourceBlockSize s at hh; have := Nat.le_mul_of_pos_right (2^s) (by omega : 0 < 2); rw [pow_succ] at hh; omega
      exact_mod_cast hh'
    calc
      _ ≤ (sourceBlockSize s : ℝ)^(-1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hm1 (by norm_num)
      _ = 1/(sourceBlockSize s : ℝ) := by rw [Real.rpow_neg_one, one_div]
      _ ≤ 1/(2 : ℝ)^s := one_div_le_one_div_of_le (by positivity) hp
      _ = (1/2 : ℝ)^s := by rw [one_div_pow]

theorem sourcePhaseFailureMajorant_summable : Summable sourcePhaseFailureMajorant := by
  apply sourceBlockSize_inverseSquare_summable.of_norm_bounded_eventually_nat
  filter_upwards [sourcePhaseFailureMajorant_eventually] with s hs
  rwa [Real.norm_eq_abs, abs_of_nonneg (by unfold sourcePhaseFailureMajorant sourceWidth; dsimp; positivity)]

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_OrbitSampling_Powers
attribute [-instance] _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open Finset Filter
open scoped Topology
noncomputable section

theorem sourceSamplingPowers_spec (s : ℕ) (hs : 200000 ≤ sourceBlockSize s) :
    (∀ n ∈ sourceSamplingPowers s,
      samplingQ (sourceBlockSize s)/2 ≤ (n : ℝ) ∧
      (n : ℝ) ≤ samplingQ (sourceBlockSize s) ∧ 0 < n) ∧
    (sourceBlockSize s : ℝ)^((69/100 : ℝ)*(sourceBlockSize s : ℝ)) ≤
      ((sourceSamplingPowers s).card : ℝ) ∧
    ((sourceSamplingPowers s : Finset ℤ) : Set ℤ).Pairwise (fun n n' =>
      ¬SamplingConflict (samplingH (sourceBlockSize s))
        (samplingR (sourceBlockSize s) (sourceStageState s).K) n n') := by
  unfold sourceSamplingPowers
  rw [dite_eq_left hs]
  exact Classical.choose_spec (exists_source_sampling_powers _ _ hs (sourceStage s).m_ge_K)

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_Sampling_Weights
attribute [-instance] _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory
noncomputable section

theorem samplingWeight_measurable (triangular : Bool) (h α : ℝ) :
    Measurable (fun p : ℝ × ℝ => samplingWeight triangular h α p.1 p.2) := by
  cases triangular <;> unfold samplingWeight samplingDistance <;> simp only [Bool.false_eq_true,ite_false,ite_true]
  · apply Measurable.ite _ (by fun_prop) measurable_const
    exact (measurableSet_le measurable_const (measurable_fst.min (measurable_const.sub measurable_fst))).inter
      ((measurableSet_lt measurable_const measurable_snd).inter
        (measurableSet_lt measurable_snd (measurable_const.mul (measurable_fst.min (measurable_const.sub measurable_fst)))))
  · exact Measurable.ite ((measurableSet_lt measurable_const measurable_snd).inter
      (measurableSet_lt measurable_snd (measurable_const.sub measurable_fst))) measurable_const measurable_const

theorem samplingWeight_support (triangular : Bool) (h α s t : ℝ)
    (_hh : 0 < h) (hh1 : h < 1) (hα : 0 < α)
    (_hs : s ∈ Set.Ico (0 : ℝ) 1) (hw : samplingWeight triangular h α s t ≠ 0) :
    0 < t ∧ t < 1-s := by
  cases triangular
  · unfold samplingWeight at hw
    simp only [Bool.false_eq_true,ite_false] at hw
    split_ifs at hw with hc
    · have hd : 0 < samplingDistance s := hα.trans_le hc.1
      have hd1 : samplingDistance s ≤ 1-s := min_le_right _ _
      exact ⟨hc.2.1, hc.2.2.trans_le ((by simpa using
        (mul_lt_mul_of_pos_right hh1 hd).le : h * samplingDistance s ≤ samplingDistance s).trans hd1)⟩
    · exact False.elim (hw rfl)
  · simpa only [samplingWeight,ite_true,ne_eq,ite_eq_right_iff,one_ne_zero,imp_false,not_not] using hw

/-- The positive weight already orders each prefix coordinate strictly,
with no wrap of the orbit endpoint. -/
theorem samplingWeight_orders (triangular : Bool) (h α s t : ℝ)
    (hh : 0 < h) (hh1 : h < 1) (hα : 0 < α)
    (hs : s ∈ Set.Ico (0 : ℝ) 1) (hw : samplingWeight triangular h α s t ≠ 0) :
    Int.fract (s+t) = s+t ∧ s < Int.fract (s+t) := by
  have ht := samplingWeight_support triangular h α s t hh hh1 hα hs hw
  have he := Int.fract_eq_self.mpr (show s+t ∈ Set.Ico (0 : ℝ) 1 from ⟨by linarith [hs.1],by linarith⟩)
  exact ⟨he,by rw [he]; linarith⟩

/-- Exact first marginal of either untested one-coordinate weight. -/
theorem samplingWeight_first_integral (triangular : Bool) (h α s : ℝ)
    (hh : 0 < h) (hh1 : h < 1) (hα : 0 < α) (hs : s ∈ Set.Ico (0 : ℝ) 1) :
    (∫ t, samplingWeight triangular h α s t ∂unitIntervalMeasure) =
      if triangular then 1-s else if α ≤ samplingDistance s then 1 else 0 := by
  have hvol (L : ℝ) (hL : 0 ≤ L) (hL1 : L ≤ 1) :
      unitIntervalMeasure (Set.Ioo (0 : ℝ) L) = ENNReal.ofReal L := by
    unfold unitIntervalMeasure
    rw [Measure.restrict_apply measurableSet_Ioo,Set.inter_eq_left.mpr (by
      intro t ht; exact ⟨ht.1.le,ht.2.trans_le hL1⟩),Real.volume_Ioo,sub_zero]
  cases triangular
  · simp only [Bool.false_eq_true,ite_false]
    by_cases hc : α ≤ samplingDistance s
    · have hd : 0 < samplingDistance s := hα.trans_le hc
      have hL : 0 < h*samplingDistance s := mul_pos hh hd
      have hL1 : h*samplingDistance s ≤ 1 := by
        have := min_le_right s (1-s)
        change samplingDistance s ≤ 1-s at this
        nlinarith [hs.1]
      have he : samplingWeight false h α s =
          (Set.Ioo 0 (h*samplingDistance s)).indicator (fun _ => 1/(h*samplingDistance s)) := by
        funext t
        simp [samplingWeight,hc,Set.indicator,Set.mem_Ioo]
      rw [he,integral_indicator measurableSet_Ioo]
      simp [hc,hvol (h*samplingDistance s) hL.le hL1,ENNReal.toReal_ofReal hL.le,measureReal_def]
      field_simp
    · have he : samplingWeight false h α s = fun _ => 0 := by funext t; simp [samplingWeight,hc]
      simp [he,hc]
  · simp only [ite_true]
    have he : samplingWeight true h α s = (Set.Ioo 0 (1-s)).indicator (fun _ => (1 : ℝ)) := by
      funext t
      simp [samplingWeight,Set.indicator,Set.mem_Ioo]
    rw [he,integral_indicator measurableSet_Ioo]
    simp [hvol (1-s) (by linarith [hs.2]) (by linarith [hs.1]),ENNReal.toReal_ofReal,show 0 ≤ 1-s by linarith [hs.2],measureReal_def]

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_OrbitSampling_Weights
attribute [-instance] _root_.OAI.FiniteFactor.sourceBiasedRealMeasure_probability _root_.OAI.FiniteFactor.sourceFiniteReferenceKernel_markov _root_.OAI.FiniteFactor.sourceHilbert_separable _root_.OAI.FiniteFactor.sourceNormalFunctionalSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedGroup _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedSpace _root_.OAI.FiniteFactor.sourceResamplingKernel_markov _root_.OAI.FiniteFactor.sourceSamplingLambda_finite _root_.OAI.FiniteFactor.sourceSamplingSummand_finite _root_.OAI.FiniteFactor.sourceSamplingTorus_borel _root_.OAI.FiniteFactor.sourceSamplingTorus_compact _root_.OAI.FiniteFactor.sourceSamplingTrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingUntrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingWeightedMeasure_finite _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Finset Filter
open scoped ENNReal
noncomputable section

theorem sourceSamplingWeight_measurable (I : Finset SourceCoordinate) (s : ℕ)
    (θ : SourceCoordinate → ℝ) (n : ℤ) : Measurable (sourceSamplingWeight I s θ n) := by
  apply Finset.measurable_prod
  intro i hi
  have hp : Measurable (fun x : SourceCoordinate → ℝ => (x i, Int.fract ((n : ℝ)*θ i))) :=
    (measurable_pi_apply i).prodMk measurable_const
  exact (samplingWeight_measurable (decide (i ∈ I)) (sourceSamplingWidth s) (sourceSamplingCutoff s)).comp hp

/-- Every nonzero summand orders all prefix coordinates under the actual rotation. -/
theorem sourceSamplingWeight_orders_prefix (I : Finset SourceCoordinate) (s : ℕ)
    (θ : SourceCoordinate → ℝ) (n : ℤ) (x : SourceCoordinate → ℝ)
    (hx : ∀ i, x i ∈ Set.Ico (0 : ℝ) 1) (hw : sourceSamplingWeight I s θ n x ≠ 0) :
    ∀ i ∈ sourceSamplingPrefix s, x i < coordinateRotate θ n x i := by
  intro i hi
  have hp := sourceSampling_parameters s
  have hwi := Finset.prod_ne_zero_iff.mp hw i hi
  have horder := (samplingWeight_orders (decide (i ∈ I)) _ _ (x i)
    (Int.fract ((n : ℝ)*θ i)) hp.1 hp.2.1 hp.2.2 (hx i) hwi).2
  have he : x i+(n : ℝ)*θ i = (x i+Int.fract ((n : ℝ)*θ i)) + (⌊(n : ℝ)*θ i⌋ : ℝ) := by
    linarith [Int.fract_add_floor ((n : ℝ)*θ i)]
  unfold coordinateRotate
  rw [he,Int.fract_add_intCast]
  exact horder

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_OrbitSampling_Measures
attribute [-instance] _root_.OAI.FiniteFactor.sourceBiasedRealMeasure_probability _root_.OAI.FiniteFactor.sourceFiniteReferenceKernel_markov _root_.OAI.FiniteFactor.sourceHilbert_separable _root_.OAI.FiniteFactor.sourceNormalFunctionalSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedGroup _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedSpace _root_.OAI.FiniteFactor.sourceResamplingKernel_markov _root_.OAI.FiniteFactor.sourceSamplingLambda_finite _root_.OAI.FiniteFactor.sourceSamplingTorus_borel _root_.OAI.FiniteFactor.sourceSamplingTorus_compact _root_.OAI.FiniteFactor.sourceSamplingTrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingUntrimmed_finite _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Finset Filter
open scoped ENNReal
noncomputable section

theorem sourceSamplingHaar_cube : ∀ᵐ x ∂sourceSamplingHaar,
    ∀ i : SourceCoordinate, x i ∈ Set.Ico (0 : ℝ) 1 := by
  rw [ae_all_iff]
  intro i
  have hh : ∀ᵐ t ∂sourceSamplingHaar.map (fun x => x i), t ∈ Set.Ico (0 : ℝ) 1 := by
    rw [Measure.infinitePi_map_eval]
    exact ae_restrict_mem measurableSet_Ico
  exact (ae_map_iff (measurable_pi_apply i).aemeasurable measurableSet_Ico).mp hh

/-- The weighted source law already orders every coordinate in its prefix. -/
theorem sourceSamplingWeightedMeasure_orders (I : Finset SourceCoordinate) (s : ℕ)
    (θ : SourceCoordinate → ℝ) (n : ℤ) :
    ∀ᵐ x ∂sourceSamplingWeightedMeasure I s θ n,
      ∀ i ∈ sourceSamplingPrefix s, x i < coordinateRotate θ n x i := by
  rw [sourceSamplingWeightedMeasure,ae_withDensity_iff
    ((sourceSamplingWeight_measurable I s θ n).ennreal_ofReal)]
  filter_upwards [sourceSamplingHaar_cube] with x hx hw
  have hw' : sourceSamplingWeight I s θ n x ≠ 0 := by
    intro he
    exact hw (by rw [he]; simp)
  exact sourceSamplingWeight_orders_prefix I s θ n x hx hw'

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_OrbitSampling_TestedTransport
attribute [-instance] _root_.OAI.FiniteFactor.sourceBiasedRealMeasure_probability _root_.OAI.FiniteFactor.sourceFiniteReferenceKernel_markov _root_.OAI.FiniteFactor.sourceHilbert_separable _root_.OAI.FiniteFactor.sourceNormalFunctionalSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedGroup _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedSpace _root_.OAI.FiniteFactor.sourceResamplingKernel_markov _root_.OAI.FiniteFactor.sourceSamplingLambda_finite _root_.OAI.FiniteFactor.sourceSamplingTorus_borel _root_.OAI.FiniteFactor.sourceSamplingTorus_compact _root_.OAI.FiniteFactor.sourceSamplingTrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingUntrimmed_finite _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter Finset
open scoped Classical ENNReal
noncomputable section

theorem sourceSamplingRectangle_measurable (E G : SourceCoordinate → Set ℝ)
    (hE : ∀ i, MeasurableSet (E i)) (hG : ∀ i, MeasurableSet (G i)) :
    MeasurableSet (sourceSamplingRectangle E G) := by
  simp only [sourceSamplingRectangle,Set.ofPred_forall]
  apply MeasurableSet.iInter
  intro i
  exact ((hE i).preimage ((measurable_pi_apply i).comp measurable_fst)).inter
    ((hG i).preimage ((measurable_pi_apply i).comp measurable_snd))

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_OrbitSampling_TestedMarginals
attribute [-instance] _root_.OAI.FiniteFactor.sourceBiasedRealMeasure_probability _root_.OAI.FiniteFactor.sourceFiniteReferenceKernel_markov _root_.OAI.FiniteFactor.sourceHilbert_separable _root_.OAI.FiniteFactor.sourceNormalFunctionalSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedGroup _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedSpace _root_.OAI.FiniteFactor.sourceResamplingKernel_markov _root_.OAI.FiniteFactor.sourceSamplingLambda_finite _root_.OAI.FiniteFactor.sourceSamplingTorus_borel _root_.OAI.FiniteFactor.sourceSamplingTorus_compact _root_.OAI.FiniteFactor.sourceSamplingTrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingUntrimmed_finite _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter Finset
open scoped Classical ENNReal
noncomputable section

theorem sourceSamplingEndpoint_measurable (r : Bool) : Measurable (sourceSamplingEndpoint r) := by
  cases r
  · exact measurable_fst
  · exact measurable_snd

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_OrbitSampling_CutoffMass
attribute [-instance] _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter Finset
open scoped Classical ENNReal Topology
noncomputable section

/-- Exact whole-circle first density, including the retained cutoff. -/
theorem samplingTestedFirstDensity_whole (b : Bool) (h α s : ℝ)
    (hh : 0 < h) (hh1 : h < 1) (hα : 0 < α) (hs : s ∈ Set.Ico (0 : ℝ) 1) :
    samplingTestedFirstDensity b h α (Set.Icc 0 1) (Set.Icc 0 1) s =
      if b then 1-s else if α ≤ samplingDistance s then 1 else 0 := by
  have he : samplingTestedFirstDensity b h α (Set.Icc 0 1) (Set.Icc 0 1) s =
      ∫ t, samplingWeight b h α s t ∂unitIntervalMeasure := by
    apply integral_congr_ae
    filter_upwards [] with t
    have hs' : s ∈ Set.Icc (0 : ℝ) 1 := ⟨hs.1,hs.2.le⟩
    have ht' : Int.fract (s+t) ∈ Set.Icc (0 : ℝ) 1 := ⟨Int.fract_nonneg _,(Int.fract_lt_one _).le⟩
    simp only [samplingTestedFirstWeight,hs',ht',and_self,ite_true]
  exact he.trans (samplingWeight_first_integral b h α s hh hh1 hα hs)

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_OrbitSampling_TriangleLaw
attribute [-instance] _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped Classical ENNReal Topology
noncomputable section

/-- The actual triangular phase weight is precisely the order indicator
of the rotated endpoint, on the Haar representatives. -/
theorem samplingWeight_triangular_order (h α s t : ℝ)
    (hs : s ∈ Set.Ico (0 : ℝ) 1) (ht : t ∈ Set.Ico (0 : ℝ) 1) :
    samplingWeight true h α s t = if s < Int.fract (s+t) then 1 else 0 := by
  by_cases hst : s+t < 1
  · have hf : Int.fract (s+t) = s+t := Int.fract_eq_self.mpr ⟨by linarith [hs.1,ht.1],hst⟩
    simp only [samplingWeight,ite_true,hf]
    have he : (0 < t ∧ t < 1-s) ↔ s < s+t := by
      constructor
      · intro h; linarith [h.1]
      · intro h; constructor <;> linarith
    simp only [he]
  · have hf : ⌊s+t⌋ = (1 : ℤ) := Int.floor_eq_iff.mpr ⟨by norm_num; linarith,by norm_num; linarith [hs.2,ht.2]⟩
    have hn : ¬ (0 < t ∧ t < 1-s) := by intro h; linarith [h.2]
    have ho : ¬ s < Int.fract (s+t) := by rw [Int.fract,hf]; norm_num; linarith [ht.2]
    simp only [samplingWeight,ite_true,ite_eq_right hn,ite_eq_right ho]

/-- The first tested triangular density is its actual vertical section of
Lebesgue measure on 0≤x<y<1. No triangular marginal identity is assumed. -/
theorem samplingTestedFirstDensity_triangular_section (h α s : ℝ) (E G : Set ℝ)
    (hG : MeasurableSet G) (hs : s ∈ Set.Ico (0 : ℝ) 1) :
    samplingTestedFirstDensity true h α E G s =
      ∫ y, (if s ∈ E ∧ y ∈ G ∧ s < y then (1 : ℝ) else 0) ∂unitIntervalMeasure := by
  let F := fun y : ℝ => if s ∈ E ∧ y ∈ G ∧ s < y then (1 : ℝ) else 0
  have hm : Measurable F := by
    apply Measurable.ite _ measurable_const measurable_const
    by_cases htest : s ∈ E
    · simp only [htest,true_and]
      change MeasurableSet (G ∩ {y : ℝ | s < y})
      exact hG.inter (measurableSet_lt measurable_const measurable_id)
    · simp [htest]
  have hp : MeasurePreserving (fun t : ℝ => Int.fract (s+t)) unitIntervalMeasure unitIntervalMeasure := by
    simpa only [add_comm] using unitInterval_rotate_preserving s
  have he : samplingTestedFirstWeight true h α E G s =ᵐ[unitIntervalMeasure]
      (fun t => F (Int.fract (s+t))) := by
    filter_upwards [ae_restrict_mem measurableSet_Ico] with t ht
    rw [samplingTestedFirstWeight,samplingWeight_triangular_order h α s t hs ht]
    simp only [F]
    split_ifs <;> simp_all
  rw [samplingTestedFirstDensity,integral_congr_ae he]
  rw [← integral_map hp.measurable.aemeasurable hm.aestronglyMeasurable,hp.map_eq]

/-- The two-dimensional tested source integral equals the genuine triangular
restriction of product Lebesgue measure. -/
theorem samplingTestedFirstDensity_triangular_mass (h α : ℝ) (E G : Set ℝ)
    (hE : MeasurableSet E) (hG : MeasurableSet G) :
    (∫ s, samplingTestedFirstDensity true h α E G s ∂unitIntervalMeasure) =
      ((unitIntervalMeasure.prod unitIntervalMeasure)
        {p : ℝ × ℝ | p.1 ∈ E ∧ p.2 ∈ G ∧ p.1 < p.2}).toReal := by
  let A := {p : ℝ × ℝ | p.1 ∈ E ∧ p.2 ∈ G ∧ p.1 < p.2}
  have hA : MeasurableSet A := (hE.preimage measurable_fst).inter
    ((hG.preimage measurable_snd).inter (measurableSet_lt measurable_fst measurable_snd))
  have hm : Measurable (A.indicator (fun _ => (1 : ℝ))) := measurable_const.indicator hA
  have hi : Integrable (A.indicator (fun _ => (1 : ℝ))) (unitIntervalMeasure.prod unitIntervalMeasure) :=
    (integrable_const (1 : ℝ)).indicator hA
  calc
    _ = ∫ s, ∫ y, A.indicator (fun _ => (1 : ℝ)) (s,y) ∂unitIntervalMeasure ∂unitIntervalMeasure := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ico] with s hs
      simpa only [A,Set.indicator_apply,Set.mem_ofPred_eq] using
        samplingTestedFirstDensity_triangular_section h α s E G hG hs
    _ = ∫ p, A.indicator (fun _ => (1 : ℝ)) p ∂unitIntervalMeasure.prod unitIntervalMeasure :=
      (integral_prod _ hi).symm
    _ = _ := by rw [integral_indicator hA]; simp [measureReal_def,A]

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_OrbitSampling_LimitMeasure
attribute [-instance] _root_.OAI.FiniteFactor.sourceBiasedRealMeasure_probability _root_.OAI.FiniteFactor.sourceFiniteReferenceKernel_markov _root_.OAI.FiniteFactor.sourceHilbert_separable _root_.OAI.FiniteFactor.sourceNormalFunctionalSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedGroup _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedSpace _root_.OAI.FiniteFactor.sourceResamplingKernel_markov _root_.OAI.FiniteFactor.sourceSamplingTorus_borel _root_.OAI.FiniteFactor.sourceSamplingTorus_compact _root_.OAI.FiniteFactor.sourceSamplingTrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingUntrimmed_finite _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter Finset
open scoped Classical ENNReal Topology
noncomputable section

theorem sourceSamplingTriangleSet_measurable (I : Finset SourceCoordinate) :
    MeasurableSet (sourceSamplingTriangleSet I) := by
  simp only [sourceSamplingTriangleSet,Set.ofPred_forall]
  apply MeasurableSet.iInter
  intro i
  apply MeasurableSet.iInter
  intro _
  exact measurableSet_lt (measurable_fst.comp (measurable_pi_apply i))
    (measurable_snd.comp (measurable_pi_apply i))

theorem sourceSamplingLimitMap_measurable (I : Finset SourceCoordinate) :
    Measurable (sourceSamplingLimitMap I) := by
  apply Measurable.prodMk
  · exact Measurable.of_eval (fun i => measurable_fst.comp (measurable_pi_apply i))
  · apply Measurable.of_eval
    intro i
    by_cases hi : i ∈ I
    · simpa only [hi,ite_true,Function.comp_def] using measurable_snd.comp (measurable_pi_apply i)
    · simpa only [hi,ite_false,Function.comp_def] using measurable_fst.comp (measurable_pi_apply i)

theorem sourceSamplingPairHaar_cube : ∀ᵐ p ∂sourceSamplingPairHaar,
    ∀ i, (p i).1 ∈ Set.Ico (0 : ℝ) 1 ∧ (p i).2 ∈ Set.Ico (0 : ℝ) 1 := by
  apply ae_all_iff.mpr
  intro i
  have hp : ∀ᵐ z ∂unitIntervalMeasure.prod unitIntervalMeasure,
      z.1 ∈ Set.Ico (0 : ℝ) 1 ∧ z.2 ∈ Set.Ico (0 : ℝ) 1 := by
    apply (Measure.ae_prod_iff_ae_ae (measurableSet_Ico.prod measurableSet_Ico)).mpr
    filter_upwards [ae_restrict_mem measurableSet_Ico] with x hx
    filter_upwards [ae_restrict_mem measurableSet_Ico] with y hy
    exact ⟨hx,hy⟩
  have hh : ∀ᵐ z ∂sourceSamplingPairHaar.map (fun p => p i),
      z.1 ∈ Set.Ico (0 : ℝ) 1 ∧ z.2 ∈ Set.Ico (0 : ℝ) 1 := by
    rw [Measure.infinitePi_map_eval]
    exact hp
  exact ae_of_ae_map (measurable_pi_apply i).aemeasurable hh

/-- The finite rectangle formula for the source limit, written using actual
Lebesgue triangular and diagonal masses. -/
theorem sourceSamplingLimitRectangleMass_formula (I : Finset SourceCoordinate) (T : SourceSamplingRationalTest) :
    sourceSamplingLimitRectangleMass I T = ∏ i ∈ I ∪ T.1,
      if i ∈ I then ((unitIntervalMeasure.prod unitIntervalMeasure)
        {p : ℝ × ℝ | p.1 ∈ sourceSamplingRationalX T i ∧
          p.2 ∈ sourceSamplingRationalY T i ∧ p.1 < p.2}).toReal
      else (unitIntervalMeasure (sourceSamplingRationalX T i ∩ sourceSamplingRationalY T i)).toReal := by
  apply Finset.prod_congr rfl
  intro i _
  by_cases hi : i ∈ I
  · simp only [ite_eq_left hi]
    exact samplingTestedFirstDensity_triangular_mass _ _ _ _ measurableSet_Icc measurableSet_Icc
  · simp only [ite_eq_right hi]

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_OrbitSampling_LambdaRectangles
attribute [-instance] _root_.OAI.FiniteFactor.sourceBiasedRealMeasure_probability _root_.OAI.FiniteFactor.sourceFiniteReferenceKernel_markov _root_.OAI.FiniteFactor.sourceHilbert_separable _root_.OAI.FiniteFactor.sourceNormalFunctionalSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedGroup _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedSpace _root_.OAI.FiniteFactor.sourceResamplingKernel_markov _root_.OAI.FiniteFactor.sourceSamplingTorus_borel _root_.OAI.FiniteFactor.sourceSamplingTorus_compact _root_.OAI.FiniteFactor.sourceSamplingTrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingUntrimmed_finite _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter Finset
open scoped Classical ENNReal Topology
noncomputable section

theorem sourceSamplingLambdaTest_measurable (I : Finset SourceCoordinate) (T : SourceSamplingRationalTest)
    (i : SourceCoordinate) : MeasurableSet {p | sourceSamplingLambdaTest I T i p} := by
  by_cases hi : i ∈ I
  · simp only [sourceSamplingLambdaTest,ite_eq_left hi]
    exact (measurableSet_Icc.preimage measurable_fst).inter
      ((measurableSet_Icc.preimage measurable_snd).inter (measurableSet_lt measurable_fst measurable_snd))
  · simp only [sourceSamplingLambdaTest,ite_eq_right hi]
    exact (measurableSet_Icc.preimage measurable_fst).inter (measurableSet_Icc.preimage measurable_fst)

/-- The finite coordinate conditions are equivalent to restriction by the
triangle and the full cylinder rectangle on the conull Haar cube. -/
theorem sourceSamplingLambdaTest_iff (I : Finset SourceCoordinate) (T : SourceSamplingRationalTest)
    (p : SourceCoordinate → ℝ × ℝ)
    (hp : ∀ i, (p i).1 ∈ Set.Ico (0 : ℝ) 1 ∧ (p i).2 ∈ Set.Ico (0 : ℝ) 1) :
    (∀ i ∈ I ∪ T.1, sourceSamplingLambdaTest I T i (p i)) ↔
      sourceSamplingLimitMap I p ∈ sourceSamplingRectangle (sourceSamplingRationalX T) (sourceSamplingRationalY T) ∧
      p ∈ sourceSamplingTriangleSet I := by
  constructor
  · intro h
    constructor
    · intro i
      by_cases hi : i ∈ I
      · have hh := h i (Finset.mem_union_left _ hi)
        simp only [sourceSamplingLambdaTest,ite_eq_left hi] at hh
        exact ⟨hh.1,by simpa only [sourceSamplingLimitMap,ite_eq_left hi] using hh.2.1⟩
      · by_cases ht : i ∈ T.1
        · have hh := h i (Finset.mem_union_right _ ht)
          simpa only [sourceSamplingLambdaTest,sourceSamplingLimitMap,ite_eq_right hi] using hh
        · have hx : (p i).1 ∈ Set.Icc (0 : ℝ) 1 := ⟨(hp i).1.1,(hp i).1.2.le⟩
          simpa only [sourceSamplingLimitMap,ite_eq_right hi,sourceSamplingRationalX,sourceSamplingRationalY,
            sourceSamplingRationalEndpoints,dite_eq_right ht,Rat.cast_zero,Rat.cast_one] using And.intro hx hx
    · intro i hi
      have hh := h i (Finset.mem_union_left _ hi)
      simp only [sourceSamplingLambdaTest,ite_eq_left hi] at hh
      exact hh.2.2
  · rintro ⟨hrect,htri⟩ i _
    have hh := hrect i
    by_cases hi : i ∈ I
    · simp only [sourceSamplingLambdaTest,ite_eq_left hi]
      exact ⟨hh.1,by simpa only [sourceSamplingLimitMap,ite_eq_left hi] using hh.2,htri i hi⟩
    · simpa only [sourceSamplingLambdaTest,sourceSamplingLimitMap,ite_eq_right hi] using hh

/-- The constructed infinite-coordinate measure has exactly the rectangle
values previously obtained as sampling limits. -/
theorem sourceSamplingLambda_rectangle (I : Finset SourceCoordinate) (T : SourceSamplingRationalTest) :
    ((sourceSamplingLambda I)
      (sourceSamplingRectangle (sourceSamplingRationalX T) (sourceSamplingRationalY T))).toReal =
      sourceSamplingLimitRectangleMass I T := by
  let R := sourceSamplingRectangle (sourceSamplingRationalX T) (sourceSamplingRationalY T)
  let C := sourceSamplingLimitMap I ⁻¹' R ∩ sourceSamplingTriangleSet I
  have hR : MeasurableSet R := sourceSamplingRectangle_measurable _ _
    (fun _ => measurableSet_Icc) (fun _ => measurableSet_Icc)
  have hmap := sourceSamplingLimitMap_measurable I
  have hC : MeasurableSet C := (hmap hR).inter (sourceSamplingTriangleSet_measurable I)
  have he : C.indicator (fun _ => (1 : ℝ)) =ᵐ[sourceSamplingPairHaar]
      (fun p => ∏ i ∈ I ∪ T.1, if sourceSamplingLambdaTest I T i (p i) then (1 : ℝ) else 0) := by
    filter_upwards [sourceSamplingPairHaar_cube] with p hp
    simp only [Finset.prod_ite_zero,Finset.prod_const_one,
      sourceSamplingLambdaTest_iff I T p hp,Set.indicator_apply]
    rfl
  rw [sourceSamplingLambda,Measure.map_apply hmap hR,Measure.restrict_apply (hmap hR)]
  change (sourceSamplingPairHaar C).toReal = _
  calc
    _ = ∫ p, C.indicator (fun _ => (1 : ℝ)) p ∂sourceSamplingPairHaar := by
      rw [integral_indicator hC]; simp [measureReal_def]
    _ = ∫ p, ∏ i ∈ I ∪ T.1, if sourceSamplingLambdaTest I T i (p i) then (1 : ℝ) else 0
        ∂sourceSamplingPairHaar := integral_congr_ae he
    _ = ∏ i ∈ I ∪ T.1, ∫ z, (if sourceSamplingLambdaTest I T i z then (1 : ℝ) else 0)
        ∂unitIntervalMeasure.prod unitIntervalMeasure :=
      integral_infinitePi_finset_prod _ _ _ (fun i =>
        Measurable.ite (sourceSamplingLambdaTest_measurable I T i) measurable_const measurable_const)
    _ = _ := by
      rw [sourceSamplingLimitRectangleMass_formula]
      apply Finset.prod_congr rfl
      intro i _
      have hA := sourceSamplingLambdaTest_measurable I T i
      have hh : (∫ z, (if sourceSamplingLambdaTest I T i z then (1 : ℝ) else 0)
          ∂unitIntervalMeasure.prod unitIntervalMeasure) =
          ((unitIntervalMeasure.prod unitIntervalMeasure) {z | sourceSamplingLambdaTest I T i z}).toReal := by
        change (∫ z, {z | sourceSamplingLambdaTest I T i z}.indicator (fun _ => (1 : ℝ)) z
          ∂unitIntervalMeasure.prod unitIntervalMeasure) = _
        rw [integral_indicator hA]; simp [measureReal_def]
      rw [hh]
      by_cases hi : i ∈ I
      · simp only [sourceSamplingLambdaTest,ite_eq_left hi]
      · simp only [sourceSamplingLambdaTest,ite_eq_right hi]
        have heq : {z : ℝ × ℝ | z.1 ∈ sourceSamplingRationalX T i ∧ z.1 ∈ sourceSamplingRationalY T i} =
            (sourceSamplingRationalX T i ∩ sourceSamplingRationalY T i) ×ˢ Set.univ := by ext z; simp
        rw [heq,Measure.prod_prod]
        simp

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_OrbitSampling_Cube
attribute [-instance] _root_.OAI.FiniteFactor.sourceBiasedRealMeasure_probability _root_.OAI.FiniteFactor.sourceFiniteReferenceKernel_markov _root_.OAI.FiniteFactor.sourceHilbert_separable _root_.OAI.FiniteFactor.sourceNormalFunctionalSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedGroup _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedSpace _root_.OAI.FiniteFactor.sourceResamplingKernel_markov _root_.OAI.FiniteFactor.sourceSamplingTorus_borel _root_.OAI.FiniteFactor.sourceSamplingTorus_compact _root_.OAI.FiniteFactor.sourceSamplingTrimmed_finite _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter Finset
open scoped Classical ENNReal Topology
noncomputable section

theorem sourceSamplingCube_measurable : MeasurableSet sourceSamplingCube := by
  exact sourceSamplingRectangle_measurable _ _ (fun _ => measurableSet_Icc) (fun _ => measurableSet_Icc)

theorem sourceSamplingSummand_cube (I : Finset SourceCoordinate) (s : ℕ)
    (θ : SourceCoordinate → ℝ) (n : ℤ) :
    ∀ᵐ p ∂sourceSamplingSummand I s θ n, p ∈ sourceSamplingCube := by
  apply (ae_map_iff (measurable_id.prodMk (coordinateRotate_preserving θ n).measurable).aemeasurable
    sourceSamplingCube_measurable).mpr
  have hh : ∀ᵐ x ∂sourceSamplingWeightedMeasure I s θ n, ∀ i, x i ∈ Set.Ico (0 : ℝ) 1 :=
    ae_iff.mpr (withDensity_absolutelyContinuous _ _ (ae_iff.mp sourceSamplingHaar_cube))
  filter_upwards [hh] with x hx
  intro i
  exact ⟨⟨(hx i).1,(hx i).2.le⟩,Int.fract_nonneg _,(Int.fract_lt_one _).le⟩

theorem sourceSamplingUntrimmed_cube (I : Finset SourceCoordinate) (s : ℕ)
    (θ : SourceCoordinate → ℝ) :
    ∀ᵐ p ∂sourceSamplingUntrimmed I s θ, p ∈ sourceSamplingCube := by
  apply Measure.ae_smul_measure
  rw [ae_iff, Measure.finsetSum_apply]
  apply Finset.sum_eq_zero
  intro n hn
  exact ae_iff.mp (sourceSamplingSummand_cube I s θ n)

theorem sourceSamplingLambda_cube (I : Finset SourceCoordinate) :
    ∀ᵐ p ∂sourceSamplingLambda I, p ∈ sourceSamplingCube := by
  apply (ae_map_iff (sourceSamplingLimitMap_measurable I).aemeasurable
    sourceSamplingCube_measurable).mpr
  filter_upwards [ae_restrict_of_ae sourceSamplingPairHaar_cube] with p hp
  intro i
  refine ⟨⟨(hp i).1.1,(hp i).1.2.le⟩,?_⟩
  by_cases hi : i ∈ I
  · simpa [sourceSamplingLimitMap,hi] using And.intro (hp i).2.1 (hp i).2.2.le
  · simpa [sourceSamplingLimitMap,hi] using And.intro (hp i).1.1 (hp i).1.2.le

theorem sourceSamplingEmptyTest_rectangle :
    sourceSamplingRectangle (sourceSamplingRationalX sourceSamplingEmptyTest)
      (sourceSamplingRationalY sourceSamplingEmptyTest) = sourceSamplingCube := by
  ext p
  simp [sourceSamplingRectangle,sourceSamplingRationalX,sourceSamplingRationalY,
    sourceSamplingRationalEndpoints,sourceSamplingEmptyTest,sourceSamplingCube]

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_OrbitSampling_LambdaMass
attribute [-instance] _root_.OAI.FiniteFactor.sourceBiasedRealMeasure_probability _root_.OAI.FiniteFactor.sourceFiniteReferenceKernel_markov _root_.OAI.FiniteFactor.sourceHilbert_separable _root_.OAI.FiniteFactor.sourceNormalFunctionalSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedGroup _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedSpace _root_.OAI.FiniteFactor.sourceResamplingKernel_markov _root_.OAI.FiniteFactor.sourceSamplingTorus_borel _root_.OAI.FiniteFactor.sourceSamplingTorus_compact _root_.OAI.FiniteFactor.sourceSamplingTrimmed_finite _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter Finset
open scoped Classical ENNReal Topology
noncomputable section

theorem sourceSampling_triangle_mass :
    ((unitIntervalMeasure.prod unitIntervalMeasure)
      {p : ℝ × ℝ | p.1 ∈ Set.Icc (0 : ℝ) 1 ∧ p.2 ∈ Set.Icc (0 : ℝ) 1 ∧ p.1 < p.2}).toReal = 1/2 := by
  rw [← samplingTestedFirstDensity_triangular_mass (1/2) 1 _ _ measurableSet_Icc measurableSet_Icc]
  have he : samplingTestedFirstDensity true (1/2) 1 (Set.Icc 0 1) (Set.Icc 0 1) =ᵐ[unitIntervalMeasure]
      (fun s => 1-s) := by
    filter_upwards [ae_restrict_mem measurableSet_Ico] with s hs
    simpa only [ite_true] using samplingTestedFirstDensity_whole true (1/2) 1 s
      (by norm_num) (by norm_num) (by norm_num) hs
  rw [integral_congr_ae he,unitIntervalMeasure,restrict_Ico_eq_restrict_Ioc,
    ← intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 1 by norm_num)]
  rw [intervalIntegral.integral_sub (f := fun _ : ℝ => (1 : ℝ)) (g := fun x : ℝ => x)
    intervalIntegrable_const (continuous_id.intervalIntegrable _ _)]
  norm_num [intervalIntegral.integral_const]

theorem sourceSamplingLambda_mass (I : Finset SourceCoordinate) :
    ((sourceSamplingLambda I) Set.univ).toReal = (1/2 : ℝ)^I.card := by
  have he : sourceSamplingLambda I sourceSamplingCube = sourceSamplingLambda I Set.univ :=
    measure_congr (by filter_upwards [sourceSamplingLambda_cube I] with p hp; exact propext (iff_true_intro hp))
  rw [← he,← sourceSamplingEmptyTest_rectangle,sourceSamplingLambda_rectangle,
    sourceSamplingLimitRectangleMass_formula]
  have hE (i : SourceCoordinate) : sourceSamplingRationalX sourceSamplingEmptyTest i = Set.Icc (0 : ℝ) 1 ∧
      sourceSamplingRationalY sourceSamplingEmptyTest i = Set.Icc (0 : ℝ) 1 := by
    simp [sourceSamplingRationalX,sourceSamplingRationalY,sourceSamplingRationalEndpoints,sourceSamplingEmptyTest]
  change (∏ i ∈ I ∪ ∅, _) = _
  rw [Finset.union_empty]
  calc
    _ = ∏ _i ∈ I, (1/2 : ℝ) := by
      apply Finset.prod_congr rfl
      intro i hi
      rw [ite_eq_left hi,(hE i).1,(hE i).2]
      exact sourceSampling_triangle_mass
    _ = _ := by simp

theorem sourceSamplingLambda_mass_pos (I : Finset SourceCoordinate) :
    0 < ((sourceSamplingLambda I) Set.univ).toReal := by
  rw [sourceSamplingLambda_mass]
  positivity

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_OrbitSampling_Tail
attribute [-instance] _root_.OAI.FiniteFactor.sourceAngleLaw_probability _root_.OAI.FiniteFactor.sourceAngleMarginal_atomless _root_.OAI.FiniteFactor.sourceAngleMarginal_probability _root_.OAI.FiniteFactor.sourceBiasedRealMeasure_probability _root_.OAI.FiniteFactor.sourceFiniteReferenceKernel_markov _root_.OAI.FiniteFactor.sourceHilbert_separable _root_.OAI.FiniteFactor.sourceNormalFunctionalSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedGroup _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedSpace _root_.OAI.FiniteFactor.sourceResamplingKernel_markov _root_.OAI.FiniteFactor.sourceSamplingLambda_finite _root_.OAI.FiniteFactor.sourceSamplingSummand_finite _root_.OAI.FiniteFactor.sourceSamplingTorus_borel _root_.OAI.FiniteFactor.sourceSamplingTorus_compact _root_.OAI.FiniteFactor.sourceSamplingTrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingUntrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingWeightedMeasure_finite _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter Finset
open scoped ENNReal Topology
noncomputable section

theorem sourceCutoff_ge_shift (s n : ℕ) :
    2^n * (sourceStageState s).K ≤ (sourceStageState (s+n)).K := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hh := sourceStage_cutoff_growth (s+n)
    rw [pow_succ, Nat.add_succ]
    nlinarith

/-- The exact geometric tail estimate used in scales and tail trimming. -/
theorem sourceCutoff_tail_bound (s : ℕ) :
    (∑' n : ℕ, 1 / ((sourceStageState (s+n)).K : ℝ)) ≤
      2 / ((sourceStageState s).K : ℝ) := by
  let b (n : ℕ) : ℝ := (1 / ((sourceStageState s).K : ℝ)) * (1/2 : ℝ)^n
  have hb : Summable b := (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1/2)
    (by norm_num : (1/2 : ℝ) < 1)).mul_left _
  have hle (n : ℕ) : 1 / ((sourceStageState (s+n)).K : ℝ) ≤ b n := by
    have hh : (2 : ℝ)^n * (sourceStageState s).K ≤ (sourceStageState (s+n)).K :=
      by exact_mod_cast sourceCutoff_ge_shift s n
    have hp : (0 : ℝ) < 2^n * (sourceStageState s).K := mul_pos (by positivity) (sourceCutoff_pos s)
    have ht := one_div_le_one_div_of_le hp hh
    simpa [b, one_div_pow, mul_comm, mul_left_comm] using ht
  calc
    _ ≤ ∑' n, b n := (hb.of_nonneg_of_le (fun _ => by positivity) hle).tsum_le_tsum hle hb
    _ = 2 / ((sourceStageState s).K : ℝ) := by
      rw [tsum_mul_left, tsum_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1/2) (by norm_num)]
      ring

theorem SourceAngles.tail_sum_bound {θ : SourceCoordinate → ℝ} (hθ : SourceAngles θ) (s : ℕ) :
    sourceTailAngleSum θ s ≤ 4 / ((sourceStageState s).K : ℝ) := by
  have hb (n : ℕ) :
      (∑ i : Fin (sourceBlockSize (s+n)), θ ⟨s+n,i⟩) ≤ 2 / ((sourceStageState (s+n)).K : ℝ) := by
    have hh := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => (hθ ⟨s+n,i⟩).2)
    have he : (∑ _i : Fin (sourceBlockSize (s+n)),
        2 / ((sourceBlockSize (s+n) : ℝ)*(sourceStageState (s+n)).K)) =
        2 / ((sourceStageState (s+n)).K : ℝ) := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      field_simp [(sourceBlockSize_pos (s+n)).ne', (sourceCutoff_pos (s+n)).ne']
    exact hh.trans_eq he
  have hs : Summable (fun n => 2 / ((sourceStageState (s+n)).K : ℝ)) := by
    have hh := sourceCutoff_reciprocal_summable.comp_injective (add_right_injective s)
    simpa [div_eq_mul_inv] using hh.mul_left 2
  calc
    sourceTailAngleSum θ s ≤ ∑' n, 2 / ((sourceStageState (s+n)).K : ℝ) :=
      (hs.of_nonneg_of_le (fun n => Finset.sum_nonneg (fun i _ => hθ.nonneg _)) hb).tsum_le_tsum hb hs
    _ = 2 * ∑' n, 1 / ((sourceStageState (s+n)).K : ℝ) := by
      rw [← tsum_mul_left]; congr; funext n; ring
    _ ≤ 2 * (2 / ((sourceStageState s).K : ℝ)) :=
      mul_le_mul_of_nonneg_left (sourceCutoff_tail_bound s) (by norm_num)
    _ = 4 / ((sourceStageState s).K : ℝ) := by ring

/-- The largest proposed sampling power divided by the next cutoff has the
source exponent gap 7/10 - 3/4 = -1/20. -/
theorem sourceSampling_tail_ratio (s : ℕ) :
    4 * (sourceBlockSize s : ℝ)^((7/10 : ℝ)*(sourceBlockSize s : ℝ)) /
      ((sourceStageState (s+1)).K : ℝ) ≤
    4 * (sourceBlockSize s : ℝ)^(-(sourceBlockSize s : ℝ)/20) := by
  have hm := sourceBlockSize_pos s
  have hK := sourceCutoff_pos (s+1)
  have hc : (sourceBlockSize s : ℝ)^((3/4 : ℝ)*(sourceBlockSize s : ℝ)) ≤
      (sourceStageState (s+1)).K := Nat.le_ceil _
  apply (div_le_iff₀ hK).mpr
  calc
    _ = (4 * (sourceBlockSize s : ℝ)^(-(sourceBlockSize s : ℝ)/20)) *
        (sourceBlockSize s : ℝ)^((3/4 : ℝ)*(sourceBlockSize s : ℝ)) := by
      rw [mul_assoc, ← Real.rpow_add hm]
      congr 2
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hc (by positivity)

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_CrossedProduct_TailTrimming
attribute [-instance] _root_.OAI.FiniteFactor.sourceBiasedRealMeasure_probability _root_.OAI.FiniteFactor.sourceFiniteReferenceKernel_markov _root_.OAI.FiniteFactor.sourceHilbert_separable _root_.OAI.FiniteFactor.sourceNormalFunctionalSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedGroup _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedSpace _root_.OAI.FiniteFactor.sourceResamplingKernel_markov _root_.OAI.FiniteFactor.sourceSamplingLambda_finite _root_.OAI.FiniteFactor.sourceSamplingSummand_finite _root_.OAI.FiniteFactor.sourceSamplingTorus_borel _root_.OAI.FiniteFactor.sourceSamplingTorus_compact _root_.OAI.FiniteFactor.sourceSamplingTrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingUntrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingWeightedMeasure_finite _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter Finset
open scoped ENNReal Topology
noncomputable section

theorem unitInterval_order_failure (a : ℝ) (ha : 0 ≤ a) :
    unitIntervalMeasure {x : ℝ | Int.fract (x+a) < x} ≤ ENNReal.ofReal a := by
  have hsub : {x : ℝ | Int.fract (x+a) < x} ⊆ {x : ℝ | Int.floor (x+a) ≠ 0} := by
    intro x hx he
    change Int.fract (x+a) < x at hx
    rw [Int.fract, he, Int.cast_zero, sub_zero] at hx
    linarith
  simpa only [abs_of_nonneg ha] using (measure_mono hsub).trans (unitInterval_floor_exception a)

theorem SourceAngles.block_sum_le {θ : SourceCoordinate → ℝ} (hθ : SourceAngles θ) (s : ℕ) :
    (∑ i : Fin (sourceBlockSize s), θ ⟨s,i⟩) ≤ 2 / ((sourceStageState s).K : ℝ) := by
  have hh := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => (hθ ⟨s,i⟩).2)
  have he : (∑ _i : Fin (sourceBlockSize s),
      2 / ((sourceBlockSize s : ℝ)*(sourceStageState s).K)) =
      2 / ((sourceStageState s).K : ℝ) := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp [(sourceBlockSize_pos s).ne', (sourceCutoff_pos s).ne']
  exact hh.trans_eq he

theorem SourceAngles.tail_block_summable {θ : SourceCoordinate → ℝ} (hθ : SourceAngles θ) (s : ℕ) :
    Summable (fun r : ℕ => ∑ i : Fin (sourceBlockSize (s+r)), θ ⟨s+r,i⟩) := by
  have hh := sourceCutoff_reciprocal_summable.comp_injective (add_right_injective s)
  have hs : Summable (fun r => 2 / ((sourceStageState (s+r)).K : ℝ)) := by
    simpa [div_eq_mul_inv] using hh.mul_left 2
  exact hs.of_nonneg_of_le (fun r => Finset.sum_nonneg (fun i _ => hθ.nonneg _))
    (fun r => hθ.block_sum_le (s+r))

/-- The source's trimming error tends to zero for every admissible angle
realization, uniformly for all positive powers up to Q_s=m_s^((7/10)m_s). -/
theorem sourceSampling_tail_error_tendsto :
    Tendsto (fun s => 4*(sourceBlockSize s : ℝ)^(-(sourceBlockSize s : ℝ)/20)) atTop (𝓝 0) := by
  have ht : Tendsto (fun s => 4*(sourceBlockSize s : ℝ)⁻¹) atTop (𝓝 0) := by
    have hi : Tendsto (fun s => (sourceBlockSize s : ℝ)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.comp sourceBlockSize_tendsto)
    simpa using hi.const_mul (4 : ℝ)
  apply squeeze_zero (fun s => by positivity) _ ht
  intro s
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  rw [← Real.rpow_neg_one]
  have hm : (100 : ℝ) ≤ sourceBlockSize s := by exact_mod_cast (sourceStage s).m_ge_100
  exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_Sampling_WeightedCoordinate
attribute [-instance] _root_.OAI.FiniteFactor.sourceBiasedRealMeasure_probability _root_.OAI.FiniteFactor.sourceFiniteReferenceKernel_markov _root_.OAI.FiniteFactor.sourceHilbert_separable _root_.OAI.FiniteFactor.sourceNormalFunctionalSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedGroup _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedSpace _root_.OAI.FiniteFactor.sourceResamplingKernel_markov _root_.OAI.FiniteFactor.sourceSamplingLambda_finite _root_.OAI.FiniteFactor.sourceSamplingTorus_borel _root_.OAI.FiniteFactor.sourceSamplingTorus_compact _root_.OAI.FiniteFactor.sourceSamplingTrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingUntrimmed_finite _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal
noncomputable section

/-- Exact relative mass of a tail-coordinate event under a prefix product
weight. This includes zero-mass weights and requires no division by mass. -/
theorem weighted_prefix_coordinate_mass {ι : Type*} [DecidableEq ι]
    (μi : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (μi i)]
    (J : Finset ι) (F : ι → ℝ → ℝ≥0∞) (hF : ∀ j, Measurable (F j))
    (i : ι) (hi : i ∉ J) (E : Set ℝ) (hE : MeasurableSet E) :
    ((Measure.infinitePi μi).withDensity (fun x => ∏ j ∈ J, F j (x j))) {x | x i ∈ E} =
      ((Measure.infinitePi μi).withDensity (fun x => ∏ j ∈ J, F j (x j))) Set.univ * μi i E := by
  classical
  let μ := Measure.infinitePi μi
  let W := fun x : ι → ℝ => ∏ j ∈ J, F j (x j)
  let B := fun x : ι → ℝ => E.indicator (fun _ => (1 : ℝ≥0∞)) (x i)
  let G := fun j : ι => if j = i then E.indicator (fun _ => (1 : ℝ≥0∞)) else F j
  have hG (j : ι) : Measurable (G j) := by
    dsimp [G]
    split_ifs
    · exact measurable_const.indicator hE
    · exact hF j
  have hind : iIndepFun (fun j (x : ι → ℝ) => G j (x j)) μ := iIndepFun_infinitePi hG
  have hproduct : (∏ j ∈ J, (fun x : ι → ℝ => G j (x j))) = W := by
    funext x
    simp only [Finset.prod_apply]
    apply prod_congr rfl
    intro j hj
    simp only [G,ite_eq_right (ne_of_mem_of_not_mem hj hi)]
  have heval : (fun x : ι → ℝ => G i (x i)) = B := by funext x; simp [G,B]
  have hind' := hind.indepFun_finsetProd_of_notMem (fun j => (hG j).comp (measurable_pi_apply j)) hi
  rw [hproduct,heval] at hind'
  have hW : Measurable W := Finset.measurable_prod J (fun j hj => (hF j).comp (measurable_pi_apply j))
  have hB : Measurable B := (measurable_const.indicator hE).comp (measurable_pi_apply i)
  have hEpre : MeasurableSet {x : ι → ℝ | x i ∈ E} := hE.preimage (measurable_pi_apply i)
  have hfub := lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun hW hB hind'
  have hcoord : (∫⁻ x, B x ∂μ) = μi i E := by
    rw [show B = {x : ι → ℝ | x i ∈ E}.indicator (fun _ => (1 : ℝ≥0∞)) by
      funext x; simp [B,Set.indicator]]
    rw [lintegral_indicator hEpre]
    simp only [lintegral_const,one_mul,Measure.restrict_apply_univ]
    have hh := congrArg (fun ν : Measure ℝ => ν E) (Measure.infinitePi_map_eval μi i)
    rw [Measure.map_apply (measurable_pi_apply i) hE] at hh
    exact hh
  rw [hcoord] at hfub
  rw [withDensity_apply _ hEpre,withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ,← lintegral_indicator hEpre]
  have he : {x : ι → ℝ | x i ∈ E}.indicator W = W*B := by
    funext x
    by_cases hx : x i ∈ E <;> simp [W,B,Set.indicator,hx]
  change (∫⁻ x, ({x : ι → ℝ | x i ∈ E}.indicator W) x ∂μ) = _
  rw [he]
  exact hfub

/-- The source sampling summand has exactly the Haar tail-coordinate
probability multiplied by its own mass. -/
theorem sourceSampling_tail_coordinate_mass (I : Finset SourceCoordinate) (s : ℕ)
    (θ : SourceCoordinate → ℝ) (n : ℤ) (i : SourceCoordinate) (hi : s < i.1)
    (E : Set ℝ) (hE : MeasurableSet E) :
    sourceSamplingWeightedMeasure I s θ n {x | x i ∈ E} =
      sourceSamplingWeightedMeasure I s θ n Set.univ * unitIntervalMeasure E := by
  let F := fun j : SourceCoordinate => fun t : ℝ => ENNReal.ofReal
    (samplingWeight (decide (j ∈ I)) (sourceSamplingWidth s) (sourceSamplingCutoff s)
      t (Int.fract ((n : ℝ)*θ j)))
  have hF (j : SourceCoordinate) : Measurable (F j) := by
    apply Measurable.ennreal_ofReal
    exact (samplingWeight_measurable _ _ _).comp (measurable_id.prodMk measurable_const)
  have he : (fun x => ENNReal.ofReal (sourceSamplingWeight I s θ n x)) =
      (fun x => ∏ j ∈ sourceSamplingPrefix s, F j (x j)) := by
    funext x
    exact ENNReal.ofReal_prod_of_nonneg (fun j hj => (sourceSampling_weight_bound s _ _ _).1)
  rw [sourceSamplingWeightedMeasure,he]
  apply weighted_prefix_coordinate_mass _ _ F hF i _ E hE
  rw [sourceSamplingPrefix,CouplingParameters.mem_blockPrefix]
  omega

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_OrbitSampling_WeightedTail
attribute [-instance] _root_.OAI.FiniteFactor.sourceBiasedRealMeasure_probability _root_.OAI.FiniteFactor.sourceFiniteReferenceKernel_markov _root_.OAI.FiniteFactor.sourceHilbert_separable _root_.OAI.FiniteFactor.sourceNormalFunctionalSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedGroup _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedSpace _root_.OAI.FiniteFactor.sourceResamplingKernel_markov _root_.OAI.FiniteFactor.sourceSamplingLambda_finite _root_.OAI.FiniteFactor.sourceSamplingTorus_borel _root_.OAI.FiniteFactor.sourceSamplingTorus_compact _root_.OAI.FiniteFactor.sourceSamplingTrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingUntrimmed_finite _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter Finset
open scoped ENNReal
noncomputable section

/-- The actual prefix-weighted summand loses at most the source tail budget
relative to its own mass. Coordinate independence is applied before the
countable union bound; a Haar estimate alone would not prove this statement. -/
theorem sourceSampling_weighted_tail_loss (I : Finset SourceCoordinate) (s : ℕ)
    (θ : SourceCoordinate → ℝ) (hθ : SourceAngles θ) (n : ℕ) :
    sourceSamplingWeightedMeasure I s θ (n : ℤ) (sourceTailOrderFailure θ (s+1) n) ≤
      sourceSamplingWeightedMeasure I s θ (n : ℤ) Set.univ *
        ENNReal.ofReal (4*(n : ℝ)/((sourceStageState (s+1)).K : ℝ)) := by
  let ν := sourceSamplingWeightedMeasure I s θ (n : ℤ)
  let M := ν Set.univ
  have hcoord (i : SourceCoordinate) (hi : s < i.1) :
      ν {x | Int.fract (x i+(n : ℝ)*θ i) < x i} ≤ M*ENNReal.ofReal ((n : ℝ)*θ i) := by
    have hE : MeasurableSet {t : ℝ | Int.fract (t+(n : ℝ)*θ i) < t} :=
      measurableSet_lt (sourceFract_measurable.comp (measurable_id.add measurable_const)) measurable_id
    have he := sourceSampling_tail_coordinate_mass I s θ (n : ℤ) i hi _ hE
    change ν {x | Int.fract (x i+(n : ℝ)*θ i) < x i} =
      M*unitIntervalMeasure {t | Int.fract (t+(n : ℝ)*θ i) < t} at he
    rw [he]
    have hh := unitInterval_order_failure ((n : ℝ)*θ i) (mul_nonneg (Nat.cast_nonneg _) (hθ.nonneg _))
    gcongr
  have hblock (r : ℕ) :
      ν (⋃ i : Fin (sourceBlockSize (s+1+r)),
        {x | Int.fract (x ⟨s+1+r,i⟩+(n : ℝ)*θ ⟨s+1+r,i⟩) < x ⟨s+1+r,i⟩}) ≤
      M*ENNReal.ofReal ((n : ℝ)*(∑ i : Fin (sourceBlockSize (s+1+r)), θ ⟨s+1+r,i⟩)) := by
    apply (measure_iUnion_le _).trans
    calc
      _ ≤ ∑' i : Fin (sourceBlockSize (s+1+r)), M*ENNReal.ofReal ((n : ℝ)*θ ⟨s+1+r,i⟩) :=
        ENNReal.tsum_le_tsum (fun i => hcoord ⟨s+1+r,i⟩ (by simp; omega))
      _ = _ := by
        rw [tsum_fintype, ← Finset.mul_sum,
          ← ENNReal.ofReal_sum_of_nonneg (fun i _ => mul_nonneg (Nat.cast_nonneg _) (hθ.nonneg _)),
          ← Finset.mul_sum]
  calc
    _ ≤ ∑' r : ℕ, ν (⋃ i : Fin (sourceBlockSize (s+1+r)),
        {x | Int.fract (x ⟨s+1+r,i⟩+(n : ℝ)*θ ⟨s+1+r,i⟩) < x ⟨s+1+r,i⟩}) := measure_iUnion_le _
    _ ≤ ∑' r : ℕ, M*ENNReal.ofReal ((n : ℝ)*(∑ i : Fin (sourceBlockSize (s+1+r)), θ ⟨s+1+r,i⟩)) :=
      ENNReal.tsum_le_tsum hblock
    _ = M*ENNReal.ofReal ((n : ℝ)*sourceTailAngleSum θ (s+1)) := by
      rw [ENNReal.tsum_mul_left, ← ENNReal.ofReal_tsum_of_nonneg
        (fun r => mul_nonneg (Nat.cast_nonneg _) (Finset.sum_nonneg (fun i _ => hθ.nonneg _)))
        ((hθ.tail_block_summable (s+1)).mul_left (n : ℝ)),tsum_mul_left]
      rfl
    _ ≤ _ := by
      gcongr 1
      apply ENNReal.ofReal_le_ofReal
      have hh := mul_le_mul_of_nonneg_left (hθ.tail_sum_bound (s+1)) (Nat.cast_nonneg n)
      simpa [mul_div_assoc,mul_comm,mul_left_comm] using hh

/-- The source exponent gap now bounds actual weighted lost mass, uniformly
for every positive power at most Q. -/
theorem sourceSampling_weighted_tail_small (I : Finset SourceCoordinate) (s : ℕ)
    (θ : SourceCoordinate → ℝ) (hθ : SourceAngles θ) (n : ℕ)
    (hn : (n : ℝ) ≤ samplingQ (sourceBlockSize s)) :
    sourceSamplingWeightedMeasure I s θ (n : ℤ) (sourceTailOrderFailure θ (s+1) n) ≤
      sourceSamplingWeightedMeasure I s θ (n : ℤ) Set.univ *
        ENNReal.ofReal (4*(sourceBlockSize s : ℝ)^(-(sourceBlockSize s : ℝ)/20)) := by
  apply (sourceSampling_weighted_tail_loss I s θ hθ n).trans
  gcongr 1
  apply ENNReal.ofReal_le_ofReal
  calc
    _ ≤ 4*samplingQ (sourceBlockSize s)/((sourceStageState (s+1)).K : ℝ) := by gcongr
    _ ≤ _ := sourceSampling_tail_ratio s

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_OrbitSampling_OrderedRestriction
attribute [-instance] _root_.OAI.FiniteFactor.sourceBiasedRealMeasure_probability _root_.OAI.FiniteFactor.sourceFiniteReferenceKernel_markov _root_.OAI.FiniteFactor.sourceHilbert_separable _root_.OAI.FiniteFactor.sourceNormalFunctionalSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedGroup _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedSpace _root_.OAI.FiniteFactor.sourceResamplingKernel_markov _root_.OAI.FiniteFactor.sourceSamplingTorus_borel _root_.OAI.FiniteFactor.sourceSamplingTorus_compact _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter Finset
open scoped Classical ENNReal Topology
noncomputable section

theorem sourceSamplingOrdered_measurable : MeasurableSet sourceSamplingOrdered := by
  simp only [sourceSamplingOrdered,Set.ofPred_forall]
  exact MeasurableSet.iInter (fun i => measurableSet_le
    ((measurable_pi_apply i).comp measurable_fst) ((measurable_pi_apply i).comp measurable_snd))

theorem sourceSamplingTrimmed_ordered (I : Finset SourceCoordinate) (s : ℕ)
    (θ : SourceCoordinate → ℝ) : ∀ᵐ p ∂sourceSamplingTrimmed I s θ, ∀ i, p.1 i ≤ p.2 i :=
  ae_restrict_mem sourceSamplingOrdered_measurable

theorem sourceSamplingPowers_positive (s : ℕ) (n : ℤ) (hn : n ∈ sourceSamplingPowers s) :
    0 < n ∧ (n : ℝ) ≤ samplingQ (sourceBlockSize s) := by
  by_cases hs : 200000 ≤ sourceBlockSize s
  · exact ⟨((sourceSamplingPowers_spec s hs).1 n hn).2.2,
      ((sourceSamplingPowers_spec s hs).1 n hn).2.1⟩
  · simp [sourceSamplingPowers,hs] at hn

/-- Outside the finite prefix, every failure of global order is an actual
member of the source's countable tail-failure event. -/
theorem sourceSampling_order_failure_tail (s n : ℕ) (θ x : SourceCoordinate → ℝ)
    (hprefix : ∀ i ∈ sourceSamplingPrefix s, x i < coordinateRotate θ (n : ℤ) x i)
    (hbad : (x,coordinateRotate θ (n : ℤ) x) ∉ sourceSamplingOrdered) :
    x ∈ sourceTailOrderFailure θ (s+1) n := by
  have hb : ∃ i, coordinateRotate θ (n : ℤ) x i < x i := by
    simpa only [sourceSamplingOrdered,Set.mem_ofPred_eq,not_forall,not_le] using hbad
  obtain ⟨i,hi⟩ := hb
  have hout : i ∉ sourceSamplingPrefix s := fun hh => (hprefix i hh).asymm hi
  have hk : s+1 ≤ i.1 := by
    have hh := (CouplingParameters.mem_blockPrefix sourceBlockSize (s+1) i)
    change i ∉ CouplingParameters.blockPrefix sourceBlockSize (s+1) at hout
    have hnot : ¬ i.1 < s+1 := fun hi => hout (hh.mpr hi)
    omega
  rcases i with ⟨k,j⟩
  obtain ⟨r,rfl⟩ := Nat.exists_eq_add_of_le hk
  apply Set.mem_iUnion.mpr ⟨r,?_⟩
  apply Set.mem_iUnion.mpr ⟨j,?_⟩
  simpa only [coordinateRotate,Int.cast_natCast,Set.mem_ofPred_eq] using hi

/-- Discarded mass of each real summand obeys the preserved relative
weighted-tail estimate. This includes summands of mass zero. -/
theorem sourceSamplingSummand_discarded_le (I : Finset SourceCoordinate) (s : ℕ)
    (θ : SourceCoordinate → ℝ) (hθ : SourceAngles θ) (n : ℤ)
    (hn : n ∈ sourceSamplingPowers s) :
    sourceSamplingSummand I s θ n sourceSamplingOrderedᶜ ≤
      sourceSamplingSummand I s θ n Set.univ *
        ENNReal.ofReal (4*(sourceBlockSize s : ℝ)^(-(sourceBlockSize s : ℝ)/20)) := by
  have hp := sourceSamplingPowers_positive s n hn
  have he : (n.toNat : ℤ) = n := Int.toNat_of_nonneg hp.1.le
  have hm : Measurable (fun x => (x,coordinateRotate θ n x)) :=
    measurable_id.prodMk (coordinateRotate_preserving θ n).measurable
  rw [sourceSamplingSummand,Measure.map_apply hm sourceSamplingOrdered_measurable.compl,
    Measure.map_apply hm MeasurableSet.univ,Set.preimage_univ]
  have hc : (n.toNat : ℝ) = (n : ℝ) := by exact_mod_cast he
  have hb := sourceSampling_weighted_tail_small I s θ hθ n.toNat (by rw [hc]; exact hp.2)
  rw [he] at hb
  apply le_trans _ hb
  apply measure_mono_ae
  filter_upwards [sourceSamplingWeightedMeasure_orders I s θ n] with x hx
  intro hb
  change (x,coordinateRotate θ n x) ∉ sourceSamplingOrdered at hb
  exact sourceSampling_order_failure_tail s n.toNat θ x (by simpa [he] using hx) (by simpa [he] using hb)

/-- The average loses at most the same relative error as each summand. -/
theorem sourceSamplingUntrimmed_discarded_le (I : Finset SourceCoordinate) (s : ℕ)
    (θ : SourceCoordinate → ℝ) (hθ : SourceAngles θ) :
    sourceSamplingUntrimmed I s θ sourceSamplingOrderedᶜ ≤
      sourceSamplingUntrimmed I s θ Set.univ *
        ENNReal.ofReal (4*(sourceBlockSize s : ℝ)^(-(sourceBlockSize s : ℝ)/20)) := by
  simp only [sourceSamplingUntrimmed,Measure.smul_apply,smul_eq_mul,Measure.finsetSum_apply]
  rw [mul_assoc,Finset.sum_mul]
  exact mul_le_mul' le_rfl (Finset.sum_le_sum (fun n hn => sourceSamplingSummand_discarded_le I s θ hθ n hn))

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_OrbitSampling_OrbitSupport
attribute [-instance] _root_.OAI.FiniteFactor.sourceBiasedRealMeasure_probability _root_.OAI.FiniteFactor.sourceFiniteReferenceKernel_markov _root_.OAI.FiniteFactor.sourceHilbert_separable _root_.OAI.FiniteFactor.sourceNormalFunctionalSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedGroup _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedSpace _root_.OAI.FiniteFactor.sourceResamplingKernel_markov _root_.OAI.FiniteFactor.sourceSamplingTorus_borel _root_.OAI.FiniteFactor.sourceSamplingTorus_compact _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter Finset
open scoped Classical ENNReal Topology
noncomputable section

theorem sourceSamplingPositiveOrbits_measurable (s : ℕ) (θ : SourceCoordinate → ℝ) :
    MeasurableSet (sourceSamplingPositiveOrbits s θ) := by
  simp only [sourceSamplingPositiveOrbits,Set.ofPred_exists]
  apply MeasurableSet.iUnion
  intro n
  by_cases hn : n ∈ sourceSamplingPowers s
  · simp only [hn,true_and]
    by_cases hp : 0 < n
    · simp only [hp,true_and]
      exact measurableSet_eq_fun measurable_snd ((coordinateRotate_preserving θ n).measurable.comp measurable_fst)
    · simp [hp]
  · simp [hn]

theorem sourceSamplingSummand_positive_orbit (I : Finset SourceCoordinate) (s : ℕ)
    (θ : SourceCoordinate → ℝ) (n : ℤ) (hn : n ∈ sourceSamplingPowers s) :
    ∀ᵐ p ∂sourceSamplingSummand I s θ n, p ∈ sourceSamplingPositiveOrbits s θ := by
  apply (ae_map_iff (measurable_id.prodMk (coordinateRotate_preserving θ n).measurable).aemeasurable
    (sourceSamplingPositiveOrbits_measurable s θ)).mpr
  exact Eventually.of_forall (fun x => ⟨n,hn,(sourceSamplingPowers_positive s n hn).1,rfl⟩)

/-- Trimming preserves the constructed finite set of strictly positive
orbit powers while imposing coordinatewise order everywhere. -/
theorem sourceSamplingTrimmed_orbits (I : Finset SourceCoordinate) (s : ℕ)
    (θ : SourceCoordinate → ℝ) : ∀ᵐ p ∂sourceSamplingTrimmed I s θ,
      (∀ i, p.1 i ≤ p.2 i) ∧ ∃ n ∈ sourceSamplingPowers s, 0 < n ∧ p.2 = coordinateRotate θ n p.1 := by
  have hu : ∀ᵐ p ∂sourceSamplingUntrimmed I s θ, p ∈ sourceSamplingPositiveOrbits s θ := by
    apply Measure.ae_smul_measure
    rw [ae_iff,Measure.finsetSum_apply]
    exact Finset.sum_eq_zero (fun n hn => ae_iff.mp (sourceSamplingSummand_positive_orbit I s θ n hn))
  filter_upwards [sourceSamplingTrimmed_ordered I s θ,ae_restrict_of_ae hu] with p ho hp
  exact ⟨ho,hp⟩

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_FiniteMeasureCylinderCriterion
attribute [-instance] _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped Topology
noncomputable section

/-- Finite-measure version of the neighborhood pi-system criterion. Total
mass convergence is required; zero limiting mass is handled separately. -/
theorem finiteMeasure_tendsto_of_piSystem {Ω : Type*} [MeasurableSpace Ω]
    [TopologicalSpace Ω] [SecondCountableTopology Ω] [OpensMeasurableSpace Ω]
    [Nonempty Ω] {S : Set (Set Ω)} (hS : IsPiSystem S)
    {μ : ℕ → FiniteMeasure Ω} {ν : FiniteMeasure Ω}
    (hmeas : ∀ s ∈ S, MeasurableSet s)
    (hbasis : ∀ u : Set Ω, IsOpen u → ∀ x ∈ u, ∃ s ∈ S, s ∈ 𝓝 x ∧ s ⊆ u)
    (hmass : Tendsto (fun n => (μ n).mass) atTop (𝓝 ν.mass))
    (hsets : ∀ s ∈ S, Tendsto (fun n => μ n s) atTop (𝓝 (ν s))) :
    Tendsto μ atTop (𝓝 ν) := by
  by_cases hν : ν = 0
  · subst ν
    exact FiniteMeasure.tendsto_zero_of_tendsto_zero_mass hmass
  apply FiniteMeasure.tendsto_of_tendsto_normalize_testAgainstNN_of_tendsto_mass _ hmass
  apply hS.tendsto_probabilityMeasure_of_tendsto_of_mem hmeas hbasis
  intro s hs
  have hv := ν.mass_nonzero_iff.mpr hν
  have he : ∀ᶠ n in atTop, μ n ≠ 0 := by
    filter_upwards [hmass.eventually (eventually_ne_nhds hv)] with n hn
    exact (μ n).mass_nonzero_iff.mp hn
  have hi : Tendsto (fun n => (μ n).mass⁻¹ * μ n s) atTop (𝓝 (ν.mass⁻¹ * ν s)) :=
    (hmass.inv₀ hv).mul (hsets s hs)
  rw [← ν.normalize_eq_of_nonzero hν s] at hi
  apply hi.congr'
  filter_upwards [he] with n hn
  exact ((μ n).normalize_eq_of_nonzero hn s).symm

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_OrbitSampling_CylinderSystem
attribute [-instance] _root_.OAI.FiniteFactor.sourceBiasedRealMeasure_probability _root_.OAI.FiniteFactor.sourceFiniteReferenceKernel_markov _root_.OAI.FiniteFactor.sourceHilbert_separable _root_.OAI.FiniteFactor.sourceNormalFunctionalSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedGroup _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedSpace _root_.OAI.FiniteFactor.sourceResamplingKernel_markov _root_.OAI.FiniteFactor.sourceSamplingTorus_borel _root_.OAI.FiniteFactor.sourceSamplingTorus_compact _root_.OAI.FiniteFactor.sourceSamplingTrimmed_finite _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter Finset
open scoped Classical ENNReal Topology
noncomputable section

theorem sourceSamplingCylinder_measurable (T : SourceSamplingRationalTest) :
    MeasurableSet (sourceSamplingCylinder T) := by
  simp only [sourceSamplingCylinder,Set.ofPred_forall]
  exact MeasurableSet.iInter (fun i => MeasurableSet.iInter (fun _ =>
    (measurableSet_Icc.preimage ((measurable_pi_apply i).comp measurable_fst)).inter
    (measurableSet_Icc.preimage ((measurable_pi_apply i).comp measurable_snd))))

theorem sourceSamplingCylinder_on_cube (T : SourceSamplingRationalTest) (p : SourceSamplingPair)
    (hp : p ∈ sourceSamplingCube) :
    p ∈ sourceSamplingCylinder T ↔
    p ∈ sourceSamplingRectangle (sourceSamplingRationalX T) (sourceSamplingRationalY T) := by
  constructor
  · intro h i
    by_cases hi : i ∈ T.1
    · exact h i hi
    · simpa [sourceSamplingRationalX,sourceSamplingRationalY,sourceSamplingRationalEndpoints,hi]
        using hp i
  · intro h i _
    exact h i

theorem sourceSamplingCylinder_inter (T U : SourceSamplingRationalTest) :
    sourceSamplingCylinder (sourceSamplingTestMeet T U) =
      sourceSamplingCylinder T ∩ sourceSamplingCylinder U := by
  have hcoord (p : SourceSamplingPair) (i : SourceCoordinate) :
      (i ∈ T.1 ∪ U.1 → p.1 i ∈ sourceSamplingRationalX (sourceSamplingTestMeet T U) i ∧
        p.2 i ∈ sourceSamplingRationalY (sourceSamplingTestMeet T U) i) ↔
      (i ∈ T.1 → p.1 i ∈ sourceSamplingRationalX T i ∧ p.2 i ∈ sourceSamplingRationalY T i) ∧
      (i ∈ U.1 → p.1 i ∈ sourceSamplingRationalX U i ∧ p.2 i ∈ sourceSamplingRationalY U i) := by
    by_cases ht : i ∈ T.1 <;> by_cases hu : i ∈ U.1 <;>
      simp [sourceSamplingRationalX,sourceSamplingRationalY,sourceSamplingRationalEndpoints,
        sourceSamplingTestMeet,ht,hu,Set.mem_Icc]
    tauto
  ext p
  change (∀ i, i ∈ T.1 ∪ U.1 → _) ↔ (∀ i, i ∈ T.1 → _) ∧ (∀ i, i ∈ U.1 → _)
  constructor
  · intro h
    exact ⟨fun i => ((hcoord p i).mp (h i)).1,fun i => ((hcoord p i).mp (h i)).2⟩
  · rintro ⟨hT,hU⟩ i
    exact (hcoord p i).mpr ⟨hT i,hU i⟩

theorem sourceSamplingCylinder_piSystem : IsPiSystem (Set.range sourceSamplingCylinder) := by
  rintro _ ⟨T,rfl⟩ _ ⟨U,rfl⟩ _
  exact ⟨sourceSamplingTestMeet T U,sourceSamplingCylinder_inter T U⟩

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_OrbitSampling_CylinderBasis
attribute [-instance] _root_.OAI.FiniteFactor.sourceBiasedRealMeasure_probability _root_.OAI.FiniteFactor.sourceFiniteReferenceKernel_markov _root_.OAI.FiniteFactor.sourceHilbert_separable _root_.OAI.FiniteFactor.sourceNormalFunctionalSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedGroup _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedSpace _root_.OAI.FiniteFactor.sourceResamplingKernel_markov _root_.OAI.FiniteFactor.sourceSamplingTorus_borel _root_.OAI.FiniteFactor.sourceSamplingTorus_compact _root_.OAI.FiniteFactor.sourceSamplingTrimmed_finite _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter Finset
open scoped Classical ENNReal Topology
noncomputable section

theorem rational_Icc_nhds {x : ℝ} {u : Set ℝ} (hu : u ∈ 𝓝 x) :
    ∃ a b : ℚ, Set.Icc (a : ℝ) b ∈ 𝓝 x ∧ Set.Icc (a : ℝ) b ⊆ u := by
  obtain ⟨l,r,hlr,hsub⟩ := mem_nhds_iff_exists_Ioo_subset.mp hu
  obtain ⟨a,hla,hax⟩ := exists_rat_btwn hlr.1
  obtain ⟨b,hxb,hbr⟩ := exists_rat_btwn hlr.2
  exact ⟨a,b,Icc_mem_nhds hax hxb,fun y hy => hsub ⟨hla.trans_le hy.1,hy.2.trans_lt hbr⟩⟩

/-- The finite rational cylinders contain arbitrarily small neighborhoods
in the full real product, including points outside the unit cube. -/
theorem sourceSamplingCylinder_basis (u : Set SourceSamplingPair) (hu : IsOpen u)
    (p : SourceSamplingPair) (hp : p ∈ u) :
    ∃ s ∈ Set.range sourceSamplingCylinder, s ∈ 𝓝 p ∧ s ⊆ u := by
  obtain ⟨ux,hux,uy,huy,hxy⟩ := mem_nhds_prod_iff.mp (hu.mem_nhds hp)
  rw [nhds_pi,Filter.mem_pi'] at hux huy
  obtain ⟨Kx,tx,htx,hsubx⟩ := hux
  obtain ⟨Ky,ty,hty,hsuby⟩ := huy
  choose ax bx hnx hsx using fun i => rational_Icc_nhds (htx i)
  choose ay by' hny hsy using fun i => rational_Icc_nhds (hty i)
  let T : SourceSamplingRationalTest := ⟨Kx ∪ Ky,fun i => ((ax i,bx i),(ay i,by' i))⟩
  have hTx (i : SourceCoordinate) (hi : i ∈ T.1) :
      sourceSamplingRationalX T i = Set.Icc (ax i : ℝ) (bx i) := by
    simp [sourceSamplingRationalX,sourceSamplingRationalEndpoints,hi,T]
  have hTy (i : SourceCoordinate) (hi : i ∈ T.1) :
      sourceSamplingRationalY T i = Set.Icc (ay i : ℝ) (by' i) := by
    simp [sourceSamplingRationalY,sourceSamplingRationalEndpoints,hi,T]
  refine ⟨sourceSamplingCylinder T,⟨T,rfl⟩,?_,?_⟩
  · have he : sourceSamplingCylinder T = ⋂ i ∈ T.1,
        {q : SourceSamplingPair | q.1 i ∈ sourceSamplingRationalX T i ∧
          q.2 i ∈ sourceSamplingRationalY T i} := by ext q; simp [sourceSamplingCylinder]
    rw [he]
    apply (Filter.biInter_mem (Set.toFinite (T.1 : Set SourceCoordinate))).mpr
    intro i hi
    have hx := ((continuous_apply i).comp continuous_fst).continuousAt (hnx i)
    have hy := ((continuous_apply i).comp continuous_snd).continuousAt (hny i)
    change {q : SourceSamplingPair | q.1 i ∈ Set.Icc (ax i : ℝ) (bx i)} ∈ 𝓝 p at hx
    change {q : SourceSamplingPair | q.2 i ∈ Set.Icc (ay i : ℝ) (by' i)} ∈ 𝓝 p at hy
    filter_upwards [hx,hy] with q hq1 hq2
    exact ⟨by simpa only [hTx i hi] using hq1,by simpa only [hTy i hi] using hq2⟩
  · intro q hq
    apply hxy
    constructor
    · apply hsubx
      intro i hi
      have hmem : i ∈ T.1 := Finset.mem_union_left _ hi
      exact hsx i (by simpa only [hTx i hmem] using (hq i hmem).1)
    · apply hsuby
      intro i hi
      have hmem : i ∈ T.1 := Finset.mem_union_right _ hi
      exact hsy i (by simpa only [hTy i hmem] using (hq i hmem).2)

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_OrbitSampling_WeakLimit
attribute [-instance] _root_.OAI.FiniteFactor.sourceBiasedRealMeasure_probability _root_.OAI.FiniteFactor.sourceFiniteReferenceKernel_markov _root_.OAI.FiniteFactor.sourceHilbert_separable _root_.OAI.FiniteFactor.sourceNormalFunctionalSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedGroup _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedSpace _root_.OAI.FiniteFactor.sourceResamplingKernel_markov _root_.OAI.FiniteFactor.sourceSamplingTorus_borel _root_.OAI.FiniteFactor.sourceSamplingTorus_compact _root_.OAI.FiniteFactor.sourceSamplingTrimmed_finite _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter Finset
open scoped Classical ENNReal Topology
noncomputable section

theorem sourceSamplingCylinder_mass_eq {μ : Measure SourceSamplingPair}
    (hμ : ∀ᵐ p ∂μ, p ∈ sourceSamplingCube) (T : SourceSamplingRationalTest) :
    μ (sourceSamplingCylinder T) =
      μ (sourceSamplingRectangle (sourceSamplingRationalX T) (sourceSamplingRationalY T)) := by
  apply measure_congr
  filter_upwards [hμ] with p hp
  exact propext (sourceSamplingCylinder_on_cube T p hp)

/-- Actual finite measures converge weakly on the full real product. The
normalization and total-mass obligations are discharged by the empty test;
the original full sampling error is retained through the rectangle event. -/
theorem sourceSamplingUntrimmed_weak_event : ∀ᵐ θ ∂sourceAngleLaw,
    ∀ I : Finset SourceCoordinate,
      Tendsto (fun s => sourceSamplingUntrimmedFinite I s θ) atTop
        (𝓝 (sourceSamplingLambdaFinite I)) := by
  filter_upwards [sourceSamplingLambda_rectangle_limit_event,sourceSampling_mass_limit_event]
    with θ hrect hmass
  intro I
  apply finiteMeasure_tendsto_of_piSystem sourceSamplingCylinder_piSystem
  · rintro _ ⟨T,rfl⟩
    exact sourceSamplingCylinder_measurable T
  · exact sourceSamplingCylinder_basis
  · apply NNReal.tendsto_coe.mp
    exact hmass I
  · rintro _ ⟨T,rfl⟩
    apply NNReal.tendsto_coe.mp
    have h := hrect I T
    have hu (s : ℕ) := sourceSamplingCylinder_mass_eq (sourceSamplingUntrimmed_cube I s θ) T
    have hl := sourceSamplingCylinder_mass_eq (sourceSamplingLambda_cube I) T
    change Tendsto (fun s => ((sourceSamplingUntrimmed I s θ) (sourceSamplingCylinder T)).toReal)
      atTop (𝓝 (((sourceSamplingLambda I) (sourceSamplingCylinder T)).toReal))
    simpa only [← hu,← hl] using h

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_OrbitSampling_CompactTorus
attribute [-instance] _root_.OAI.FiniteFactor.sourceBiasedRealMeasure_probability _root_.OAI.FiniteFactor.sourceFiniteReferenceKernel_markov _root_.OAI.FiniteFactor.sourceHilbert_separable _root_.OAI.FiniteFactor.sourceNormalFunctionalSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedGroup _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedSpace _root_.OAI.FiniteFactor.sourceResamplingKernel_markov _root_.OAI.FiniteFactor.sourceSamplingTrimmed_finite _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter Finset
open scoped Classical ENNReal Topology
noncomputable section

theorem sourceSamplingTorusMap_continuous : Continuous sourceSamplingTorusMap := by
  exact (continuous_pi (fun i => (AddCircle.continuous_mk' (1 : ℝ)).comp
    ((continuous_apply i).comp continuous_fst))).prodMk
    (continuous_pi (fun i => (AddCircle.continuous_mk' (1 : ℝ)).comp
      ((continuous_apply i).comp continuous_snd)))

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_OrbitSampling_TrimmedWeak
attribute [-instance] _root_.OAI.FiniteFactor.sourceBiasedRealMeasure_probability _root_.OAI.FiniteFactor.sourceFiniteReferenceKernel_markov _root_.OAI.FiniteFactor.sourceHilbert_separable _root_.OAI.FiniteFactor.sourceNormalFunctionalSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedGroup _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedSpace _root_.OAI.FiniteFactor.sourceResamplingKernel_markov _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter Finset
open scoped Classical ENNReal Topology
noncomputable section

theorem sourceSampling_discarded_tendsto (I : Finset SourceCoordinate)
    (θ : SourceCoordinate → ℝ) (hθ : SourceAngles θ)
    (hmass : Tendsto (fun s => ((sourceSamplingUntrimmed I s θ) Set.univ).toReal)
      atTop (𝓝 (((sourceSamplingLambda I) Set.univ).toReal))) :
    Tendsto (fun s => ((sourceSamplingUntrimmed I s θ) sourceSamplingOrderedᶜ).toReal)
      atTop (𝓝 0) := by
  have hlim := hmass.mul sourceSampling_tail_error_tendsto
  rw [mul_zero] at hlim
  apply squeeze_zero (fun s => ENNReal.toReal_nonneg) _ hlim
  intro s
  have h := ENNReal.toReal_mono (by finiteness)
    (sourceSamplingUntrimmed_discarded_le I s θ hθ)
  simpa only [ENNReal.toReal_mul,ENNReal.toReal_ofReal (by positivity :
    0 ≤ 4*(sourceBlockSize s : ℝ)^(-(sourceBlockSize s : ℝ)/20))] using h

/-- A restriction whose discarded mass tends to zero has the same finite
weak limit. The norm bound gives the actual error for every test function. -/
theorem finiteMeasure_restrict_tendsto {Ω : Type*} [MeasurableSpace Ω]
    [TopologicalSpace Ω] [OpensMeasurableSpace Ω]
    (μ : ℕ → FiniteMeasure Ω) (ν : FiniteMeasure Ω) (A : Set Ω) (hA : MeasurableSet A)
    (hμ : Tendsto μ atTop (𝓝 ν))
    (hloss : Tendsto (fun n => ((μ n : Measure Ω) Aᶜ).toReal) atTop (𝓝 0)) :
    Tendsto (fun n => finiteMeasureRestrict (μ n) A)
      atTop (𝓝 ν) := by
  apply FiniteMeasure.tendsto_of_forall_integral_tendsto
  intro f
  have hf := FiniteMeasure.tendsto_iff_forall_integral_tendsto.mp hμ f
  have he : Tendsto (fun n => ∫ x in Aᶜ, f x ∂(μ n : Measure Ω)) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    have hb := hloss.const_mul ‖f‖
    rw [mul_zero] at hb
    apply squeeze_zero (fun n => norm_nonneg _) _ hb
    intro n
    have hh := norm_integral_le_of_norm_le_const
      (μ := (μ n : Measure Ω).restrict Aᶜ)
      (Eventually.of_forall (fun x => f.norm_coe_le_norm x))
    simpa only [measureReal_def,Measure.restrict_apply MeasurableSet.univ,Set.univ_inter] using hh
  have hsub := hf.sub he
  rw [sub_zero] at hsub
  convert hsub using 1
  funext n
  exact (eq_sub_iff_add_eq.mpr (integral_add_compl (μ := (μ n : Measure Ω)) hA (f.integrable (μ := (μ n : Measure Ω)))))

/-- Actual ordered measures have the same compact-torus weak limit, for
all continuous tests, on one probability-one angle event. -/
theorem sourceSamplingTrimmed_weak_event : ∀ᵐ θ ∂sourceAngleLaw,
    ∀ I : Finset SourceCoordinate,
      Tendsto (fun s => sourceSamplingTrimmedFinite I s θ) atTop (𝓝 (sourceSamplingLambdaFinite I)) ∧
      Tendsto (fun s => sourceSamplingTrimmedTorus I s θ) atTop (𝓝 (sourceSamplingLambdaTorus I)) ∧
      ∀ f : C(SourceSamplingTorus,ℝ),
        Tendsto (fun s => ∫ p, f p ∂(sourceSamplingTrimmedTorus I s θ : Measure SourceSamplingTorus))
          atTop (𝓝 (∫ p, f p ∂(sourceSamplingLambdaTorus I : Measure SourceSamplingTorus))) := by
  filter_upwards [sourceSamplingUntrimmed_weak_event,sourceSampling_mass_limit_event,sourceAngleLaw_admissible]
    with θ hw hm ha
  intro I
  have h := finiteMeasure_restrict_tendsto (fun s => sourceSamplingUntrimmedFinite I s θ)
    (sourceSamplingLambdaFinite I) sourceSamplingOrdered sourceSamplingOrdered_measurable
    (hw I) (sourceSampling_discarded_tendsto I θ ha (hm I))
  have ht := FiniteMeasure.tendsto_map_of_tendsto_of_continuous _ _ h sourceSamplingTorusMap_continuous
  refine ⟨h,ht,fun f => ?_⟩
  exact (FiniteMeasure.tendsto_iff_forall_integral_tendsto.mp ht) (BoundedContinuousFunction.mkOfCompact f)

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_CrossedProduct_OrderedSampling
attribute [-instance] _root_.OAI.FiniteFactor.sourceBiasedRealMeasure_probability _root_.OAI.FiniteFactor.sourceFiniteReferenceKernel_markov _root_.OAI.FiniteFactor.sourceHilbert_separable _root_.OAI.FiniteFactor.sourceNormalFunctionalSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedGroup _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedSpace _root_.OAI.FiniteFactor.sourceResamplingKernel_markov _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter Finset
open scoped Classical ENNReal Topology
noncomputable section

theorem sourceOrderedSampling_event : ∀ᵐ θ ∂sourceAngleLaw,
    ∀ I : Finset SourceCoordinate,
      (∀ f : C(SourceSamplingTorus,ℝ),
        Tendsto (fun s => ∫ p, f p ∂(sourceSamplingTrimmedTorus I s θ : Measure SourceSamplingTorus))
          atTop (𝓝 (∫ p, f p ∂(sourceSamplingLambdaTorus I : Measure SourceSamplingTorus)))) ∧
      (∀ s, ∀ᵐ p ∂sourceSamplingTrimmed I s θ,
        (∀ i, p.1 i ≤ p.2 i) ∧ ∃ n ∈ sourceSamplingPowers s, 0 < n ∧ p.2 = coordinateRotate θ n p.1) ∧
      (∀ r : Bool, ∃ C : ℝ, ∀ s, ∃ g : (SourceCoordinate → ℝ) → ℝ,
        Measurable g ∧ (∀ x, 0 ≤ g x) ∧
        (sourceSamplingTrimmed I s θ).map (sourceSamplingEndpoint r) =
          sourceSamplingHaar.withDensity (fun x => ENNReal.ofReal (g x)) ∧
        MemLp g 2 sourceSamplingHaar ∧ (∫ x, g x^2 ∂sourceSamplingHaar) ≤ C) ∧
      (∀ᶠ s in atTop, 0 < ((sourceSamplingTrimmed I s θ) Set.univ).toReal) := by
  filter_upwards [sourceSamplingTrimmed_weak_event,sourceSamplingTrimmed_marginals_event] with θ hw hm
  intro I
  refine ⟨(hw I).2.2,fun s => sourceSamplingTrimmed_orbits I s θ,hm I,?_⟩
  have hmass : Tendsto (fun s => ((sourceSamplingTrimmed I s θ) Set.univ).toReal) atTop
      (𝓝 (((sourceSamplingLambda I) Set.univ).toReal)) :=
    NNReal.continuous_coe.continuousAt.tendsto.comp (hw I).1.mass
  exact hmass.eventually (Ioi_mem_nhds (sourceSamplingLambda_mass_pos I))

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_CrossedProduct_TorusModel
attribute [-instance] _root_.OAI.FiniteFactor.sourceBiasedRealMeasure_probability _root_.OAI.FiniteFactor.sourceFiniteReferenceKernel_markov _root_.OAI.FiniteFactor.sourceHilbert_separable _root_.OAI.FiniteFactor.sourceNormalFunctionalSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedGroup _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedSpace _root_.OAI.FiniteFactor.sourceResamplingKernel_markov _root_.OAI.FiniteFactor.sourceSamplingTrimmed_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped ENNReal Classical
noncomputable section

theorem sourceTorusQuotient_preserving : MeasurePreserving sourceTorusQuotient sourceSamplingHaar sourceTorusHaar := by
  refine ⟨Measurable.of_eval (fun i => sourceCircle_mk_preserving.measurable.comp (measurable_pi_apply i)),?_⟩
  unfold sourceTorusQuotient
  rw [Measure.infinitePi_map_pi _ (fun _ => sourceCircle_mk_preserving.measurable)]
  simp only [sourceCircle_mk_preserving.map_eq]

theorem sourceTorusRepresentative_preserving :
    MeasurePreserving sourceTorusRepresentative sourceTorusHaar sourceSamplingHaar := by
  refine ⟨Measurable.of_eval (fun i => sourceCircleRepresentative_measurable.comp (measurable_pi_apply i)),?_⟩
  unfold sourceTorusRepresentative
  rw [Measure.infinitePi_map_pi _ (fun _ => sourceCircleRepresentative_measurable)]
  simp only [sourceCircleRepresentative_preserving.map_eq]

theorem sourceTorusRepresentative_quotient (x : SourceCoordinate → ℝ)
    (hx : ∀ i, x i ∈ Set.Ico (0 : ℝ) 1) :
    sourceTorusRepresentative (sourceTorusQuotient x) = x := by
  funext i
  exact (sourceCircleRepresentative_coe (x i)).trans (Int.fract_eq_self.mpr (hx i))

/-- Change of variables for actual weighted laws across the real
representatives and compact torus, with the inverse needed only almost everywhere. -/
theorem sourceTorusQuotient_withDensity (w : (SourceCoordinate → ℝ) → ℝ≥0∞) (hw : Measurable w) :
    (sourceSamplingHaar.withDensity w).map sourceTorusQuotient =
      sourceTorusHaar.withDensity (fun z => w (sourceTorusRepresentative z)) := by
  ext A hA
  have hQ := sourceTorusQuotient_preserving
  have hR := sourceTorusRepresentative_preserving
  rw [Measure.map_apply hQ.measurable hA,withDensity_apply _ (hQ.measurable hA),withDensity_apply _ hA,
    ← lintegral_indicator (hQ.measurable hA),← lintegral_indicator hA]
  have hm := (hw.comp hR.measurable).indicator hA
  calc
    _ = ∫⁻ x, A.indicator (fun z => w (sourceTorusRepresentative z)) (sourceTorusQuotient x) ∂sourceSamplingHaar := by
      apply lintegral_congr_ae
      filter_upwards [sourceSamplingHaar_cube] with x hx
      change (if sourceTorusQuotient x ∈ A then w x else 0) =
        (if sourceTorusQuotient x ∈ A then w (sourceTorusRepresentative (sourceTorusQuotient x)) else 0)
      rw [sourceTorusRepresentative_quotient x hx]
    _ = _ := hQ.lintegral_comp hm

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_OrbitSampling_TorusMarginals
attribute [-instance] _root_.OAI.FiniteFactor.sourceBiasedRealMeasure_probability _root_.OAI.FiniteFactor.sourceFiniteReferenceKernel_markov _root_.OAI.FiniteFactor.sourceHilbert_separable _root_.OAI.FiniteFactor.sourceNormalFunctionalSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedGroup _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedSpace _root_.OAI.FiniteFactor.sourceResamplingKernel_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped ENNReal
noncomputable section

theorem sourceTorusEndpoint_measurable (r : Bool) : Measurable (sourceTorusEndpoint r) := by
  cases r
  · exact measurable_fst
  · exact measurable_snd

theorem sourceSamplingTorus_marginal_transport (μ : Measure SourceSamplingPair) (r : Bool)
    (g : (SourceCoordinate → ℝ) → ℝ) (hg : Measurable g)
    (hm : μ.map (sourceSamplingEndpoint r) = sourceSamplingHaar.withDensity (fun x => ENNReal.ofReal (g x))) :
    (μ.map sourceSamplingTorusMap).map (sourceTorusEndpoint r) =
      sourceTorusHaar.withDensity (fun z => ENNReal.ofReal (g (sourceTorusRepresentative z))) := by
  have he : sourceTorusEndpoint r ∘ sourceSamplingTorusMap = sourceTorusQuotient ∘ sourceSamplingEndpoint r := by
    funext p
    cases r <;> rfl
  rw [Measure.map_map (sourceTorusEndpoint_measurable r) sourceSamplingTorusMap_continuous.measurable,he,
    ← Measure.map_map sourceTorusQuotient_preserving.measurable (sourceSamplingEndpoint_measurable r),hm]
  exact sourceTorusQuotient_withDensity _ hg.ennreal_ofReal

/-- The actual torus marginals, rather than only the representative-space
marginals, have uniformly bounded L2 densities with respect to product Haar. -/
theorem sourceSamplingTrimmed_torus_marginals_event : ∀ᵐ θ ∂sourceAngleLaw,
    ∀ (I : Finset SourceCoordinate) (r : Bool), ∃ C : ℝ, ∀ s,
      ∃ g : SourceTorus → ℝ,
        Measurable g ∧ (∀ z, 0 ≤ g z) ∧
        (sourceSamplingTrimmedTorus I s θ : Measure SourceSamplingTorus).map (sourceTorusEndpoint r) =
          sourceTorusHaar.withDensity (fun z => ENNReal.ofReal (g z)) ∧
        MemLp g 2 sourceTorusHaar ∧ (∫ z, g z^2 ∂sourceTorusHaar) ≤ C := by
  filter_upwards [sourceSamplingTrimmed_marginals_event] with θ hθ
  intro I r
  obtain ⟨C,hC⟩ := hθ I r
  refine ⟨C,fun s => ?_⟩
  obtain ⟨g,hg,hg0,hgm,hglp,hgint⟩ := hC s
  refine ⟨g ∘ sourceTorusRepresentative,hg.comp sourceTorusRepresentative_preserving.measurable,
    fun z => hg0 _,sourceSamplingTorus_marginal_transport _ r g hg hgm,?_,?_⟩
  · exact hglp.comp_measurePreserving sourceTorusRepresentative_preserving
  · have he : (∫ z, (g (sourceTorusRepresentative z))^2 ∂sourceTorusHaar) =
        ∫ x, g x^2 ∂sourceSamplingHaar := by
      rw [← sourceTorusRepresentative_preserving.map_eq]
      exact (integral_map sourceTorusRepresentative_preserving.measurable.aemeasurable
        (hg.pow_const 2).aestronglyMeasurable).symm
    exact he.trans_le hgint

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_OrbitSampling_TorusSupport
attribute [-instance] _root_.OAI.FiniteFactor.sourceBiasedRealMeasure_probability _root_.OAI.FiniteFactor.sourceFiniteReferenceKernel_markov _root_.OAI.FiniteFactor.sourceHilbert_separable _root_.OAI.FiniteFactor.sourceNormalFunctionalSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedGroup _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedSpace _root_.OAI.FiniteFactor.sourceResamplingKernel_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped ENNReal Classical
noncomputable section

theorem sourceSamplingPairRepresentative_measurable : Measurable sourceSamplingPairRepresentative :=
  (sourceTorusRepresentative_preserving.measurable.comp measurable_fst).prodMk
    (sourceTorusRepresentative_preserving.measurable.comp measurable_snd)

theorem sourceTorusRotate_continuous (θ : SourceCoordinate → ℝ) (n : ℤ) : Continuous (sourceTorusRotate θ n) :=
  continuous_pi (fun i => (continuous_apply i).add continuous_const)

theorem sourceTorusQuotient_rotate (θ x : SourceCoordinate → ℝ) (n : ℤ) :
    sourceTorusQuotient (coordinateRotate θ n x) = sourceTorusRotate θ n (sourceTorusQuotient x) := by
  funext i
  simp only [sourceTorusQuotient,coordinateRotate,sourceTorusRotate,AddCircle.coe_fract,
    AddCircle.coe_add,← zsmul_eq_mul,AddCircle.coe_zsmul]

/-- The chosen real representatives recover the actual orbit measures;
closed-cube endpoints are not silently identified with distinct real points. -/
theorem sourceSamplingTrimmed_representatives (I : Finset SourceCoordinate) (s : ℕ)
    (θ : SourceCoordinate → ℝ) : ∀ᵐ p ∂sourceSamplingTrimmed I s θ,
      sourceSamplingPairRepresentative (sourceSamplingTorusMap p) = p := by
  have hmeas : MeasurableSet {p : SourceSamplingPair |
      sourceSamplingPairRepresentative (sourceSamplingTorusMap p) = p} :=
    measurableSet_eq_fun (sourceSamplingPairRepresentative_measurable.comp sourceSamplingTorusMap_continuous.measurable)
      measurable_id
  have hu : ∀ᵐ p ∂sourceSamplingUntrimmed I s θ,
      sourceSamplingPairRepresentative (sourceSamplingTorusMap p) = p := by
    apply Measure.ae_smul_measure
    rw [ae_iff,Measure.finsetSum_apply]
    apply Finset.sum_eq_zero
    intro n hn
    apply ae_iff.mp
    apply (ae_map_iff (measurable_id.prodMk (coordinateRotate_preserving θ n).measurable).aemeasurable hmeas).mpr
    have hh : ∀ᵐ x ∂sourceSamplingWeightedMeasure I s θ n, ∀ i, x i ∈ Set.Ico (0 : ℝ) 1 :=
      ae_iff.mpr (withDensity_absolutelyContinuous _ _ (ae_iff.mp sourceSamplingHaar_cube))
    filter_upwards [hh] with x hx
    apply Prod.ext
    · exact sourceTorusRepresentative_quotient x hx
    · exact sourceTorusRepresentative_quotient _ (fun i => ⟨Int.fract_nonneg _,Int.fract_lt_one _⟩)
  exact ae_restrict_of_ae hu

theorem sourceSamplingTorusOrderedOrbits_measurable (s : ℕ) (θ : SourceCoordinate → ℝ) :
    MeasurableSet (sourceSamplingTorusOrderedOrbits s θ) := by
  change MeasurableSet ({p : SourceSamplingTorus | ∀ i, sourceTorusRepresentative p.1 i ≤ sourceTorusRepresentative p.2 i} ∩
    {p : SourceSamplingTorus | ∃ n ∈ sourceSamplingPowers s, 0 < n ∧ p.2 = sourceTorusRotate θ n p.1})
  apply MeasurableSet.inter
  · simp only [Set.ofPred_forall]
    exact MeasurableSet.iInter (fun i => measurableSet_le
      ((measurable_pi_apply i).comp (sourceTorusRepresentative_preserving.measurable.comp measurable_fst))
      ((measurable_pi_apply i).comp (sourceTorusRepresentative_preserving.measurable.comp measurable_snd)))
  · simp only [Set.ofPred_exists]
    apply MeasurableSet.iUnion
    intro n
    by_cases hn : n ∈ sourceSamplingPowers s ∧ 0 < n
    · simp only [hn.1,hn.2,true_and]
      exact measurableSet_eq_fun measurable_snd ((sourceTorusRotate_continuous θ n).measurable.comp measurable_fst)
    · have he : {p : SourceSamplingTorus | n ∈ sourceSamplingPowers s ∧ 0 < n ∧ p.2 = sourceTorusRotate θ n p.1} = ∅ := by
        ext p; simp only [Set.mem_ofPred_eq,Set.mem_empty_iff_false,iff_false]; tauto
      rw [he]
      exact MeasurableSet.empty

/-- Actual compact-torus support: representatives are ordered, and each pair
lies on one of the constructed finitely many strictly positive rotation graphs. -/
theorem sourceSamplingTrimmed_torus_orbits (I : Finset SourceCoordinate) (s : ℕ)
    (θ : SourceCoordinate → ℝ) :
    ∀ᵐ p ∂(sourceSamplingTrimmedTorus I s θ : Measure SourceSamplingTorus),
      (∀ i, sourceTorusRepresentative p.1 i ≤ sourceTorusRepresentative p.2 i) ∧
      ∃ n ∈ sourceSamplingPowers s, 0 < n ∧ p.2 = sourceTorusRotate θ n p.1 := by
  apply (ae_map_iff sourceSamplingTorusMap_continuous.measurable.aemeasurable
    (sourceSamplingTorusOrderedOrbits_measurable s θ)).mpr
  filter_upwards [sourceSamplingTrimmed_orbits I s θ,sourceSamplingTrimmed_representatives I s θ] with p hp he
  refine ⟨?_,?_⟩
  · have h1 := congrArg Prod.fst he
    have h2 := congrArg Prod.snd he
    change sourceTorusRepresentative (sourceTorusQuotient p.1) = p.1 at h1
    change sourceTorusRepresentative (sourceTorusQuotient p.2) = p.2 at h2
    change ∀ i, sourceTorusRepresentative (sourceTorusQuotient p.1) i ≤ sourceTorusRepresentative (sourceTorusQuotient p.2) i
    rw [h1,h2]
    exact hp.1
  · obtain ⟨n,hn,hpos,hrot⟩ := hp.2
    refine ⟨n,hn,hpos,?_⟩
    change sourceTorusQuotient p.2 = sourceTorusRotate θ n (sourceTorusQuotient p.1)
    rw [hrot]
    exact sourceTorusQuotient_rotate θ p.1 n

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_CrossedProduct_OrderedTorusSampling
attribute [-instance] _root_.OAI.FiniteFactor.sourceBiasedRealMeasure_probability _root_.OAI.FiniteFactor.sourceFiniteReferenceKernel_markov _root_.OAI.FiniteFactor.sourceHilbert_separable _root_.OAI.FiniteFactor.sourceNormalFunctionalSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedGroup _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedSpace _root_.OAI.FiniteFactor.sourceResamplingKernel_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped ENNReal Topology
noncomputable section

theorem sourceOrderedTorusSampling_event : ∀ᵐ θ ∂sourceAngleLaw, SourceOrderedTorusSampling θ := by
  filter_upwards [sourceOrderedSampling_event,sourceSamplingTrimmed_torus_marginals_event] with θ hs hm
  refine ⟨fun I => (hs I).1,fun I s => sourceSamplingTrimmed_torus_orbits I s θ,hm,?_⟩
  intro I
  have he (s : ℕ) : (sourceSamplingTrimmedTorus I s θ : Measure SourceSamplingTorus) Set.univ =
      sourceSamplingTrimmed I s θ Set.univ := by
    exact Measure.map_apply sourceSamplingTorusMap_continuous.measurable MeasurableSet.univ
  simpa only [he] using (hs I).2.2.2

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_CrossedProduct_Phases
attribute [-instance] _root_.OAI.FiniteFactor.sourceBiasedRealMeasure_probability _root_.OAI.FiniteFactor.sourceFiniteReferenceKernel_markov _root_.OAI.FiniteFactor.sourceHilbert_separable _root_.OAI.FiniteFactor.sourceNormalFunctionalSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedGroup _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedSpace _root_.OAI.FiniteFactor.sourceResamplingKernel_markov _root_.OAI.FiniteFactor.sourceSamplingLambda_finite _root_.OAI.FiniteFactor.sourceSamplingSummand_finite _root_.OAI.FiniteFactor.sourceSamplingTorus_borel _root_.OAI.FiniteFactor.sourceSamplingTorus_compact _root_.OAI.FiniteFactor.sourceSamplingTrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingUntrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingWeightedMeasure_finite _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter Finset
open scoped ENNReal Topology Classical
noncomputable section

theorem sourcePhaseFailure_bound (s : ℕ) :
    sourceAngleLaw (sourcePhaseFailure s) ≤ ENNReal.ofReal (sourcePhaseFailureMajorant s) := by
  let B : ℝ≥0∞ := (2 : ℝ≥0∞)^sourceBlockSize s *
    (ENNReal.ofReal (10*sourceWidth s 1))^sourceMissCount s
  have hn (n : ℕ) : sourceAngleLaw
      (if sourcePhaseLower s ≤ (n : ℝ) then sourceFewPhases s (n : ℤ) else ∅) ≤ B := by
    split_ifs with h
    · apply sourceFewPhases_probability
      simpa only [sourcePhaseLower, Int.cast_natCast, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) n)] using h
    · simp
  have hQ : 0 ≤ sourcePhaseUpper s := by unfold sourcePhaseUpper; positivity
  have hc : ((Finset.Icc 1 (Nat.floor (sourcePhaseUpper s))).card : ℝ≥0∞) ≤
      ENNReal.ofReal (sourcePhaseUpper s) := by
    simp only [Nat.card_Icc, Nat.add_sub_cancel]
    exact_mod_cast ENNReal.ofReal_le_ofReal (Nat.floor_le hQ)
  calc
    _ ≤ ∑ n ∈ Finset.Icc 1 (Nat.floor (sourcePhaseUpper s)), sourceAngleLaw
        (if sourcePhaseLower s ≤ (n : ℝ) then sourceFewPhases s (n : ℤ) else ∅) :=
      measure_biUnion_finset_le _ _
    _ ≤ ∑ _n ∈ Finset.Icc 1 (Nat.floor (sourcePhaseUpper s)), B :=
      Finset.sum_le_sum (fun n _ => hn n)
    _ = ((Finset.Icc 1 (Nat.floor (sourcePhaseUpper s))).card : ℝ≥0∞)*B := by simp [nsmul_eq_mul]
    _ ≤ ENNReal.ofReal (sourcePhaseUpper s)*B := by gcongr
    _ = ENNReal.ofReal (sourcePhaseFailureMajorant s) := by
      have hw : 0 ≤ 10*sourceWidth s 1 := by unfold sourceWidth; dsimp; positivity
      dsimp [B]
      rw [show (2 : ℝ≥0∞)^sourceBlockSize s = ENNReal.ofReal ((2 : ℝ)^sourceBlockSize s) by simp,
        ← ENNReal.ofReal_pow hw,
        ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 2^sourceBlockSize s),
        ← ENNReal.ofReal_mul hQ]
      congr 1
      unfold sourcePhaseFailureMajorant sourcePhaseUpper
      ring

theorem sourcePhaseFailure_finite :
    ∀ᵐ θ ∂sourceAngleLaw, {s | θ ∈ sourcePhaseFailure s}.Finite := by
  apply ae_finite_setOfPred_mem
  apply ne_of_lt
  apply lt_of_le_of_lt (ENNReal.tsum_le_tsum sourcePhaseFailure_bound)
  rw [← ENNReal.ofReal_tsum_of_nonneg
    (fun s => by unfold sourcePhaseFailureMajorant sourceWidth; dsimp; positivity)
    sourcePhaseFailureMajorant_summable]
  exact ENNReal.ofReal_lt_top

theorem sourcePhaseMissSet_natAbs (s : ℕ) (k : ℤ) :
    sourcePhaseMissSet s (k.natAbs : ℤ) = sourcePhaseMissSet s k := by
  ext t
  simp only [sourcePhaseMissSet, Set.mem_ofPred_eq, threshold_middle_iff]
  rcases le_total 0 k with hp | hn
  · have he : (k.natAbs : ℤ) = k := by rw [Int.natCast_natAbs, abs_of_nonneg hp]
    rw [he]
  · have he : (k.natAbs : ℤ) = -k := by rw [Int.natCast_natAbs, abs_of_nonpos hn]
    rw [he, Int.cast_neg, neg_mul, fract_neg_middle_iff]

/-- Proposition phases, assertion 2, for all signed integer powers at every
sufficiently late stage on one probability-one event. -/
theorem sourceAngleLaw_second_phases : ∀ᵐ θ ∂sourceAngleLaw,
    ∀ᶠ s in atTop, ∀ k : ℤ, sourcePhaseLower s ≤ |(k : ℝ)| →
      |(k : ℝ)| ≤ sourcePhaseUpper s →
      (sourceBlockSize s : ℝ)/20 ≤
        (((sourceBlockCoordinates s).filter (fun i => θ i ∉ sourcePhaseMissSet s k)).card : ℝ) := by
  filter_upwards [sourcePhaseFailure_finite] with θ hθ
  have he : ∀ᶠ s in atTop, θ ∉ sourcePhaseFailure s := by
    apply Filter.eventually_atTop.mpr
    refine ⟨hθ.toFinset.sup id+1, ?_⟩
    intro s hs hm
    have hh := Finset.le_sup (f := id) (hθ.mem_toFinset.mpr hm)
    dsimp only [id] at hh
    omega
  filter_upwards [he] with s hs
  intro k hklo hkhi
  by_contra h
  have hcast : (k.natAbs : ℝ) = |(k : ℝ)| := by rw [← Int.cast_abs, ← Int.natCast_natAbs, Int.cast_natCast]
  have hnpos : 1 ≤ k.natAbs := by
    have hh : (0 : ℝ) < sourcePhaseLower s := by
      unfold sourcePhaseLower
      exact div_pos (mul_pos (sourceBlockSize_pos s) (sourceCutoff_pos s)) (by norm_num)
    have : (0 : ℝ) < k.natAbs := by rw [hcast]; exact hh.trans_le hklo
    exact_mod_cast this
  have hnupper : k.natAbs ≤ Nat.floor (sourcePhaseUpper s) := Nat.le_floor (by rwa [hcast])
  apply hs
  apply Set.mem_iUnion.mpr
  refine ⟨k.natAbs, Set.mem_iUnion.mpr ⟨Finset.mem_Icc.mpr ⟨hnpos, hnupper⟩, ?_⟩⟩
  rw [ite_eq_left (by rwa [hcast])]
  change (((sourceBlockCoordinates s).filter
    (fun i => θ i ∉ sourcePhaseMissSet s (k.natAbs : ℤ))).card : ℝ) < (sourceBlockSize s : ℝ)/20
  rw [sourcePhaseMissSet_natAbs]
  exact lt_of_not_ge h

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_CrossedProduct_PhaseCoverage
attribute [-instance] _root_.OAI.FiniteFactor.sourceBiasedRealMeasure_probability _root_.OAI.FiniteFactor.sourceFiniteReferenceKernel_markov _root_.OAI.FiniteFactor.sourceHilbert_separable _root_.OAI.FiniteFactor.sourceNormalFunctionalSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedGroup _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedSpace _root_.OAI.FiniteFactor.sourceResamplingKernel_markov _root_.OAI.FiniteFactor.sourceSamplingLambda_finite _root_.OAI.FiniteFactor.sourceSamplingSummand_finite _root_.OAI.FiniteFactor.sourceSamplingTorus_borel _root_.OAI.FiniteFactor.sourceSamplingTorus_compact _root_.OAI.FiniteFactor.sourceSamplingTrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingUntrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingWeightedMeasure_finite _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter Finset
open scoped ENNReal Topology Classical
noncomputable section

theorem sourceAngleLaw_second_phases_from :
    ∀ᵐ θ ∂sourceAngleLaw, ∃ j : ℕ, SourceSecondPhasesFrom θ j := by
  filter_upwards [sourceAngleLaw_second_phases] with θ hθ
  obtain ⟨j,hj⟩ := Filter.eventually_atTop.mp hθ
  refine ⟨j, fun s hs k hlo hhi => ?_⟩
  simpa [sourceQualifying, sourcePhaseMissSet] using hj s hs k hlo hhi

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_CrossedProduct_PreparedBase
attribute [-instance] _root_.OAI.FiniteFactor.sourceBiasedRealMeasure_probability _root_.OAI.FiniteFactor.sourceFiniteReferenceKernel_markov _root_.OAI.FiniteFactor.sourceNormalFunctionalSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedGroup _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedSpace _root_.OAI.FiniteFactor.sourceResamplingKernel_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped ENNReal Topology
noncomputable section

/-- One fixed realization supplies phases, rational independence, ordered
sampling and the actual nonzero quasinilpotent operator in its generated
algebra, before any candidate invariant projection. Factor and predual
properties are not included: they remain obligations about this algebra. -/
theorem exists_source_prepared_base : ∃ θ : SourceCoordinate → ℝ,
    SourceRationalIndependent θ ∧
    (∃ j : ℕ, SourceSecondPhasesFrom θ j) ∧
    SourceOrderedTorusSampling θ ∧
    (∀ k : ℤ, MeasurePreserving (coordinateRotate θ k) sourceSamplingHaar sourceSamplingHaar) ∧
    (∀ k : ℤ, k ≠ 0 → ∀ x, coordinateRotate θ k x ≠ x) ∧
    ∃ hθ : SourceAngles θ,
      let T := sourceOperator θ sourceLogWeight hθ.nonneg sourceLogWeight_nonneg
      T ∈ sourceAlgebra θ ∧ T ≠ 0 ∧ Function.Injective T ∧ ‖T‖ ≤ 1 ∧
        Tendsto (fun n : ℕ => ‖T^n‖^(1/(n : ℝ))) atTop (𝓝 0) := by
  have hall := sourceAngleLaw_admissible.and (sourceAngleLaw_rationalIndependent.and
    (sourceAngleLaw_second_phases_from.and sourceOrderedTorusSampling_event))
  obtain ⟨θ,ha,hr,hp,hs⟩ := hall.exists
  exact ⟨θ,hr,hp,hs,fun k => coordinateRotate_preserving θ k,
    fun k hk x => hr.rotation_free k hk x,ha,staged_sourceOperator_mem θ ha,
    staged_sourceOperator_properties θ ha⟩

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_CrossedProduct_PreparedFinite
attribute [-instance] _root_.OAI.FiniteFactor.sourceBiasedRealMeasure_probability _root_.OAI.FiniteFactor.sourceFiniteReferenceKernel_markov _root_.OAI.FiniteFactor.sourceNormalFunctionalSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedGroup _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedSpace _root_.OAI.FiniteFactor.sourceResamplingKernel_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped ENNReal Topology
noncomputable section

/-- One actual finite tracial source algebra, with the sampled rotation and
nonzero quasinilpotent operator. Scalar center, no minimal projections,
separable predual and the invariant-projection conclusion remain separate. -/
theorem exists_source_prepared_finite_oai : ∃ θ : SourceCoordinate → ℝ,
    SourceRationalIndependent θ ∧
    (∃ j : ℕ, SourceSecondPhasesFrom θ j) ∧
    SourceOrderedTorusSampling θ ∧
    (∀ k : ℤ, MeasurePreserving (coordinateRotate θ k) sourceSamplingHaar sourceSamplingHaar) ∧
    (∀ k : ℤ, k ≠ 0 → ∀ x, coordinateRotate θ k x ≠ x) ∧
    IsFiniteAlgebra (sourceAlgebra θ) ∧
    Nonempty (TracialRepresentation (sourceAlgebra θ)) ∧
    ∃ hθ : SourceAngles θ,
      let T := sourceOperator θ sourceLogWeight hθ.nonneg sourceLogWeight_nonneg
      T ∈ sourceAlgebra θ ∧ T ≠ 0 ∧ Function.Injective T ∧ ‖T‖ ≤ 1 ∧
        Tendsto (fun n : ℕ => ‖T^n‖^(1/(n : ℝ))) atTop (𝓝 0) := by
  obtain ⟨θ,hr,hp,hs,hm,hf,ho⟩ := exists_source_prepared_base
  exact ⟨θ,hr,hp,hs,hm,hf,sourceAlgebra_finite θ,⟨sourceTracialRepresentation θ⟩,ho⟩

end
end FiniteFactor

end OAI
end

theorem solution : type_of% @OAI.FiniteFactor.exists_source_prepared_finite_oai := @OAI.FiniteFactor.exists_source_prepared_finite_oai
