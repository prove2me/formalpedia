-- Prove2me | solution 1 for OAI.FiniteFactor.productBrown
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-25T22:24:47.731307+00:00
-- url     : https://prove2.me/submissions/f8b70619-79f0-43d9-a3ec-75fa5d80e1eb

import Mathlib
import Definitions.Def_ProductBrown
import Definitions.Def_OAIQ2Br000

section
-- module Solutions.OAIQ2_Brown.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : ¬p) :
    (if p then a else b) = b := if_neg h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ2_Brown.FiniteFactor_CrossedProduct_FloorSupport
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
-- module Solutions.OAIQ2_Brown.FiniteFactor_CrossedProduct_Cocycle
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
-- module Solutions.OAIQ2_Brown.FiniteFactor_CrossedProduct_Attenuation
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
-- module Solutions.OAIQ2_Brown.FiniteFactor_CrossedProduct_Operator
attribute [-instance] _root_.OAI.FiniteFactor.productHilbertNontrivial _root_.OAI.FiniteFactor.sourceCStar_closed _root_.OAI.FiniteFactor.sourceCStar_nontrivial
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
-- module Solutions.OAIQ2_Brown.FiniteFactor_Quasinilpotence
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
-- module Solutions.OAIQ2_Brown.FiniteFactor_CrossedProduct_Powers
attribute [-instance] _root_.OAI.FiniteFactor.productHilbertNontrivial _root_.OAI.FiniteFactor.sourceCStar_closed _root_.OAI.FiniteFactor.sourceCStar_nontrivial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped ENNReal Topology
noncomputable section

/-- Composition of the actual representative rotations. -/
theorem coordinateRotate_add {ι : Type*} (θ : ι → ℝ) (k n : ℤ) (x : ι → ℝ) :
    coordinateRotate θ n (coordinateRotate θ k x) = coordinateRotate θ (k+n) x := by
  funext i
  unfold coordinateRotate
  rw [Int.fract_eq_fract]
  refine ⟨-Int.floor (x i + (k : ℝ)*θ i), ?_⟩
  rw [Int.fract]
  push_cast
  ring

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
-- module Solutions.OAIQ2_Brown.FiniteFactor_CrossedProduct_Stages
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open Filter Finset
open scoped Topology
noncomputable section

theorem sourceStage_cutoff_growth (s : ℕ) :
    2*(sourceStageState s).K < (sourceStageState (s+1)).K := by
  have h := sourceNextCutoff_large (sourceStage s).m (sourceStage s).m_ge_100
  exact (Nat.mul_le_mul_left 2 (sourceStage s).m_ge_K).trans_lt h

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ2_Brown.FiniteFactor_CrossedProduct_StageOperator
attribute [-instance] _root_.OAI.FiniteFactor.productHilbertNontrivial _root_.OAI.FiniteFactor.sourceCStar_closed _root_.OAI.FiniteFactor.sourceCStar_nontrivial
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
-- module Solutions.OAIQ2_Brown.FiniteFactor_CrossedProduct_VacuumFunctional
attribute [-instance] _root_.OAI.FiniteFactor.productHilbertNontrivial _root_.OAI.FiniteFactor.sourceCStar_closed _root_.OAI.FiniteFactor.sourceCStar_nontrivial
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

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ2_Brown.BrownMeasure_Mercator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Filter
open scoped Topology
namespace BrownLog
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A] [NormOneClass A]

lemma inv_nat_succ_le_one (n : ℕ) : |(n+1 : ℝ)⁻¹|≤1 := by
  rw [abs_of_pos (inv_pos.mpr (by positivity))]
  exact (inv_le_one₀ (by positivity)).mpr (by linarith [Nat.cast_nonneg (α:=ℝ) n])

lemma mercator_summable {a : A} (ha : ‖a‖<1) :
    Summable (fun n : ℕ=>((n+1 : ℝ)⁻¹) • a^(n+1)) := by
  apply (summable_geometric_of_lt_one (norm_nonneg a) ha).mul_right ‖a‖ |>.of_norm_bounded
  intro n
  rw [norm_smul,Real.norm_eq_abs]
  calc
    _ ≤ 1*‖a^(n+1)‖ := mul_le_mul_of_nonneg_right (inv_nat_succ_le_one n) (norm_nonneg _)
    _ ≤ ‖a‖^n*‖a‖ := by simpa [pow_succ] using norm_pow_le a (n+1)

variable (τ : A →L[ℝ] ℝ) (hτ : ∀ a b,τ (a*b)=τ (b*a))

omit [CompleteSpace A] [NormOneClass A] in
include hτ in
lemma trace_pow_deriv {f : ℝ → A} {d : A} {x : ℝ} (hf : HasDerivAt f d x) (n : ℕ) :
    HasDerivAt (fun t=>τ (f t^(n+1))) (((n+1:ℝ))*τ (f x^n*d)) x := by
  have hd := τ.hasFDerivAt.comp_hasDerivAt x (hf.fun_pow' (n+1))
  have hsum : τ (∑ i ∈ Finset.range (n+1),f x ^ ((n+1).pred-i)*d*f x^i)=
      ((n+1:ℝ))*τ (f x^n*d) := by
    rw [map_sum]
    have he (i : ℕ) (hi : i∈Finset.range (n+1)) :
        τ (f x ^ ((n+1).pred-i)*d*f x^i)=τ (f x^n*d) := by
      rw [hτ _ (f x^i),← mul_assoc,← pow_add]
      have hi' : i≤n := by simpa only [Finset.mem_range,Nat.lt_succ_iff] using hi
      simp [Nat.add_sub_of_le hi']
    simp_rw [Finset.sum_congr rfl he]
    simp
  simpa only [Function.comp_def,hsum] using hd

lemma trace_mercator_hasSum {a : A} (ha : ‖a‖<1) :
    HasSum (fun n : ℕ=>-((n+1 : ℝ)⁻¹)*τ (a^(n+1))) (τ (mercator a)) := by
  have h := (τ.hasSum (mercator_summable ha).hasSum).neg
  simpa [mercator,map_neg,map_smul,smul_eq_mul] using h
end BrownLog
end

end OAI
end

section
-- module Solutions.OAIQ2_Brown.BrownMeasure_MercatorCalculus
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Filter
open scoped Topology
namespace BrownLog
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A] [NormOneClass A] [Nontrivial A]
  [StarRing A] [IsometricContinuousFunctionalCalculus ℝ A IsSelfAdjoint]

lemma mercator_eq_cfc_log_one_sub {a : A} (ha : IsSelfAdjoint a) (hn : ‖a‖<1) :
    mercator a=CFC.log (1-a) := by
  let : CompactSpace (spectrum ℝ a) := isCompact_iff_compactSpace.mp (spectrum.isCompact a)
  let : Nonempty (spectrum ℝ a) := (ContinuousFunctionalCalculus.spectrum_nonempty a ha).to_subtype
  let X : C(spectrum ℝ a,ℝ) := (ContinuousMap.id ℝ).restrict (spectrum ℝ a)
  have hX : ‖X‖<1 := by
    apply lt_of_le_of_lt ?_ hn
    apply (X.norm_le (norm_nonneg a)).mpr
    intro x
    exact spectrum.norm_le_norm_of_mem x.property
  let L : C(spectrum ℝ a,ℝ) →L[ℝ] A :=
    { toLinearMap := (cfcHom ha).toLinearMap, cont := cfcHom_continuous ha }
  have hXa : L X=a := cfcHom_id ha
  have hLX (n : ℕ) : L (((n+1:ℝ)⁻¹) • X^(n+1))=((n+1:ℝ)⁻¹) • a^(n+1) := by
    rw [map_smul]
    change ((n+1:ℝ)⁻¹) • (cfcHom ha) (X^(n+1))=_
    rw [map_pow]
    exact congrArg (fun z:A=>((n+1:ℝ)⁻¹) • z^(n+1)) hXa
  have hML : L (mercator X)=mercator a := by
    unfold mercator
    rw [map_neg,L.map_tsum (mercator_summable hX)]
    simp_rw [hLX]
  have hx1 (x : spectrum ℝ a) : |(x:ℝ)|<1 :=
    lt_of_le_of_lt (spectrum.norm_le_norm_of_mem x.property) hn
  have hxne (x : spectrum ℝ a) : 1-(x:ℝ)≠0 := by
    have := (abs_lt.mp (hx1 x)).2
    linarith
  let g : C(spectrum ℝ a,ℝ) :=
    ⟨fun x=>Real.log (1-(x:ℝ)),(continuous_const.sub continuous_subtype_val).log hxne⟩
  have hMg : mercator X=g := by
    apply ContinuousMap.ext
    intro x
    have h := (ContinuousMap.evalCLM ℝ x).hasSum (mercator_summable hX).hasSum
    have hv := Real.hasSum_pow_div_log_of_abs_lt_one (hx1 x)
    have he : (∑' n:ℕ,((n+1:ℝ)⁻¹) • X^(n+1)) x= -Real.log (1-(x:ℝ)) := by
      apply HasSum.unique ?_ hv
      simpa [X,smul_eq_mul,div_eq_mul_inv,mul_comm] using h
    change -(∑' n:ℕ,((n+1:ℝ)⁻¹) • X^(n+1)) x=_
    rw [he,neg_neg]
    rfl
  rw [← hML,hMg]
  change (cfcHom ha) g=CFC.log (1-a)
  have hcont : ContinuousOn (fun t:ℝ=>Real.log (1-t)) (spectrum ℝ a) := by
    exact continuousOn_iff_continuous_domRestrict.mpr g.continuous
  have hc1 : cfc (fun x:ℝ=>1-x) a=1-a := by
    rw [cfc_sub _ _ a (by fun_prop) (by fun_prop),cfc_const 1 a ha,cfc_id' ℝ a ha]
    simp
  rw [CFC.log,← hc1,← cfc_comp Real.log (fun x:ℝ=>1-x) a ha (by
    rintro _ ⟨x,hx,rfl⟩
    exact Real.continuousAt_log (hxne ⟨x,hx⟩) |>.continuousWithinAt) (by fun_prop)]
  exact (cfc_apply (fun x:ℝ=>Real.log (1-x)) a ha hcont).symm
end BrownLog
end

end OAI
end

section
-- module Solutions.OAIQ2_Brown.BrownMeasure_TraceDerivative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Filter
open scoped Topology Ring
namespace BrownLog
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A] [NormOneClass A]
variable (τ : A →L[ℝ] ℝ) (hτ : ∀ a b,τ (a*b)=τ (b*a))

include hτ in
lemma trace_mercator_deriv_of_bounds
    {f d : ℝ → A} {s : Set ℝ} {x r D : ℝ}
    (hs : IsOpen s) (hsp : IsPreconnected s) (hx : x∈s)
    (hr0 : 0≤r) (hr1 : r<1) (_hD : 0≤D)
    (hf : ∀ t∈s, HasDerivAt f (d t) t)
    (hfn : ∀ t∈s,‖f t‖≤r) (hdn : ∀ t∈s,‖d t‖≤D) :
    HasDerivAt (fun t=>τ (mercator (f t))) (-τ ((1-f x)⁻¹ʳ*d x)) x := by
  let g : ℕ → ℝ → ℝ := fun n t=>-((n+1:ℝ)⁻¹)*τ (f t^(n+1))
  let g' : ℕ → ℝ → ℝ := fun n t=>-τ (f t^n*d t)
  have hg (n : ℕ) (t : ℝ) (ht : t∈s) : HasDerivAt (g n) (g' n t) t := by
    have hd := (trace_pow_deriv τ hτ (hf t ht) n).const_mul (-((n+1:ℝ)⁻¹))
    have he : -((n+1:ℝ)⁻¹)*((n+1:ℝ)*τ (f t^n*d t))= -τ (f t^n*d t) := by
      field_simp
    simpa only [g,g',he] using hd
  have hgn (n : ℕ) (t : ℝ) (ht : t∈s) : ‖g' n t‖≤r^n*(‖τ‖*D) := by
    dsimp [g']
    rw [abs_neg]
    calc
      _ ≤ ‖τ‖*‖f t^n*d t‖ := τ.le_opNorm _
      _ ≤ ‖τ‖*(‖f t‖^n*‖d t‖) := by
        gcongr
        exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_pow_le _ _) (norm_nonneg _))
      _ ≤ ‖τ‖*(r^n*D) := by gcongr; exact hfn t ht; exact hdn t ht
      _ = r^n*(‖τ‖*D) := by ring
  have h0 : Summable (fun n=>g n x) :=
    (trace_mercator_hasSum τ ((hfn x hx).trans_lt hr1)).summable
  have hder := hasDerivAt_tsum_of_isPreconnected
    ((summable_geometric_of_lt_one hr0 hr1).mul_right (‖τ‖*D)) hs hsp hg hgn hx h0 hx
  have hsD := (hasSum_geom_series_inverse (f x) ((hfn x hx).trans_lt hr1)).mul_right (d x)
  have hsd : HasSum (fun n=>g' n x) (-τ ((1-f x)⁻¹ʳ*d x)) := by
    simpa [g'] using (τ.hasSum hsD).neg
  rw [hsd.tsum_eq] at hder
  apply hder.congr_of_eventuallyEq
  filter_upwards [hs.mem_nhds hx] with t ht
  exact (trace_mercator_hasSum τ ((hfn t ht).trans_lt hr1)).tsum_eq.symm
end BrownLog
end

end OAI
end

section
-- module Solutions.OAIQ2_Brown.BrownMeasure_LogDerivative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Filter
open scoped Topology Ring
namespace BrownLog
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A] [NormOneClass A] [Nontrivial A]
  [StarRing A] [StarModule ℝ A] [IsometricContinuousFunctionalCalculus ℝ A IsSelfAdjoint]

omit [Nontrivial A] [StarModule ℝ A] in
lemma exists_smul_close_one {b : A} (hb : IsSelfAdjoint b)
    (hp : ∀ y∈spectrum ℝ b,0<y) : ∃ c : ℝ,0<c ∧ ‖1-c•b‖<1 := by
  let c : ℝ := (‖b‖+1)⁻¹
  have hc : 0<c := inv_pos.mpr (by positivity)
  refine ⟨c,hc,?_⟩
  have he : cfc (fun y:ℝ=>1-c*y) b=1-c•b := by
    rw [cfc_sub _ _ b (by fun_prop) (by fun_prop),cfc_const 1 b hb]
    change (algebraMap ℝ A) 1-cfc (fun y:ℝ=>c•y) b=_
    rw [cfc_smul_id c b hb,map_one]
  rw [← he]
  apply norm_cfc_lt zero_lt_one
  intro y hy
  have hy0 := hp y hy
  have hyb : y≤‖b‖ := (le_abs_self y).trans (spectrum.norm_le_norm_of_mem hy)
  have hcy : c*y<1 := by
    dsimp [c]
    rw [inv_mul_lt_iff₀ (by positivity)]
    linarith
  rw [Real.norm_eq_abs,abs_lt]
  constructor <;> nlinarith [mul_pos hc hy0]

variable (τ : A →L[ℝ] ℝ) (hτ : ∀ a b,τ (a*b)=τ (b*a))
include hτ in
lemma trace_log_hasDerivAt {b d : ℝ → A} {x : ℝ}
    (hb : ∀t,IsSelfAdjoint (b t)) (hp : ∀t y,y∈spectrum ℝ (b t) → 0<y)
    (hf : ∀t,HasDerivAt b (d t) t) (hd : ContinuousAt d x) :
    HasDerivAt (fun t=>τ (CFC.log (b t))) (τ ((b x)⁻¹ʳ*d x)) x := by
  obtain ⟨c,hc,hcn⟩ := exists_smul_close_one (hb x) (hp x)
  let f : ℝ → A := fun t=>1-c•b t
  let df : ℝ → A := fun t=>-c•d t
  have hdf (t : ℝ) : HasDerivAt f (df t) t := by
    simpa [f,df,neg_smul] using ((hf t).fun_const_smul c).const_sub (1:A)
  let r : ℝ := (‖f x‖+1)/2
  let D : ℝ := ‖df x‖+1
  have hr0 : 0≤r := by dsimp [r]; positivity
  have hr1 : r<1 := by change (‖1-c•b x‖+1)/2<1; linarith
  have hDr : 0≤D := by dsimp [D]; positivity
  have hn : ∀ᶠ t in 𝓝 x,‖f t‖<r ∧ ‖df t‖<D := by
    apply Filter.Eventually.and
    · apply (hdf x).continuousAt.norm.eventually_lt continuousAt_const
      change ‖1-c•b x‖<(‖1-c•b x‖+1)/2
      linarith
    · apply (hd.const_smul (-c)).norm.eventually_lt continuousAt_const
      exact lt_add_one _
  obtain ⟨ε,hε,hball⟩ := Metric.mem_nhds_iff.mp hn
  have H := trace_mercator_deriv_of_bounds τ hτ (s:=Metric.ball x ε)
    Metric.isOpen_ball (convex_ball x ε).isPreconnected (Metric.mem_ball_self hε)
    hr0 hr1 hDr (fun t _=>hdf t) (fun t ht=>(hball ht).1.le) (fun t ht=>(hball ht).2.le)
  have he (t : ℝ) (ht : t∈Metric.ball x ε) :
      τ (mercator (f t))=τ (algebraMap ℝ A (Real.log c))+τ (CFC.log (b t)) := by
    rw [mercator_eq_cfc_log_one_sub ((IsSelfAdjoint.one A).sub ((isSelfAdjoint_iff.mpr rfl).smul (hb t))) ((hball ht).1.trans hr1)]
    have he : 1-f t=c•b t := by dsimp [f]; abel
    rw [he,CFC.log_smul (b t) (fun y hy=>(hp t y hy).ne') hc.ne' (hb t),map_add]
  have hi : IsUnit (c•b x) := by
    have hu : IsUnit (b x) := spectrum.isUnit_of_zero_notMem ℝ (fun h=>(hp x 0 h).false)
    rw [Algebra.smul_def]
    exact ((isUnit_iff_ne_zero.mpr hc.ne').map (algebraMap ℝ A)).mul hu
  have hv : (1-f x)⁻¹ʳ*df x= -((b x)⁻¹ʳ*d x) := by
    have he : 1-f x=c•b x := by dsimp [f]; abel
    rw [he,Ring.inverse_mul_eq_iff_eq_mul _ _ _ hi]
    dsimp [df]
    simp only [mul_neg,smul_mul_assoc]
    rw [Ring.mul_inverse_cancel_left _ _ (spectrum.isUnit_of_zero_notMem ℝ (fun h=>(hp x 0 h).false))]
    exact neg_smul c (d x)
  rw [hv,map_neg,neg_neg] at H
  have H' := H.sub_const (τ (algebraMap ℝ A (Real.log c)))
  apply H'.congr_of_eventuallyEq
  filter_upwards [Metric.ball_mem_nhds x hε] with t ht
  rw [he t ht]
  ring
end BrownLog
end

end OAI
end

section
-- module Solutions.OAIQ2_Brown.BrownMeasure_RootSeries
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Filter
open scoped Topology Ring
namespace BrownLog
variable {A : Type*} [NormedRing A] [CompleteSpace A]
lemma summable_pow_of_root_tendsto (a : A)
    (ha : Tendsto (fun n:ℕ=>‖a^n‖^(1/(n:ℝ))) atTop (𝓝 0)) : Summable (fun n:ℕ=>a^n) := by
  have he : ∀ᶠ n : ℕ in atTop,0<n ∧ ‖a^n‖^(1/(n:ℝ))≤(1/2:ℝ) := by
    filter_upwards [eventually_gt_atTop 0,ha.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1/2))] with n hn h
    exact ⟨hn,h.le⟩
  apply (summable_geometric_of_lt_one (by norm_num : (0:ℝ)≤1/2) (by norm_num : (1/2:ℝ)<1)).of_norm_bounded_eventually_nat
  filter_upwards [he] with n hn
  have h := pow_le_pow_left₀ (Real.rpow_nonneg (norm_nonneg _) _) hn.2 n
  have hi : (‖a^n‖^(1/(n:ℝ)))^n=‖a^n‖ := by
    rw [← Real.rpow_natCast,← Real.rpow_mul (norm_nonneg _)]
    rw [one_div_mul_cancel (by exact_mod_cast hn.1.ne'),Real.rpow_one]
  rwa [hi] at h

omit [CompleteSpace A] in
lemma norm_root_smul_tendsto {𝕜 : Type*} [RCLike 𝕜] [NormedAlgebra 𝕜 A]
    (a : A) (c : 𝕜) (ha : Tendsto (fun n:ℕ=>‖a^n‖^(1/(n:ℝ))) atTop (𝓝 0)) :
    Tendsto (fun n:ℕ=>‖(c•a)^n‖^(1/(n:ℝ))) atTop (𝓝 0) := by
  have hc := ha.const_mul ‖c‖
  simp only [mul_zero] at hc
  apply hc.congr'
  filter_upwards [eventually_gt_atTop 0] with n hn
  rw [smul_pow,norm_smul,norm_pow c n,Real.mul_rpow (by positivity) (norm_nonneg _)]
  rw [← Real.rpow_natCast,← Real.rpow_mul (norm_nonneg c)]
  rw [mul_one_div_cancel (by exact_mod_cast hn.ne'),Real.rpow_one]

omit [CompleteSpace A] in
lemma inverse_one_sub_eq_tsum (a : A) (ha : Summable (fun n:ℕ=>a^n)) :
    IsUnit (1-a) ∧ (1-a)⁻¹ʳ=∑' n:ℕ,a^n := by
  let u : Aˣ := ⟨1-a,∑' n:ℕ,a^n,ha.one_sub_mul_tsum_pow,ha.tsum_pow_mul_one_sub⟩
  refine ⟨u.isUnit,?_⟩
  change (↑u:A)⁻¹ʳ=(↑u⁻¹:A)
  exact Ring.inverse_unit u
end BrownLog
end

end OAI
end

section
-- module Solutions.OAIQ2_Brown.BrownMeasure_Quasinilpotent
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Filter
open scoped Topology Ring
namespace BrownLog
variable {A : Type*} [CStarAlgebra A] [Nontrivial A]
local instance instIsometricContinuousFunctionalCalculusRealIsSelfAdjoint_solutions : IsometricContinuousFunctionalCalculus ℝ A IsSelfAdjoint :=
  IsSelfAdjoint.instIsometricContinuousFunctionalCalculus
variable (τ : A →L[ℝ] ℝ) (hτ : ∀a b,τ (a*b)=τ (b*a)) (hstar : ∀a,τ (star a)=τ a)

omit [Nontrivial A] in
include hτ hstar in
lemma trace_inverse_square_deriv (a d : A) (hu : IsUnit a) :
    τ ((star a*a)⁻¹ʳ*(star d*a+star a*d))=2*τ (a⁻¹ʳ*d) := by
  rw [Ring.inverse_mul (Or.inl hu.star),mul_add,map_add]
  have h1 : τ ((a⁻¹ʳ*(star a)⁻¹ʳ)*(star d*a))=τ (a⁻¹ʳ*d) := by
    rw [← mul_assoc,hτ _ a]
    rw [← mul_assoc,← mul_assoc,Ring.mul_inverse_cancel a hu,one_mul,Ring.inverse_star]
    rw [← star_mul,hstar,hτ]
  have h2 : (a⁻¹ʳ*(star a)⁻¹ʳ)*(star a*d)=a⁻¹ʳ*d := by
    calc
      _ = a⁻¹ʳ*((star a)⁻¹ʳ*star a)*d := by simp only [mul_assoc]
      _ = _ := by rw [Ring.inverse_mul_cancel _ hu.star,mul_one]
  rw [h1,h2]
  ring

omit [Nontrivial A] in
lemma trace_resolvent_mul_zero (S : A)
    (hQ : Tendsto (fun n:ℕ=>‖S^n‖^(1/(n:ℝ))) atTop (𝓝 0))
    (hzero : ∀n:ℕ,τ (S^(n+1))=0) (t : ℝ) : τ ((1-t•S)⁻¹ʳ*S)=0 := by
  have hs := summable_pow_of_root_tendsto (t•S) (norm_root_smul_tendsto S t hQ)
  rw [(inverse_one_sub_eq_tsum _ hs).2,← hs.tsum_mul_right,τ.map_tsum (hs.mul_right S)]
  have he (n : ℕ) : τ ((t•S)^n*S)=0 := by
    rw [smul_pow,smul_mul_assoc,← pow_succ,map_smul,hzero,smul_zero]
  simp_rw [he]
  exact tsum_zero

include hτ hstar in
lemma trace_log_square_one_sub_eq_zero (S : A)
    (hQ : Tendsto (fun n:ℕ=>‖S^n‖^(1/(n:ℝ))) atTop (𝓝 0))
    (hzero : ∀n:ℕ,τ (S^(n+1))=0) : τ (CFC.log (star (1-S)*(1-S)))=0 := by
  let a : ℝ → A := fun t=>1-t•S
  let b : ℝ → A := fun t=>star (a t)*a t
  let d : ℝ → A := fun t=>star (-S)*a t+star (a t)*(-S)
  have ha (t : ℝ) : HasDerivAt a (-S) t := by
    simpa only [a,id_eq,one_smul] using ((hasDerivAt_id t).smul_const S).const_sub (1:A)
  have hb (t : ℝ) : IsSelfAdjoint (b t) := by
    exact isSelfAdjoint_iff.mpr (by simp [b,star_mul])
  have hu (t : ℝ) : IsUnit (a t) :=
    (inverse_one_sub_eq_tsum _ (summable_pow_of_root_tendsto _ (norm_root_smul_tendsto S t hQ))).1
  have hp (t y : ℝ) (hy : y∈spectrum ℝ (b t)) : 0<y := by
    have hnn : 0≤y := spectrum_star_mul_self_nonneg y hy
    refine hnn.lt_of_ne ?_
    intro he
    have hn := spectrum.zero_notMem ℝ ((hu t).star.mul (hu t))
    exact hn (he ▸ hy)
  have hdf (t : ℝ) : HasDerivAt b (d t) t := (ha t).star.fun_mul (ha t)
  have hc : Continuous d := by
    have hca : Continuous a := continuous_const.sub (continuous_id.smul continuous_const)
    exact (continuous_const.mul hca).add (hca.star.mul continuous_const)
  have hd0 (t : ℝ) : HasDerivAt (fun t=>τ (CFC.log (b t))) 0 t := by
    have hd := trace_log_hasDerivAt τ hτ (x:=t) hb hp hdf hc.continuousAt
    have he : τ ((b t)⁻¹ʳ*d t)=0 := by
      rw [trace_inverse_square_deriv τ hτ hstar _ _ (hu t),mul_neg,map_neg]
      rw [trace_resolvent_mul_zero τ S hQ hzero t]
      ring
    rwa [he] at hd
  have he := is_const_of_deriv_eq_zero (fun t=>(hd0 t).differentiableAt) (fun t=>(hd0 t).deriv) (1:ℝ) 0
  simpa [b,a,CFC.log_one] using he
end BrownLog
end

end OAI
end

section
-- module Solutions.OAIQ2_Brown.FiniteFactor_CrossedProduct_MultiplicationAdjoint
attribute [-instance] _root_.OAI.FiniteFactor.productHilbertNontrivial _root_.OAI.FiniteFactor.sourceCStar_closed _root_.OAI.FiniteFactor.sourceCStar_nontrivial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped ENNReal ComplexConjugate
noncomputable section

/-- Any two such multiplication operators commute, even for different angles. -/
theorem sourcePi_commute (θ φ : SourceCoordinate → ℝ) (g h : SourceBaseFunction) :
    sourcePi θ g * sourcePi φ h = sourcePi φ h * sourcePi θ g := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards [sourcePi_apply_ae θ g (sourcePi φ h f),
    sourcePi_apply_ae φ h f, sourcePi_apply_ae φ h (sourcePi θ g f),
    sourcePi_apply_ae θ g f] with z hg hh hg' hh'
  change (sourcePi θ g (sourcePi φ h f)) z = (sourcePi φ h (sourcePi θ g f)) z
  rw [hg, hh, hg', hh']
  ring

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ2_Brown.FiniteFactor_CrossedProduct_Transport
attribute [-instance] _root_.OAI.FiniteFactor.productHilbertNontrivial _root_.OAI.FiniteFactor.sourceCStar_closed _root_.OAI.FiniteFactor.sourceCStar_nontrivial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
noncomputable section

theorem sourceTransport_apply_ae (θ : SourceCoordinate → ℝ) (n m : ℤ)
    (f : SourceHilbert SourceCoordinate) :
    sourceTransport θ n m f =ᵐ[sourceMeasure SourceCoordinate]
      fun z => f (sourceTransportIndex θ n m z) :=
  Lp.coeFn_compMeasurePreserving f (sourceTransportIndex_preserving θ n m)

theorem sourceTransport_mul (θ : SourceCoordinate → ℝ) (n m p q : ℤ) :
    sourceTransport θ n m * sourceTransport θ p q = sourceTransport θ (n+p) (m+q) := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  have ht := (sourceTransportIndex_preserving θ n m).quasiMeasurePreserving.ae
    (sourceTransport_apply_ae θ p q f)
  filter_upwards [sourceTransport_apply_ae θ n m (sourceTransport θ p q f),
    sourceTransport_apply_ae θ (n+p) (m+q) f, ht] with z h1 h2 h3
  change (sourceTransport θ n m (sourceTransport θ p q f)) z = _
  rw [h1, h2, h3]
  congr 1
  simp [sourceTransportIndex, coordinateRotate_add, sub_sub]

theorem sourceHilbert_cube : ∀ᵐ z ∂sourceMeasure SourceCoordinate,
    ∀ i, z.1 i ∈ Set.Ico (0 : ℝ) 1 := by
  have hc : ∀ᵐ x ∂Measure.infinitePi (fun _ : SourceCoordinate => unitIntervalMeasure),
      ∀ i, x i ∈ Set.Ico (0 : ℝ) 1 := by
    rw [ae_all_iff]
    intro i
    have hh : ∀ᵐ t ∂(Measure.infinitePi (fun _ : SourceCoordinate => unitIntervalMeasure)).map
        (fun x => x i), t ∈ Set.Ico (0 : ℝ) 1 := by
      rw [Measure.infinitePi_map_eval]
      exact ae_restrict_mem measurableSet_Ico
    exact (ae_map_iff (measurable_pi_apply i).aemeasurable measurableSet_Ico).mp hh
  exact Measure.quasiMeasurePreserving_fst.ae hc

theorem sourceTransport_zero (θ : SourceCoordinate → ℝ) : sourceTransport θ 0 0 = 1 := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards [sourceTransport_apply_ae θ 0 0 f, sourceHilbert_cube] with z hz hc
  change (sourceTransport θ 0 0 f) z = f z
  rw [hz]
  congr 1
  apply Prod.ext
  · funext i
    simpa [sourceTransportIndex, coordinateRotate] using Int.fract_eq_self.mpr (hc i)
  · simp [sourceTransportIndex]

theorem sourceTransport_star (θ : SourceCoordinate → ℝ) (n m : ℤ) :
    star (sourceTransport θ n m) = sourceTransport θ (-n) (-m) := by
  have hi (f h : SourceHilbert SourceCoordinate) :
      inner ℂ (sourceTransport θ n m f) (sourceTransport θ n m h) = inner ℂ f h :=
    (Lp.compMeasurePreservingₗᵢ ℂ (sourceTransportIndex θ n m)
      (sourceTransportIndex_preserving θ n m)).inner_map_map f h
  have hinv : sourceTransport θ n m * sourceTransport θ (-n) (-m) = 1 := by
    rw [sourceTransport_mul]; simp only [add_neg_cancel, sourceTransport_zero]
  rw [ContinuousLinearMap.star_eq_adjoint]
  symm
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro f h
  have hih := hi (sourceTransport θ (-n) (-m) f) h
  have he : sourceTransport θ n m (sourceTransport θ (-n) (-m) f) = f := by
    change (sourceTransport θ n m * sourceTransport θ (-n) (-m)) f = f
    rw [hinv]; rfl
  rw [he] at hih
  exact hih.symm

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ2_Brown.FiniteFactor_CrossedProduct_Reflection
attribute [-instance] _root_.OAI.FiniteFactor.productHilbertNontrivial _root_.OAI.FiniteFactor.sourceCStar_closed _root_.OAI.FiniteFactor.sourceCStar_nontrivial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped ComplexConjugate
noncomputable section

theorem sourceConjugation_apply_ae (θ : SourceCoordinate → ℝ) (f : SourceHilbert SourceCoordinate) :
    sourceConjugation θ f =ᵐ[sourceMeasure SourceCoordinate]
      fun z => star (f (sourceReflectionIndex θ z)) := by
  filter_upwards [Lp.coeFn_star (sourceReflectionLinear θ f),
    Lp.coeFn_compMeasurePreserving f (sourceReflectionIndex_preserving θ)] with z hs hr
  change (star (sourceReflectionLinear θ f)) z = _
  rw [hs]
  change star ((sourceReflectionLinear θ f) z) = _
  change (sourceReflectionLinear θ f) z = f (sourceReflectionIndex θ z) at hr
  rw [hr]

theorem sourceConjugation_involutive (θ : SourceCoordinate → ℝ) (f : SourceHilbert SourceCoordinate) :
    sourceConjugation θ (sourceConjugation θ f) = f := by
  apply Lp.ext
  have ht := (sourceReflectionIndex_preserving θ).quasiMeasurePreserving.ae (sourceConjugation_apply_ae θ f)
  filter_upwards [sourceConjugation_apply_ae θ (sourceConjugation θ f), ht, sourceHilbert_cube] with z h1 h2 hc
  rw [h1,h2,star_star]
  congr 1
  apply Prod.ext
  · change coordinateRotate θ (-z.2) (coordinateRotate θ z.2 z.1) = z.1
    rw [coordinateRotate_add, add_neg_cancel]
    funext i
    simpa [coordinateRotate] using Int.fract_eq_self.mpr (hc i)
  · simp [sourceReflectionIndex]

theorem sourceL2_star_inner (f g : SourceHilbert SourceCoordinate) :
    inner ℂ (star f) (star g) = star (inner ℂ f g) := by
  rw [L2.inner_def, L2.inner_def]
  change _ = conj (∫ z, inner ℂ (f z) (g z) ∂sourceMeasure SourceCoordinate)
  rw [← integral_conj]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_star f, Lp.coeFn_star g] with z hf hg
  rw [hf,hg]
  simp [RCLike.inner_apply, mul_comm]

theorem sourceConjugation_inner (θ : SourceCoordinate → ℝ) (f g : SourceHilbert SourceCoordinate) :
    inner ℂ (sourceConjugation θ f) (sourceConjugation θ g) = star (inner ℂ f g) := by
  rw [sourceConjugation, sourceConjugation, sourceL2_star_inner,
    (sourceReflectionLinear θ).inner_map_map]

theorem sourceConjugation_inner_symm (θ : SourceCoordinate → ℝ) (f g : SourceHilbert SourceCoordinate) :
    inner ℂ f (sourceConjugation θ g) = inner ℂ g (sourceConjugation θ f) := by
  have hh := sourceConjugation_inner θ (sourceConjugation θ f) g
  rw [sourceConjugation_involutive] at hh
  rw [hh]
  exact inner_conj_symm _ _

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ2_Brown.FiniteFactor_CrossedProduct_ScalarCommutant
attribute [-instance] _root_.OAI.FiniteFactor.productHilbertNontrivial _root_.OAI.FiniteFactor.sourceCStar_closed _root_.OAI.FiniteFactor.sourceCStar_nontrivial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
noncomputable section

theorem sourceScalar_star (g : SourceBaseFunction) :
    star (sourceScalar g) = sourceScalar (sourceBaseStar g) :=
  sourcePi_star _ _

theorem sourceShift_apply_ae (f : SourceHilbert SourceCoordinate) :
    sourceShift SourceCoordinate f =ᵐ[sourceMeasure SourceCoordinate]
      fun z => f (sourceShiftIndex z) :=
  Lp.coeFn_compMeasurePreserving f (sourceShiftIndex_preserving _)

theorem sourceScalar_shift_commute (g : SourceBaseFunction) :
    sourceScalar g * sourceShift SourceCoordinate =
      sourceShift SourceCoordinate * sourceScalar g := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  have hg := (sourceShiftIndex_preserving SourceCoordinate).quasiMeasurePreserving.ae
    (sourcePi_apply_ae (fun _ => 0) g f)
  filter_upwards [sourcePi_apply_ae (fun _ => 0) g (sourceShift SourceCoordinate f),
    sourceShift_apply_ae f, sourceShift_apply_ae (sourceScalar g f), hg] with z h1 h2 h3 h4
  change (sourcePi (fun _ => 0) g (sourceShift SourceCoordinate f)) z =
    (sourceShift SourceCoordinate (sourceScalar g f)) z
  rw [h1, h2, h3]
  change _ = (sourcePi (fun _ => 0) g f) (sourceShiftIndex z)
  rw [h4]
  have he : sourcePiSymbol (fun _ => 0) g z =
      sourcePiSymbol (fun _ => 0) g (sourceShiftIndex z) := by
    unfold sourcePiSymbol
    congr 1
    funext i
    simp [coordinateRotate, sourceShiftIndex]
  rw [he]

/-- The scalar multipliers commute with the generators and their adjoints. -/
theorem sourceScalar_mem_generator_commutant (θ : SourceCoordinate → ℝ)
    (g : SourceBaseFunction) :
    sourceScalar g ∈ StarSubalgebra.centralizer ℂ
      ({sourceShift SourceCoordinate} ∪ Set.range (sourcePi θ)) := by
  apply (StarSubalgebra.mem_centralizer_iff ℂ).mpr
  intro A hA
  rcases hA with hA | ⟨h, rfl⟩
  · obtain rfl : A = sourceShift SourceCoordinate := hA
    refine ⟨(sourceScalar_shift_commute g).symm, ?_⟩
    have hs := congrArg star (sourceScalar_shift_commute (sourceBaseStar g))
    have hg : star (sourceScalar (sourceBaseStar g)) = sourceScalar g := by
      rw [← sourceScalar_star, star_star]
    simpa only [star_mul, hg] using hs
  · exact ⟨sourcePi_commute θ _ h g, by
      rw [sourcePi_star]
      exact sourcePi_commute θ _ (sourceBaseStar h) g⟩

/-- The commutation holds for every element of the actual double commutant. -/
theorem sourceAlgebra_commutes_scalar (θ : SourceCoordinate → ℝ)
    {H : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate}
    (hH : H ∈ sourceAlgebra θ) (g : SourceBaseFunction) :
    sourceScalar g * H = H * sourceScalar g := by
  change H ∈ StarSubalgebra.centralizer ℂ
    (StarSubalgebra.centralizer ℂ
      ({sourceShift SourceCoordinate} ∪ Set.range (sourcePi θ))) at hH
  exact ((StarSubalgebra.mem_centralizer_iff ℂ).mp hH _
    (sourceScalar_mem_generator_commutant θ g)).1

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ2_Brown.FiniteFactor_CrossedProduct_RotationCommutant
attribute [-instance] _root_.OAI.FiniteFactor.productHilbertNontrivial _root_.OAI.FiniteFactor.sourceCStar_closed _root_.OAI.FiniteFactor.sourceCStar_nontrivial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
noncomputable section

theorem sourceCommutantRotation_star (θ : SourceCoordinate → ℝ) (n : ℤ) :
    star (sourceCommutantRotation θ n) = sourceCommutantRotation θ (-n) :=
  sourceTransport_star θ n n

theorem sourceCommutantRotation_pi (θ : SourceCoordinate → ℝ) (n : ℤ)
    (g : SourceBaseFunction) :
    sourceCommutantRotation θ n * sourcePi θ g = sourcePi θ g * sourceCommutantRotation θ n := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  have ht := (sourceTransportIndex_preserving θ n n).quasiMeasurePreserving.ae
    (sourcePi_apply_ae θ g f)
  filter_upwards [sourceTransport_apply_ae θ n n (sourcePi θ g f),
    sourcePi_apply_ae θ g (sourceTransport θ n n f), sourceTransport_apply_ae θ n n f,
    ht] with z h1 h2 h3 h4
  change (sourceTransport θ n n (sourcePi θ g f)) z = (sourcePi θ g (sourceTransport θ n n f)) z
  rw [h1,h2,h3,h4]
  have he : sourcePiSymbol θ g (sourceTransportIndex θ n n z) = sourcePiSymbol θ g z := by
    unfold sourcePiSymbol sourceTransportIndex
    dsimp only
    rw [coordinateRotate_add]
    congr 2
    omega
  rw [he]

theorem sourceTransport_shift (θ : SourceCoordinate → ℝ) (n m : ℤ) :
    sourceTransport θ n m * sourceShift SourceCoordinate =
      sourceShift SourceCoordinate * sourceTransport θ n m := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  have ht := (sourceTransportIndex_preserving θ n m).quasiMeasurePreserving.ae
    (sourceShift_apply_ae f)
  have hs := (sourceShiftIndex_preserving SourceCoordinate).quasiMeasurePreserving.ae
    (sourceTransport_apply_ae θ n m f)
  filter_upwards [sourceTransport_apply_ae θ n m (sourceShift SourceCoordinate f),
    sourceShift_apply_ae (sourceTransport θ n m f), ht, hs] with z h1 h2 h3 h4
  change (sourceTransport θ n m (sourceShift SourceCoordinate f)) z =
    (sourceShift SourceCoordinate (sourceTransport θ n m f)) z
  rw [h1,h2,h3,h4]
  congr 1
  apply Prod.ext
  · rfl
  · dsimp [sourceTransportIndex, sourceShiftIndex]; omega

theorem sourceCommutantRotation_mem (θ : SourceCoordinate → ℝ) (n : ℤ) :
    sourceCommutantRotation θ n ∈ StarSubalgebra.centralizer ℂ
      ({sourceShift SourceCoordinate} ∪ Set.range (sourcePi θ)) := by
  apply (StarSubalgebra.mem_centralizer_iff ℂ).mpr
  intro A hA
  rcases hA with hA | ⟨g,rfl⟩
  · obtain rfl : A = sourceShift SourceCoordinate := hA
    refine ⟨(sourceTransport_shift θ n n).symm, ?_⟩
    have hs := congrArg star (sourceTransport_shift θ (-n) (-n))
    have he : star (sourceTransport θ (-n) (-n)) = sourceTransport θ n n := by
      rw [sourceTransport_star]; simp
    simpa only [star_mul, he, sourceCommutantRotation] using hs
  · exact ⟨(sourceCommutantRotation_pi θ n g).symm, by
      rw [sourcePi_star]
      exact (sourceCommutantRotation_pi θ n (sourceBaseStar g)).symm⟩

theorem sourceAlgebra_commutes_rotation (θ : SourceCoordinate → ℝ)
    {H : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate}
    (hH : H ∈ sourceAlgebra θ) (n : ℤ) :
    sourceCommutantRotation θ n * H = H * sourceCommutantRotation θ n := by
  change H ∈ StarSubalgebra.centralizer ℂ
    (StarSubalgebra.centralizer ℂ
      ({sourceShift SourceCoordinate} ∪ Set.range (sourcePi θ))) at hH
  exact ((StarSubalgebra.mem_centralizer_iff ℂ).mp hH _
    (sourceCommutantRotation_mem θ n)).1

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ2_Brown.FiniteFactor_CrossedProduct_FiberIndicators
attribute [-instance] _root_.OAI.FiniteFactor.productHilbertNontrivial _root_.OAI.FiniteFactor.sourceCStar_closed _root_.OAI.FiniteFactor.sourceCStar_nontrivial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped ENNReal
noncomputable section

theorem sourceFiberIndicator_coe (A : Set (SourceCoordinate → ℝ)) (hA : MeasurableSet A) (n : ℤ) :
    sourceFiberIndicator A hA n =ᵐ[sourceMeasure SourceCoordinate]
      (A ×ˢ {n}).indicator (fun _ => (1 : ℂ)) :=
  indicatorConstLp_coeFn

theorem sourceVacuum_coe : sourceVacuum =ᵐ[sourceMeasure SourceCoordinate]
    (Set.univ ×ˢ {(0 : ℤ)}).indicator (fun _ => (1 : ℂ)) :=
  indicatorConstLp_coeFn

/-- Every bounded base indicator on an arbitrary fiber is in the vacuum's
commutant orbit. No cyclicity or separating property is assumed. -/
theorem sourceFiberIndicator_eq_orbit (θ : SourceCoordinate → ℝ)
    (A : Set (SourceCoordinate → ℝ)) (hA : MeasurableSet A) (n : ℤ) :
    sourceFiberIndicator A hA n = sourceScalar (sourceBaseIndicator A hA)
      (sourceCommutantRotation θ n sourceVacuum) := by
  apply Lp.ext
  have hv := (sourceTransportIndex_preserving θ n n).quasiMeasurePreserving.ae sourceVacuum_coe
  filter_upwards [sourceFiberIndicator_coe A hA n, sourceHilbert_cube,
    sourcePi_apply_ae (fun _ => 0) (sourceBaseIndicator A hA)
      (sourceTransport θ n n sourceVacuum), sourceTransport_apply_ae θ n n sourceVacuum,
    hv] with z hi hc hs ht hv
  change (sourceFiberIndicator A hA n) z =
    (sourcePi (fun _ => 0) (sourceBaseIndicator A hA) (sourceTransport θ n n sourceVacuum)) z
  rw [hi,hs,ht,hv]
  have he : coordinateRotate (fun _ : SourceCoordinate => 0) z.2 z.1 = z.1 := by
    funext i
    simpa [coordinateRotate] using Int.fract_eq_self.mpr (hc i)
  unfold sourcePiSymbol
  rw [he]
  by_cases ha : z.1 ∈ A <;> by_cases hn : z.2 = n <;>
    simp [sourceBaseIndicator, sourceTransportIndex, ha, hn, sub_eq_zero]

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ2_Brown.FiniteFactor_CrossedProduct_FiberTotal
attribute [-instance] _root_.OAI.FiniteFactor.productHilbertNontrivial _root_.OAI.FiniteFactor.sourceCStar_closed _root_.OAI.FiniteFactor.sourceCStar_nontrivial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped ENNReal
noncomputable section

/-- Measurable base indicators on the integer fibers determine an L2 vector. -/
theorem sourceFiberIndicators_total (f : SourceHilbert SourceCoordinate)
    (hf : ∀ (A : Set (SourceCoordinate → ℝ)) (hA : MeasurableSet A) (n : ℤ),
      inner ℂ (sourceFiberIndicator A hA n) f = 0) : f = 0 := by
  apply Lp.ext
  refine (Lp.ae_eq_zero_of_forall_setIntegral_eq_zero f (by norm_num) (by norm_num)
    (fun s _ hs => integrableOn_Lp_of_measure_ne_top f (by norm_num) hs.ne) ?_).trans ?_
  · intro s hs hμs
    let A : ℤ → Set (SourceCoordinate → ℝ) := fun n => {x | (x,n) ∈ s}
    have hA (n : ℤ) : MeasurableSet (A n) := hs.preimage (measurable_id.prodMk measurable_const)
    have hcover : s = ⋃ n : ℤ, A n ×ˢ {n} := by
      ext z
      simp only [Set.mem_iUnion, Set.mem_prod, Set.mem_singleton_iff, A, Set.mem_ofPred_eq]
      constructor
      · intro hz; exact ⟨z.2, hz, rfl⟩
      · rintro ⟨n,hn,he⟩; simpa only [← he, Prod.eta] using hn
    have hd : Pairwise (fun n m : ℤ => Disjoint (A n ×ˢ {n}) (A m ×ˢ {m})) := by
      intro n m hnm
      apply Set.disjoint_left.mpr
      rintro z ⟨_,hn⟩ ⟨_,hm⟩
      exact hnm (hn.symm.trans hm)
    have hi : IntegrableOn f (⋃ n : ℤ, A n ×ˢ {n}) (sourceMeasure SourceCoordinate) := by
      rw [← hcover]
      exact integrableOn_Lp_of_measure_ne_top f (by norm_num) hμs.ne
    rw [hcover, integral_iUnion (fun n => (hA n).prod (measurableSet_singleton n)) hd hi]
    have hz (n : ℤ) : ∫ z in A n ×ˢ {n}, f z ∂sourceMeasure SourceCoordinate = 0 := by
      have he := hf (A n) (hA n) n
      rw [sourceFiberIndicator, L2.inner_indicatorConstLp_one] at he
      exact he
    simp_rw [hz]
    exact tsum_zero
  · exact (Lp.coeFn_zero _ _ _).symm

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ2_Brown.FiniteFactor_CrossedProduct_ConjugationVacuum
attribute [-instance] _root_.OAI.FiniteFactor.productHilbertNontrivial _root_.OAI.FiniteFactor.sourceCStar_closed _root_.OAI.FiniteFactor.sourceCStar_nontrivial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
noncomputable section

/-- Reflection of each total vacuum test equals its commutant adjoint on the vacuum. -/
theorem sourceConjugation_fiberIndicator (θ : SourceCoordinate → ℝ)
    (A : Set (SourceCoordinate → ℝ)) (hA : MeasurableSet A) (n : ℤ) :
    sourceConjugation θ (sourceFiberIndicator A hA n) =
      star (sourceScalar (sourceBaseIndicator A hA) * sourceCommutantRotation θ n) sourceVacuum := by
  rw [star_mul, sourceScalar_star, sourceCommutantRotation_star]
  apply Lp.ext
  have hf := (sourceReflectionIndex_preserving θ).quasiMeasurePreserving.ae
    (sourceFiberIndicator_coe A hA n)
  have hs := (sourceTransportIndex_preserving θ (-n) (-n)).quasiMeasurePreserving.ae
    (sourcePi_apply_ae (fun _ => 0) (sourceBaseStar (sourceBaseIndicator A hA)) sourceVacuum)
  have hv := (sourceTransportIndex_preserving θ (-n) (-n)).quasiMeasurePreserving.ae sourceVacuum_coe
  filter_upwards [sourceConjugation_apply_ae θ (sourceFiberIndicator A hA n), hf,
    sourceTransport_apply_ae θ (-n) (-n)
      (sourcePi (fun _ => 0) (sourceBaseStar (sourceBaseIndicator A hA)) sourceVacuum), hs, hv]
      with z h1 h2 h3 h4 h5
  change (sourceConjugation θ (sourceFiberIndicator A hA n)) z =
    (sourceTransport θ (-n) (-n) (sourcePi (fun _ => 0) (sourceBaseStar (sourceBaseIndicator A hA)) sourceVacuum)) z
  rw [h1,h2,h3,h4,h5]
  have he : coordinateRotate (fun _ : SourceCoordinate => 0) (z.2 - -n)
      (coordinateRotate θ (-n) z.1) = coordinateRotate θ (-n) z.1 := by
    funext i
    simp [coordinateRotate, Int.fract_fract]
  unfold sourcePiSymbol sourceTransportIndex
  dsimp only
  rw [he]
  by_cases hn : z.2 = -n
  · by_cases ha : coordinateRotate θ (-n) z.1 ∈ A <;>
      simp [sourceReflectionIndex, sourceBaseStar, sourceBaseIndicator, hn, ha]
  · have hn' : -z.2 ≠ n := by omega
    have hn'' : z.2 + n ≠ 0 := by omega
    simp [sourceReflectionIndex, sourceBaseStar, sourceBaseIndicator, hn', hn'']

/-- The actual reflection sends H e_0 to H* e_0 for every source-algebra element. -/
theorem sourceConjugation_algebra_vacuum (θ : SourceCoordinate → ℝ)
    {H : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate}
    (hH : H ∈ sourceAlgebra θ) :
    sourceConjugation θ (H sourceVacuum) = star H sourceVacuum := by
  apply sub_eq_zero.mp
  apply sourceFiberIndicators_total
  intro A hA n
  rw [inner_sub_right]
  apply sub_eq_zero.mpr
  rw [sourceConjugation_inner_symm, sourceConjugation_fiberIndicator,
    ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right,
    ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right]
  have hr := congrArg (fun T : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate =>
    T sourceVacuum) (sourceAlgebra_commutes_rotation θ hH n)
  rw [sourceFiberIndicator_eq_orbit θ A hA n]
  congr 1
  change sourceScalar (sourceBaseIndicator A hA) (sourceCommutantRotation θ n (H sourceVacuum)) =
    H (sourceScalar (sourceBaseIndicator A hA) (sourceCommutantRotation θ n sourceVacuum))
  have hs' := congrArg (fun T : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate =>
    T (sourceCommutantRotation θ n sourceVacuum))
    (sourceAlgebra_commutes_scalar θ hH (sourceBaseIndicator A hA))
  change sourceCommutantRotation θ n (H sourceVacuum) = H (sourceCommutantRotation θ n sourceVacuum) at hr
  change sourceScalar (sourceBaseIndicator A hA) (H (sourceCommutantRotation θ n sourceVacuum)) = _ at hs'
  rw [hr]
  exact hs'

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ2_Brown.FiniteFactor_CrossedProduct_Trace
attribute [-instance] _root_.OAI.FiniteFactor.productHilbertNontrivial _root_.OAI.FiniteFactor.sourceCStar_closed _root_.OAI.FiniteFactor.sourceCStar_nontrivial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
noncomputable section

/-- Traciality of the actual, previously constructed normal vacuum functional. -/
theorem sourceVacuumFunctional_tracial (θ : SourceCoordinate → ℝ)
    {A B : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate}
    (hA : A ∈ sourceAlgebra θ) (hB : B ∈ sourceAlgebra θ) :
    sourceVacuumFunctional (A * B) = sourceVacuumFunctional (B * A) := by
  have hh := sourceConjugation_inner_symm θ (A sourceVacuum) (B sourceVacuum)
  rw [sourceConjugation_algebra_vacuum θ hA, sourceConjugation_algebra_vacuum θ hB] at hh
  have hc := congrArg (starRingEnd ℂ) hh
  rw [inner_conj_symm, inner_conj_symm] at hc
  change inner ℂ sourceVacuum (A (B sourceVacuum)) = inner ℂ sourceVacuum (B (A sourceVacuum))
  rw [← ContinuousLinearMap.adjoint_inner_left A (B sourceVacuum) sourceVacuum,
    ← ContinuousLinearMap.adjoint_inner_left B (A sourceVacuum) sourceVacuum]
  exact hc.symm

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ2_Brown.FiniteFactor_Matrix_Entries
attribute [-instance] _root_.OAI.FiniteFactor.productHilbertNontrivial _root_.OAI.FiniteFactor.sourceCStar_closed _root_.OAI.FiniteFactor.sourceCStar_nontrivial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped ENNReal
noncomputable section

/-- A product almost-everywhere identity holds on every integer fiber. -/
theorem source_ae_all_fibers {p : (SourceCoordinate → ℝ) × ℤ → Prop}
    (hp : ∀ᵐ z ∂sourceMeasure SourceCoordinate, p z) :
    ∀ᵐ x ∂sourceBaseMeasure, ∀ n : ℤ, p (x,n) := by
  exact (Measure.ae_ae_of_ae_prod hp).mono fun x hx => Measure.ae_count_iff.mp hx

theorem sourceBasis_coe (n : ℤ) : sourceBasis n =ᵐ[sourceMeasure SourceCoordinate]
    fun z => if z.2 = n then 1 else 0 := by
  filter_upwards [sourceFiberIndicator_coe Set.univ MeasurableSet.univ n] with z hz
  rw [show (sourceBasis n) z = _ from hz]
  by_cases hn : z.2 = n <;> simp [hn]

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ2_Brown.FiniteFactor_Matrix_Integrals
attribute [-instance] _root_.OAI.FiniteFactor.productHilbertNontrivial _root_.OAI.FiniteFactor.sourceCStar_closed _root_.OAI.FiniteFactor.sourceCStar_nontrivial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped ENNReal ComplexConjugate
noncomputable section

theorem source_fiber_restrict (A : Set (SourceCoordinate → ℝ)) (n : ℤ) :
    (sourceMeasure SourceCoordinate).restrict (A ×ˢ {n}) =
      (sourceBaseMeasure.restrict A).map (fun x => (x,n)) := by
  rw [← Measure.prod_restrict]
  simp only [Measure.restrict_singleton, Measure.count_singleton, one_smul]
  exact Measure.prod_dirac _

theorem source_fiber_integral (f : SourceHilbert SourceCoordinate)
    (A : Set (SourceCoordinate → ℝ)) (n : ℤ) :
    ∫ z in A ×ˢ {n}, f z ∂sourceMeasure SourceCoordinate =
      ∫ x in A, f (x,n) ∂sourceBaseMeasure := by
  rw [source_fiber_restrict]
  exact integral_map (measurable_id.prodMk measurable_const).aemeasurable
    (Lp.stronglyMeasurable f).aestronglyMeasurable

theorem sourceMatrixEntry_setIntegral
    (H : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate)
    (A : Set (SourceCoordinate → ℝ)) (hA : MeasurableSet A) (k n : ℤ) :
    ∫ x in A, sourceMatrixEntry H k n x ∂sourceBaseMeasure =
      inner ℂ (sourceFiberIndicator A hA k) (H (sourceBasis n)) := by
  rw [sourceFiberIndicator, L2.inner_indicatorConstLp_one, source_fiber_integral]
  rfl

/-- The displayed trace integral is the actual previously proved normal state. -/
theorem sourceVacuumFunctional_matrixIntegral
    (H : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate) :
    sourceVacuumFunctional H = ∫ x, sourceMatrixEntry H 0 0 x ∂sourceBaseMeasure := by
  rw [← setIntegral_univ, sourceMatrixEntry_setIntegral H Set.univ MeasurableSet.univ]
  rfl

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ2_Brown.FiniteFactor_Matrix_Covariance
attribute [-instance] _root_.OAI.FiniteFactor.productHilbertNontrivial _root_.OAI.FiniteFactor.sourceCStar_closed _root_.OAI.FiniteFactor.sourceCStar_nontrivial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
noncomputable section

/-- Matrix entries of the actual multiplication generators. -/
theorem sourceMatrixEntry_pi (θ : SourceCoordinate → ℝ) (g : SourceBaseFunction) (n : ℤ) :
    ∀ᵐ x ∂sourceBaseMeasure, ∀ k : ℤ,
      sourceMatrixEntry (sourcePi θ g) k n x =
        if k = n then g.toFun (coordinateRotate θ n x) else 0 := by
  filter_upwards [source_ae_all_fibers (sourcePi_apply_ae θ g (sourceBasis n)),
    source_ae_all_fibers (sourceBasis_coe n)] with x hp hb k
  unfold sourceMatrixEntry
  rw [hp, hb]
  by_cases hk : k = n <;> simp [hk, sourcePiSymbol]

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ2_Brown.FiniteFactor_CrossedProduct_WeightedShiftField
attribute [-instance] _root_.OAI.FiniteFactor.productHilbertNontrivial _root_.OAI.FiniteFactor.sourceCStar_closed _root_.OAI.FiniteFactor.sourceCStar_nontrivial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped ENNReal
noncomputable section

theorem sourceMatrixEntry_sourceOperator_pow (θ : SourceCoordinate → ℝ) (hθ : SourceAngles θ)
    (q : ℕ) (m : ℤ) :
    ∀ᵐ x ∂sourceBaseMeasure, ∀ k : ℤ,
      sourceMatrixEntry (sourceOperator θ sourceLogWeight hθ.nonneg sourceLogWeight_nonneg ^ q) k m x =
        if k = m + (q : ℤ) then
          (sourceCocycle θ sourceLogWeight q (coordinateRotate θ m x) : ℂ) else 0 := by
  have hb := (sourceShiftNIndex_preserving SourceCoordinate q).quasiMeasurePreserving.ae
    (sourceBasis_coe m)
  filter_upwards [source_ae_all_fibers (sourceOperator_pow_apply_ae θ sourceLogWeight hθ.nonneg
    sourceLogWeight_nonneg hθ.summable q (sourceBasis m)), source_ae_all_fibers hb] with x hp hb k
  unfold sourceMatrixEntry
  rw [hp, hb]
  simp only [sourceShiftNIndex]
  by_cases hk : k = m + (q : ℤ)
  · simp [hk]
  · have he : k - (q : ℤ) ≠ m := by omega
    simp [he, hk]

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ2_Brown.BrownMeasure_ConcreteTrace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter InnerProductSpace
open scoped ComplexInnerProductSpace Topology Ring
namespace FiniteFactor
lemma sourceRealTrace_cyclic (θ : SourceCoordinate → ℝ) (a b : SourceCStar θ) :
    sourceRealTrace θ (a*b)=sourceRealTrace θ (b*a) :=
  congrArg Complex.re (sourceVacuumFunctional_tracial θ a.property b.property)
lemma sourceRealTrace_star (θ : SourceCoordinate → ℝ) (a : SourceCStar θ) :
    sourceRealTrace θ (star a)=sourceRealTrace θ a := by
  change (inner ℂ sourceVacuum ((star (a:ProductOp)) sourceVacuum)).re=(sourceVacuumFunctional a).re
  rw [ContinuousLinearMap.star_eq_adjoint,ContinuousLinearMap.adjoint_inner_right]
  rw [← inner_conj_symm]
  rfl
lemma sourceOperator_trace_pow_zero (θ : SourceCoordinate → ℝ) (hθ : SourceAngles θ) (n : ℕ) :
    sourceVacuumFunctional (sourceOperator θ sourceLogWeight hθ.nonneg sourceLogWeight_nonneg^(n+1))=0 := by
  rw [sourceVacuumFunctional_matrixIntegral]
  have he : (fun x=>sourceMatrixEntry (sourceOperator θ sourceLogWeight hθ.nonneg sourceLogWeight_nonneg^(n+1)) 0 0 x)=ᵐ[sourceBaseMeasure] fun _=>0 := by
    filter_upwards [sourceMatrixEntry_sourceOperator_pow θ hθ (n+1) 0] with x hx
    rw [hx,ite_eq_right (by omega)]
  rw [integral_congr_ae he,integral_zero]

lemma sourceCStarOperator_root (θ : SourceCoordinate → ℝ) (hθ : SourceAngles θ) :
    Tendsto (fun n:ℕ=>‖sourceCStarOperator θ hθ^n‖^(1/(n:ℝ))) atTop (𝓝 0) :=
  (staged_sourceOperator_properties θ hθ).2.2.2

lemma sourceOperator_one_sub_isUnit (θ : SourceCoordinate → ℝ) (hθ : SourceAngles θ) (c : ℂ) :
    IsUnit (1-c•sourceOperator θ sourceLogWeight hθ.nonneg sourceLogWeight_nonneg) :=
  (BrownLog.inverse_one_sub_eq_tsum _ (BrownLog.summable_pow_of_root_tendsto _
    (BrownLog.norm_root_smul_tendsto _ c (staged_sourceOperator_properties θ hθ).2.2.2))).1

local instance localInst_re610ac_1 : IsometricContinuousFunctionalCalculus ℝ ProductOp IsSelfAdjoint :=
  IsSelfAdjoint.instIsometricContinuousFunctionalCalculus
lemma sourceOperator_trace_log_square_one_sub (θ : SourceCoordinate → ℝ) (hθ : SourceAngles θ) (c : ℂ) :
    (sourceVacuumFunctional (CFC.log (star (1-c•sourceOperator θ sourceLogWeight hθ.nonneg sourceLogWeight_nonneg)*
      (1-c•sourceOperator θ sourceLogWeight hθ.nonneg sourceLogWeight_nonneg)))).re=0 := by
  let S : SourceCStar θ := c•sourceCStarOperator θ hθ
  have hQ := BrownLog.norm_root_smul_tendsto _ c (sourceCStarOperator_root θ hθ)
  have hz (n : ℕ) : sourceRealTrace θ (S^(n+1))=0 := by
    change (sourceVacuumFunctional ((c•sourceOperator θ sourceLogWeight hθ.nonneg sourceLogWeight_nonneg)^(n+1))).re=0
    rw [smul_pow,sourceVacuumFunctional_smul,sourceOperator_trace_pow_zero θ hθ,mul_zero,Complex.zero_re]
  have H := BrownLog.trace_log_square_one_sub_eq_zero (sourceRealTrace θ) (sourceRealTrace_cyclic θ)
    (sourceRealTrace_star θ) S hQ hz
  let φ := (sourceAlgebra θ).toStarSubalgebra.subtype
  have hu : IsUnit (1-S) := (BrownLog.inverse_one_sub_eq_tsum _ (BrownLog.summable_pow_of_root_tendsto _ hQ)).1
  have hi : IsUnit (star (1-S)*(1-S)) := hu.star.mul hu
  have hs : IsSelfAdjoint (star (1-S)*(1-S)) := isSelfAdjoint_iff.mpr (by simp)
  have hc : ContinuousOn Real.log (spectrum ℝ (star (1-S)*(1-S))) := by
    apply Real.continuousOn_log.mono
    intro y hy
    exact fun h=>(spectrum.zero_notMem ℝ hi) (h ▸ hy)
  have he := φ.map_cfc Real.log (star (1-S)*(1-S)) hc continuous_subtype_val hs (hs.map φ)
  change (sourceVacuumFunctional (φ (cfc Real.log (star (1-S)*(1-S))))).re=0 at H
  rw [he] at H
  exact H
end FiniteFactor
end

end OAI
end

section
-- module Solutions.OAIQ2_Brown.FiniteFactor_OrbitSampling_Measures
attribute [-instance] _root_.OAI.FiniteFactor.productHilbertNontrivial _root_.OAI.FiniteFactor.sourceCStar_closed _root_.OAI.FiniteFactor.sourceCStar_nontrivial
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

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ2_Brown.BrownMeasure_Weight
attribute [-instance] _root_.OAI.FiniteFactor.sourceCStar_closed _root_.OAI.FiniteFactor.sourceCStar_nontrivial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped Topology ENNReal
namespace FiniteFactor

lemma SourceAngles.lt_one {θ : SourceCoordinate → ℝ} (hθ : SourceAngles θ) (i : SourceCoordinate) : θ i<1 := by
  have hm : (100:ℝ)≤ sourceBlockSize i.1 := by exact_mod_cast (sourceStage i.1).m_ge_100
  have hK : (1:ℝ)≤(sourceStageState i.1).K := by exact_mod_cast (sourceStageState i.1).K_ge
  apply (hθ i).2.trans_lt
  apply (div_lt_one (mul_pos (sourceBlockSize_pos _) (sourceCutoff_pos _))).mpr
  change (2 : ℝ) < (sourceBlockSize i.1 : ℝ) * (sourceStageState i.1).K
  nlinarith

lemma unitInterval_floor_lintegral (a c : ℝ) (ha : 0≤a) (ha1 : a≤1) (hc : 0≤c) :
    (∫⁻ t,ENNReal.ofReal (c*(Int.floor (t+a):ℝ)) ∂unitIntervalMeasure)=ENNReal.ofReal (c*a) := by
  classical
  have he : (fun t=>ENNReal.ofReal (c*(Int.floor (t+a):ℝ))) =ᵐ[unitIntervalMeasure]
      (Set.Ico (1-a) 1).indicator (fun _=>ENNReal.ofReal c) := by
    filter_upwards [ae_restrict_mem measurableSet_Ico] with t ht
    rcases ht with ⟨ht0,ht1⟩
    by_cases hlt : t<1-a
    · have hz : Int.floor (t+a)=0 := Int.floor_eq_zero_iff.mpr ⟨by linarith,by linarith⟩
      have hn : t∉Set.Ico (1-a) 1 := fun h=>not_le_of_gt hlt h.1
      simp [hz,Set.indicator_of_notMem hn]
    · have ho : Int.floor (t+a)=1 := by
        apply Int.floor_eq_iff.mpr
        constructor <;> push_cast <;> linarith
      have hh : t∈Set.Ico (1-a) 1 := ⟨le_of_not_gt hlt,ht1⟩
      simp [ho,Set.indicator_of_mem hh]
  rw [lintegral_congr_ae he,lintegral_indicator measurableSet_Ico,lintegral_const]
  rw [Measure.restrict_apply_univ]
  have hs : Set.Ico (1-a) 1⊆Set.Ico (0:ℝ) 1 := by intro t ht; exact ⟨by linarith [ht.1],ht.2⟩
  rw [unitIntervalMeasure,Measure.restrict_apply measurableSet_Ico,Set.inter_eq_left.mpr hs,Real.volume_Ico]
  rw [show (1:ℝ)-(1-a)=a by ring,ENNReal.ofReal_mul hc]

lemma source_coordinate_log_integral (θ : SourceCoordinate → ℝ) (hθ : SourceAngles θ)
    (i : SourceCoordinate) :
    (∫⁻ x,ENNReal.ofReal (sourceLogWeight i*(coordinateFloor θ 1 x i:ℝ)) ∂sourceBaseMeasure)=
      ENNReal.ofReal (sourceLogWeight i*θ i) := by
  have hm : Measurable (fun t : ℝ=>ENNReal.ofReal (sourceLogWeight i*(Int.floor (t+θ i):ℝ))) := by fun_prop
  have he := lintegral_map (μ := sourceBaseMeasure) hm (measurable_pi_apply i)
  rw [Measure.infinitePi_map_eval] at he
  simpa only [Function.comp_def,coordinateFloor,Int.cast_one,one_mul] using
    he.symm.trans (unitInterval_floor_lintegral (θ i) (sourceLogWeight i) (hθ.nonneg i)
      (hθ.lt_one i).le (sourceLogWeight_nonneg i))

lemma sourceLog_nonneg (θ : SourceCoordinate → ℝ) (hθ : SourceAngles θ)
    {x : SourceCoordinate → ℝ} (hx : ∀ i,x i∈Set.Ico 0 1) : 0≤ sourceLog θ sourceLogWeight 1 x := by
  apply tsum_nonneg
  intro i
  apply mul_nonneg (sourceLogWeight_nonneg i)
  change 0 ≤ (Int.floor (x i + ((1:ℤ):ℝ)*θ i):ℝ)
  simp only [Int.cast_nonneg_iff, Int.floor_nonneg, Int.cast_one, one_mul]
  exact add_nonneg (hx i).1 (hθ.nonneg i)

lemma sourceLog_lintegral_prefix (θ : SourceCoordinate → ℝ) (hθ : SourceAngles θ) (s : Finset SourceCoordinate) :
    ENNReal.ofReal (∑ i∈s,sourceLogWeight i*θ i)≤
      ∫⁻ x,ENNReal.ofReal (sourceLog θ sourceLogWeight 1 x) ∂sourceBaseMeasure := by
  classical
  have hnonneg (i : SourceCoordinate) : 0≤ sourceLogWeight i*θ i := mul_nonneg (sourceLogWeight_nonneg i) (hθ.nonneg i)
  rw [ENNReal.ofReal_sum_of_nonneg (fun i _=>hnonneg i)]
  simp_rw [← source_coordinate_log_integral θ hθ]
  rw [← lintegral_finsetSum _ (fun i _=> by unfold coordinateFloor; fun_prop)]
  apply lintegral_mono_ae
  filter_upwards [ae_finiteFloorSupport θ hθ.summable,sourceSamplingHaar_cube] with x hx hcube
  have hnn (i : SourceCoordinate) : 0≤ sourceLogWeight i*(coordinateFloor θ 1 x i:ℝ) := by
    apply mul_nonneg (sourceLogWeight_nonneg i)
    change 0 ≤ (Int.floor (x i + ((1:ℤ):ℝ)*θ i):ℝ)
    simp only [Int.cast_nonneg_iff, Int.floor_nonneg, Int.cast_one, one_mul]
    exact add_nonneg (hcube i).1 (hθ.nonneg i)
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _=>hnn i)]
  exact ENNReal.ofReal_le_ofReal ((sourceLog_summable θ sourceLogWeight hx 1).sum_le_tsum s (fun i _=>hnn i))

theorem sourceLog_lintegral_top (θ : SourceCoordinate → ℝ) (hθ : SourceAngles θ) :
    (∫⁻ x,ENNReal.ofReal (sourceLog θ sourceLogWeight 1 x) ∂sourceBaseMeasure)=∞ := by
  apply ENNReal.eq_top_of_forall_nnreal_le
  intro a
  obtain ⟨q,hq⟩ := (hθ.weighted_prefix_diverges.eventually (eventually_ge_atTop (a:ℝ))).exists
  exact (show (a:ℝ≥0∞)≤ENNReal.ofReal (∑ i∈CouplingParameters.blockPrefix sourceBlockSize q,sourceLogWeight i*θ i) by
    simpa using ENNReal.ofReal_le_ofReal hq).trans (sourceLog_lintegral_prefix θ hθ _)
end FiniteFactor
end

end OAI
end

section
-- module Solutions.OAIQ2_Brown.BrownMeasure_Modulus
attribute [-instance] _root_.OAI.FiniteFactor.sourceCStar_closed _root_.OAI.FiniteFactor.sourceCStar_nontrivial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter InnerProductSpace
open scoped ComplexInnerProductSpace Topology ENNReal CStarAlgebra
namespace FiniteFactor
local instance instIsometricContinuousFunctionalCalculusRealProductOpIsSelfAdjoint_1 : IsometricContinuousFunctionalCalculus ℝ ProductOp IsSelfAdjoint :=
  IsSelfAdjoint.instIsometricContinuousFunctionalCalculus

lemma sourceShift_eq_transport (θ : SourceCoordinate → ℝ) :
    sourceShift SourceCoordinate=sourceTransport θ 0 1 := by
  apply ContinuousLinearMap.ext
  intro u
  apply Lp.ext
  filter_upwards [sourceShift_apply_ae u,sourceTransport_apply_ae θ 0 1 u,sourceHilbert_cube] with z hz ht hc
  rw [hz,ht]
  congr 1
  apply Prod.ext
  · funext i
    change z.1 i=Int.fract (z.1 i+(0:ℤ)*θ i)
    simpa using (Int.fract_eq_self.mpr (hc i)).symm
  · rfl

lemma sourceShift_unitary : star (sourceShift SourceCoordinate)*sourceShift SourceCoordinate=1 ∧
    sourceShift SourceCoordinate*star (sourceShift SourceCoordinate)=1 := by
  rw [sourceShift_eq_transport (fun _=>0),sourceTransport_star,sourceTransport_mul,sourceTransport_mul]
  simp [sourceTransport_zero]

attribute [local instance] OAI.FiniteFactor.instModuleRealProductOp_1
lemma sourceOperator_abs (θ : SourceCoordinate → ℝ) (hθ : SourceAngles θ) :
    CFC.abs (sourceOperator θ sourceLogWeight hθ.nonneg sourceLogWeight_nonneg)=
      sourcePi θ (sourceWeightBase θ hθ) := by
  let P := sourcePi θ (sourceWeightBase θ hθ)
  have hp : 0 ≤ P := sourceWeight_positive θ hθ
  change CFC.sqrt (star (sourceShift SourceCoordinate*P)*(sourceShift SourceCoordinate*P))=P
  have he : star (sourceShift SourceCoordinate*P)*(sourceShift SourceCoordinate*P)=P*P := by
    rw [star_mul]
    calc
      star P * star (sourceShift SourceCoordinate) * (sourceShift SourceCoordinate * P) =
        star P * ((star (sourceShift SourceCoordinate)*sourceShift SourceCoordinate)*P) := by
          noncomm_ring
      _ = P*P := by rw [sourceShift_unitary.1,one_mul,hp.star_eq]
  rw [he,CFC.sqrt_mul_self P hp]

end FiniteFactor
end

end OAI
end

section
-- module Solutions.OAIQ2_Brown.BrownMeasure_FunctionalCalculus
attribute [-instance] _root_.OAI.FiniteFactor.sourceCStar_closed _root_.OAI.FiniteFactor.sourceCStar_nontrivial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter InnerProductSpace
open scoped ComplexInnerProductSpace Topology
namespace FiniteFactor
lemma sourceWeightPoint_val (θ : SourceCoordinate → ℝ) (hθ : SourceAngles θ)
    {x : SourceCoordinate → ℝ} (hx : ∀ i,x i∈Set.Ico 0 1) :
    (sourceWeightPoint θ x:ℝ)=sourceCocycle θ sourceLogWeight 1 x :=
  min_eq_right (sourceWeight_le_one θ sourceLogWeight hθ.nonneg sourceLogWeight_nonneg hx)

lemma sourceContinuousWeightHom_continuous (θ : SourceCoordinate → ℝ) : Continuous (sourceContinuousWeightHom θ) := by
  exact ((sourceContinuousWeightHom θ).toAlgHom.toLinearMap.mkContinuous (1:ℝ)
    (fun φ=>by
      change ‖sourcePi θ (sourceContinuousWeightBase θ φ)‖ ≤ 1*‖φ‖
      simpa only [one_mul, sourceContinuousWeightBase] using sourcePi_norm_le θ (sourceContinuousWeightBase θ φ))).continuous

lemma sourceContinuousWeight_id (θ : SourceCoordinate → ℝ) (hθ : SourceAngles θ) :
    sourceContinuousWeight θ ((ContinuousMap.id ℝ).restrict WeightInterval)=sourcePi θ (sourceWeightBase θ hθ) := by
  apply ContinuousLinearMap.ext
  intro u
  apply Lp.ext
  filter_upwards [sourceContinuousWeight_apply_ae θ ((ContinuousMap.id ℝ).restrict WeightInterval) u,
    sourcePi_apply_ae θ (sourceWeightBase θ hθ) u] with z h1 h2
  change (sourceContinuousWeight θ _ u) z=(sourcePi θ (sourceWeightBase θ hθ) u) z
  rw [h1,h2]
  simp only [ContinuousMap.restrict_apply,ContinuousMap.id_apply,
    sourcePiSymbol,sourceWeightBase]
  have hc : ∀ i,coordinateRotate θ z.2 z.1 i∈Set.Ico (0:ℝ) 1 := by
    intro i
    exact ⟨Int.fract_nonneg _,Int.fract_lt_one _⟩
  rw [sourceWeightPoint_val θ hθ hc]

attribute [local instance] OAI.FiniteFactor.instIsometricContinuousFunctionalCalculusRealProductOpIsSelfAdjoint_2
lemma sourceContinuousWeightHom_eq_cfc (θ : SourceCoordinate → ℝ) (hθ : SourceAngles θ) :
    sourceContinuousWeightHom θ=cfcHomSuperset (sourceWeight_positive θ hθ).isSelfAdjoint (sourceWeight_spectrum_subset θ hθ) := by
  apply ContinuousMap.UniqueHom.eq_of_continuous_of_map_id
  · exact sourceContinuousWeightHom_continuous θ
  · exact cfcHomSuperset_continuous _ _
  · rw [cfcHomSuperset_id]
    exact sourceContinuousWeight_id θ hθ

lemma sourcePi_trace (θ : SourceCoordinate → ℝ) (g : SourceBaseFunction) :
    sourceVacuumFunctional (sourcePi θ g)=∫ x,g.toFun x ∂sourceBaseMeasure := by
  rw [sourceVacuumFunctional_matrixIntegral]
  apply integral_congr_ae
  filter_upwards [sourceMatrixEntry_pi θ g 0,sourceSamplingHaar_cube] with x hx hc
  have hr : coordinateRotate θ 0 x=x := by
    funext i
    simpa [coordinateRotate] using Int.fract_eq_self.mpr (hc i)
  simpa only [hr,ite_true] using hx 0
end FiniteFactor
end

end OAI
end

section
-- module Solutions.OAIQ2_Brown.BrownMeasure_Determinant
attribute [-instance] _root_.OAI.FiniteFactor.sourceCStar_closed _root_.OAI.FiniteFactor.sourceCStar_nontrivial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter InnerProductSpace
open scoped ComplexInnerProductSpace Topology ENNReal
namespace FiniteFactor

lemma sourceLog_measurable (θ : SourceCoordinate → ℝ) (c : SourceCoordinate → ℝ) (k : ℤ) :
    Measurable (sourceLog θ c k) := by
  have he : sourceLog θ c k = fun x=> -Real.log (sourceCocycle θ c k x) := by
    funext x
    simp [sourceCocycle]
  rw [he]
  exact (Real.measurable_log.comp (sourceCocycle_measurable θ c k)).neg

attribute [local instance] OAI.FiniteFactor.instIsometricContinuousFunctionalCalculusRealProductOpIsSelfAdjoint_3
lemma sourceWeight_cfc (θ : SourceCoordinate → ℝ) (hθ : SourceAngles θ) (φ : C(ℝ,ℝ)) :
    cfc φ (sourcePi θ (sourceWeightBase θ hθ))=
      sourceContinuousWeight θ (φ.restrict WeightInterval) := by
  have he := congrArg (fun H : C(WeightInterval,ℝ) →⋆ₐ[ℝ] ProductOp=>H (φ.restrict WeightInterval))
    (sourceContinuousWeightHom_eq_cfc θ hθ)
  rw [cfcHomSuperset_apply] at he
  rw [cfc_apply φ _ (sourceWeight_positive θ hθ).isSelfAdjoint φ.continuous.continuousOn]
  exact he.symm

lemma logarithmCutoff_exp_neg (n : ℕ) (x : ℝ) : logarithmCutoff n (Real.exp (-x))= -min (n:ℝ) x := by
  change Real.log (max (Real.exp (-(n:ℝ))) (Real.exp (-x)))= -min (n:ℝ) x
  by_cases h : (n:ℝ)≤x
  · rw [min_eq_left h,max_eq_left (Real.exp_le_exp.mpr (neg_le_neg h)),Real.log_exp]
  · have h' := le_of_not_ge h
    rw [min_eq_right h',max_eq_right (Real.exp_le_exp.mpr (neg_le_neg h')),Real.log_exp]

lemma sourceLog_trunc_integrable (θ : SourceCoordinate → ℝ) (hθ : SourceAngles θ) (n : ℕ) :
    Integrable (fun x=>min (n:ℝ) (sourceLog θ sourceLogWeight 1 x)) sourceBaseMeasure := by
  apply Integrable.of_bound ((measurable_const.min (sourceLog_measurable _ _ _)).aestronglyMeasurable) (n:ℝ)
  filter_upwards [sourceSamplingHaar_cube] with x hx
  rw [Real.norm_of_nonneg (le_min (Nat.cast_nonneg n) (sourceLog_nonneg θ hθ hx))]
  exact min_le_left _ _

attribute [local instance] OAI.FiniteFactor.instModuleRealProductOp_2
lemma sourceDeterminant_trace_logCutoff (θ : SourceCoordinate → ℝ) (hθ : SourceAngles θ) (n : ℕ) :
    (sourceVacuumFunctional (cfc (logarithmCutoff n)
      (CFC.abs (sourceOperator θ sourceLogWeight hθ.nonneg sourceLogWeight_nonneg)))).re =
      -(∫ x,min (n:ℝ) (sourceLog θ sourceLogWeight 1 x) ∂sourceBaseMeasure) := by
  rw [sourceOperator_abs θ hθ,sourceWeight_cfc θ hθ]
  change (sourceVacuumFunctional (sourcePi θ (sourceContinuousWeightBase θ ((logarithmCutoff n).restrict WeightInterval)))).re=_
  rw [sourcePi_trace]
  have he : (fun x=>(sourceContinuousWeightBase θ ((logarithmCutoff n).restrict WeightInterval)).toFun x)=ᵐ[sourceBaseMeasure]
      fun x=>(-min (n:ℝ) (sourceLog θ sourceLogWeight 1 x):ℝ) := by
    filter_upwards [sourceSamplingHaar_cube] with x hx
    change (logarithmCutoff n (sourceWeightPoint θ x):ℂ)=((-min (n:ℝ) (sourceLog θ sourceLogWeight 1 x):ℝ):ℂ)
    rw [sourceWeightPoint_val θ hθ hx]
    exact congrArg Complex.ofReal (logarithmCutoff_exp_neg n (sourceLog θ sourceLogWeight 1 x))
  rw [integral_congr_ae he,integral_complex_ofReal,Complex.ofReal_re,integral_neg]

lemma sourceLog_trunc_antibounded (θ : SourceCoordinate → ℝ) (hθ : SourceAngles θ) (a : ℝ) :
    ∃ n : ℕ,a≤∫ x,min (n:ℝ) (sourceLog θ sourceLogWeight 1 x) ∂sourceBaseMeasure := by
  let f : ℕ → (SourceCoordinate → ℝ) → ℝ≥0∞ := fun n x=> ENNReal.ofReal (min (n:ℝ) (sourceLog θ sourceLogWeight 1 x))
  have hmeas (n) : Measurable (f n) := ENNReal.measurable_ofReal.comp (measurable_const.min (sourceLog_measurable _ _ _))
  have hmono : Monotone f := by
    intro n m hnm x
    apply ENNReal.ofReal_le_ofReal
    exact min_le_min_right _ (by exact_mod_cast hnm)
  have hs : (⨆ n,∫⁻ x,f n x ∂sourceBaseMeasure)=∞ := by
    rw [← lintegral_iSup hmeas hmono]
    have he (x) : (⨆ n,f n x)=ENNReal.ofReal (sourceLog θ sourceLogWeight 1 x) := by
      apply le_antisymm
      · exact iSup_le (fun n=>ENNReal.ofReal_le_ofReal (min_le_right _ _))
      · obtain ⟨n,hn⟩ := exists_nat_ge (sourceLog θ sourceLogWeight 1 x)
        exact le_iSup_of_le n (by dsimp [f]; rw [min_eq_right hn])
    simp_rw [he]
    exact sourceLog_lintegral_top θ hθ
  by_contra hn
  have hb : ∀ n,∫⁻ x,f n x ∂sourceBaseMeasure≤ENNReal.ofReal a := by
    intro n
    have hnn : ∀ᵐ x ∂sourceBaseMeasure,0 ≤ min (n:ℝ) (sourceLog θ sourceLogWeight 1 x) := by
      filter_upwards [sourceSamplingHaar_cube] with x hx
      exact le_min (Nat.cast_nonneg n) (sourceLog_nonneg θ hθ hx)
    rw [← ofReal_integral_eq_lintegral_ofReal (sourceLog_trunc_integrable θ hθ n) hnn]
    exact ENNReal.ofReal_le_ofReal (le_of_lt (not_le.mp (fun h=>hn ⟨n,h⟩)))
  have := iSup_le hb
  rw [hs] at this
  exact ENNReal.ofReal_ne_top (top_le_iff.mp this)

theorem sourceOperator_determinant_zero (θ : SourceCoordinate → ℝ) (hθ : SourceAngles θ) :
    FugledeKadisonDeterminant sourceVacuumFunctional
      (sourceOperator θ sourceLogWeight hθ.nonneg sourceLogWeight_nonneg)=0 := by
  let Δ := FugledeKadisonDeterminant sourceVacuumFunctional
    (sourceOperator θ sourceLogWeight hθ.nonneg sourceLogWeight_nonneg)
  have hb (k : ℕ) : Δ≤ENNReal.ofReal (Real.exp (-(k:ℝ))) := by
    obtain ⟨n,hn⟩ := sourceLog_trunc_antibounded θ hθ (k:ℝ)
    apply (iInf_le _ n).trans
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    exact (sourceDeterminant_trace_logCutoff θ hθ n).trans_le (neg_le_neg hn)
  have ht : Tendsto (fun k:ℕ=>ENNReal.ofReal (Real.exp (-(k:ℝ)))) atTop (𝓝 0) := by
    have he := Real.tendsto_exp_neg_atTop_nhds_zero.comp tendsto_natCast_atTop_atTop
    simpa only [Function.comp_def,ENNReal.ofReal_zero] using ENNReal.continuous_ofReal.continuousAt.tendsto.comp he
  exact le_antisymm (ge_of_tendsto ht (Eventually.of_forall hb)) bot_le
end FiniteFactor
end

end OAI
end

section
-- module Solutions.OAIQ2_Brown.BrownMeasure_Dirac
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology
namespace FiniteFactor
lemma expLogPotential_dirac_zero (z : ℂ) :
    expLogPotential (Measure.dirac (0:ℂ)) z=ENNReal.ofReal ‖z‖ := by
  have he (n : ℕ) : ENNReal.ofReal (Real.exp (∫ w,logarithmCutoff n ‖z-w‖ ∂Measure.dirac (0:ℂ)))=
      ENNReal.ofReal (max (Real.exp (-(n:ℝ))) ‖z‖) := by
    rw [integral_dirac]
    simp only [sub_zero]
    change ENNReal.ofReal (Real.exp (Real.log (max (Real.exp (-(n:ℝ))) ‖z‖)))=_
    rw [Real.exp_log ((Real.exp_pos _).trans_le (le_max_left _ _))]
  unfold expLogPotential
  simp_rw [he]
  apply le_antisymm
  · have ht : Tendsto (fun n:ℕ=>ENNReal.ofReal (max (Real.exp (-(n:ℝ))) ‖z‖)) atTop (𝓝 (ENNReal.ofReal ‖z‖)) := by
      have hmax : Tendsto (fun index : ℕ => max (Real.exp (-(index : ℝ))) ‖z‖)
          atTop (𝓝 (max 0 ‖z‖)) :=
        (Real.tendsto_exp_neg_atTop_nhds_zero.comp tendsto_natCast_atTop_atTop).max
          (tendsto_const_nhds (x := ‖z‖))
      simpa only [max_eq_right (norm_nonneg z)] using ENNReal.tendsto_ofReal hmax
    exact ge_of_tendsto ht (Eventually.of_forall (iInf_le _))
  · exact le_iInf (fun n=>ENNReal.ofReal_le_ofReal (le_max_right _ _))
lemma dirac_zero_support_compact : IsCompact (Measure.dirac (0:ℂ)).support := by
  have hs : (Measure.dirac (0:ℂ)).support⊆{0} := by
    apply Measure.support_subset_of_isClosed isClosed_singleton
    simp
  exact isCompact_singleton.of_isClosed_subset Measure.isClosed_support hs
end FiniteFactor
end

end OAI
end

section
-- module Solutions.OAIQ2_Brown.BrownMeasure_UnitDeterminant
attribute [-instance] _root_.OAI.FiniteFactor.sourceCStar_closed _root_.OAI.FiniteFactor.sourceCStar_nontrivial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter InnerProductSpace
open scoped ComplexInnerProductSpace Topology ENNReal Ring
namespace FiniteFactor

lemma sourceVacuumFunctional_mono {A B : ProductOp} (h : A≤B) :
    (sourceVacuumFunctional A).re≤(sourceVacuumFunctional B).re := by
  have hpos := (ContinuousLinearMap.nonneg_iff_isPositive (f := B-A)).mp
    (sub_nonneg.mpr h)
  have hb := hpos.re_inner_nonneg_right sourceVacuum
  change 0≤(inner ℂ sourceVacuum ((B-A) sourceVacuum)).re at hb
  simp only [sub_apply,inner_sub_right,Complex.sub_re] at hb
  exact sub_nonneg.mp hb

attribute [local instance] OAI.FiniteFactor.unitDeterminantRealModule
lemma product_abs_isUnit {T : ProductOp} (hT : IsUnit T) : IsUnit (CFC.abs T) := by
  apply (isUnit_pow_iff (by norm_num : (2:ℕ)≠0)).mp
  rw [pow_two, CFC.abs_mul_abs]
  exact hT.star.mul hT

lemma product_abs_spectrum_pos {T : ProductOp} (hT : IsUnit T) {y : ℝ}
    (hy : y∈spectrum ℝ (CFC.abs T)) : 0<y := by
  refine (spectrum_nonneg_of_nonneg (CFC.abs_nonneg T) hy).lt_of_ne ?_
  intro he
  exact spectrum.zero_notMem ℝ (product_abs_isUnit hT) (he ▸ hy)

attribute [local instance] OAI.FiniteFactor.unitDeterminantFunctionalCalculus
lemma logarithmCutoff_cfc_eq_log {A : ProductOp} (hA : 0≤A) (hu : IsUnit A) :
    ∃ n:ℕ,cfc (logarithmCutoff n) A=CFC.log A := by
  have hself := hA.isSelfAdjoint
  obtain ⟨y,hy,hmin⟩ := (spectrum.isCompact (𝕜:=ℝ) A).exists_isMinOn
    (ContinuousFunctionalCalculus.spectrum_nonempty A hself) continuous_id.continuousOn
  have hy0 : 0<y := by
    refine (spectrum_nonneg_of_nonneg hA hy).lt_of_ne ?_
    intro he
    exact spectrum.zero_notMem ℝ hu (he ▸ hy)
  have ht := Real.tendsto_exp_neg_atTop_nhds_zero.comp tendsto_natCast_atTop_atTop
  obtain ⟨n,hn⟩ := (ht.eventually (gt_mem_nhds hy0)).exists
  refine ⟨n,?_⟩
  apply cfc_congr
  intro x hx
  change Real.log (max (Real.exp (-(n:ℝ))) x)=Real.log x
  have hn' : Real.exp (-(n:ℝ))≤x := hn.le.trans (hmin hx)
  rw [max_eq_right hn']

lemma FugledeKadisonDeterminant_of_isUnit (T : ProductOp) (hu : IsUnit T) :
    FugledeKadisonDeterminant sourceVacuumFunctional T=
      ENNReal.ofReal (Real.exp (sourceVacuumFunctional (CFC.log (CFC.abs T))).re) := by
  have hp : ∀y∈spectrum ℝ (CFC.abs T),0<y := fun y hy=>product_abs_spectrum_pos hu hy
  have hc : ContinuousOn Real.log (spectrum ℝ (CFC.abs T)) := by
    apply Real.continuousOn_log.mono
    intro y hy
    exact (hp y hy).ne'
  apply le_antisymm
  · obtain ⟨n,hn⟩ := logarithmCutoff_cfc_eq_log (CFC.abs_nonneg T) (product_abs_isUnit hu)
    exact (iInf_le _ n).trans_eq
      (congrArg (fun operator : ProductOp =>
        ENNReal.ofReal (Real.exp (sourceVacuumFunctional operator).re)) hn)
  · apply le_iInf
    intro n
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    apply sourceVacuumFunctional_mono
    apply cfc_mono (hf:=hc) (hg:=(logarithmCutoff n).continuous.continuousOn)
    intro y hy
    exact Real.log_le_log (hp y hy) (le_max_right _ _)
end FiniteFactor
end

end OAI
end

section
-- module Solutions.OAIQ2_Brown.BrownMeasure_Resolvent
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter InnerProductSpace
open scoped ComplexInnerProductSpace Topology Ring ENNReal
namespace FiniteFactor

lemma sourceResolvent_factor (θ : SourceCoordinate → ℝ) (hθ : SourceAngles θ) {z : ℂ} (hz : z≠0) :
    sourceOperator θ sourceLogWeight hθ.nonneg sourceLogWeight_nonneg-algebraMap ℂ ProductOp z =
    (-z)•(1-z⁻¹•sourceOperator θ sourceLogWeight hθ.nonneg sourceLogWeight_nonneg) := by
  rw [smul_sub,smul_smul,neg_mul,mul_inv_cancel₀ hz,neg_one_smul (M := ProductOp) ℂ]
  rw [← Algebra.algebraMap_eq_smul_one, map_neg]
  abel

lemma sourceResolvent_isUnit (θ : SourceCoordinate → ℝ) (hθ : SourceAngles θ) {z : ℂ} (hz : z≠0) :
    IsUnit (sourceOperator θ sourceLogWeight hθ.nonneg sourceLogWeight_nonneg-algebraMap ℂ ProductOp z) := by
  rw [sourceResolvent_factor θ hθ hz,Algebra.smul_def (A := ProductOp) (-z)]
  exact ((isUnit_iff_ne_zero.mpr (neg_ne_zero.mpr hz)).map (algebraMap ℂ ProductOp)).mul
    (sourceOperator_one_sub_isUnit θ hθ z⁻¹)

lemma sourceVacuumFunctional_algebraMap_real (r : ℝ) :
    (sourceVacuumFunctional (algebraMap ℝ ProductOp r)).re=r := by
  rw [Algebra.algebraMap_eq_smul_one]
  change (sourceVacuumFunctional ((r:ℂ)•(1:ProductOp))).re=r
  rw [sourceVacuumFunctional_smul,sourceVacuumFunctional_one,mul_one,Complex.ofReal_re]

lemma sourceResolvent_trace_log_square (θ : SourceCoordinate → ℝ) (hθ : SourceAngles θ) {z : ℂ} (hz : z≠0) :
    (sourceVacuumFunctional (CFC.log (star (sourceOperator θ sourceLogWeight hθ.nonneg sourceLogWeight_nonneg-algebraMap ℂ ProductOp z)*
      (sourceOperator θ sourceLogWeight hθ.nonneg sourceLogWeight_nonneg-algebraMap ℂ ProductOp z)))).re=2*Real.log ‖z‖ := by
  let A : ProductOp := 1-z⁻¹•sourceOperator θ sourceLogWeight hθ.nonneg sourceLogWeight_nonneg
  have hu : IsUnit A := sourceOperator_one_sub_isUnit θ hθ z⁻¹
  have hn : ∀y∈spectrum ℝ (star A*A),y≠0 := by
    intro y hy he
    exact spectrum.zero_notMem ℝ (hu.star.mul hu) (he ▸ hy)
  have hs : IsSelfAdjoint (star A*A) := isSelfAdjoint_iff.mpr (by simp)
  have he : star ((-z)•A)*((-z)•A)=(‖z‖^2:ℝ)•(star A*A) := by
    rw [star_smul,smul_mul_smul_comm,star_neg,neg_mul_neg]
    change ((starRingEnd ℂ) z*z)•(star A*A)=_
    rw [Complex.conj_mul',← Complex.ofReal_pow]
    rfl
  rw [sourceResolvent_factor θ hθ hz]
  change (sourceVacuumFunctional (CFC.log (star ((-z)•A)*((-z)•A)))).re=_
  rw [he]
  have hlog : CFC.log ((‖z‖^2:ℝ)•(star A*A))=
      algebraMap ℝ ProductOp (Real.log (‖z‖^2))+CFC.log (star A*A) :=
    CFC.log_smul (r:=‖z‖^2) (star A*A) hn (pow_ne_zero 2 (norm_ne_zero_iff.mpr hz)) hs
  rw [hlog,sourceVacuumFunctional_add,Complex.add_re,sourceVacuumFunctional_algebraMap_real]
  rw [sourceOperator_trace_log_square_one_sub θ hθ z⁻¹,add_zero,Real.log_pow]
  norm_num

attribute [local instance] OAI.FiniteFactor.resolventRealModule
lemma sourceResolvent_trace_log_abs (θ : SourceCoordinate → ℝ) (hθ : SourceAngles θ) {z : ℂ} (hz : z≠0) :
    (sourceVacuumFunctional (CFC.log (CFC.abs (sourceOperator θ sourceLogWeight hθ.nonneg sourceLogWeight_nonneg-algebraMap ℂ ProductOp z)))).re=Real.log ‖z‖ := by
  let T := sourceOperator θ sourceLogWeight hθ.nonneg sourceLogWeight_nonneg-algebraMap ℂ ProductOp z
  have hu : IsUnit T := sourceResolvent_isUnit θ hθ hz
  have hn : ∀y∈spectrum ℝ (CFC.abs T),y≠0 := fun y hy=>(product_abs_spectrum_pos hu hy).ne'
  have hh := CFC.log_pow 2 (CFC.abs T) hn (CFC.abs_nonneg T).isSelfAdjoint
  rw [pow_two, CFC.abs_mul_abs] at hh
  have he := congrArg (fun a:ProductOp=>(sourceVacuumFunctional a).re) hh
  rw [sourceResolvent_trace_log_square θ hθ hz] at he
  simp only [two_nsmul,sourceVacuumFunctional_add,Complex.add_re] at he
  change _=_ at he
  linarith

theorem sourceResolvent_determinant (θ : SourceCoordinate → ℝ) (hθ : SourceAngles θ) {z : ℂ} (hz : z≠0) :
    FugledeKadisonDeterminant sourceVacuumFunctional
      (sourceOperator θ sourceLogWeight hθ.nonneg sourceLogWeight_nonneg-algebraMap ℂ ProductOp z)=ENNReal.ofReal ‖z‖ := by
  rw [FugledeKadisonDeterminant_of_isUnit _ (sourceResolvent_isUnit θ hθ hz),
    sourceResolvent_trace_log_abs θ hθ hz,Real.exp_log (norm_pos_iff.mpr hz)]
end FiniteFactor
end

end OAI
end

section
-- module Solutions.OAIQ2_Brown.FiniteFactor_CrossedProduct_TorusModel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped ENNReal Classical
noncomputable section

instance sourceUnitCircle_probability : IsProbabilityMeasure (volume : Measure UnitAddCircle) := by
  rw [← sourceCircle_mk_preserving.map_eq]
  exact Measure.isProbabilityMeasure_map sourceCircle_mk_preserving.measurable.aemeasurable

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ2_Brown.FiniteFactor_CrossedProduct_HilbertSeparable
attribute [-instance] _root_.OAI.FiniteFactor.productHilbertNontrivial _root_.OAI.FiniteFactor.sourceCStar_closed _root_.OAI.FiniteFactor.sourceCStar_nontrivial _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
noncomputable section

/-- The actual regular-representation Hilbert space is separable. This uses
the countably generated Borel structure of the countable real product times
Z and the finite exponent 2. It does not assert a predual for the algebra. -/
instance sourceHilbert_separable : TopologicalSpace.SeparableSpace (SourceHilbert SourceCoordinate) := by
  let : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by norm_num⟩
  infer_instance

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ2_Brown.BrownMeasure_Main
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
namespace FiniteFactor

theorem productBrown_oai : ProductBrownClaim := by
  intro θ hθ
  refine ⟨inferInstance, dirac_zero_support_compact, ?_⟩
  intro z
  rw [expLogPotential_dirac_zero]
  by_cases hz : z = 0
  · subst z
    simp only [map_zero, sub_zero, norm_zero, ENNReal.ofReal_zero]
    exact sourceOperator_determinant_zero θ hθ
  · exact sourceResolvent_determinant θ hθ hz
end FiniteFactor

end

end OAI
end

theorem solution : type_of% @OAI.FiniteFactor.productBrown_oai := @OAI.FiniteFactor.productBrown_oai
