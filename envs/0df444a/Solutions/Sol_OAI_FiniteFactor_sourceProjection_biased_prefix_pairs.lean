-- Prove2me | solution 1 for OAI.FiniteFactor.sourceProjection_biased_prefix_pairs
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-25T23:42:53.310515+00:00
-- url     : https://prove2.me/submissions/edb2a032-811e-4f99-a900-71d85fa9dab0

import Mathlib
import Definitions.Def_OAIQ3Ff001
import Definitions.Def_OAIQ3Ff002
import Theorems.Thm_OAI_FiniteFactor_sourceBiasedPrefix_domination

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
end OAICompat434

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

/-- Ordered endpoints give the ratio bound for every integer, including
negative integers. Both infinite sums are justified by finite support. -/
theorem sourceCocycle_ordered {ι : Type*} (θ c : ι → ℝ)
    (hc : ∀ i, 0 ≤ c i) {x y : ι → ℝ}
    (hx : finiteFloorSupport θ x) (hy : finiteFloorSupport θ y)
    (hxy : ∀ i, x i ≤ y i) (k : ℤ) : sourceCocycle θ c k y ≤ sourceCocycle θ c k x := by
  apply Real.exp_le_exp.mpr
  apply neg_le_neg
  exact Summable.tsum_le_tsum (fun i => mul_le_mul_of_nonneg_left
    (by
      have hh : coordinateFloor θ k x i ≤ coordinateFloor θ k y i :=
        Int.floor_mono (add_le_add (hxy i) le_rfl)
      exact_mod_cast hh) (hc i))
    (sourceLog_summable θ c hx k) (sourceLog_summable θ c hy k)

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

theorem sourceMultiplication_apply_ae {ι : Type*} [Countable ι] (θ c : ι → ℝ)
    (hθ : ∀ i, 0 ≤ θ i) (hc : ∀ i, 0 ≤ c i) (f : SourceHilbert ι) :
    sourceMultiplication θ c hθ hc f =ᵐ[sourceMeasure ι] fun z => sourceDiagonal θ c z * f z := by
  have hh := (ContinuousLinearMap.mul ℂ ℂ).coeFn_holder
    ((sourceDiagonal_memLp θ c hθ hc).toLp (sourceDiagonal θ c)) f (r := 2)
  filter_upwards [hh, (sourceDiagonal_memLp θ c hθ hc).coeFn_toLp] with z hz hw
  simpa [sourceMultiplication, hw] using hz

end
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

theorem sourceTorusQuotient_representative (z : SourceTorus) :
    sourceTorusQuotient (sourceTorusRepresentative z) = z := by
  funext i
  exact (AddCircle.equivIco 1 0).symm_apply_apply (z i)

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_CompactZeroTransfer
attribute [-instance] _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped Topology ENNReal NNReal

/-- Compact subsets carrying uniformly almost all approximating mass carry
all limiting mass as their uniform losses tend to zero. -/
theorem finiteMeasure_ae_of_compact_approximation {X : Type*}
    [MeasurableSpace X] [TopologicalSpace X] [T2Space X]
    [OpensMeasurableSpace X] [HasOuterApproxClosed X]
    (μ : ℕ → FiniteMeasure X) (ν : FiniteMeasure X)
    (hlim : Tendsto μ atTop (𝓝 ν)) (Z : Set X) (hZ : MeasurableSet Z)
    (hcompact : ∀ ε : ℝ≥0, 0 < ε → ∃ K, IsCompact K ∧ K ⊆ Z ∧
      ∀ n, (μ n : Measure X) Kᶜ ≤ ε) :
    ∀ᵐ x ∂(ν : Measure X), x ∈ Z := by
  have hmass : Tendsto (fun n => (μ n : Measure X) Set.univ) atTop
      (𝓝 ((ν : Measure X) Set.univ)) := by
    simpa only [Function.comp_def, FiniteMeasure.ennreal_mass] using
      (ENNReal.continuous_coe.tendsto ν.mass).comp hlim.mass
  have hfull : (ν : Measure X) Set.univ ≤ (ν : Measure X) Z := by
    apply ENNReal.le_of_forall_pos_le_add
    intro ε hε _
    obtain ⟨K,hK,hKZ,hbound⟩ := hcompact ε hε
    have hle : ∀ n, (μ n : Measure X) Set.univ ≤ (μ n : Measure X) K + ε := by
      intro n
      rw [← measure_add_measure_compl hK.isClosed.measurableSet]
      exact add_le_add le_rfl (hbound n)
    have hsup := Filter.limsup_le_limsup (f := atTop) (Eventually.of_forall hle)
    rw [hmass.limsup_eq, limsup_add_const atTop _ _ (by isBoundedDefault) (by isBoundedDefault)] at hsup
    exact hsup.trans (add_le_add
      ((FiniteMeasure.limsup_measure_closed_le_of_tendsto hlim hK.isClosed).trans
        (measure_mono hKZ)) le_rfl)
  rw [ae_iff]
  change (ν : Measure X) Zᶜ = 0
  rw [measure_compl hZ (by finiteness), tsub_eq_zero_of_le hfull]

/-- The loss outside a product compact set is bounded by its two marginal
losses. The identity set itself may only be Borel. -/
theorem measure_pair_compact_loss {X : Type*} [MeasurableSpace X]
    (μ : Measure (X × X)) (Q : Set X) (hQ : MeasurableSet Q)
    (Z : Set (X × X)) (hZ : ∀ᵐ z ∂μ, z ∈ Z) :
    μ ((Q ×ˢ Q) ∩ Z)ᶜ ≤ (μ.map Prod.fst) Qᶜ + (μ.map Prod.snd) Qᶜ := by
  have he : (((Q ×ˢ Q) ∩ Z)ᶜ : Set (X × X)) =ᵐ[μ] ((Q ×ˢ Q)ᶜ : Set (X × X)) := by
    filter_upwards [hZ] with z hz
    apply propext
    change (¬ (z ∈ Q ×ˢ Q ∧ z ∈ Z)) ↔ ¬ z ∈ Q ×ˢ Q
    simp [hz]
  rw [measure_congr he]
  have hs : (Q ×ˢ Q)ᶜ = (Prod.fst ⁻¹' Qᶜ) ∪ (Prod.snd ⁻¹' Qᶜ) := by
    ext z
    simp only [Set.mem_compl_iff, Set.mem_prod, Set.mem_union, Set.mem_preimage]
    tauto
  rw [hs, Measure.map_apply measurable_fst hQ.compl,
    Measure.map_apply measurable_snd hQ.compl]
  exact measure_union_le _ _

end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_CompactGraphLusin
attribute [-instance] _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Set Filter
open scoped ENNReal
noncomputable section

/-- A function whose graph is compact above Q is continuous on Q. -/
theorem continuousOn_of_compact_graph {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [T2Space X] {f : X → Y} {K : Set (X × Y)} (hK : IsCompact K)
    (hgraph : ∀ z ∈ K, f z.1 = z.2) : ContinuousOn f (Prod.fst '' K) := by
  let Q := Prod.fst '' K
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let g : K → X := fun z => z.1.1
  have hg : Continuous g := continuous_fst.comp continuous_subtype_val
  have hi : Function.Injective g := by
    intro z w h
    apply Subtype.ext
    apply Prod.ext h
    exact (hgraph z.1 z.2).symm.trans ((congrArg f h).trans (hgraph w.1 w.2))
  have hmem (x : Q) : (x.1, f x.1) ∈ K := by
    obtain ⟨z,hz,hx⟩ := x.2
    have he : (x.1, f x.1) = z := by
      apply Prod.ext hx.symm
      simpa only [← hx] using hgraph z hz
    rwa [he]
  let inv : Q → K := fun x => ⟨(x.1, f x.1), hmem x⟩
  have hinv : Continuous inv :=
    (hg.isClosedEmbedding hi).isEmbedding.isInducing.continuous_iff.mpr continuous_subtype_val
  exact continuousOn_iff_continuous_domRestrict.mpr
    (continuous_snd.comp (continuous_subtype_val.comp hinv))

/-- Lusin's theorem on Polish spaces, obtained from compact subsets of the
measurable graph. The compact set can be required to lie in a prescribed
Borel conull set. -/
theorem exists_compact_lusin {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [PolishSpace X] [PolishSpace Y] [MeasurableSpace X] [MeasurableSpace Y]
    [BorelSpace X] [BorelSpace Y] (μ : Measure X) [IsFiniteMeasure μ]
    {f : X → Y} (hf : Measurable f) {s : Set X} (hs : MeasurableSet s)
    (hfull : ∀ᵐ x ∂μ, x ∈ s) {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ Q, Q ⊆ s ∧ IsCompact Q ∧ μ Qᶜ < ε ∧ ContinuousOn f Q := by
  let graph : X → X × Y := fun x => (x,f x)
  have hgraph : Measurable graph := measurable_id.prodMk hf
  let G : Set (X × Y) := {z | z.1 ∈ s ∧ f z.1 = z.2}
  have hG : MeasurableSet G :=
    (hs.preimage measurable_fst).inter (measurableSet_eq_fun (hf.comp measurable_fst) measurable_snd)
  let ν := μ.map graph
  obtain ⟨K,hKG,hK,hsmall⟩ := hG.exists_isCompact_sdiff_lt (μ := ν) (measure_ne_top _ _) hε
  let Q : Set X := Prod.fst '' K
  have hQ : IsCompact Q := hK.image continuous_fst
  have hQs : Q ⊆ s := by
    rintro x ⟨z,hz,rfl⟩
    exact (hKG hz).1
  have hmem (x : X) : graph x ∈ K ↔ x ∈ Q := by
    constructor
    · intro hx; exact ⟨graph x,hx,rfl⟩
    · rintro ⟨z,hz,hx⟩
      have he : graph x = z := by
        apply Prod.ext hx.symm
        simpa only [graph, ← hx] using (hKG hz).2
      rwa [he]
  have hpre : graph ⁻¹' (G \ K) = s \ Q := by
    ext x
    change ((x ∈ s ∧ f x = f x) ∧ graph x ∉ K) ↔ (x ∈ s ∧ x ∉ Q)
    rw [hmem]
    simp
  have hsmall' : μ (s \ Q) < ε := by
    have he : ν (G \ K) = μ (s \ Q) := by
      rw [Measure.map_apply hgraph (hG.diff hK.isClosed.measurableSet), hpre]
    rwa [he] at hsmall
  have heq : μ (s \ Q) = μ Qᶜ := by
    apply measure_congr
    filter_upwards [hfull] with x hx
    apply propext
    change (x ∈ s ∧ x ∉ Q) ↔ x ∉ Q
    simp [hx]
  refine ⟨Q,hQs,hQ,heq ▸ hsmall',?_⟩
  exact continuousOn_of_compact_graph hK (fun z hz => (hKG hz).2)

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_BoundedMatrixOperator
attribute [-instance] _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open Filter
open scoped ENNReal Topology
noncomputable section

theorem fiberFiniteEmbedding_single (n : ℤ) (c : ℂ) :
    fiberFiniteEmbedding (Finsupp.single n c) = lp.single 2 n c := by
  simp [fiberFiniteEmbedding, ← lp.single_smul]

theorem fiberFiniteEmbedding_sum (a : ℤ →₀ ℂ) :
    fiberFiniteEmbedding a = ∑ n ∈ a.support, lp.single 2 n (a n) := by
  simp [fiberFiniteEmbedding, Finsupp.linearCombination_apply, Finsupp.sum, ← lp.single_smul]

theorem fiberFiniteEmbedding_norm_sq (a : ℤ →₀ ℂ) :
    ‖fiberFiniteEmbedding a‖ ^ 2 = ∑ n ∈ a.support, ‖a n‖ ^ 2 := by
  rw [fiberFiniteEmbedding_sum]
  simpa using lp.norm_sum_single (p := (2 : ℝ≥0∞)) (by norm_num) a a.support

theorem fiberFiniteEmbedding_dense : DenseRange fiberFiniteEmbedding := by
  intro x
  apply isClosed_closure.mem_of_tendsto (lp.hasSum_single (by norm_num : (2 : ℝ≥0∞) ≠ ∞) x)
  apply Eventually.of_forall
  intro s
  apply subset_closure
  refine ⟨∑ n ∈ s, Finsupp.single n (x n), ?_⟩
  simp [fiberFiniteEmbedding_single]

/-- Every bounded operator is determined by its coordinate matrix. -/
theorem fiberOperator_ext {A B : SourceFiberHilbert →L[ℂ] SourceFiberHilbert}
    (h : ∀ k n : ℤ, (A (lp.single 2 n (1 : ℂ))) k = (B (lp.single 2 n (1 : ℂ))) k) : A = B := by
  apply lp.ext_continuousLinearMap (by norm_num : (2 : ℝ≥0∞) ≠ ∞)
  intro n
  apply ContinuousLinearMap.ext
  intro c
  apply Subtype.ext
  funext k
  change (A (lp.single 2 n c)) k = (B (lp.single 2 n c)) k
  have he : lp.single 2 n c = c • (lp.single 2 n (1 : ℂ) : SourceFiberHilbert) := by
    simp [← lp.single_smul]
  rw [he, map_smul, map_smul]
  change c * (A (lp.single 2 n 1)) k = c * (B (lp.single 2 n 1)) k
  rw [h]

theorem fiberOperator_hasSum (A : SourceFiberHilbert →L[ℂ] SourceFiberHilbert)
    (v : SourceFiberHilbert) :
    HasSum (fun n : ℤ => v n • A (lp.single 2 n (1 : ℂ))) (A v) := by
  convert (lp.hasSum_single (by norm_num : (2 : ℝ≥0∞) ≠ ∞) v).map A A.continuous using 1
  funext n
  have he : lp.single 2 n (v n) = v n • (lp.single 2 n (1 : ℂ) : SourceFiberHilbert) := by
    simp [← lp.single_smul]
  change v n • A (lp.single 2 n (1 : ℂ)) = A (lp.single 2 n (v n))
  rw [he, map_smul]

theorem fiberOperator_action (A : SourceFiberHilbert →L[ℂ] SourceFiberHilbert)
    (v : SourceFiberHilbert) (k : ℤ) :
    (A v) k = ∑' n : ℤ, (A (lp.single 2 n (1 : ℂ))) k * v n := by
  have h := (fiberOperator_hasSum A v).map
    (lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 k) (lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 k).continuous
  have he := h.tsum_eq.symm
  change (A v) k = ∑' n : ℤ, v n * (A (lp.single 2 n (1 : ℂ))) k at he
  simpa only [mul_comm] using he

variable (m : ℤ → ℤ → ℂ) (C : ℝ)
variable (hb : ∀ (s t : Finset ℤ) (a : ℤ → ℂ),
  (∑ k ∈ t, ‖∑ n ∈ s, a n * m k n‖ ^ 2) ≤ C ^ 2 * ∑ n ∈ s, ‖a n‖ ^ 2)

theorem fiberMatrixFinite_norm_le (hC : 0 ≤ C) (a : ℤ →₀ ℂ) :
    ‖fiberMatrixFinite m C hb a‖ ≤ C * ‖fiberFiniteEmbedding a‖ := by
  have he : ‖fiberMatrixFinite m C hb a‖ ^ 2 =
      ∑' k, ‖fiberMatrixLinear m a k‖ ^ 2 := by
    simpa [fiberMatrixFinite] using lp.norm_rpow_eq_tsum (p := (2 : ℝ≥0∞)) (by norm_num)
      (fiberMatrixFinite m C hb a)
  have hsum : (∑' k, ‖fiberMatrixLinear m a k‖ ^ 2) ≤
      C ^ 2 * ∑ n ∈ a.support, ‖a n‖ ^ 2 := by
    apply Real.tsum_le_of_sum_le
    · intro k; positivity
    · intro t; simpa [fiberMatrixLinear_apply] using hb a.support t a
  rw [← he, ← fiberFiniteEmbedding_norm_sq] at hsum
  have hpos := mul_nonneg hC (norm_nonneg (fiberFiniteEmbedding a))
  nlinarith [norm_nonneg (fiberMatrixFinite m C hb a)]

theorem boundedMatrixOperator_norm (hC : 0 ≤ C) : ‖boundedMatrixOperator m C hb‖ ≤ C :=
  LinearMap.opNorm_extendOfNorm_le fiberFiniteEmbedding_dense hC
    (fiberMatrixFinite_norm_le m C hb hC)

theorem boundedMatrixOperator_entry (hC : 0 ≤ C) (k n : ℤ) :
    (boundedMatrixOperator m C hb (lp.single 2 n (1 : ℂ))) k = m k n := by
  rw [← fiberFiniteEmbedding_single n 1]
  change ((fiberMatrixFinite m C hb).extendOfNorm fiberFiniteEmbedding
    (fiberFiniteEmbedding (Finsupp.single n 1))) k = _
  rw [LinearMap.extendOfNorm_eq fiberFiniteEmbedding_dense
    ⟨C, fiberMatrixFinite_norm_le m C hb hC⟩]
  change fiberMatrixLinear m (Finsupp.single n 1) k = _
  simp [fiberMatrixLinear]

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_CrossedProduct_FiberSeparable
attribute [-instance] _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open Set TopologicalSpace
noncomputable section

/-- Separability of the actual l2(Z) fiber, from its countable coordinate basis. -/
instance sourceFiber_separable : TopologicalSpace.SeparableSpace SourceFiberHilbert := by
  let b : ℤ → SourceFiberHilbert := fun n => lp.single 2 n (1 : ℂ)
  let S := Submodule.span ℂ (Set.range b)
  have hmem (a : ℤ →₀ ℂ) : fiberFiniteEmbedding a ∈ S := by
    change (∑ n ∈ a.support, a n • b n) ∈ S
    exact Submodule.sum_mem S fun n _ => Submodule.smul_mem S (a n) (Submodule.subset_span ⟨n,rfl⟩)
  have hd : Dense (S : Set SourceFiberHilbert) := by
    intro x
    exact closure_mono (by rintro _ ⟨a,rfl⟩; exact hmem a) (fiberFiniteEmbedding_dense x)
  have hs : IsSeparable (closure (S : Set SourceFiberHilbert)) :=
    (Set.countable_range b).isSeparable.span.closure
  rw [hd.closure_eq] at hs
  exact isSeparable_univ_iff.mp hs

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_CrossedProduct_GeneratedAlgebra
attribute [-instance] _root_.OAI.FiniteFactor.sourceAngleMarginal_atomless _root_.OAI.FiniteFactor.sourceBiasedRealMeasure_probability _root_.OAI.FiniteFactor.sourceFiniteReferenceKernel_markov _root_.OAI.FiniteFactor.sourceHilbert_separable _root_.OAI.FiniteFactor.sourceNormalFunctionalSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedGroup _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedSpace _root_.OAI.FiniteFactor.sourceResamplingKernel_markov _root_.OAI.FiniteFactor.sourceSamplingLambda_finite _root_.OAI.FiniteFactor.sourceSamplingSummand_finite _root_.OAI.FiniteFactor.sourceSamplingTorus_borel _root_.OAI.FiniteFactor.sourceSamplingTorus_compact _root_.OAI.FiniteFactor.sourceSamplingTrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingUntrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingWeightedMeasure_finite _root_.OAI.FiniteFactor.sourceUnitCircle_probability
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
-- module Solutions.OAIQ3_FF.FiniteFactor_Matrix_Entries
attribute [-instance] _root_.OAI.FiniteFactor.sourceAngleMarginal_atomless _root_.OAI.FiniteFactor.sourceBiasedRealMeasure_probability _root_.OAI.FiniteFactor.sourceFiniteReferenceKernel_markov _root_.OAI.FiniteFactor.sourceHilbert_separable _root_.OAI.FiniteFactor.sourceNormalFunctionalSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedGroup _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedSpace _root_.OAI.FiniteFactor.sourceResamplingKernel_markov _root_.OAI.FiniteFactor.sourceSamplingLambda_finite _root_.OAI.FiniteFactor.sourceSamplingSummand_finite _root_.OAI.FiniteFactor.sourceSamplingTorus_borel _root_.OAI.FiniteFactor.sourceSamplingTorus_compact _root_.OAI.FiniteFactor.sourceSamplingTrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingUntrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingWeightedMeasure_finite _root_.OAI.FiniteFactor.sourceUnitCircle_probability
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

theorem sourceScalar_apply_ae (g : SourceBaseFunction) (f : SourceHilbert SourceCoordinate) :
    sourceScalar g f =ᵐ[sourceMeasure SourceCoordinate] fun z => g.toFun z.1 * f z := by
  filter_upwards [sourcePi_apply_ae (fun _ => 0) g f, sourceHilbert_cube] with z hz hc
  change (sourcePi (fun _ => 0) g f) z = _
  rw [hz]
  have he : coordinateRotate (fun _ : SourceCoordinate => 0) z.2 z.1 = z.1 := by
    funext i
    simpa [coordinateRotate] using Int.fract_eq_self.mpr (hc i)
  simp [sourcePiSymbol, he]

theorem sourceScalar_indicator_basis (A : Set (SourceCoordinate → ℝ)) (hA : MeasurableSet A)
    (n : ℤ) : sourceScalar (sourceBaseIndicator A hA) (sourceBasis n) =
      sourceFiberIndicator A hA n := by
  apply Lp.ext
  filter_upwards [sourceScalar_apply_ae (sourceBaseIndicator A hA) (sourceBasis n),
    sourceBasis_coe n, sourceFiberIndicator_coe A hA n] with z hs hb hi
  rw [hs, hb, hi]
  by_cases ha : z.1 ∈ A <;> by_cases hn : z.2 = n <;> simp [sourceBaseIndicator, ha, hn]

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_CrossedProduct_FiberEnergy
attribute [-instance] _root_.OAI.FiniteFactor.sourceAngleMarginal_atomless _root_.OAI.FiniteFactor.sourceBiasedRealMeasure_probability _root_.OAI.FiniteFactor.sourceFiniteReferenceKernel_markov _root_.OAI.FiniteFactor.sourceHilbert_separable _root_.OAI.FiniteFactor.sourceNormalFunctionalSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedGroup _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedSpace _root_.OAI.FiniteFactor.sourceResamplingKernel_markov _root_.OAI.FiniteFactor.sourceSamplingLambda_finite _root_.OAI.FiniteFactor.sourceSamplingSummand_finite _root_.OAI.FiniteFactor.sourceSamplingTorus_borel _root_.OAI.FiniteFactor.sourceSamplingTorus_compact _root_.OAI.FiniteFactor.sourceSamplingTrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingUntrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingWeightedMeasure_finite _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped ENNReal
noncomputable section

theorem source_norm_sq_integrable (f : SourceHilbert SourceCoordinate) :
    Integrable (fun z => ‖f z‖ ^ 2) (sourceMeasure SourceCoordinate) :=
  (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable f)).mp (Lp.memLp f)

theorem sourceFiberEnergy_integrable (f : SourceHilbert SourceCoordinate) :
    Integrable (sourceFiberEnergy f) sourceBaseMeasure :=
  (source_norm_sq_integrable f).integral_prod_left

theorem source_norm_sq_integral (f : SourceHilbert SourceCoordinate) :
    ‖f‖ ^ 2 = ∫ z, ‖f z‖ ^ 2 ∂sourceMeasure SourceCoordinate := by
  calc
    ‖f‖ ^ 2 = RCLike.re (inner ℂ f f) := InnerProductSpace.norm_sq_eq_re_inner f
    _ = ∫ z, RCLike.re (inner ℂ (f z) (f z)) ∂sourceMeasure SourceCoordinate :=
      (integral_re (L2.integrable_inner (𝕜 := ℂ) f f)).symm
    _ = _ := by simp_rw [← InnerProductSpace.norm_sq_eq_re_inner]

theorem source_norm_sq_energy (f : SourceHilbert SourceCoordinate) :
    ‖f‖ ^ 2 = ∫ x, sourceFiberEnergy f x ∂sourceBaseMeasure := by
  rw [source_norm_sq_integral, integral_prod _ (source_norm_sq_integrable f)]
  rfl

/-- Measurable localization commutes with taking the squared fiber norm. -/
theorem sourceFiberEnergy_indicator (A : Set (SourceCoordinate → ℝ)) (hA : MeasurableSet A)
    (f : SourceHilbert SourceCoordinate) :
    sourceFiberEnergy (sourceScalar (sourceBaseIndicator A hA) f) =ᵐ[sourceBaseMeasure]
      A.indicator (sourceFiberEnergy f) := by
  filter_upwards [source_ae_all_fibers
    (sourceScalar_apply_ae (sourceBaseIndicator A hA) f)] with x hx
  unfold sourceFiberEnergy
  by_cases ha : x ∈ A
  · simp only [Set.indicator_of_mem ha]
    apply integral_congr_ae
    exact Eventually.of_forall fun n => by dsimp only; rw [hx]; simp [sourceBaseIndicator, ha]
  · simp only [Set.indicator_of_notMem ha]
    have he : (fun n : ℤ => ‖(sourceScalar (sourceBaseIndicator A hA) f) (x,n)‖ ^ 2) =
        fun _ => (0 : ℝ) := by
      funext n
      rw [hx]
      simp [sourceBaseIndicator, ha]
    rw [he, integral_zero]

theorem sourceScalar_indicator_norm_sq (A : Set (SourceCoordinate → ℝ))
    (hA : MeasurableSet A) (f : SourceHilbert SourceCoordinate) :
    ‖sourceScalar (sourceBaseIndicator A hA) f‖ ^ 2 =
      ∫ x in A, sourceFiberEnergy f x ∂sourceBaseMeasure := by
  rw [source_norm_sq_energy, integral_congr_ae (sourceFiberEnergy_indicator A hA f),
    integral_indicator hA]

theorem sourceAlgebra_fiberEnergy_le (θ : SourceCoordinate → ℝ)
    {H : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate}
    (hH : H ∈ sourceAlgebra θ) (f : SourceHilbert SourceCoordinate) :
    ∀ᵐ x ∂sourceBaseMeasure,
      sourceFiberEnergy (H f) x ≤ ‖H‖ ^ 2 * sourceFiberEnergy f x := by
  apply ae_le_of_forall_setIntegral_le (sourceFiberEnergy_integrable (H f))
    ((sourceFiberEnergy_integrable f).const_mul (‖H‖ ^ 2))
  intro A hA _
  rw [← sourceScalar_indicator_norm_sq A hA, integral_const_mul,
    ← sourceScalar_indicator_norm_sq A hA]
  have he : sourceScalar (sourceBaseIndicator A hA) (H f) =
      H (sourceScalar (sourceBaseIndicator A hA) f) :=
    congrArg (fun T : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate => T f)
      (sourceAlgebra_commutes_scalar θ hH (sourceBaseIndicator A hA))
  rw [he]
  have hb := H.le_opNorm (sourceScalar (sourceBaseIndicator A hA) f)
  have hn := norm_nonneg (H (sourceScalar (sourceBaseIndicator A hA) f))
  have hp := mul_nonneg (norm_nonneg H)
    (norm_nonneg (sourceScalar (sourceBaseIndicator A hA) f))
  nlinarith [sq_nonneg (‖H‖ * ‖sourceScalar (sourceBaseIndicator A hA) f‖ -
    ‖H (sourceScalar (sourceBaseIndicator A hA) f)‖)]

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_CrossedProduct_FiniteVectors
attribute [-instance] _root_.OAI.FiniteFactor.sourceAngleMarginal_atomless _root_.OAI.FiniteFactor.sourceBiasedRealMeasure_probability _root_.OAI.FiniteFactor.sourceFiniteReferenceKernel_markov _root_.OAI.FiniteFactor.sourceHilbert_separable _root_.OAI.FiniteFactor.sourceNormalFunctionalSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedGroup _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedSpace _root_.OAI.FiniteFactor.sourceResamplingKernel_markov _root_.OAI.FiniteFactor.sourceSamplingLambda_finite _root_.OAI.FiniteFactor.sourceSamplingSummand_finite _root_.OAI.FiniteFactor.sourceSamplingTorus_borel _root_.OAI.FiniteFactor.sourceSamplingTorus_compact _root_.OAI.FiniteFactor.sourceSamplingTrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingUntrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingWeightedMeasure_finite _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped ENNReal
noncomputable section

theorem sourceHilbert_sum_coe {ι : Type*} (s : Finset ι)
    (f : ι → SourceHilbert SourceCoordinate) :
    ⇑(∑ i ∈ s, f i : SourceHilbert SourceCoordinate) =ᵐ[sourceMeasure SourceCoordinate] fun z => ∑ i ∈ s, f i z := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    filter_upwards [Lp.coeFn_zero ℂ 2 (sourceMeasure SourceCoordinate)] with z hz
    exact hz
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    filter_upwards [Lp.coeFn_add (f i) (∑ j ∈ s, f j), ih] with z ha hs
    simp only [ha, Pi.add_apply, hs]

theorem sourceFiniteVector_coe (s : Finset ℤ) (a : ℤ → ℂ) :
    sourceFiniteVector s a =ᵐ[sourceMeasure SourceCoordinate]
      fun z => if z.2 ∈ s then a z.2 else 0 := by
  have hs : ∀ᵐ z ∂sourceMeasure SourceCoordinate, ∀ n : ℤ,
      (a n • sourceBasis n) z = a n * (if z.2 = n then 1 else 0) := by
    rw [ae_all_iff]
    intro n
    filter_upwards [Lp.coeFn_smul (a n) (sourceBasis n), sourceBasis_coe n] with z hc hb
    simp only [hc, Pi.smul_apply, smul_eq_mul, hb]
  filter_upwards [sourceHilbert_sum_coe s (fun n => a n • sourceBasis n), hs] with z hz hs
  change (∑ n ∈ s, a n • sourceBasis n) z = _
  rw [hz]
  simp_rw [hs, mul_ite, mul_one, mul_zero]
  simp

theorem sourceFiniteVector_image_coe
    (H : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate)
    (s : Finset ℤ) (a : ℤ → ℂ) :
    ∀ᵐ x ∂sourceBaseMeasure, ∀ k : ℤ,
      (H (sourceFiniteVector s a)) (x,k) = ∑ n ∈ s, a n * sourceMatrixEntry H k n x := by
  have hs : ∀ᵐ z ∂sourceMeasure SourceCoordinate, ∀ n : ℤ,
      (a n • H (sourceBasis n)) z = a n * (H (sourceBasis n)) z := by
    rw [ae_all_iff]
    intro n
    exact Lp.coeFn_smul (a n) (H (sourceBasis n))
  have he : H (sourceFiniteVector s a) = ∑ n ∈ s, a n • H (sourceBasis n) := by
    simp [sourceFiniteVector]
  rw [he]
  filter_upwards [source_ae_all_fibers (sourceHilbert_sum_coe s (fun n => a n • H (sourceBasis n))),
    source_ae_all_fibers hs] with x he hs k
  rw [he]
  exact Finset.sum_congr rfl fun n _ => hs k n

theorem sourceFiniteVector_energy (s : Finset ℤ) (a : ℤ → ℂ) :
    ∀ᵐ x ∂sourceBaseMeasure,
      sourceFiberEnergy (sourceFiniteVector s a) x = ∑ n ∈ s, ‖a n‖ ^ 2 := by
  filter_upwards [source_ae_all_fibers (sourceFiniteVector_coe s a)] with x hx
  unfold sourceFiberEnergy
  have he : (fun n : ℤ => ‖(sourceFiniteVector s a) (x,n)‖ ^ 2) =
      (s : Set ℤ).indicator (fun n => ‖a n‖ ^ 2) := by
    funext n
    rw [hx]
    by_cases hn : n ∈ s <;> simp [hn]
  rw [he, integral_indicator s.measurableSet, setIntegral_finset]
  · simp [measureReal_def]
  · rw [← (s : Set ℤ).biUnion_of_singleton]
    simp [integrableOn_finset_iUnion, integrableOn_singleton_iff]

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_Matrix_Bounds
attribute [-instance] _root_.OAI.FiniteFactor.sourceAngleMarginal_atomless _root_.OAI.FiniteFactor.sourceBiasedRealMeasure_probability _root_.OAI.FiniteFactor.sourceFiniteReferenceKernel_markov _root_.OAI.FiniteFactor.sourceHilbert_separable _root_.OAI.FiniteFactor.sourceNormalFunctionalSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedGroup _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedSpace _root_.OAI.FiniteFactor.sourceResamplingKernel_markov _root_.OAI.FiniteFactor.sourceSamplingLambda_finite _root_.OAI.FiniteFactor.sourceSamplingSummand_finite _root_.OAI.FiniteFactor.sourceSamplingTorus_borel _root_.OAI.FiniteFactor.sourceSamplingTorus_compact _root_.OAI.FiniteFactor.sourceSamplingTrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingUntrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingWeightedMeasure_finite _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped ENNReal
noncomputable section

/-- Continuity in a separable parameter lets a countable dense family of
almost-everywhere inequalities determine every parameter on one conull set. -/
theorem ae_forall_le_of_continuous {X E : Type*} [MeasurableSpace X]
    (μ : Measure X) [TopologicalSpace E] [TopologicalSpace.SeparableSpace E]
    (f g : E → X → ℝ) (hf : ∀ x, Continuous (fun e => f e x))
    (hg : ∀ x, Continuous (fun e => g e x))
    (h : ∀ e, ∀ᵐ x ∂μ, f e x ≤ g e x) :
    ∀ᵐ x ∂μ, ∀ e, f e x ≤ g e x := by
  obtain ⟨s, hsc, hsd⟩ := TopologicalSpace.exists_countable_dense E
  have hs : ∀ᵐ x ∂μ, ∀ e ∈ s, f e x ≤ g e x :=
    (ae_ball_iff hsc).mpr fun e _ => h e
  filter_upwards [hs] with x hx e
  exact le_on_closure hx (hf x).continuousOn (hg x).continuousOn (hsd e)

theorem sourceFiberEnergy_finite_le (f : SourceHilbert SourceCoordinate) (s : Finset ℤ) :
    ∀ᵐ x ∂sourceBaseMeasure, ∑ n ∈ s, ‖f (x,n)‖ ^ 2 ≤ sourceFiberEnergy f x := by
  filter_upwards [(source_norm_sq_integrable f).prod_right_ae] with x hx
  have h := setIntegral_le_integral (μ := Measure.count) (s := (s : Set ℤ))
    hx (Eventually.of_forall fun n => sq_nonneg ‖f (x,n)‖)
  rw [setIntegral_finset s hx.integrableOn] at h
  simpa [measureReal_def, sourceFiberEnergy] using h

/-- Each finite scalar matrix compression satisfies the actual operator norm bound. -/
theorem sourceMatrix_finite_bound (θ : SourceCoordinate → ℝ)
    {H : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate}
    (hH : H ∈ sourceAlgebra θ) (s t : Finset ℤ) (a : ℤ → ℂ) :
    ∀ᵐ x ∂sourceBaseMeasure,
      (∑ k ∈ t, ‖∑ n ∈ s, a n * sourceMatrixEntry H k n x‖ ^ 2) ≤
        ‖H‖ ^ 2 * ∑ n ∈ s, ‖a n‖ ^ 2 := by
  filter_upwards [sourceFiniteVector_image_coe H s a,
    sourceFiniteVector_energy s a,
    sourceFiberEnergy_finite_le (H (sourceFiniteVector s a)) t,
    sourceAlgebra_fiberEnergy_le θ hH (sourceFiniteVector s a)] with x hc he hf hh
  calc
    _ = ∑ k ∈ t, ‖(H (sourceFiniteVector s a)) (x,k)‖ ^ 2 := by simp_rw [hc]
    _ ≤ sourceFiberEnergy (H (sourceFiniteVector s a)) x := hf
    _ ≤ ‖H‖ ^ 2 * sourceFiberEnergy (sourceFiniteVector s a) x := hh
    _ = _ := by rw [he]

/-- One conull set works for every complex finite input vector and every finite
output truncation. No field or boundedness hypothesis has been substituted. -/
theorem sourceMatrix_finite_bound_all (θ : SourceCoordinate → ℝ)
    {H : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate}
    (hH : H ∈ sourceAlgebra θ) :
    ∀ᵐ x ∂sourceBaseMeasure, ∀ (s t : Finset ℤ) (a : ℤ → ℂ),
      (∑ k ∈ t, ‖∑ n ∈ s, a n * sourceMatrixEntry H k n x‖ ^ 2) ≤
        ‖H‖ ^ 2 * ∑ n ∈ s, ‖a n‖ ^ 2 := by
  rw [ae_all_iff]
  intro s
  rw [ae_all_iff]
  intro t
  apply ae_forall_le_of_continuous (E := ℤ → ℂ) sourceBaseMeasure
    (fun a x => ∑ k ∈ t, ‖∑ n ∈ s, a n * sourceMatrixEntry H k n x‖ ^ 2)
    (fun a _ => ‖H‖ ^ 2 * ∑ n ∈ s, ‖a n‖ ^ 2)
  · intro x; fun_prop
  · intro x; fun_prop
  · exact sourceMatrix_finite_bound θ hH s t

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_Matrix_Integrals
attribute [-instance] _root_.OAI.FiniteFactor.sourceAngleMarginal_atomless _root_.OAI.FiniteFactor.sourceBiasedRealMeasure_probability _root_.OAI.FiniteFactor.sourceFiniteReferenceKernel_markov _root_.OAI.FiniteFactor.sourceHilbert_separable _root_.OAI.FiniteFactor.sourceNormalFunctionalSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedGroup _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedSpace _root_.OAI.FiniteFactor.sourceResamplingKernel_markov _root_.OAI.FiniteFactor.sourceSamplingLambda_finite _root_.OAI.FiniteFactor.sourceSamplingSummand_finite _root_.OAI.FiniteFactor.sourceSamplingTorus_borel _root_.OAI.FiniteFactor.sourceSamplingTorus_compact _root_.OAI.FiniteFactor.sourceSamplingTrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingUntrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingWeightedMeasure_finite _root_.OAI.FiniteFactor.sourceUnitCircle_probability
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

theorem source_fiber_integrable (f : SourceHilbert SourceCoordinate) (n : ℤ) :
    Integrable (fun x => f (x,n)) sourceBaseMeasure := by
  have hi := integrableOn_Lp_of_measure_ne_top f (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    (sourceFiberMeasure_ne_top Set.univ n)
  rw [IntegrableOn, source_fiber_restrict, Measure.restrict_univ] at hi
  exact (integrable_map_measure (Lp.stronglyMeasurable f).aestronglyMeasurable
    (measurable_id.prodMk measurable_const).aemeasurable).mp hi

theorem sourceMatrixEntry_measurable
    (H : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate) (k n : ℤ) :
    Measurable (sourceMatrixEntry H k n) :=
  (Lp.stronglyMeasurable (H (sourceBasis n))).measurable.comp
    (measurable_id.prodMk measurable_const)

theorem sourceMatrixEntry_integrable
    (H : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate) (k n : ℤ) :
    Integrable (sourceMatrixEntry H k n) sourceBaseMeasure :=
  source_fiber_integrable _ _

theorem sourceMatrixEntry_setIntegral
    (H : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate)
    (A : Set (SourceCoordinate → ℝ)) (hA : MeasurableSet A) (k n : ℤ) :
    ∫ x in A, sourceMatrixEntry H k n x ∂sourceBaseMeasure =
      inner ℂ (sourceFiberIndicator A hA k) (H (sourceBasis n)) := by
  rw [sourceFiberIndicator, L2.inner_indicatorConstLp_one, source_fiber_integral]
  rfl

/-- Adjoint matrix coefficients agree almost everywhere, on the actual source base. -/
theorem sourceMatrixEntry_star (θ : SourceCoordinate → ℝ)
    {H : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate}
    (hH : H ∈ sourceAlgebra θ) (k n : ℤ) :
    sourceMatrixEntry (star H) k n =ᵐ[sourceBaseMeasure]
      fun x => star (sourceMatrixEntry H n k x) := by
  apply Integrable.ae_eq_of_forall_setIntegral_eq _ _
    (sourceMatrixEntry_integrable _ _ _)
    (Complex.conjCLE.integrable_comp_iff.mpr (sourceMatrixEntry_integrable H n k))
  intro A hA _
  change (∫ x in A, sourceMatrixEntry (star H) k n x ∂sourceBaseMeasure) =
    ∫ x in A, conj (sourceMatrixEntry H n k x) ∂sourceBaseMeasure
  rw [sourceMatrixEntry_setIntegral _ A hA, integral_conj, sourceMatrixEntry_setIntegral _ A hA,
    inner_conj_symm]
  rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right]
  have he : H (sourceFiberIndicator A hA k) =
      sourceScalar (sourceBaseIndicator A hA) (H (sourceBasis k)) := by
    rw [← sourceScalar_indicator_basis]
    exact (congrArg (fun T : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate =>
      T (sourceBasis k)) (sourceAlgebra_commutes_scalar θ hH (sourceBaseIndicator A hA))).symm
  rw [he]
  have hs : star (sourceScalar (sourceBaseIndicator A hA)) =
      sourceScalar (sourceBaseIndicator A hA) := by
    rw [sourceScalar_star]
    congr 1
    unfold sourceBaseStar sourceBaseIndicator
    congr 1
    funext x
    by_cases hx : x ∈ A <;> simp [hx]
  rw [← ContinuousLinearMap.adjoint_inner_right, ← ContinuousLinearMap.star_eq_adjoint,
    hs, sourceScalar_indicator_basis]

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_CrossedProduct_OperatorField
attribute [-instance] _root_.OAI.FiniteFactor.sourceAngleMarginal_atomless _root_.OAI.FiniteFactor.sourceBiasedRealMeasure_probability _root_.OAI.FiniteFactor.sourceFiber_separable _root_.OAI.FiniteFactor.sourceFiniteReferenceKernel_markov _root_.OAI.FiniteFactor.sourceHilbert_separable _root_.OAI.FiniteFactor.sourceNormalFunctionalSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedGroup _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedSpace _root_.OAI.FiniteFactor.sourceResamplingKernel_markov _root_.OAI.FiniteFactor.sourceSamplingLambda_finite _root_.OAI.FiniteFactor.sourceSamplingSummand_finite _root_.OAI.FiniteFactor.sourceSamplingTorus_borel _root_.OAI.FiniteFactor.sourceSamplingTorus_compact _root_.OAI.FiniteFactor.sourceSamplingTrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingUntrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingWeightedMeasure_finite _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped ENNReal
noncomputable section

theorem sourceFieldGoodSet_measurable
    (H : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate) :
    MeasurableSet (sourceFieldGoodSet H) := (measurableSet_toMeasurable _ _).compl

theorem sourceFieldGoodSet_ae (θ : SourceCoordinate → ℝ)
    {H : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate}
    (hH : H ∈ sourceAlgebra θ) : ∀ᵐ x ∂sourceBaseMeasure, x ∈ sourceFieldGoodSet H := by
  have hb : ∀ᵐ x ∂sourceBaseMeasure, sourceMatrixGood H x := sourceMatrix_finite_bound_all θ hH
  rw [ae_iff] at hb ⊢
  simpa [sourceFieldGoodSet, measure_toMeasurable] using hb

theorem sourceOperatorField_norm
    (H : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate) (x) :
    ‖sourceOperatorField H x‖ ≤ ‖H‖ := by
  classical
  unfold sourceOperatorField
  split_ifs
  · exact boundedMatrixOperator_norm _ _ _ (norm_nonneg H)
  · simp

theorem sourceOperatorField_entry
    (H : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate) (k n : ℤ) (x) :
    (sourceOperatorField H x (lp.single 2 n (1 : ℂ))) k =
      (sourceFieldGoodSet H).indicator (sourceMatrixEntry H k n) x := by
  classical
  unfold sourceOperatorField
  split_ifs with hx
  · rw [Set.indicator_of_mem hx]
    exact boundedMatrixOperator_entry _ _ _ (norm_nonneg H) k n
  · simp [hx]

theorem sourceOperatorField_entry_measurable
    (H : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate) (k n : ℤ) :
    Measurable (fun x => (sourceOperatorField H x (lp.single 2 n (1 : ℂ))) k) := by
  simp_rw [sourceOperatorField_entry]
  exact (sourceMatrixEntry_measurable H k n).indicator (sourceFieldGoodSet_measurable H)

/-- Field entries recover the original coefficients on one conull set. -/
theorem sourceOperatorField_entries_ae (θ : SourceCoordinate → ℝ)
    {H : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate}
    (hH : H ∈ sourceAlgebra θ) :
    ∀ᵐ x ∂sourceBaseMeasure, ∀ k n : ℤ,
      (sourceOperatorField H x (lp.single 2 n (1 : ℂ))) k = sourceMatrixEntry H k n x := by
  filter_upwards [sourceFieldGoodSet_ae θ hH] with x hx k n
  rw [sourceOperatorField_entry, Set.indicator_of_mem hx]

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_Matrix_Action
attribute [-instance] _root_.OAI.FiniteFactor.sourceAngleMarginal_atomless _root_.OAI.FiniteFactor.sourceBiasedRealMeasure_probability _root_.OAI.FiniteFactor.sourceFiniteReferenceKernel_markov _root_.OAI.FiniteFactor.sourceHilbert_separable _root_.OAI.FiniteFactor.sourceNormalFunctionalSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedGroup _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedSpace _root_.OAI.FiniteFactor.sourceResamplingKernel_markov _root_.OAI.FiniteFactor.sourceSamplingLambda_finite _root_.OAI.FiniteFactor.sourceSamplingSummand_finite _root_.OAI.FiniteFactor.sourceSamplingTorus_borel _root_.OAI.FiniteFactor.sourceSamplingTorus_compact _root_.OAI.FiniteFactor.sourceSamplingTrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingUntrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingWeightedMeasure_finite _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped ENNReal ComplexConjugate
noncomputable section

theorem sourceFiberInner_integrable (f g : SourceHilbert SourceCoordinate) :
    Integrable (sourceFiberInner f g) sourceBaseMeasure :=
  (L2.integrable_inner (𝕜 := ℂ) f g).integral_prod_left

theorem source_inner_fiber (f g : SourceHilbert SourceCoordinate) :
    inner ℂ f g = ∫ x, sourceFiberInner f g x ∂sourceBaseMeasure :=
  integral_prod _ (L2.integrable_inner (𝕜 := ℂ) f g)

theorem sourceScalar_indicator_inner (A : Set (SourceCoordinate → ℝ)) (hA : MeasurableSet A)
    (f g : SourceHilbert SourceCoordinate) :
    inner ℂ (sourceScalar (sourceBaseIndicator A hA) f) g =
      ∫ x in A, sourceFiberInner f g x ∂sourceBaseMeasure := by
  rw [source_inner_fiber, ← integral_indicator hA]
  apply integral_congr_ae
  filter_upwards [source_ae_all_fibers (sourceScalar_apply_ae (sourceBaseIndicator A hA) f)] with x hx
  unfold sourceFiberInner
  by_cases ha : x ∈ A
  · simp only [Set.indicator_of_mem ha]
    apply integral_congr_ae
    exact Eventually.of_forall fun n => by dsimp only; rw [hx]; simp [sourceBaseIndicator, ha]
  · simp only [Set.indicator_of_notMem ha]
    have he : (fun n : ℤ => inner ℂ ((sourceScalar (sourceBaseIndicator A hA) f) (x,n)) (g (x,n))) =
        fun _ => (0 : ℂ) := by
      funext n
      rw [hx]
      simp [sourceBaseIndicator, ha]
    rw [he, integral_zero]

/-- The scalar distribution identity determining every output coordinate of H. -/
theorem source_coordinate_action_inner (θ : SourceCoordinate → ℝ)
    {H : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate}
    (hH : H ∈ sourceAlgebra θ) (f : SourceHilbert SourceCoordinate) (k : ℤ) :
    (fun x => (H f) (x,k)) =ᵐ[sourceBaseMeasure]
      sourceFiberInner ((star H) (sourceBasis k)) f := by
  apply Integrable.ae_eq_of_forall_setIntegral_eq _ _ (source_fiber_integrable _ _)
    (sourceFiberInner_integrable _ _)
  intro A hA _
  rw [← source_fiber_integral, ← L2.inner_indicatorConstLp_one]
  change inner ℂ (sourceFiberIndicator A hA k) (H f) = _
  rw [← ContinuousLinearMap.adjoint_inner_left, ← ContinuousLinearMap.star_eq_adjoint]
  have he : (star H) (sourceFiberIndicator A hA k) =
      sourceScalar (sourceBaseIndicator A hA) ((star H) (sourceBasis k)) := by
    rw [← sourceScalar_indicator_basis]
    exact (congrArg (fun T : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate =>
      T (sourceBasis k)) (sourceAlgebra_commutes_scalar θ (star_mem hH)
      (sourceBaseIndicator A hA))).symm
  rw [he, sourceScalar_indicator_inner]

/-- Actual action on arbitrary L2 input, expressed through the constructed
matrix entries. The counting integral is an absolutely convergent series a.e. -/
theorem sourceMatrix_action (θ : SourceCoordinate → ℝ)
    {H : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate}
    (hH : H ∈ sourceAlgebra θ) (f : SourceHilbert SourceCoordinate) (k : ℤ) :
    (fun x => (H f) (x,k)) =ᵐ[sourceBaseMeasure]
      fun x => ∫ n : ℤ, sourceMatrixEntry H k n x * f (x,n) ∂Measure.count := by
  have hs : ∀ᵐ x ∂sourceBaseMeasure, ∀ n : ℤ,
      sourceMatrixEntry (star H) n k x = star (sourceMatrixEntry H k n x) := by
    rw [ae_all_iff]
    intro n
    exact sourceMatrixEntry_star θ hH n k
  filter_upwards [source_coordinate_action_inner θ hH f k, hs] with x hx hs
  rw [hx]
  unfold sourceFiberInner
  apply integral_congr_ae
  exact Eventually.of_forall fun n => by
    change inner ℂ (sourceMatrixEntry (star H) n k x) (f (x,n)) = _
    rw [hs]
    simp [RCLike.inner_apply, mul_comm]

/-- The matrix action is absolutely integrable over the counting measure. -/
theorem sourceMatrix_action_integrable (θ : SourceCoordinate → ℝ)
    {H : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate}
    (hH : H ∈ sourceAlgebra θ) (f : SourceHilbert SourceCoordinate) (k : ℤ) :
    ∀ᵐ x ∂sourceBaseMeasure,
      Integrable (fun n : ℤ => sourceMatrixEntry H k n x * f (x,n)) Measure.count := by
  have hs : ∀ᵐ x ∂sourceBaseMeasure, ∀ n : ℤ,
      sourceMatrixEntry (star H) n k x = star (sourceMatrixEntry H k n x) := by
    rw [ae_all_iff]
    intro n
    exact sourceMatrixEntry_star θ hH n k
  filter_upwards [(L2.integrable_inner (𝕜 := ℂ) ((star H) (sourceBasis k)) f).prod_right_ae,
    hs] with x hi hs
  apply hi.congr
  exact Eventually.of_forall fun n => by
    change inner ℂ (sourceMatrixEntry (star H) n k x) (f (x,n)) = _
    rw [hs]
    simp [RCLike.inner_apply, mul_comm]

theorem sourceMatrix_action_tsum (θ : SourceCoordinate → ℝ)
    {H : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate}
    (hH : H ∈ sourceAlgebra θ) (f : SourceHilbert SourceCoordinate) (k : ℤ) :
    ∀ᵐ x ∂sourceBaseMeasure,
      (H f) (x,k) = ∑' n : ℤ, sourceMatrixEntry H k n x * f (x,n) := by
  filter_upwards [sourceMatrix_action θ hH f k, sourceMatrix_action_integrable θ hH f k]
    with x hx hi
  rw [hx, integral_countable hi]
  simp [measureReal_def]

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_CrossedProduct_FieldRepresentation
attribute [-instance] _root_.OAI.FiniteFactor.sourceAngleMarginal_atomless _root_.OAI.FiniteFactor.sourceBiasedRealMeasure_probability _root_.OAI.FiniteFactor.sourceFiber_separable _root_.OAI.FiniteFactor.sourceFiniteReferenceKernel_markov _root_.OAI.FiniteFactor.sourceHilbert_separable _root_.OAI.FiniteFactor.sourceNormalFunctionalSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedGroup _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedSpace _root_.OAI.FiniteFactor.sourceResamplingKernel_markov _root_.OAI.FiniteFactor.sourceSamplingLambda_finite _root_.OAI.FiniteFactor.sourceSamplingSummand_finite _root_.OAI.FiniteFactor.sourceSamplingTorus_borel _root_.OAI.FiniteFactor.sourceSamplingTorus_compact _root_.OAI.FiniteFactor.sourceSamplingTrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingUntrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingWeightedMeasure_finite _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped ENNReal Topology
noncomputable section

/-- Coordinate measurability suffices for strong measurability in l2(Z). -/
theorem fiberCoordinates_stronglyMeasurable {X : Type*} [MeasurableSpace X]
    (f : X → SourceFiberHilbert) (hf : ∀ n : ℤ, Measurable (fun x => f x n)) :
    StronglyMeasurable f := by
  apply stronglyMeasurable_of_tendsto (atTop : Filter (Finset ℤ))
    (f := fun s x => ∑ n ∈ s, lp.single 2 n (f x n))
  · intro s
    have h (n : ℤ) : StronglyMeasurable (fun x => (lp.single 2 n (f x n) : SourceFiberHilbert)) :=
      (lp.singleContinuousLinearMap ℂ (fun _ : ℤ => ℂ) 2 n).continuous.comp_stronglyMeasurable
        (hf n).stronglyMeasurable
    convert Finset.stronglyMeasurable_sum s (fun n _ => h n) using 1
    funext x
    simp only [Finset.sum_apply]
  · rw [tendsto_pi_nhds]
    intro x
    exact lp.hasSum_single (by norm_num : (2 : ℝ≥0∞) ≠ ∞) (f x)

/-- Every basis column of the actual field is a strongly measurable l2 vector. -/
theorem sourceOperatorField_basis_stronglyMeasurable
    (H : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate) (n : ℤ) :
    StronglyMeasurable (fun x => sourceOperatorField H x (lp.single 2 n (1 : ℂ))) :=
  fiberCoordinates_stronglyMeasurable _ (fun k => sourceOperatorField_entry_measurable H k n)

theorem sourceOperatorField_stronglyMeasurable
    (H : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate)
    (v : SourceFiberHilbert) : StronglyMeasurable (fun x => sourceOperatorField H x v) := by
  apply stronglyMeasurable_of_tendsto (atTop : Filter (Finset ℤ))
    (f := fun s x => ∑ n ∈ s, v n • sourceOperatorField H x (lp.single 2 n (1 : ℂ)))
  · intro s
    have h (n : ℤ) : StronglyMeasurable (fun x => v n • sourceOperatorField H x (lp.single 2 n (1 : ℂ))) :=
      (sourceOperatorField_basis_stronglyMeasurable H n).const_smul (v n)
    convert Finset.stronglyMeasurable_sum s (fun n _ => h n) using 1
    funext x
    simp only [Finset.sum_apply]
  · rw [tendsto_pi_nhds]
    intro x
    exact fiberOperator_hasSum (sourceOperatorField H x) v

/-- Fubini puts almost every actual L2 section in l2(Z). -/
theorem source_fiber_memℓp (f : SourceHilbert SourceCoordinate) :
    ∀ᵐ x ∂sourceBaseMeasure, Memℓp (fun n : ℤ => f (x,n)) 2 := by
  filter_upwards [(source_norm_sq_integrable f).prod_right_ae] with x hx
  apply memℓp_gen
  have hs := integrable_count_iff.mp hx
  simpa only [norm_pow, norm_norm, ENNReal.toReal_ofNat, Real.rpow_two] using hs

theorem sourceFiberVector_coe (f : SourceHilbert SourceCoordinate) :
    ∀ᵐ x ∂sourceBaseMeasure, ∀ n : ℤ, sourceFiberVector f x n = f (x,n) := by
  filter_upwards [source_fiber_memℓp f] with x hx n
  simp [sourceFiberVector, hx]

/-- The constructed field acts as the original operator on every source L2
vector. Neither decomposability nor a replacement representation is assumed. -/
theorem sourceOperatorField_represents (θ : SourceCoordinate → ℝ)
    {H : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate}
    (hH : H ∈ sourceAlgebra θ) (f : SourceHilbert SourceCoordinate) :
    ∀ᵐ x ∂sourceBaseMeasure,
      sourceFiberVector (H f) x = sourceOperatorField H x (sourceFiberVector f x) := by
  have ha : ∀ᵐ x ∂sourceBaseMeasure, ∀ k : ℤ,
      (H f) (x,k) = ∑' n : ℤ, sourceMatrixEntry H k n x * f (x,n) := by
    rw [ae_all_iff]
    exact sourceMatrix_action_tsum θ hH f
  filter_upwards [sourceFiberVector_coe f, sourceFiberVector_coe (H f),
    sourceOperatorField_entries_ae θ hH, ha] with x hf hHf he ha
  apply Subtype.ext
  funext k
  rw [hHf, fiberOperator_action]
  simp_rw [he, hf]
  exact ha k

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_CrossedProduct_FieldAlgebra
attribute [-instance] _root_.OAI.FiniteFactor.sourceAngleMarginal_atomless _root_.OAI.FiniteFactor.sourceBiasedRealMeasure_probability _root_.OAI.FiniteFactor.sourceFiber_separable _root_.OAI.FiniteFactor.sourceFiniteReferenceKernel_markov _root_.OAI.FiniteFactor.sourceHilbert_separable _root_.OAI.FiniteFactor.sourceNormalFunctionalSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedGroup _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedSpace _root_.OAI.FiniteFactor.sourceResamplingKernel_markov _root_.OAI.FiniteFactor.sourceSamplingLambda_finite _root_.OAI.FiniteFactor.sourceSamplingSummand_finite _root_.OAI.FiniteFactor.sourceSamplingTorus_borel _root_.OAI.FiniteFactor.sourceSamplingTorus_compact _root_.OAI.FiniteFactor.sourceSamplingTrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingUntrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingWeightedMeasure_finite _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped ENNReal ComplexConjugate
noncomputable section

theorem sourceFiberVector_basis (n : ℤ) :
    ∀ᵐ x ∂sourceBaseMeasure, sourceFiberVector (sourceBasis n) x = lp.single 2 n (1 : ℂ) := by
  filter_upwards [sourceFiberVector_coe (sourceBasis n), source_ae_all_fibers (sourceBasis_coe n)]
    with x hf hb
  apply Subtype.ext
  funext k
  rw [hf, hb]
  by_cases hk : k = n
  · subst k; simp [lp.single_apply]
  · simp [lp.single_apply, hk]

theorem sourceOperatorField_mul (θ : SourceCoordinate → ℝ)
    {A B : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate}
    (hA : A ∈ sourceAlgebra θ) (hB : B ∈ sourceAlgebra θ) :
    ∀ᵐ x ∂sourceBaseMeasure,
      sourceOperatorField (A * B) x = sourceOperatorField A x * sourceOperatorField B x := by
  have h (n : ℤ) : ∀ᵐ x ∂sourceBaseMeasure,
      sourceOperatorField (A * B) x (lp.single 2 n (1 : ℂ)) =
        sourceOperatorField A x (sourceOperatorField B x (lp.single 2 n (1 : ℂ))) := by
    filter_upwards [sourceOperatorField_represents θ (mul_mem hA hB) (sourceBasis n),
      sourceOperatorField_represents θ hA (B (sourceBasis n)),
      sourceOperatorField_represents θ hB (sourceBasis n), sourceFiberVector_basis n]
      with x hab ha hb he
    rw [he] at hab hb
    change sourceFiberVector (A (B (sourceBasis n))) x = _ at hab
    rw [ha, hb] at hab
    exact hab.symm
  filter_upwards [ae_all_iff.mpr h] with x hx
  apply fiberOperator_ext
  intro k n
  exact congrArg (fun v : SourceFiberHilbert => v k) (hx n)

theorem sourceOperatorField_one (θ : SourceCoordinate → ℝ) :
    ∀ᵐ x ∂sourceBaseMeasure, sourceOperatorField (1 : SourceHilbert SourceCoordinate →L[ℂ]
      SourceHilbert SourceCoordinate) x = 1 := by
  have h (n : ℤ) : ∀ᵐ x ∂sourceBaseMeasure,
      sourceOperatorField (1 : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate)
        x (lp.single 2 n (1 : ℂ)) = lp.single 2 n 1 := by
    filter_upwards [sourceOperatorField_represents θ (one_mem (sourceAlgebra θ)) (sourceBasis n),
      sourceFiberVector_basis n] with x hi he
    change sourceFiberVector (sourceBasis n) x = _ at hi
    rw [he] at hi
    exact hi.symm
  filter_upwards [ae_all_iff.mpr h] with x hx
  apply fiberOperator_ext
  intro k n
  exact congrArg (fun v : SourceFiberHilbert => v k) (hx n)

theorem sourceOperatorField_zero (x : SourceCoordinate → ℝ) :
    sourceOperatorField (0 : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate) x = 0 := by
  apply norm_eq_zero.mp
  exact le_antisymm (by simpa using sourceOperatorField_norm 0 x) (norm_nonneg _)

theorem sourceOperatorField_sub (θ : SourceCoordinate → ℝ)
    {A B : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate}
    (hA : A ∈ sourceAlgebra θ) (hB : B ∈ sourceAlgebra θ) :
    ∀ᵐ x ∂sourceBaseMeasure,
      sourceOperatorField (A - B) x = sourceOperatorField A x - sourceOperatorField B x := by
  have hsub : ∀ᵐ x ∂sourceBaseMeasure, ∀ n k : ℤ,
      sourceMatrixEntry (A-B) k n x = sourceMatrixEntry A k n x - sourceMatrixEntry B k n x := by
    rw [ae_all_iff]
    intro n
    exact source_ae_all_fibers (Lp.coeFn_sub (A (sourceBasis n)) (B (sourceBasis n)))
  filter_upwards [sourceOperatorField_entries_ae θ hA, sourceOperatorField_entries_ae θ hB,
    sourceOperatorField_entries_ae θ (sub_mem hA hB), hsub] with x ha hb hab hs
  apply fiberOperator_ext
  intro k n
  change (sourceOperatorField (A-B) x (lp.single 2 n (1 : ℂ))) k =
    (sourceOperatorField A x (lp.single 2 n (1 : ℂ))) k -
      (sourceOperatorField B x (lp.single 2 n (1 : ℂ))) k
  rw [hab, ha, hb, hs]

/-- The original invariant-projection equation holds fiberwise for the actual
operator and projection fields. -/
theorem sourceOperatorField_invariant (θ : SourceCoordinate → ℝ)
    {p T : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate}
    (hp : p ∈ sourceAlgebra θ) (hT : T ∈ sourceAlgebra θ)
    (hinv : (1-p)*T*p = 0) :
    ∀ᵐ x ∂sourceBaseMeasure,
      (1-sourceOperatorField p x)*sourceOperatorField T x*sourceOperatorField p x = 0 := by
  have hsub := sub_mem (one_mem (sourceAlgebra θ)) hp
  filter_upwards [sourceOperatorField_mul θ (mul_mem hsub hT) hp,
    sourceOperatorField_mul θ hsub hT, sourceOperatorField_sub θ (one_mem (sourceAlgebra θ)) hp,
    sourceOperatorField_one θ] with x hab ha hs h1
  rw [hinv, sourceOperatorField_zero, ha, hs, h1] at hab
  exact hab.symm

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_Matrix_Covariance
attribute [-instance] _root_.OAI.FiniteFactor.sourceAngleMarginal_atomless _root_.OAI.FiniteFactor.sourceBiasedRealMeasure_probability _root_.OAI.FiniteFactor.sourceFiniteReferenceKernel_markov _root_.OAI.FiniteFactor.sourceHilbert_separable _root_.OAI.FiniteFactor.sourceNormalFunctionalSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedGroup _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedSpace _root_.OAI.FiniteFactor.sourceResamplingKernel_markov _root_.OAI.FiniteFactor.sourceSamplingLambda_finite _root_.OAI.FiniteFactor.sourceSamplingSummand_finite _root_.OAI.FiniteFactor.sourceSamplingTorus_borel _root_.OAI.FiniteFactor.sourceSamplingTorus_compact _root_.OAI.FiniteFactor.sourceSamplingTrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingUntrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingWeightedMeasure_finite _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
noncomputable section

theorem sourceCommutantRotation_basis (θ : SourceCoordinate → ℝ) (n m : ℤ) :
    sourceCommutantRotation θ n (sourceBasis m) = sourceBasis (m+n) := by
  apply Lp.ext
  have hb := (sourceTransportIndex_preserving θ n n).quasiMeasurePreserving.ae
    (sourceBasis_coe m)
  filter_upwards [sourceTransport_apply_ae θ n n (sourceBasis m), hb,
    sourceBasis_coe (m+n)] with z ht hb he
  change (sourceTransport θ n n (sourceBasis m)) z = _
  rw [ht, hb, he]
  simp only [sourceTransportIndex]
  simp only [sub_eq_iff_eq_add]

/-- Matrix form of H(sigma^r x) = S^(-r) H(x) S^r, for the original
regular representation and every integer power of the base rotation. -/
theorem sourceMatrixEntry_covariance (θ : SourceCoordinate → ℝ)
    {H : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate}
    (hH : H ∈ sourceAlgebra θ) (r n : ℤ) :
    ∀ᵐ x ∂sourceBaseMeasure, ∀ k : ℤ,
      sourceMatrixEntry H k n (coordinateRotate θ r x) =
        sourceMatrixEntry H (k+r) (n+r) x := by
  have he : H (sourceBasis (n+r)) = sourceCommutantRotation θ r (H (sourceBasis n)) := by
    rw [← sourceCommutantRotation_basis θ r n]
    exact (congrArg (fun T : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate =>
      T (sourceBasis n)) (sourceAlgebra_commutes_rotation θ hH r)).symm
  have ht := source_ae_all_fibers (sourceTransport_apply_ae θ r r (H (sourceBasis n)))
  filter_upwards [ht] with x hx k
  unfold sourceMatrixEntry
  rw [he]
  change _ = (sourceTransport θ r r (H (sourceBasis n))) (x,k+r)
  rw [hx]
  simp [sourceTransportIndex]

/-- All countably many covariance identities hold on one conull base set. -/
theorem sourceMatrixEntry_covariance_all (θ : SourceCoordinate → ℝ)
    {H : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate}
    (hH : H ∈ sourceAlgebra θ) :
    ∀ᵐ x ∂sourceBaseMeasure, ∀ r n k : ℤ,
      sourceMatrixEntry H k n (coordinateRotate θ r x) =
        sourceMatrixEntry H (k+r) (n+r) x := by
  rw [ae_all_iff]
  intro r
  rw [ae_all_iff]
  exact sourceMatrixEntry_covariance θ hH r

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_CrossedProduct_WeightedShiftField
attribute [-instance] _root_.OAI.FiniteFactor.sourceAngleMarginal_atomless _root_.OAI.FiniteFactor.sourceBiasedRealMeasure_probability _root_.OAI.FiniteFactor.sourceFiber_separable _root_.OAI.FiniteFactor.sourceFiniteReferenceKernel_markov _root_.OAI.FiniteFactor.sourceHilbert_separable _root_.OAI.FiniteFactor.sourceNormalFunctionalSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedGroup _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedSpace _root_.OAI.FiniteFactor.sourceResamplingKernel_markov _root_.OAI.FiniteFactor.sourceSamplingLambda_finite _root_.OAI.FiniteFactor.sourceSamplingSummand_finite _root_.OAI.FiniteFactor.sourceSamplingTorus_borel _root_.OAI.FiniteFactor.sourceSamplingTorus_compact _root_.OAI.FiniteFactor.sourceSamplingTrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingUntrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingWeightedMeasure_finite _root_.OAI.FiniteFactor.sourceUnitCircle_probability
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

/-- The field of each power of the original quasinilpotent operator acts by
its verified source cocycle, simultaneously on every l2 vector. -/
theorem sourceOperatorField_sourceOperator_pow (θ : SourceCoordinate → ℝ) (hθ : SourceAngles θ)
    (q : ℕ) :
    ∀ᵐ x ∂sourceBaseMeasure, ∀ (v : SourceFiberHilbert) (k : ℤ),
      (sourceOperatorField
        (sourceOperator θ sourceLogWeight hθ.nonneg sourceLogWeight_nonneg ^ q) x v) k =
        (sourceCocycle θ sourceLogWeight q (coordinateRotate θ (k - (q : ℤ)) x) : ℂ) *
          v (k - (q : ℤ)) := by
  have hm := ae_all_iff.mpr (sourceMatrixEntry_sourceOperator_pow θ hθ q)
  filter_upwards [sourceOperatorField_entries_ae θ (pow_mem (staged_sourceOperator_mem θ hθ) q),
    hm] with x he hm v k
  rw [fiberOperator_action]
  simp_rw [he, hm]
  have ht (n : ℤ) :
      (if k = n + (q : ℤ) then
        (sourceCocycle θ sourceLogWeight q (coordinateRotate θ n x) : ℂ) else 0) * v n =
      if n = k - (q : ℤ) then
        (sourceCocycle θ sourceLogWeight q (coordinateRotate θ (k - (q : ℤ)) x) : ℂ) *
          v (k - (q : ℤ)) else 0 := by
    by_cases hn : n = k - (q : ℤ)
    · have hk : k = n + (q : ℤ) := by omega
      rw [ite_eq_left hk, ite_eq_left hn, hn]
    · have hk : k ≠ n + (q : ℤ) := by omega
      rw [ite_eq_right hk, ite_eq_right hn, zero_mul]
  simp_rw [ht]
  simp

/-- Covariance for the actual field's matrix, with all integer indices on one
conull set. This is the coordinate form of conjugation by the fiber shift. -/
theorem sourceOperatorField_covariance (θ : SourceCoordinate → ℝ)
    {H : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate}
    (hH : H ∈ sourceAlgebra θ) :
    ∀ᵐ x ∂sourceBaseMeasure, ∀ r n k : ℤ,
      (sourceOperatorField H (coordinateRotate θ r x) (lp.single 2 n (1 : ℂ))) k =
        (sourceOperatorField H x (lp.single 2 (n+r) (1 : ℂ))) (k+r) := by
  have he : ∀ᵐ x ∂sourceBaseMeasure, ∀ r : ℤ, ∀ k n : ℤ,
      (sourceOperatorField H (coordinateRotate θ r x) (lp.single 2 n (1 : ℂ))) k =
        sourceMatrixEntry H k n (coordinateRotate θ r x) := by
    rw [ae_all_iff]
    intro r
    exact (coordinateRotate_preserving θ r).quasiMeasurePreserving.ae
      (sourceOperatorField_entries_ae θ hH)
  filter_upwards [he, sourceOperatorField_entries_ae θ hH,
    sourceMatrixEntry_covariance_all θ hH] with x he hx hc r n k
  rw [he, hx, hc]

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_CrossedProduct_TorusOperatorField
attribute [-instance] _root_.OAI.FiniteFactor.sourceBiasedRealMeasure_probability _root_.OAI.FiniteFactor.sourceFiber_separable _root_.OAI.FiniteFactor.sourceFiniteReferenceKernel_markov _root_.OAI.FiniteFactor.sourceHilbert_separable _root_.OAI.FiniteFactor.sourceNormalFunctionalSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedGroup _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedSpace _root_.OAI.FiniteFactor.sourceResamplingKernel_markov _root_.OAI.FiniteFactor.sourceSamplingTrimmed_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped ENNReal
noncomputable section

theorem sourceTorusOperatorField_stronglyMeasurable
    (H : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate)
    (v : SourceFiberHilbert) :
    StronglyMeasurable (fun z => sourceTorusOperatorField H z v) :=
  (sourceOperatorField_stronglyMeasurable H v).comp_measurable sourceTorusRepresentative_preserving.measurable

theorem sourceTorusOperatorField_norm
    (H : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate) (z : SourceTorus) :
    ‖sourceTorusOperatorField H z‖ ≤ ‖H‖ := sourceOperatorField_norm H _

theorem sourceTorusOperatorField_invariant (θ : SourceCoordinate → ℝ)
    {p T : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate}
    (hp : p ∈ sourceAlgebra θ) (hT : T ∈ sourceAlgebra θ)
    (hinv : (1-p)*T*p = 0) :
    ∀ᵐ z ∂sourceTorusHaar,
      (1-sourceTorusOperatorField p z)*sourceTorusOperatorField T z*sourceTorusOperatorField p z = 0 :=
  sourceTorusRepresentative_preserving.quasiMeasurePreserving.ae
    (sourceOperatorField_invariant θ hp hT hinv)

theorem sourceTorusOperatorField_sourceOperator_pow (θ : SourceCoordinate → ℝ)
    (hθ : SourceAngles θ) (q : ℕ) :
    ∀ᵐ z ∂sourceTorusHaar, ∀ (v : SourceFiberHilbert) (k : ℤ),
      (sourceTorusOperatorField
        (sourceOperator θ sourceLogWeight hθ.nonneg sourceLogWeight_nonneg ^ q) z v) k =
        (sourceCocycle θ sourceLogWeight q
          (coordinateRotate θ (k - (q : ℤ)) (sourceTorusRepresentative z)) : ℂ) *
          v (k - (q : ℤ)) :=
  sourceTorusRepresentative_preserving.quasiMeasurePreserving.ae
    (sourceOperatorField_sourceOperator_pow θ hθ q)

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_CrossedProduct_LusinCompact
attribute [-instance] _root_.OAI.FiniteFactor.sourceBiasedRealMeasure_probability _root_.OAI.FiniteFactor.sourceFiniteReferenceKernel_markov _root_.OAI.FiniteFactor.sourceHilbert_separable _root_.OAI.FiniteFactor.sourceNormalFunctionalSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedGroup _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedSpace _root_.OAI.FiniteFactor.sourceResamplingKernel_markov _root_.OAI.FiniteFactor.sourceSamplingTrimmed_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped ENNReal
noncomputable section

/-- All cocycles and all vector columns of the actual operator field are
continuous on one compact subset of any prescribed Borel conull set. -/
theorem exists_source_lusin_compact (θ : SourceCoordinate → ℝ)
    (H : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate)
    {s : Set SourceTorus} (hs : MeasurableSet s) (hfull : ∀ᵐ z ∂sourceTorusHaar, z ∈ s)
    {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ Q, Q ⊆ s ∧ IsCompact Q ∧ sourceTorusHaar Qᶜ < ε ∧
      (∀ k : ℤ, ContinuousOn
        (fun z => sourceCocycle θ sourceLogWeight k (sourceTorusRepresentative z)) Q) ∧
      (∀ k : ℤ, ContinuousOn
        (fun z => sourceTorusOperatorField H z (lp.single 2 k (1 : ℂ))) Q) := by
  borelize (↥SourceFiberHilbert)
  let f : SourceTorus → (ℤ → ℝ × SourceFiberHilbert) := fun z k =>
    (sourceCocycle θ sourceLogWeight k (sourceTorusRepresentative z),
      sourceTorusOperatorField H z (lp.single 2 k (1 : ℂ)))
  have hf : Measurable f := by
    apply Measurable.of_eval
    intro k
    exact ((sourceCocycle_measurable θ sourceLogWeight k).comp
      sourceTorusRepresentative_preserving.measurable).prodMk
        (sourceTorusOperatorField_stronglyMeasurable H (lp.single 2 k (1 : ℂ))).measurable
  obtain ⟨Q,hQs,hQ,hμQ,hfQ⟩ := exists_compact_lusin sourceTorusHaar hf hs hfull hε
  refine ⟨Q,hQs,hQ,hμQ,?_,?_⟩
  · intro k
    exact continuous_fst.comp_continuousOn ((continuous_apply k).comp_continuousOn hfQ)
  · intro k
    exact continuous_snd.comp_continuousOn ((continuous_apply k).comp_continuousOn hfQ)

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_Fiber_StrongContinuity
attribute [-instance] _root_.OAI.FiniteFactor.sourceFiber_separable _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open Filter
open scoped Topology
noncomputable section

/-- A uniformly bounded field is strongly continuous wherever all its basis
columns are continuous. No norm-continuity of the field is required. -/
theorem fiberField_continuousOn {X : Type*} [TopologicalSpace X]
    (A : X → SourceFiberHilbert →L[ℂ] SourceFiberHilbert) (Q : Set X)
    (C : ℝ) (hC : ∀ x ∈ Q, ‖A x‖ ≤ C)
    (hb : ∀ k : ℤ, ContinuousOn (fun x => A x (lp.single 2 k (1 : ℂ))) Q)
    (v : SourceFiberHilbert) : ContinuousOn (fun x => A x v) Q := by
  classical
  let w : Finset ℤ → SourceFiberHilbert := fun s => ∑ k ∈ s, lp.single 2 k (v k)
  have hw : Tendsto w atTop (𝓝 v) := lp.hasSum_single (by norm_num) v
  have he : Tendsto (fun s => C * ‖v - w s‖) atTop (𝓝 0) := by
    simpa using ((tendsto_const_nhds (x := v)).sub hw).norm.const_mul C
  have hu : TendstoUniformlyOn (fun s x => A x (w s)) (fun x => A x v) atTop Q := by
    apply Metric.tendstoUniformlyOn_iff.mpr
    intro ε hε
    filter_upwards [(tendsto_order.mp he).2 ε hε] with s hs x hx
    rw [dist_eq_norm, ← map_sub]
    exact ((A x).le_opNorm (v - w s)).trans_lt
      ((mul_le_mul_of_nonneg_right (hC x hx) (norm_nonneg _)).trans_lt hs)
  apply hu.continuousOn
  apply Filter.Eventually.frequently
  apply Eventually.of_forall
  intro s
  have hh : (fun x => A x (w s)) =
      fun x => ∑ k ∈ s, (v k) • A x (lp.single 2 k (1 : ℂ)) := by
    funext x
    simp only [w, map_sum]
    apply Finset.sum_congr rfl
    intro k _
    rw [show lp.single 2 k (v k) = (v k) • (lp.single 2 k (1 : ℂ) : SourceFiberHilbert) by
      simp [← lp.single_smul], map_smul]
  rw [hh]
  exact continuousOn_finsetSum s (fun k _ => (hb k).const_smul (v k))

/-- Evaluation on a varying continuous vector preserves strong continuity
under a uniform operator bound. -/
theorem fiberField_continuousOn_apply {X : Type*} [TopologicalSpace X]
    (A : X → SourceFiberHilbert →L[ℂ] SourceFiberHilbert) (Q : Set X)
    (C : ℝ) (hC : ∀ x ∈ Q, ‖A x‖ ≤ C)
    (hA : ∀ v, ContinuousOn (fun x => A x v) Q)
    (v : X → SourceFiberHilbert) (hv : ContinuousOn v Q) :
    ContinuousOn (fun x => A x (v x)) Q := by
  intro x hx
  have he : Tendsto (fun y => C * ‖v y - v x‖) (𝓝[Q] x) (𝓝 0) := by
    simpa using ((hv x hx).sub_const (v x)).norm.const_mul C
  have hzero : Tendsto (fun y => A y (v y - v x)) (𝓝[Q] x) (𝓝 0) := by
    apply squeeze_zero_norm' _ he
    filter_upwards [self_mem_nhdsWithin] with y hy
    exact ((A y).le_opNorm _).trans
      (mul_le_mul_of_nonneg_right (hC y hy) (norm_nonneg _))
  have ht := hzero.add (hA (v x) x hx)
  change Tendsto _ _ _
  simpa only [map_sub, sub_add_cancel, zero_add] using ht

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_Fiber_Diagonal
attribute [-instance] _root_.OAI.FiniteFactor.sourceFiber_separable _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped Topology
noncomputable section

theorem fiberDiagonal_norm (d : ℤ → ℂ) (hd : ∀ k, ‖d k‖ ≤ 1) :
    ‖fiberDiagonal d hd‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ (by norm_num) _

theorem fiberDiagonal_single (d : ℤ → ℂ) (hd : ∀ k, ‖d k‖ ≤ 1) (n : ℤ) :
    fiberDiagonal d hd (lp.single 2 n (1 : ℂ)) = d n • lp.single 2 n (1 : ℂ) := by
  classical
  apply Subtype.ext
  funext k
  change d k * (lp.single 2 n (1 : ℂ) : SourceFiberHilbert) k =
    d n * (lp.single 2 n (1 : ℂ) : SourceFiberHilbert) k
  by_cases h : n = k
  · subst k; rfl
  · simp [lp.single_apply, h]

theorem fiberDiagonal_continuousOn {X : Type*} [TopologicalSpace X]
    (d : X → ℤ → ℂ) (hd : ∀ x k, ‖d x k‖ ≤ 1) (Q : Set X)
    (hc : ∀ k, ContinuousOn (fun x => d x k) Q) (v : SourceFiberHilbert) :
    ContinuousOn (fun x => fiberDiagonal (d x) (hd x) v) Q := by
  apply fiberField_continuousOn _ Q 1 (fun x _ => fiberDiagonal_norm _ _) _ v
  intro k
  simp_rw [fiberDiagonal_single]
  exact (hc k).smul continuousOn_const

theorem fiberDiagonal_stronglyMeasurable {X : Type*} [MeasurableSpace X]
    (d : X → ℤ → ℂ) (hd : ∀ x k, ‖d x k‖ ≤ 1)
    (hm : ∀ k, Measurable (fun x => d x k)) (v : SourceFiberHilbert) :
    StronglyMeasurable (fun x => fiberDiagonal (d x) (hd x) v) := by
  apply fiberCoordinates_stronglyMeasurable
  intro k
  exact (hm k).mul_const (v k)

/-- Applying a measurable field to a measurable vector uses finite coordinate
approximations, without measurability in the operator norm topology. -/
theorem fiberField_stronglyMeasurable_apply {X : Type*} [MeasurableSpace X]
    (A : X → SourceFiberHilbert →L[ℂ] SourceFiberHilbert)
    (hA : ∀ v, StronglyMeasurable (fun x => A x v))
    (v : X → SourceFiberHilbert) (hv : StronglyMeasurable v) :
    StronglyMeasurable (fun x => A x (v x)) := by
  classical
  apply stronglyMeasurable_of_tendsto (atTop : Filter (Finset ℤ))
    (f := fun s x => ∑ k ∈ s, (v x k) • A x (lp.single 2 k (1 : ℂ)))
  · intro s
    have h (k : ℤ) : StronglyMeasurable (fun x => (v x k) • A x (lp.single 2 k (1 : ℂ))) :=
      (((lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 k).continuous.comp_stronglyMeasurable hv).smul
        (hA (lp.single 2 k (1 : ℂ))))
    convert Finset.stronglyMeasurable_sum s (fun k _ => h k) using 1
    ext x
    simp only [Finset.sum_apply]
  · rw [tendsto_pi_nhds]
    intro x
    exact fiberOperator_hasSum (A x) (v x)

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_Fiber_PairZeroSet
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

theorem fiberPairResidual_eq_zero_iff {X : Type*}
    (P : X → SourceFiberHilbert →L[ℂ] SourceFiberHilbert)
    (d : X × X → ℤ → ℂ) (hd : ∀ z k, ‖d z k‖ ≤ 1) (z : X × X) :
    fiberPairResidual P d hd z = 0 ↔
      ∀ k : ℤ, fiberPairResidual P d hd z (lp.single 2 k (1 : ℂ)) = 0 := by
  constructor
  · intro h k; rw [h]; rfl
  · intro h
    apply fiberOperator_ext
    intro k n
    rw [h n]
    rfl

theorem fiberPairResidual_continuousOn {X : Type*} [TopologicalSpace X]
    (P : X → SourceFiberHilbert →L[ℂ] SourceFiberHilbert)
    (d : X × X → ℤ → ℂ) (hd : ∀ z k, ‖d z k‖ ≤ 1)
    (Q : Set X) (C : ℝ) (hC : ∀ x ∈ Q, ‖P x‖ ≤ C)
    (hP : ∀ k : ℤ, ContinuousOn (fun x => P x (lp.single 2 k (1 : ℂ))) Q)
    (hdc : ∀ k, ContinuousOn (fun z => d z k) (Q ×ˢ Q)) (v : SourceFiberHilbert) :
    ContinuousOn (fun z => fiberPairResidual P d hd z v) (Q ×ˢ Q) := by
  have hPs (w : SourceFiberHilbert) := fiberField_continuousOn P Q C hC hP w
  have hx (w : SourceFiberHilbert) : ContinuousOn (fun z : X × X => P z.1 w) (Q ×ˢ Q) :=
    (hPs w).comp continuous_fst.continuousOn (fun z hz => hz.1)
  have hy (w : SourceFiberHilbert) : ContinuousOn (fun z : X × X => P z.2 w) (Q ×ˢ Q) :=
    (hPs w).comp continuous_snd.continuousOn (fun z hz => hz.2)
  have hD (w : SourceFiberHilbert) := fiberDiagonal_continuousOn d hd (Q ×ˢ Q) hdc w
  have hv := fiberField_continuousOn_apply (fun z => fiberDiagonal (d z) (hd z))
    (Q ×ˢ Q) 1 (fun z _ => fiberDiagonal_norm _ _) hD (fun z => P z.1 v) (hx v)
  have hpv := fiberField_continuousOn_apply (fun z : X × X => P z.2)
    (Q ×ˢ Q) C (fun z hz => hC z.2 hz.2) hy _ hv
  exact hv.sub hpv

theorem fiberPairResidual_stronglyMeasurable {X : Type*} [MeasurableSpace X]
    (P : X → SourceFiberHilbert →L[ℂ] SourceFiberHilbert)
    (d : X × X → ℤ → ℂ) (hd : ∀ z k, ‖d z k‖ ≤ 1)
    (hP : ∀ v, StronglyMeasurable (fun x => P x v))
    (hdm : ∀ k, Measurable (fun z => d z k)) (v : SourceFiberHilbert) :
    StronglyMeasurable (fun z => fiberPairResidual P d hd z v) := by
  have hv := fiberField_stronglyMeasurable_apply (fun z => fiberDiagonal (d z) (hd z))
    (fun w => fiberDiagonal_stronglyMeasurable d hd hdm w)
    (fun z => P z.1 v) ((hP v).comp_measurable measurable_fst)
  have hpv := fiberField_stronglyMeasurable_apply (fun z : X × X => P z.2)
    (fun w => (hP w).comp_measurable measurable_snd) _ hv
  exact hv.sub hpv

theorem fiberPairZeroSet_measurable {X : Type*} [MeasurableSpace X]
    (P : X → SourceFiberHilbert →L[ℂ] SourceFiberHilbert)
    (d : X × X → ℤ → ℂ) (hd : ∀ z k, ‖d z k‖ ≤ 1)
    (hP : ∀ v, StronglyMeasurable (fun x => P x v))
    (hdm : ∀ k, Measurable (fun z => d z k)) :
    MeasurableSet {z | fiberPairResidual P d hd z = 0} := by
  borelize (↥SourceFiberHilbert)
  simp_rw [fiberPairResidual_eq_zero_iff, Set.ofPred_forall]
  exact MeasurableSet.iInter (fun k => measurableSet_eq_fun
    (fiberPairResidual_stronglyMeasurable P d hd hP hdm _).measurable measurable_const)

theorem fiberPairZeroSet_compact {X : Type*} [TopologicalSpace X] [T2Space X]
    (P : X → SourceFiberHilbert →L[ℂ] SourceFiberHilbert)
    (d : X × X → ℤ → ℂ) (hd : ∀ z k, ‖d z k‖ ≤ 1)
    (Q : Set X) (hQ : IsCompact Q) (C : ℝ) (hC : ∀ x ∈ Q, ‖P x‖ ≤ C)
    (hP : ∀ k : ℤ, ContinuousOn (fun x => P x (lp.single 2 k (1 : ℂ))) Q)
    (hdc : ∀ k, ContinuousOn (fun z => d z k) (Q ×ˢ Q)) :
    IsCompact ((Q ×ˢ Q) ∩ {z | fiberPairResidual P d hd z = 0}) := by
  have he : ((Q ×ˢ Q) ∩ {z | fiberPairResidual P d hd z = 0}) =
      ⋂ k : ℤ, ((Q ×ˢ Q) ∩ {z | fiberPairResidual P d hd z (lp.single 2 k (1 : ℂ)) = 0}) := by
    ext z
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_iInter,
      fiberPairResidual_eq_zero_iff]
    constructor
    · rintro ⟨hz,h⟩ k; exact ⟨hz,h k⟩
    · intro h; exact ⟨(h 0).1,fun k => (h k).2⟩
  apply (hQ.prod hQ).of_isClosed_subset _ Set.inter_subset_left
  rw [he]
  apply isClosed_iInter
  intro k
  exact (fiberPairResidual_continuousOn P d hd Q C hC hP hdc _).preimage_isClosed_of_isClosed
    (hQ.prod hQ).isClosed isClosed_singleton

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_CrossedProduct_CappedPair
attribute [-instance] _root_.OAI.FiniteFactor.sourceBiasedRealMeasure_probability _root_.OAI.FiniteFactor.sourceFiniteReferenceKernel_markov _root_.OAI.FiniteFactor.sourceHilbert_separable _root_.OAI.FiniteFactor.sourceNormalFunctionalSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedGroup _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedSpace _root_.OAI.FiniteFactor.sourceResamplingKernel_markov _root_.OAI.FiniteFactor.sourceSamplingTrimmed_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped Topology ENNReal
noncomputable section

theorem sourceCappedRatio_measurable (θ : SourceCoordinate → ℝ) (k : ℤ) :
    Measurable (fun z => sourceCappedRatio θ z k) := by
  apply Complex.measurable_ofReal.comp
  apply Measurable.min _ measurable_const
  exact (((sourceCocycle_measurable θ sourceLogWeight k).comp
    sourceTorusRepresentative_preserving.measurable).comp measurable_snd).div
    (((sourceCocycle_measurable θ sourceLogWeight k).comp
      sourceTorusRepresentative_preserving.measurable).comp measurable_fst)

theorem sourceCappedRatio_continuousOn (θ : SourceCoordinate → ℝ) (Q : Set SourceTorus)
    (hF : ∀ k : ℤ, ContinuousOn
      (fun z => sourceCocycle θ sourceLogWeight k (sourceTorusRepresentative z)) Q) (k : ℤ) :
    ContinuousOn (fun z => sourceCappedRatio θ z k) (Q ×ˢ Q) := by
  apply Complex.continuous_ofReal.comp_continuousOn
  apply ContinuousOn.inf _ continuousOn_const
  exact ((hF k).comp continuous_snd.continuousOn (fun z hz => hz.2)).div
    ((hF k).comp continuous_fst.continuousOn (fun z hz => hz.1))
    (fun z _ => ne_of_gt (sourceCocycle_pos ..))

theorem sourceCappedPairZeroSet_measurable (θ : SourceCoordinate → ℝ)
    (H : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate) :
    MeasurableSet (sourceCappedPairZeroSet θ H) :=
  fiberPairZeroSet_measurable _ _ _ (sourceTorusOperatorField_stronglyMeasurable H)
    (sourceCappedRatio_measurable θ)

/-- The compact zero sets needed for Portmanteau are constructed from the
actual field and original cocycles, with arbitrarily small Haar loss. -/
theorem exists_source_capped_compact (θ : SourceCoordinate → ℝ)
    (H : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate)
    {s : Set SourceTorus} (hs : MeasurableSet s) (hfull : ∀ᵐ z ∂sourceTorusHaar, z ∈ s)
    {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ Q, Q ⊆ s ∧ IsCompact Q ∧ sourceTorusHaar Qᶜ < ε ∧
      IsCompact ((Q ×ˢ Q) ∩ sourceCappedPairZeroSet θ H) := by
  obtain ⟨Q,hQs,hQ,hμQ,hF,hP⟩ := exists_source_lusin_compact θ H hs hfull hε
  exact ⟨Q,hQs,hQ,hμQ,fiberPairZeroSet_compact _ _ _ Q hQ ‖H‖
    (fun z _ => sourceTorusOperatorField_norm H z) hP
      (sourceCappedRatio_continuousOn θ Q hF)⟩

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

theorem sourceTorusQuotient_rotate (θ x : SourceCoordinate → ℝ) (n : ℤ) :
    sourceTorusQuotient (coordinateRotate θ n x) = sourceTorusRotate θ n (sourceTorusQuotient x) := by
  funext i
  simp only [sourceTorusQuotient,coordinateRotate,sourceTorusRotate,AddCircle.coe_fract,
    AddCircle.coe_add,← zsmul_eq_mul,AddCircle.coe_zsmul]

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_TailEstimate
attribute [-instance] _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory
open scoped ENNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- Cauchy–Schwarz in the integral form used on Ω × ℤ. -/
theorem integral_mul_le_sqrt_squares {f g : Ω → ℝ}
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ)
    (hf0 : 0 ≤ᵐ[μ] f) (hg0 : 0 ≤ᵐ[μ] g) :
    ∫ ω, f ω * g ω ∂μ ≤
      Real.sqrt (∫ ω, f ω ^ 2 ∂μ) * Real.sqrt (∫ ω, g ω ^ 2 ∂μ) := by
  have hh : Real.HolderConjugate 2 2 := by norm_num [Real.holderConjugate_iff]
  have h := integral_mul_le_Lp_mul_Lq_of_nonneg hh hf0 hg0
    (by simpa using hf) (by simpa using hg)
  simpa [Real.sqrt_eq_rpow] using h

end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_L2UniformAbsoluteContinuity
attribute [-instance] _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped ENNReal NNReal Topology
noncomputable section

/-- Cauchy--Schwarz bounds the mass of any Borel set under an actual L2
density, in terms of the original reference measure of the set. -/
theorem withDensity_L2_set_le {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] (g : X → ℝ)
    (hg : MemLp g 2 μ) (hg0 : ∀ x, 0 ≤ g x)
    (A : Set X) (hA : MeasurableSet A) (C : ℝ) (hC : (∫ x, g x ^ 2 ∂μ) ≤ C) :
    (μ.withDensity (fun x => ENNReal.ofReal (g x))) A ≤
      ENNReal.ofReal (Real.sqrt C * Real.sqrt ((μ A).toReal)) := by
  have hi : MemLp (A.indicator (fun _ : X => (1 : ℝ))) 2 μ :=
    (memLp_const (1 : ℝ)).indicator hA
  have hcs := integral_mul_le_sqrt_squares hg hi
    (Eventually.of_forall hg0)
    (Eventually.of_forall (fun x => Set.indicator_nonneg (fun _ _ => zero_le_one) x))
  have hint : (∫ x, g x * A.indicator (fun _ : X => (1 : ℝ)) x ∂μ) = ∫ x in A, g x ∂μ := by
    rw [← integral_indicator hA]
    apply integral_congr_ae
    apply Eventually.of_forall
    intro x
    by_cases hx : x ∈ A <;> simp [hx]
  have hsquare : (∫ x, (A.indicator (fun _ : X => (1 : ℝ)) x) ^ 2 ∂μ) = (μ A).toReal := by
    have he : (fun x => (A.indicator (fun _ : X => (1 : ℝ)) x) ^ 2) =
        A.indicator (fun _ : X => (1 : ℝ)) := by
      funext x; by_cases hx : x ∈ A <;> simp [hx]
    rw [he, integral_indicator hA]
    simp [measureReal_def]
  rw [hint, hsquare] at hcs
  rw [withDensity_apply _ hA, ← ofReal_integral_eq_lintegral_ofReal
    (hg.integrable (by norm_num)).restrict (Eventually.of_forall hg0)]
  exact ENNReal.ofReal_le_ofReal (hcs.trans
    (mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hC) (Real.sqrt_nonneg _)))

/-- Uniform L2 density bounds imply uniform absolute continuity, with no
measurable-selection premise for the densities. -/
theorem uniformAC_of_L2_densities {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] (ν : ℕ → Measure X) (C : ℝ)
    (hν : ∀ n, ∃ g : X → ℝ, MemLp g 2 μ ∧ (∀ x, 0 ≤ g x) ∧
      ν n = μ.withDensity (fun x => ENNReal.ofReal (g x)) ∧ (∫ x, g x^2 ∂μ) ≤ C)
    (ε : ℝ≥0) (hε : 0 < ε) :
    ∃ δ : ℝ≥0∞, 0 < δ ∧ ∀ A, MeasurableSet A → μ A < δ → ∀ n, ν n A ≤ ε := by
  let r : ℝ := (ε : ℝ) / (Real.sqrt C + 1)
  have hr : 0 < r := div_pos (by exact_mod_cast hε) (by positivity)
  refine ⟨ENNReal.ofReal (r^2), ENNReal.ofReal_pos.mpr (sq_pos_of_pos hr), ?_⟩
  intro A hA hμ n
  obtain ⟨g,hg,hg0,he,hgC⟩ := hν n
  rw [he]
  apply (withDensity_L2_set_le μ g hg hg0 A hA C hgC).trans
  have hreal : (μ A).toReal ≤ r^2 := by
    exact (ENNReal.toReal_le_of_le_ofReal (by positivity) hμ.le)
  have hs : Real.sqrt ((μ A).toReal) ≤ r := by
    exact (Real.sqrt_le_sqrt hreal).trans_eq (Real.sqrt_sq hr.le)
  have hmul : Real.sqrt C * r ≤ (ε : ℝ) := by
    have heq : r * (Real.sqrt C + 1) = (ε : ℝ) := div_mul_cancel₀ _ (by positivity)
    nlinarith [Real.sqrt_nonneg C]
  exact (ENNReal.ofReal_le_ofReal
    ((mul_le_mul_of_nonneg_left hs (Real.sqrt_nonneg C)).trans hmul)).trans_eq (by simp)

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_CrossedProduct_CappedTransfer
attribute [-instance] _root_.OAI.FiniteFactor.sourceBiasedRealMeasure_probability _root_.OAI.FiniteFactor.sourceFiniteReferenceKernel_markov _root_.OAI.FiniteFactor.sourceHilbert_separable _root_.OAI.FiniteFactor.sourceNormalFunctionalSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedGroup _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedSpace _root_.OAI.FiniteFactor.sourceResamplingKernel_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped ENNReal NNReal Topology
noncomputable section

/-- Uniform absolute continuity of both actual ordered sampling marginals,
derived from the previously proved L2 density bounds. -/
theorem SourceOrderedTorusSampling.uniformAC {θ : SourceCoordinate → ℝ}
    (hθ : SourceOrderedTorusSampling θ) (I : Finset SourceCoordinate) (r : Bool)
    (ε : ℝ≥0) (hε : 0 < ε) :
    ∃ δ : ℝ≥0∞, 0 < δ ∧ ∀ A, MeasurableSet A → sourceTorusHaar A < δ → ∀ n,
      ((sourceSamplingTrimmedTorus I n θ : Measure SourceSamplingTorus).map
        (sourceTorusEndpoint r)) A ≤ ε := by
  obtain ⟨C,hC⟩ := hθ.marginals I r
  apply uniformAC_of_L2_densities sourceTorusHaar _ C _ ε hε
  intro n
  obtain ⟨g,hg,hg0,he,hglp,hgC⟩ := hC n
  exact ⟨g,hglp,hg0,he,hgC⟩

/-- The actual capped projection equation passes to lambda_I on the original
sampling torus. The approximant equations are the remaining orbit obligation;
no continuity or measurable-selection premise is assumed. -/
theorem sourceCappedPair_limit_transfer {θ : SourceCoordinate → ℝ}
    (hθ : SourceOrderedTorusSampling θ) (I : Finset SourceCoordinate)
    (H : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate)
    (hpair : ∀ n, ∀ᵐ z ∂(sourceSamplingTrimmedTorus I n θ : Measure SourceSamplingTorus),
      z ∈ sourceCappedPairZeroSet θ H) :
    ∀ᵐ z ∂(sourceSamplingLambdaTorus I : Measure SourceSamplingTorus),
      z ∈ sourceCappedPairZeroSet θ H := by
  have hlim : Tendsto (fun n => sourceSamplingTrimmedTorus I n θ) atTop
      (𝓝 (sourceSamplingLambdaTorus I)) := by
    apply FiniteMeasure.tendsto_of_forall_integral_tendsto
    intro f
    exact hθ.weak I f.toContinuousMap
  apply finiteMeasure_ae_of_compact_approximation _ _ hlim _
    (sourceCappedPairZeroSet_measurable θ H)
  intro ε hε
  have hhalf : 0 < ε / 2 := half_pos hε
  obtain ⟨δ₁,hδ₁,h₁⟩ := hθ.uniformAC I false (ε / 2) hhalf
  obtain ⟨δ₂,hδ₂,h₂⟩ := hθ.uniformAC I true (ε / 2) hhalf
  obtain ⟨Q,_,hQ,hμQ,hK⟩ := exists_source_capped_compact θ H
    MeasurableSet.univ (Eventually.of_forall (fun _ => Set.mem_univ _))
    (ne_of_gt (lt_min hδ₁ hδ₂))
  refine ⟨(Q ×ˢ Q) ∩ sourceCappedPairZeroSet θ H,hK,Set.inter_subset_right,?_⟩
  intro n
  have hb₁ := h₁ Qᶜ hQ.isClosed.measurableSet.compl
    (hμQ.trans_le (min_le_left _ _)) n
  have hb₂ := h₂ Qᶜ hQ.isClosed.measurableSet.compl
    (hμQ.trans_le (min_le_right _ _)) n
  have hb := add_le_add hb₁ hb₂
  have he : (↑(ε / 2) : ℝ≥0∞) + ↑(ε / 2) = ε := by
    rw [← ENNReal.coe_add, add_halves]
  rw [he] at hb
  exact (measure_pair_compact_loss _ Q hQ.isClosed.measurableSet _ (hpair n)).trans hb

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_Fiber_Shift
attribute [-instance] _root_.OAI.FiniteFactor.sourceFiber_separable _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open Filter
open scoped ENNReal
noncomputable section

theorem fiberShift_single (n m : ℤ) (c : ℂ) :
    fiberShift n (lp.single 2 m c) = lp.single 2 (m+n) c := by
  classical
  apply Subtype.ext
  funext k
  change (lp.single 2 m c : SourceFiberHilbert) (k-n) =
    (lp.single 2 (m+n) c : SourceFiberHilbert) k
  by_cases h : m = k-n
  · simp [lp.single_apply, h]
  · have hh : m+n ≠ k := by omega
    simp [lp.single_apply, h, hh]

theorem fiber_covariance_operator
    (A B : SourceFiberHilbert →L[ℂ] SourceFiberHilbert) (n : ℤ)
    (h : ∀ k m : ℤ, (B (lp.single 2 m (1 : ℂ))) k =
      (A (lp.single 2 (m+n) (1 : ℂ))) (k+n)) :
    fiberShift (-n) * A = B * fiberShift (-n) := by
  apply fiberOperator_ext
  intro k m
  change (A (lp.single 2 m (1 : ℂ))) (k-(-n)) =
    (B (fiberShift (-n) (lp.single 2 m (1 : ℂ)))) k
  rw [fiberShift_single, h]
  simp

/-- Invariance of a projection range persists under every nonnegative power. -/
theorem invariant_projection_pow {R : Type*} [Ring R] (p T : R)
    (hp : p*p = p) (hinv : (1-p)*T*p = 0) : ∀ n : ℕ, (1-p)*(T^n)*p = 0 := by
  have hTp : T*p = p*T*p := by
    have h := hinv
    rw [sub_mul, one_mul, sub_mul] at h
    exact sub_eq_zero.mp h
  have hfix : ∀ n : ℕ, T^n*p = p*(T^n)*p := by
    intro n
    induction n with
    | zero => simpa using hp.symm
    | succ n ih =>
      calc
        T^(n+1)*p = T*(T^n*p) := by rw [pow_succ', mul_assoc]
        _ = T*(p*T^n*p) := by rw [ih]
        _ = (T*p)*T^n*p := by simp only [mul_assoc]
        _ = (p*T*p)*T^n*p := by rw [hTp]
        _ = p*T*(p*T^n*p) := by simp only [mul_assoc]
        _ = p*T*(T^n*p) := by rw [← ih]
        _ = p*T^(n+1)*p := by rw [pow_succ']; simp only [mul_assoc]
  intro n
  rw [sub_mul, one_mul, sub_mul, hfix n]
  simp only [mul_assoc, sub_self]

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_CrossedProduct_OrbitNormalization
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

theorem sourceCocycle_orbit_ratio (θ c : SourceCoordinate → ℝ)
    {x : SourceCoordinate → ℝ} (hx : finiteFloorSupport θ x) (n k : ℤ) :
    sourceCocycle θ c k (coordinateRotate θ n x) / sourceCocycle θ c k x =
      sourceCocycle θ c n (coordinateRotate θ k x) / sourceCocycle θ c n x := by
  apply (div_eq_div_iff (ne_of_gt (sourceCocycle_pos ..)) (ne_of_gt (sourceCocycle_pos ..))).mpr
  rw [← sourceCocycle_add θ c hx n k, ← sourceCocycle_add θ c hx k n, add_comm n k]

theorem sourceTorusRepresentative_rotate (θ : SourceCoordinate → ℝ) (n : ℤ) (z : SourceTorus) :
    sourceTorusRepresentative (sourceTorusRotate θ n z) =
      coordinateRotate θ n (sourceTorusRepresentative z) := by
  have hc : ∀ i, coordinateRotate θ n (sourceTorusRepresentative z) i ∈ Set.Ico (0 : ℝ) 1 :=
    fun i => ⟨Int.fract_nonneg _,Int.fract_lt_one _⟩
  calc
    _ = sourceTorusRepresentative (sourceTorusQuotient
        (coordinateRotate θ n (sourceTorusRepresentative z))) := by
      rw [sourceTorusQuotient_rotate, sourceTorusQuotient_representative]
    _ = _ := sourceTorusRepresentative_quotient _ hc

/-- Covariance and invariance give the rotated range inclusion after removing
the shift. This is an identity of bounded operators, not a range assumption. -/
theorem fiber_rotated_invariant
    (A B W : SourceFiberHilbert →L[ℂ] SourceFiberHilbert) (n : ℤ)
    (hc : fiberShift (-n) * A = B * fiberShift (-n))
    (hi : (1-A)*W*A = 0) :
    (1-B)*(fiberShift (-n)*W)*A = 0 := by
  have he : (1-B)*fiberShift (-n) = fiberShift (-n)*(1-A) := by
    rw [sub_mul, one_mul, mul_sub, mul_one, hc]
  calc
    _ = ((1-B)*fiberShift (-n))*W*A := by simp only [mul_assoc]
    _ = (fiberShift (-n)*(1-A))*W*A := by rw [he]
    _ = fiberShift (-n)*((1-A)*W*A) := by simp only [mul_assoc]
    _ = 0 := by rw [hi, mul_zero]

/-- On ordered actual orbit pairs, the capped diagonal is exactly the
normalized weighted shift power. -/
theorem sourceCappedRatio_orbit_diagonal
    (θ : SourceCoordinate → ℝ) (z : SourceTorus) (n : ℕ)
    (hx : finiteFloorSupport θ (sourceTorusRepresentative z))
    (hord : ∀ i, sourceTorusRepresentative z i ≤
      sourceTorusRepresentative (sourceTorusRotate θ n z) i)
    (W : SourceFiberHilbert →L[ℂ] SourceFiberHilbert)
    (hW : ∀ (v : SourceFiberHilbert) (k : ℤ), W v k =
      (sourceCocycle θ sourceLogWeight n
        (coordinateRotate θ (k-(n : ℤ)) (sourceTorusRepresentative z)) : ℂ) * v (k-(n : ℤ))) :
    fiberDiagonal (sourceCappedRatio θ (z,sourceTorusRotate θ n z))
      (sourceCappedRatio_norm θ (z,sourceTorusRotate θ n z)) =
    (sourceCocycle θ sourceLogWeight n (sourceTorusRepresentative z) : ℂ)⁻¹ •
      (fiberShift (-(n : ℤ))*W) := by
  apply ContinuousLinearMap.ext
  intro v
  apply Subtype.ext
  funext k
  change sourceCappedRatio θ (z,sourceTorusRotate θ n z) k * v k =
    (sourceCocycle θ sourceLogWeight n (sourceTorusRepresentative z) : ℂ)⁻¹ *
      (W v (k-(-(n : ℤ))))
  have hord' : ∀ i, sourceTorusRepresentative z i ≤ coordinateRotate θ n (sourceTorusRepresentative z) i := by
    simpa only [sourceTorusRepresentative_rotate] using hord
  have hle := sourceCocycle_ordered θ sourceLogWeight sourceLogWeight_nonneg hx
    (finiteFloorSupport_rotate θ hx n) hord' k
  rw [sourceCappedRatio, sourceTorusRepresentative_rotate,
    min_eq_left ((div_le_one (sourceCocycle_pos ..)).mpr hle),
    sourceCocycle_orbit_ratio θ sourceLogWeight hx n k, Complex.ofReal_div, hW]
  have he : k-(-(n : ℤ))-(n : ℤ) = k := by omega
  rw [he]
  simp only [div_eq_mul_inv]
  ring

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_CrossedProduct_ProjectionPairIdentity
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

/-- Every original invariant projection satisfies the normalized equation on
all its ordered positive orbit pairs, on one conull set. -/
theorem sourceProjection_ordered_orbits (θ : SourceCoordinate → ℝ) (hθ : SourceAngles θ)
    {p : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate}
    (hp : p ∈ sourceAlgebra θ) (hproj : IsStarProjection p)
    (hinv : (1-p)*sourceOperator θ sourceLogWeight hθ.nonneg sourceLogWeight_nonneg*p = 0) :
    ∀ᵐ z ∂sourceTorusHaar, ∀ n : ℕ,
      (∀ i, sourceTorusRepresentative z i ≤ sourceTorusRepresentative (sourceTorusRotate θ n z) i) →
      (z,sourceTorusRotate θ n z) ∈ sourceCappedPairZeroSet θ p := by
  let T := sourceOperator θ sourceLogWeight hθ.nonneg sourceLogWeight_nonneg
  have hf := sourceTorusRepresentative_preserving.quasiMeasurePreserving.ae
    (ae_finiteFloorSupport θ hθ.summable)
  have hc := sourceTorusRepresentative_preserving.quasiMeasurePreserving.ae
    (sourceOperatorField_covariance θ hp)
  have hi : ∀ᵐ z ∂sourceTorusHaar, ∀ n : ℕ,
      (1-sourceTorusOperatorField p z)*sourceTorusOperatorField (T^n) z*sourceTorusOperatorField p z = 0 := by
    rw [ae_all_iff]
    intro n
    exact sourceTorusOperatorField_invariant θ hp (pow_mem (staged_sourceOperator_mem θ hθ) n)
      (invariant_projection_pow p T hproj.isIdempotentElem hinv n)
  have hw := ae_all_iff.mpr (sourceTorusOperatorField_sourceOperator_pow θ hθ)
  filter_upwards [hf,hc,hi,hw] with z hf hc hi hw n hord
  have hcov : fiberShift (-(n : ℤ))*sourceTorusOperatorField p z =
      sourceTorusOperatorField p (sourceTorusRotate θ n z)*fiberShift (-(n : ℤ)) := by
    apply fiber_covariance_operator
    intro k m
    change (sourceOperatorField p (sourceTorusRepresentative (sourceTorusRotate θ n z))
      (lp.single 2 m (1 : ℂ))) k = _
    rw [sourceTorusRepresentative_rotate]
    exact hc n m k
  have hrot := fiber_rotated_invariant _ _ (sourceTorusOperatorField (T^n) z) n hcov (hi n)
  change (1-sourceTorusOperatorField p (sourceTorusRotate θ n z))*
    fiberDiagonal (sourceCappedRatio θ (z,sourceTorusRotate θ n z))
      (sourceCappedRatio_norm θ (z,sourceTorusRotate θ n z))*sourceTorusOperatorField p z = 0
  rw [sourceCappedRatio_orbit_diagonal θ z n hf hord _ (hw n)]
  ext1 vector
  have hv := congrArg (fun operator : SourceFiberHilbert →L[ℂ] SourceFiberHilbert =>
    operator vector) hrot
  dsimp only [T] at hv
  simp only [mul_apply_eq_comp, zero_apply] at hv
  simp only [mul_apply_eq_comp, smul_apply, map_smul, zero_apply, hv, smul_zero]

/-- The approximant equations follow from the original invariant projection,
the actual positive orbit support, and absolute continuity of the first
marginal. They are not assumed as a transfer premise. -/
theorem sourceProjection_sampling_pairs (θ : SourceCoordinate → ℝ) (hθ : SourceAngles θ)
    (hs : SourceOrderedTorusSampling θ)
    {p : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate}
    (hp : p ∈ sourceAlgebra θ) (hproj : IsStarProjection p)
    (hinv : (1-p)*sourceOperator θ sourceLogWeight hθ.nonneg sourceLogWeight_nonneg*p = 0)
    (I : Finset SourceCoordinate) (s : ℕ) :
    ∀ᵐ z ∂(sourceSamplingTrimmedTorus I s θ : Measure SourceSamplingTorus),
      z ∈ sourceCappedPairZeroSet θ p := by
  obtain ⟨C,hC⟩ := hs.marginals I false
  obtain ⟨g,_,_,hg,_,_⟩ := hC s
  have hac : (sourceSamplingTrimmedTorus I s θ : Measure SourceSamplingTorus).map Prod.fst ≪
      sourceTorusHaar := by
    change (sourceSamplingTrimmedTorus I s θ : Measure SourceSamplingTorus).map
      (sourceTorusEndpoint false) ≪ _
    rw [hg]
    exact withDensity_absolutelyContinuous _ _
  have horbit := ae_of_ae_map measurable_fst.aemeasurable
    (hac.ae_le (sourceProjection_ordered_orbits θ hθ hp hproj hinv))
  filter_upwards [horbit,hs.support I s] with z hz hsupport
  obtain ⟨hord,n,hn,hnpos,he⟩ := hsupport
  have hn0 : 0 ≤ n := le_of_lt hnpos
  have hncast : (n.toNat : ℤ) = n := Int.toNat_of_nonneg hn0
  have hh := hz n.toNat
  rw [hncast, ← he] at hh
  exact hh hord

theorem sourceProjection_lambda_pairs (θ : SourceCoordinate → ℝ) (hθ : SourceAngles θ)
    (hs : SourceOrderedTorusSampling θ)
    {p : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate}
    (hp : p ∈ sourceAlgebra θ) (hproj : IsStarProjection p)
    (hinv : (1-p)*sourceOperator θ sourceLogWeight hθ.nonneg sourceLogWeight_nonneg*p = 0)
    (I : Finset SourceCoordinate) :
    ∀ᵐ z ∂(sourceSamplingLambdaTorus I : Measure SourceSamplingTorus),
      z ∈ sourceCappedPairZeroSet θ p :=
  sourceCappedPair_limit_transfer hs I p (sourceProjection_sampling_pairs θ hθ hs hp hproj hinv I)

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_BiasedPairs_PairIdentity
attribute [-instance] _root_.OAI.FiniteFactor.sourceHilbert_separable _root_.OAI.FiniteFactor.sourceNormalFunctionalSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedGroup _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped ENNReal NNReal Topology
noncomputable section

theorem sourceProjection_biased_prefix_pairs_oai (θ : SourceCoordinate → ℝ) (hθ : SourceAngles θ)
    (hs : SourceOrderedTorusSampling θ)
    {p : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate}
    (hp : p ∈ sourceAlgebra θ) (hproj : IsStarProjection p)
    (hinv : (1-p)*sourceOperator θ sourceLogWeight hθ.nonneg sourceLogWeight_nonneg*p = 0)
    (j n : ℕ) :
    ∀ᵐ z ∂(sourceBiasedTorusMeasure j (sourceBiasedPrefixMask n) : Measure SourceSamplingTorus),
      z ∈ sourceCappedPairZeroSet θ p := by
  apply (sourceBiasedPrefix_domination j n).ae_le
  change ∀ᵐ z ∂(∑ I ∈ (CouplingParameters.blockPrefix sourceBlockSize n).powerset,
    (sourceSamplingLambdaTorus I : Measure SourceSamplingTorus)), z ∈ sourceCappedPairZeroSet θ p
  rw [ae_iff,Measure.finsetSum_apply]
  apply Finset.sum_eq_zero
  intro I hI
  exact ae_iff.mp (sourceProjection_lambda_pairs θ hθ hs hp hproj hinv I)

end
end FiniteFactor

end OAI
end

theorem solution : type_of% @OAI.FiniteFactor.sourceProjection_biased_prefix_pairs_oai := @OAI.FiniteFactor.sourceProjection_biased_prefix_pairs_oai
