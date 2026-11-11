-- Prove2me | solution 1 for OAI.Invariant233.BlockedProductCoupling.eventually_flatSourceEvent_mass
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T19:31:15.36619+00:00
-- url     : https://prove2.me/submissions/830a5a9a-d04b-4f7b-99e2-2aae8bb2c8a8

import Mathlib
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.FiniteSupport.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Polynomial.Degree.TrailingDegree
import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.Algebra.Polynomial.OfFn
import Mathlib.Analysis.CStarAlgebra.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLogExp
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Int.Interval
import Mathlib.Dynamics.Ergodic.MeasurePreserving
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Group.AddCircle
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.QuasiMeasurePreserving
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.Kernel.Composition.MeasureCompProd
import Mathlib.Probability.Kernel.CondDistrib
import Mathlib.Probability.Moments.Variance
import Mathlib.Probability.ProductMeasure
import Mathlib.Tactic
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.Instances.AddCircle.Defs
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.MetricSpace.Cauchy
import Definitions.Def_IrrationalRotation
import Definitions.Def_Q234IR003

section
-- module Solutions.Q234_IR.Compat
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {c : Prop} {_ : Decidable c} {a b : α} (h : c) :
    (if c then a else b) = a := if_pos h
end OAICompat434

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Analysis_EndpointIntervalBounds
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal

namespace InvariantRotation.EndpointIntervalBounds

theorem measureReal_le_mul_of_le_smul {Ω : Type*} [MeasurableSpace Ω]
    {μ ν : Measure Ω} {C : ℝ} (hC : 0 ≤ C)
    (hdom : ν ≤ ENNReal.ofReal C • μ) (A : Set Ω) (hA : μ A ≠ ∞) :
    ν.real A ≤ C * μ.real A := by
  have hb : ν A ≤ ENNReal.ofReal C * μ A := by
    simpa only [Measure.smul_apply, smul_eq_mul] using hdom A
  have hfinite : ENNReal.ofReal C * μ A ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hA
  have hreal := ENNReal.toReal_mono hfinite hb
  simpa only [measureReal_def, ENNReal.toReal_mul, ENNReal.toReal_ofReal hC] using hreal

theorem intervalMeasure_lower_tail_le {d : ℝ} (hd : 0 ≤ d) :
    (volume.restrict (Ico (0 : ℝ) 1)).real (Iic d) ≤ d := by
  rw [measureReal_restrict_apply measurableSet_Iic]
  calc
    volume.real (Iic d ∩ Ico 0 1) ≤ volume.real (Icc 0 d) :=
      measureReal_mono (fun x hx => ⟨hx.2.1, hx.1⟩) (by simp)
    _ = d := by rw [Real.volume_real_Icc_of_le hd]; ring

theorem intervalMeasure_upper_tail_le {d : ℝ} (hd : 0 ≤ d) :
    (volume.restrict (Ico (0 : ℝ) 1)).real (Ici (1 - d)) ≤ d := by
  rw [measureReal_restrict_apply measurableSet_Ici]
  calc
    volume.real (Ici (1 - d) ∩ Ico 0 1) ≤ volume.real (Icc (1 - d) 1) :=
      measureReal_mono (fun x hx => ⟨hx.1, hx.2.2.le⟩) (by simp)
    _ = d := by rw [Real.volume_real_Icc_of_le (by linarith)]; ring

theorem lower_endpoint_loss_le {ν : Measure ℝ} {C d : ℝ} (hC : 0 ≤ C) (hd : 0 ≤ d)
    (hdom : ν ≤ ENNReal.ofReal C • volume.restrict (Ico (0 : ℝ) 1)) :
    ν.real (Iic d) ≤ C * d := by
  refine (measureReal_le_mul_of_le_smul hC hdom (Iic d) ?_).trans
    (mul_le_mul_of_nonneg_left (intervalMeasure_lower_tail_le hd) hC)
  rw [Measure.restrict_apply measurableSet_Iic]
  exact (measure_mono (show Iic d ∩ Ico (0 : ℝ) 1 ⊆ Ico 0 1 from inter_subset_right)
    |>.trans_lt (by simp)).ne

theorem upper_endpoint_loss_le {ν : Measure ℝ} {C d : ℝ} (hC : 0 ≤ C) (hd : 0 ≤ d)
    (hdom : ν ≤ ENNReal.ofReal C • volume.restrict (Ico (0 : ℝ) 1)) :
    ν.real (Ici (1 - d)) ≤ C * d := by
  refine (measureReal_le_mul_of_le_smul hC hdom (Ici (1 - d)) ?_).trans
    (mul_le_mul_of_nonneg_left (intervalMeasure_upper_tail_le hd) hC)
  rw [Measure.restrict_apply measurableSet_Ici]
  exact (measure_mono inter_subset_right |>.trans_lt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).ne

theorem endpoint_function_lower_loss_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) {X : Ω → ℝ} (hX : Measurable X) {C d : ℝ}
    (hC : 0 ≤ C) (hd : 0 ≤ d)
    (hdom : μ.map X ≤ ENNReal.ofReal C • volume.restrict (Ico (0 : ℝ) 1)) :
    μ.real {ω | X ω ≤ d} ≤ C * d := by
  have h := lower_endpoint_loss_le hC hd hdom
  have heq : X ⁻¹' Iic d = {ω | X ω ≤ d} := by ext ω; simp
  simpa only [measureReal_def, Measure.map_apply hX measurableSet_Iic, heq] using h

theorem endpoint_function_upper_loss_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) {X : Ω → ℝ} (hX : Measurable X) {C d : ℝ}
    (hC : 0 ≤ C) (hd : 0 ≤ d)
    (hdom : μ.map X ≤ ENNReal.ofReal C • volume.restrict (Ico (0 : ℝ) 1)) :
    μ.real {ω | 1 - d ≤ X ω} ≤ C * d := by
  have h := upper_endpoint_loss_le hC hd hdom
  have heq : X ⁻¹' Ici (1 - d) = {ω | 1 - d ≤ X ω} := by ext ω; simp
  simpa only [measureReal_def, Measure.map_apply hX measurableSet_Ici, heq] using h

theorem endpoint_pair_loss_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) {X Y : Ω → ℝ} (hX : Measurable X) (hY : Measurable Y)
    {C d : ℝ} (hC : 0 ≤ C) (hd : 0 ≤ d)
    (hdomX : μ.map X ≤ ENNReal.ofReal C • volume.restrict (Ico (0 : ℝ) 1))
    (hdomY : μ.map Y ≤ ENNReal.ofReal C • volume.restrict (Ico (0 : ℝ) 1)) :
    μ.real {ω | 1 - d ≤ X ω ∨ Y ω ≤ d} ≤ 2 * C * d := by
  have hXb := endpoint_function_upper_loss_le μ hX hC hd hdomX
  have hYb := endpoint_function_lower_loss_le μ hY hC hd hdomY
  have h := (measureReal_union_le {ω | 1 - d ≤ X ω} {ω | Y ω ≤ d}).trans
    (add_le_add hXb hYb)
  have heq : {ω | 1 - d ≤ X ω} ∪ {ω | Y ω ≤ d} =
      {ω | 1 - d ≤ X ω ∨ Y ω ≤ d} := by ext ω; simp
  rw [heq] at h
  linarith

theorem measureReal_iUnion_le_tsum_budget {Ω ι : Type*}
    [MeasurableSpace Ω] [Countable ι] (μ : Measure Ω) [IsFiniteMeasure μ]
    (E : ι → Set Ω) {b : ι → ℝ} (hb : ∀ i, 0 ≤ b i) (hs : Summable b)
    (hE : ∀ i, μ.real (E i) ≤ b i) :
    μ.real (⋃ i, E i) ≤ ∑' i, b i := by
  have hE' : ∀ i, μ (E i) ≤ ENNReal.ofReal (b i) := by
    intro i
    rw [← ENNReal.ofReal_toReal (measure_ne_top μ (E i))]
    exact ENNReal.ofReal_le_ofReal (hE i)
  have hbound : μ (⋃ i, E i) ≤ ENNReal.ofReal (∑' i, b i) := calc
    _ ≤ ∑' i, μ (E i) := measure_iUnion_le E
    _ ≤ ∑' i, ENNReal.ofReal (b i) := ENNReal.tsum_le_tsum hE'
    _ = _ := (ENNReal.ofReal_tsum_of_nonneg hb hs).symm
  have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hbound
  simpa only [measureReal_def, ENNReal.toReal_ofReal (tsum_nonneg hb)] using hreal

theorem blocked_future_endpoint_loss_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (m : ℕ → ℕ) (hm : ∀ s, 0 < m s)
    {K : ℕ → ℝ} (hK : ∀ s, 0 < K s) (hs : Summable (fun s => 1 / K s))
    {X Y : (s : ℕ) → Fin (m s) → Ω → ℝ}
    (hX : ∀ s i, Measurable (X s i)) (hY : ∀ s i, Measurable (Y s i))
    {C a W : ℝ} (hC : 0 ≤ C) (ha : 0 ≤ a) (hW : 0 ≤ W)
    (hdomX : ∀ s i, μ.map (X s i) ≤ ENNReal.ofReal C • volume.restrict (Ico (0 : ℝ) 1))
    (hdomY : ∀ s i, μ.map (Y s i) ≤ ENNReal.ofReal C • volume.restrict (Ico (0 : ℝ) 1)) :
    μ.real (⋃ s, ⋃ i : Fin (m s),
      {ω | 1 - a * W / ((m s : ℝ) * K s) ≤ X s i ω ∨
        Y s i ω ≤ a * W / ((m s : ℝ) * K s)}) ≤
      (2 * C * a * W) * ∑' s, 1 / K s := by
  let E : ℕ → Set Ω := fun s => ⋃ i : Fin (m s),
    {ω | 1 - a * W / ((m s : ℝ) * K s) ≤ X s i ω ∨
      Y s i ω ≤ a * W / ((m s : ℝ) * K s)}
  have hblock (s : ℕ) : μ.real (E s) ≤ (2 * C * a * W) * (1 / K s) := by
    have hmR : (0 : ℝ) < m s := by exact_mod_cast hm s
    have hd : 0 ≤ a * W / ((m s : ℝ) * K s) :=
      div_nonneg (mul_nonneg ha hW) (mul_nonneg hmR.le (hK s).le)
    calc
      μ.real (E s) ≤ ∑ i : Fin (m s), μ.real
          {ω | 1 - a * W / ((m s : ℝ) * K s) ≤ X s i ω ∨
            Y s i ω ≤ a * W / ((m s : ℝ) * K s)} :=
        measureReal_iUnion_fintype_le _
      _ ≤ ∑ _i : Fin (m s), 2 * C * (a * W / ((m s : ℝ) * K s)) := by
        apply Finset.sum_le_sum
        intro i hi
        exact endpoint_pair_loss_le μ (hX s i) (hY s i) hC hd (hdomX s i) (hdomY s i)
      _ = (2 * C * a * W) * (1 / K s) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        field_simp
  have hcoef : 0 ≤ 2 * C * a * W := by positivity
  have h := measureReal_iUnion_le_tsum_budget μ E
    (b := fun s => (2 * C * a * W) * (1 / K s))
    (fun s => mul_nonneg hcoef (one_div_nonneg.mpr (hK s).le))
    (hs.mul_left (2 * C * a * W)) hblock
  simpa only [E, tsum_mul_left] using h

end InvariantRotation.EndpointIntervalBounds

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Analysis_TaggedEventBounds
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace InvariantRotation.TaggedEventBounds

theorem neg_div_one_sub_le_log {t : ℝ} (ht : t < 1) :
    -t / (1 - t) ≤ Real.log (1 - t) := by
  have hp : 0 < 1 - t := sub_pos.mpr ht
  have heq : -t / (1 - t) = 1 - (1 - t)⁻¹ := by
    field_simp
    ring
  rw [heq]
  exact Real.one_sub_inv_le_log_of_pos hp

theorem exp_neg_le_one_sub_pow (n : ℕ) {t a : ℝ} (ht : t < 1)
    (hbudget : (n : ℝ) * t ≤ a * (1 - t)) :
    Real.exp (-a) ≤ (1 - t) ^ n := by
  have hp : 0 < 1 - t := sub_pos.mpr ht
  apply (Real.le_log_iff_exp_le (pow_pos hp n)).mp
  rw [Real.log_pow]
  have hb : -a ≤ (n : ℝ) * (-t / (1 - t)) := by
    rw [← mul_div_assoc]
    apply (le_div_iff₀ hp).mpr
    nlinarith
  exact hb.trans (mul_le_mul_of_nonneg_left
    (neg_div_one_sub_le_log ht) (Nat.cast_nonneg n))

theorem product_tag_bound (m : ℕ) (hm : 100 ≤ m) :
    Real.exp (-82) ≤ (1 - 41 / (m : ℝ)) ^ (m - 1) := by
  have hmR : (100 : ℝ) ≤ m := by exact_mod_cast hm
  have hmpos : (0 : ℝ) < m := by linarith
  have hsub : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega), Nat.cast_one]
  apply exp_neg_le_one_sub_pow (m - 1)
  · exact (div_lt_one hmpos).mpr (by linarith)
  · rw [hsub]
    apply (mul_le_mul_iff_left₀ hmpos).mp
    field_simp
    nlinarith

open MeasureTheory

section ProductEvent

variable {ι Ω : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace Ω]

omit [Fintype ι] [MeasurableSpace Ω] in
theorem tagRectangle_pairwiseDisjoint (T G : ι → Set Ω)
    (hdis : ∀ i, Disjoint (T i) (G i)) :
    Pairwise (fun i j => Disjoint (tagRectangle T G i) (tagRectangle T G j)) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro x hxi hxj
  have hi : x i ∈ T i := by simpa [tagRectangle] using hxi i (Set.mem_univ i)
  have hj : x i ∈ G i := by simpa [tagRectangle, hij] using hxj i (Set.mem_univ i)
  exact Set.disjoint_left.mp (hdis i) hi hj

theorem measurableSet_tagRectangle (T G : ι → Set Ω)
    (hT : ∀ i, MeasurableSet (T i)) (hG : ∀ i, MeasurableSet (G i)) (i : ι) :
    MeasurableSet (tagRectangle T G i) := by
  apply MeasurableSet.univ_pi
  intro j
  split_ifs
  · exact hT j
  · exact hG j

theorem oneTagEvent_measureReal (μ : ι → Measure Ω) [∀ i, IsFiniteMeasure (μ i)]
    (T G : ι → Set Ω) (hT : ∀ i, MeasurableSet (T i))
    (hG : ∀ i, MeasurableSet (G i)) (hdis : ∀ i, Disjoint (T i) (G i)) :
    (Measure.pi μ).real (oneTagEvent T G) =
      ∑ i, ∏ j, (μ j).real (if j = i then T j else G j) := by
  rw [oneTagEvent, measureReal_iUnion_fintype (tagRectangle_pairwiseDisjoint T G hdis)
    (measurableSet_tagRectangle T G hT hG)]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [tagRectangle, measureReal_def, Measure.pi_pi, ENNReal.toReal_prod]

theorem oneTagEvent_measureReal_lower_bound
    (μ : ι → Measure Ω) [∀ i, IsFiniteMeasure (μ i)]
    (T G : ι → Set Ω) (hT : ∀ i, MeasurableSet (T i))
    (hG : ∀ i, MeasurableSet (G i)) (hdis : ∀ i, Disjoint (T i) (G i))
    {t g : ℝ} (ht : 0 ≤ t) (hg : 0 ≤ g)
    (hTag : ∀ i, t ≤ (μ i).real (T i)) (hGood : ∀ i, g ≤ (μ i).real (G i)) :
    (Fintype.card ι : ℝ) * t * g ^ (Fintype.card ι - 1) ≤
      (Measure.pi μ).real (oneTagEvent T G) := by
  rw [oneTagEvent_measureReal μ T G hT hG hdis]
  have hprod (i : ι) : (∏ j : ι, if j = i then t else g) =
      t * g ^ (Fintype.card ι - 1) := by
    rw [← Finset.mul_prod_erase Finset.univ
      (fun j => if j = i then t else g) (Finset.mem_univ i)]
    simp only [ite_true, if_true]
    congr 1
    calc
      (∏ j ∈ Finset.univ.erase i, if j = i then t else g) =
          ∏ _j ∈ Finset.univ.erase i, g := by
        apply Finset.prod_congr rfl
        intro j hj
        exact ite_eq_right (Finset.mem_erase.mp hj).1
      _ = g ^ (Fintype.card ι - 1) := by simp
  calc
    (Fintype.card ι : ℝ) * t * g ^ (Fintype.card ι - 1) =
        ∑ _i : ι, t * g ^ (Fintype.card ι - 1) := by simp [mul_assoc]
    _ = ∑ i : ι, ∏ j : ι, if j = i then t else g := by simp_rw [hprod]
    _ ≤ ∑ i, ∏ j, (μ j).real (if j = i then T j else G j) := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.prod_le_prod
      · intro j hj
        split_ifs <;> assumption
      · intro j hj
        split_ifs
        · exact hTag j
        · exact hGood j

theorem oneTagEvent_measureReal_ge_pow (m : ℕ) (hm : 0 < m)
    (μ : Fin m → Measure Ω) [∀ i, IsFiniteMeasure (μ i)]
    (T G : Fin m → Set Ω) (hT : ∀ i, MeasurableSet (T i))
    (hG : ∀ i, MeasurableSet (G i)) (hdis : ∀ i, Disjoint (T i) (G i))
    {g : ℝ} (hg : 0 ≤ g)
    (hTag : ∀ i, 1 / (m : ℝ) ≤ (μ i).real (T i))
    (hGood : ∀ i, g ≤ (μ i).real (G i)) :
    g ^ (m - 1) ≤ (Measure.pi μ).real (oneTagEvent T G) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have h := oneTagEvent_measureReal_lower_bound μ T G hT hG hdis
    (t := 1 / (m : ℝ)) (by positivity) hg hTag hGood
  simp only [Fintype.card_fin] at h
  have hcancel : (m : ℝ) * (1 / (m : ℝ)) = 1 := by field_simp
  simpa only [hcancel, one_mul] using h

end ProductEvent

section EventLoss

variable {Ω : Type*} [MeasurableSpace Ω]

theorem admissible_nontag_measureReal_lower_bound
    (μ : Measure Ω) [IsProbabilityMeasure μ] (T B₁ B₂ : Set Ω)
    (hT : MeasurableSet T) (hB₁ : MeasurableSet B₁) (hB₂ : MeasurableSet B₂)
    {t b₁ b₂ : ℝ} (hTag : μ.real T ≤ t)
    (hBad₁ : μ.real B₁ ≤ b₁) (hBad₂ : μ.real B₂ ≤ b₂) :
    1 - t - b₁ - b₂ ≤ μ.real (Tᶜ ∩ B₁ᶜ ∩ B₂ᶜ) := by
  have hbound : μ.real (T ∪ B₁ ∪ B₂) ≤ t + b₁ + b₂ :=
    (measureReal_union_le (T ∪ B₁) B₂).trans
      (add_le_add ((measureReal_union_le T B₁).trans (add_le_add hTag hBad₁)) hBad₂)
  have heq : μ.real (Tᶜ ∩ B₁ᶜ ∩ B₂ᶜ) = 1 - μ.real (T ∪ B₁ ∪ B₂) := by
    rw [← Set.compl_union, ← Set.compl_union, measureReal_compl (hT.union hB₁ |>.union hB₂)]
    simp
  rw [heq]
  linarith

theorem eventually_half_le_measureReal_sdiff
    (μ : ℕ → Measure Ω) [∀ n, IsFiniteMeasure (μ n)]
    (A B : ℕ → Set Ω) {c : ℝ} (hc : 0 < c)
    (hbase : ∀ᶠ n in Filter.atTop, c ≤ (μ n).real (A n))
    (hloss : Filter.Tendsto (fun n => (μ n).real (B n)) Filter.atTop (nhds 0)) :
    ∀ᶠ n in Filter.atTop, c / 2 ≤ (μ n).real (A n \ B n) := by
  have hsmall : ∀ᶠ n in Filter.atTop, (μ n).real (B n) < c / 2 :=
    (tendsto_order.1 hloss).2 (c / 2) (by linarith)
  filter_upwards [hbase, hsmall] with n hn hsmalln
  have hremove := le_measureReal_sdiff (μ := μ n) (s₁ := A n) (s₂ := B n)
  linarith

end EventLoss


variable {ι Ω : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace Ω]

omit [Fintype ι] [MeasurableSpace Ω] in
theorem oneTagEvent_subset_currentBlockEvent (T B₁ B₂ : ι → Set Ω)
    (hTagSafe : ∀ i, T i ⊆ (B₁ i)ᶜ ∩ (B₂ i)ᶜ) :
    oneTagEvent T (fun i => (T i)ᶜ ∩ (B₁ i)ᶜ ∩ (B₂ i)ᶜ) ⊆
      currentBlockEvent T B₁ B₂ := by
  intro x hx
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
  have htag : x i ∈ T i := by
    simpa [tagRectangle] using hi i (Set.mem_univ i)
  refine ⟨⟨i, htag⟩, ?_⟩
  intro j
  by_cases hji : j = i
  · subst j
    exact hTagSafe i htag
  · have hj : x j ∈ (T j)ᶜ ∩ (B₁ j)ᶜ ∩ (B₂ j)ᶜ := by
      simpa [tagRectangle, hji] using hi j (Set.mem_univ j)
    exact ⟨hj.1.2, hj.2⟩

theorem currentBlockEvent_measureReal_lower_bound (m : ℕ) (hm : 0 < m)
    (μ : Fin m → Measure Ω) [∀ i, IsProbabilityMeasure (μ i)]
    (T B₁ B₂ : Fin m → Set Ω) (hT : ∀ i, MeasurableSet (T i))
    (hB₁ : ∀ i, MeasurableSet (B₁ i)) (hB₂ : ∀ i, MeasurableSet (B₂ i))
    (hTagSafe : ∀ i, T i ⊆ (B₁ i)ᶜ ∩ (B₂ i)ᶜ) {a : ℝ}
    (hg : 0 ≤ 1 - (1 + 2 * a) / (m : ℝ))
    (hTag : ∀ i, (μ i).real (T i) = 1 / (m : ℝ))
    (hBad₁ : ∀ i, (μ i).real (B₁ i) ≤ a / (m : ℝ))
    (hBad₂ : ∀ i, (μ i).real (B₂ i) ≤ a / (m : ℝ)) :
    (1 - (1 + 2 * a) / (m : ℝ)) ^ (m - 1) ≤
      (Measure.pi μ).real (currentBlockEvent T B₁ B₂) := by
  let G : Fin m → Set Ω := fun i => (T i)ᶜ ∩ (B₁ i)ᶜ ∩ (B₂ i)ᶜ
  have hG : ∀ i, MeasurableSet (G i) := fun i =>
    ((hT i).compl.inter (hB₁ i).compl).inter (hB₂ i).compl
  have hdis : ∀ i, Disjoint (T i) (G i) := by
    intro i
    exact Set.disjoint_left.mpr (fun x hx hGx => hGx.1.1 hx)
  have hGood : ∀ i, 1 - (1 + 2 * a) / (m : ℝ) ≤ (μ i).real (G i) := by
    intro i
    have h := admissible_nontag_measureReal_lower_bound (μ i) (T i) (B₁ i) (B₂ i)
      (hT i) (hB₁ i) (hB₂ i) (le_of_eq (hTag i)) (hBad₁ i) (hBad₂ i)
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    ring
  exact (oneTagEvent_measureReal_ge_pow m hm μ T G hT hG hdis hg
    (fun i => (hTag i).ge) hGood).trans
    (measureReal_mono (oneTagEvent_subset_currentBlockEvent T B₁ B₂ hTagSafe))


end InvariantRotation.TaggedEventBounds

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Analysis_TruncationEvent
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal

namespace InvariantRotation.TruncationEvent

open TaggedEventBounds EndpointIntervalBounds

variable {Ω : Type*} [MeasurableSpace Ω]

theorem currentBlock_mass_lower_bound (m : ℕ) (hm : 0 < m)
    (μ : Fin m → Measure Ω) [∀ i, IsProbabilityMeasure (μ i)]
    (T : Fin m → Set Ω) (hT : ∀ i, MeasurableSet (T i))
    {X Y : Fin m → Ω → ℝ} (hX : ∀ i, Measurable (X i)) (hY : ∀ i, Measurable (Y i))
    {C a : ℝ} (hC : 0 ≤ C) (ha : 0 ≤ a)
    (hbudget : 0 ≤ 1 - (1 + 2 * (C * a)) / (m : ℝ))
    (hTag : ∀ i, (μ i).real (T i) = 1 / (m : ℝ))
    (hSafe : ∀ i, ∀ x ∈ T i, X i x < 1 - a / (m : ℝ) ∧ a / (m : ℝ) < Y i x)
    (hdomX : ∀ i, (μ i).map (X i) ≤ ENNReal.ofReal C • volume.restrict (Ico (0 : ℝ) 1))
    (hdomY : ∀ i, (μ i).map (Y i) ≤ ENNReal.ofReal C • volume.restrict (Ico (0 : ℝ) 1)) :
    (1 - (1 + 2 * (C * a)) / (m : ℝ)) ^ (m - 1) ≤
      (Measure.pi μ).real {x | (∃ i, x i ∈ T i) ∧
        ∀ i, X i (x i) < 1 - a / (m : ℝ) ∧ a / (m : ℝ) < Y i (x i)} := by
  let B₁ : Fin m → Set Ω := fun i => {x | 1 - a / (m : ℝ) ≤ X i x}
  let B₂ : Fin m → Set Ω := fun i => {x | Y i x ≤ a / (m : ℝ)}
  have hB₁ : ∀ i, MeasurableSet (B₁ i) := fun i =>
    measurableSet_le measurable_const (hX i)
  have hB₂ : ∀ i, MeasurableSet (B₂ i) := fun i =>
    measurableSet_le (hY i) measurable_const
  have hSafe' : ∀ i, T i ⊆ (B₁ i)ᶜ ∩ (B₂ i)ᶜ := by
    intro i x hx
    exact ⟨not_le.mpr (hSafe i x hx).1, not_le.mpr (hSafe i x hx).2⟩
  have hd : 0 ≤ a / (m : ℝ) := div_nonneg ha (Nat.cast_nonneg m)
  have hBad₁ : ∀ i, (μ i).real (B₁ i) ≤ C * a / (m : ℝ) := by
    intro i
    simpa only [mul_div_assoc] using endpoint_function_upper_loss_le
      (μ i) (hX i) hC hd (hdomX i)
  have hBad₂ : ∀ i, (μ i).real (B₂ i) ≤ C * a / (m : ℝ) := by
    intro i
    simpa only [mul_div_assoc] using endpoint_function_lower_loss_le
      (μ i) (hY i) hC hd (hdomY i)
  have h := currentBlockEvent_measureReal_lower_bound m hm μ T B₁ B₂ hT hB₁ hB₂
    hSafe' hbudget hTag hBad₁ hBad₂
  simpa only [currentBlockEvent, B₁, B₂, Set.mem_ofPred_eq, not_le] using h

theorem currentBlock_mass_lower_bound_ae (m : ℕ) (hm : 0 < m)
    (μ : Fin m → Measure Ω) [∀ i, IsProbabilityMeasure (μ i)]
    (T : Fin m → Set Ω) (hT : ∀ i, MeasurableSet (T i))
    {X Y : Fin m → Ω → ℝ} (hX : ∀ i, Measurable (X i)) (hY : ∀ i, Measurable (Y i))
    {C a : ℝ} (hC : 0 ≤ C) (ha : 0 ≤ a)
    (hbudget : 0 ≤ 1 - (1 + 2 * (C * a)) / (m : ℝ))
    (hTag : ∀ i, (μ i).real (T i) = 1 / (m : ℝ))
    (hSafe : ∀ i, ∀ᵐ x ∂μ i, x ∈ T i →
      X i x < 1 - a / (m : ℝ) ∧ a / (m : ℝ) < Y i x)
    (hdomX : ∀ i, (μ i).map (X i) ≤ ENNReal.ofReal C • volume.restrict (Ico (0 : ℝ) 1))
    (hdomY : ∀ i, (μ i).map (Y i) ≤ ENNReal.ofReal C • volume.restrict (Ico (0 : ℝ) 1)) :
    (1 - (1 + 2 * (C * a)) / (m : ℝ)) ^ (m - 1) ≤
      (Measure.pi μ).real {x | (∃ i, x i ∈ T i) ∧
        ∀ i, X i (x i) < 1 - a / (m : ℝ) ∧ a / (m : ℝ) < Y i (x i)} := by
  let T' : Fin m → Set Ω := fun i => T i ∩
    {x | X i x < 1 - a / (m : ℝ) ∧ a / (m : ℝ) < Y i x}
  have hT' : ∀ i, MeasurableSet (T' i) := fun i =>
    (hT i).inter ((measurableSet_lt (hX i) measurable_const).inter
      (measurableSet_lt measurable_const (hY i)))
  have hTag' : ∀ i, (μ i).real (T' i) = 1 / (m : ℝ) := by
    intro i
    have hae : T' i =ᵐ[μ i] T i := by
      filter_upwards [hSafe i] with x hx
      exact propext ⟨fun h => h.1, fun h => ⟨h, hx h⟩⟩
    exact (measureReal_congr hae).trans (hTag i)
  have h := currentBlock_mass_lower_bound m hm μ T' hT' hX hY hC ha hbudget hTag'
    (fun i x hx => hx.2) hdomX hdomY
  refine h.trans (measureReal_mono ?_)
  intro x hx
  obtain ⟨⟨i, hi⟩, hgood⟩ := hx
  exact ⟨⟨i, hi.1⟩, hgood⟩

end InvariantRotation.TruncationEvent

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Couplings_CouplingMarginalBounds
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Filter
open scoped BigOperators ENNReal

namespace Invariant233.CouplingMarginalBounds

lemma rho_div_width_le {κ m w : ℝ} (hκ : 0 ≤ κ)
    (hm : 0 < m) (hw : 1 / m ≤ w) : rho κ m w / w ≤ κ := by
  exact (div_le_iff₀ (width_pos hm hw)).2 (rho_le_mul_width hκ hm hw)

lemma rho_sq_div_width {κ m w : ℝ} (hm : 0 < m) (hw : 0 < w) :
    (rho κ m w) ^ 2 / w = κ ^ 2 / m := by
  unfold rho
  rw [mul_pow, Real.sq_sqrt (div_nonneg hw.le hm.le)]
  field_simp

lemma marginal_density_bounds {κ m a b t u₁ u₂ u₃ u₄ v : ℝ}
    (hκ0 : 0 ≤ κ) (hκ : κ ≤ 1 / 100) (hm : 100 ≤ m)
    (ha : 1 / m ≤ a) (ha' : a ≤ 1 / 4)
    (hb : 1 / m ≤ b) (hb' : b ≤ 1 / 4)
    (ht0 : 0 ≤ t) (ht : t ≤ 1)
    (hu₁ : 0 ≤ u₁ ∧ u₁ ≤ 2 / a) (hu₂ : 0 ≤ u₂ ∧ u₂ ≤ 2 / a)
    (hu₃ : 0 ≤ u₃ ∧ u₃ ≤ 2 / b) (hu₄ : 0 ≤ u₄ ∧ u₄ ≤ 2 / b)
    (hv : 0 ≤ v ∧ v ≤ m) :
    let h := diagonalMass κ m a b t + rho κ m a * u₁ + rho κ m a * u₂ +
      rho κ m b * u₃ + rho κ m b * u₄ + (t / m) * v
    49 / 50 ≤ h ∧ h ≤ 2 + 8 * κ ∧ h < 10 := by
  dsimp only
  have hm0 : 0 < m := by linarith
  have ha0 := width_pos hm0 ha
  have hb0 := width_pos hm0 hb
  have hra0 := rho_nonneg (m := m) (w := a) hκ0
  have hrb0 := rho_nonneg (m := m) (w := b) hκ0
  have hq := diagonalMass_bounds hκ0 hκ hm ha ha' hb hb' ht0 ht
  have hra := rho_div_width_le hκ0 hm0 ha
  have hrb := rho_div_width_le hκ0 hm0 hb
  have hu₁' : rho κ m a * u₁ ≤ 2 * κ := by
    calc
      _ ≤ rho κ m a * (2 / a) := mul_le_mul_of_nonneg_left hu₁.2 hra0
      _ = 2 * (rho κ m a / a) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hra (by norm_num)
  have hu₂' : rho κ m a * u₂ ≤ 2 * κ := by
    calc
      _ ≤ rho κ m a * (2 / a) := mul_le_mul_of_nonneg_left hu₂.2 hra0
      _ = 2 * (rho κ m a / a) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hra (by norm_num)
  have hu₃' : rho κ m b * u₃ ≤ 2 * κ := by
    calc
      _ ≤ rho κ m b * (2 / b) := mul_le_mul_of_nonneg_left hu₃.2 hrb0
      _ = 2 * (rho κ m b / b) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hrb (by norm_num)
  have hu₄' : rho κ m b * u₄ ≤ 2 * κ := by
    calc
      _ ≤ rho κ m b * (2 / b) := mul_le_mul_of_nonneg_left hu₄.2 hrb0
      _ = 2 * (rho κ m b / b) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hrb (by norm_num)
  have htm0 := div_nonneg ht0 hm0.le
  have hv' : (t / m) * v ≤ t := by
    calc
      _ ≤ (t / m) * m := mul_le_mul_of_nonneg_left hv.2 htm0
      _ = t := div_mul_cancel₀ _ hm0.ne'
  have hlow₁ := mul_nonneg hra0 hu₁.1
  have hlow₂ := mul_nonneg hra0 hu₂.1
  have hlow₃ := mul_nonneg hrb0 hu₃.1
  have hlow₄ := mul_nonneg hrb0 hu₄.1
  have hlowv := mul_nonneg htm0 hv.1
  constructor
  · linarith [hq.1]
  constructor
  · linarith [hq.2]
  · linarith [hq.2]

lemma integral_sq_sum_le {Ω I : Type*} [MeasurableSpace Ω] [Fintype I]
    {μ : Measure Ω} {f : I → Ω → ℝ} (hf : ∀ i, MemLp (f i) 2 μ) :
    (∫ ω, (∑ i, f i ω) ^ 2 ∂μ) ≤
      (Fintype.card I : ℝ) * ∑ i, ∫ ω, (f i ω) ^ 2 ∂μ := by
  classical
  have hsum : MemLp (fun ω => ∑ i, f i ω) 2 μ :=
    memLp_finsetSum Finset.univ (fun i _ => hf i)
  have hsq : Integrable (fun ω => ∑ i, (f i ω) ^ 2) μ :=
    integrable_finsetSum Finset.univ (fun i _ => (hf i).integrable_sq)
  calc
    _ ≤ ∫ ω, (Fintype.card I : ℝ) * ∑ i, (f i ω) ^ 2 ∂μ := by
      apply integral_mono hsum.integrable_sq (hsq.const_mul _)
      intro ω
      simpa using (sq_sum_le_card_mul_sum_sq (s := Finset.univ)
        (f := fun i => f i ω))
    _ = _ := by
      rw [integral_const_mul, integral_finsetSum]
      intro i _
      exact (hf i).integrable_sq

lemma integral_sq_weighted_sum_le {Ω I : Type*} [MeasurableSpace Ω] [Fintype I]
    {μ : Measure Ω} {f : I → Ω → ℝ} (hf : ∀ i, MemLp (f i) 2 μ)
    (p : I → ℝ) :
    (∫ ω, (∑ i, p i * f i ω) ^ 2 ∂μ) ≤
      (Fintype.card I : ℝ) * ∑ i, (p i) ^ 2 * ∫ ω, (f i ω) ^ 2 ∂μ := by
  have h := integral_sq_sum_le (fun i => (hf i).const_mul (p i))
  simpa only [mul_pow, integral_const_mul] using h

lemma uniformDensity_memLp {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] {s : Set Ω} (hs : MeasurableSet s)
    (p : ℝ≥0∞) : MemLp (uniformDensity μ s) p μ := by
  exact memLp_indicator_const p hs _ (Or.inr (measure_ne_top μ s))

lemma uniformDensity_integral {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {s : Set Ω} (hs : MeasurableSet s) (hpos : 0 < μ.real s) :
    ∫ ω, uniformDensity μ s ω ∂μ = 1 := by
  rw [uniformDensity, integral_indicator_const _ hs, smul_eq_mul]
  exact mul_inv_cancel₀ hpos.ne'

lemma uniformDensity_sq_integral {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {s : Set Ω} (hs : MeasurableSet s) (hpos : 0 < μ.real s) :
    ∫ ω, (uniformDensity μ s ω) ^ 2 ∂μ = (μ.real s)⁻¹ := by
  have hsq : (fun ω => (uniformDensity μ s ω) ^ 2) =
      s.indicator (fun _ => ((μ.real s)⁻¹) ^ 2) := by
    ext ω
    by_cases hω : ω ∈ s <;> simp [uniformDensity, hω]
  rw [hsq, integral_indicator_const _ hs, smul_eq_mul]
  field_simp

lemma uniformDensity_variance {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {s : Set Ω}
    (hs : MeasurableSet s) (hpos : 0 < μ.real s) :
    ∫ ω, (uniformDensity μ s ω - 1) ^ 2 ∂μ = (μ.real s)⁻¹ - 1 := by
  have hu := uniformDensity_memLp (μ := μ) hs 2
  have hui : Integrable (uniformDensity μ s) μ := hu.integrable (by norm_num)
  have hfun : (fun ω => (uniformDensity μ s ω - 1) ^ 2) =
      fun ω => (uniformDensity μ s ω) ^ 2 - 2 * uniformDensity μ s ω + 1 := by
    ext ω
    ring
  have hsub : Integrable (fun ω => (uniformDensity μ s ω) ^ 2 - 2 * uniformDensity μ s ω) μ :=
    hu.integrable_sq.sub (hui.const_mul 2)
  rw [hfun, integral_add hsub (integrable_const 1),
    integral_sub hu.integrable_sq (hui.const_mul 2), integral_const_mul,
    uniformDensity_sq_integral hs hpos, uniformDensity_integral hs hpos]
  simp
  ring

lemma uniformDensity_variance_le {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {s : Set Ω}
    (hs : MeasurableSet s) {w : ℝ} (hw : 0 < w) (hlen : w / 2 ≤ μ.real s) :
    ∫ ω, (uniformDensity μ s ω - 1) ^ 2 ∂μ ≤ 2 / w := by
  have hpos : 0 < μ.real s := lt_of_lt_of_le (by positivity) hlen
  rw [uniformDensity_variance hs hpos]
  have hinv : (μ.real s)⁻¹ ≤ 2 / w := by
    rw [inv_eq_one_div]
    apply (div_le_div_iff₀ hpos hw).2
    linarith
  linarith

lemma five_component_energy_bound {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {f : Fin 5 → Ω → ℝ} (hf : ∀ i, MemLp (f i) 2 μ)
    {κ m a b t : ℝ} (hm : 0 < m) (ha : 0 < a) (hb : 0 < b)
    (ht0 : 0 ≤ t) (ht : t ≤ 1)
    (henergy : ∀ i, (∫ ω, (f i ω) ^ 2 ∂μ) ≤ componentVarianceBounds m a b i) :
    (∫ ω, (∑ i, componentProbabilities κ m a b t i * f i ω) ^ 2 ∂μ) ≤
      20 * (2 * κ ^ 2 / m + t / m) := by
  have hbound := integral_sq_weighted_sum_le hf (componentProbabilities κ m a b t)
  have hsum : (∑ i, (componentProbabilities κ m a b t i) ^ 2 *
      ∫ ω, (f i ω) ^ 2 ∂μ) ≤
      ∑ i, (componentProbabilities κ m a b t i) ^ 2 *
        componentVarianceBounds m a b i := by
    apply Finset.sum_le_sum
    intro i _
    exact mul_le_mul_of_nonneg_left (henergy i) (sq_nonneg _)
  have hcalc : (∑ i, (componentProbabilities κ m a b t i) ^ 2 *
      componentVarianceBounds m a b i) = 8 * κ ^ 2 / m + t ^ 2 / m := by
    simp only [componentProbabilities, componentVarianceBounds, Fin.sum_univ_succ,
      Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.sum_univ_zero, add_zero]
    have hra := rho_sq_div_width (κ := κ) hm ha
    have hrb := rho_sq_div_width (κ := κ) hm hb
    have htag : (t / m) ^ 2 * m = t ^ 2 / m := by field_simp
    rw [htag]
    simp only [div_eq_mul_inv] at hra hrb ⊢
    nlinarith
  have ht2 : t ^ 2 ≤ t := by nlinarith
  have htdiv : t ^ 2 / m ≤ t / m := (div_le_div_iff_of_pos_right hm).2 ht2
  have htm : 0 ≤ t / m := div_nonneg ht0 hm.le
  norm_num only [Fintype.card_fin] at hbound
  calc
    _ ≤ 5 * (∑ i, (componentProbabilities κ m a b t i) ^ 2 *
        componentVarianceBounds m a b i) :=
      hbound.trans (mul_le_mul_of_nonneg_left hsum (by norm_num))
    _ = 5 * (8 * κ ^ 2 / m + t ^ 2 / m) := by rw [hcalc]
    _ ≤ _ := by
      simp only [div_eq_mul_inv] at htdiv htm ⊢
      nlinarith

end Invariant233.CouplingMarginalBounds

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Couplings_CouplingMixture
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal ProbabilityTheory

namespace Invariant233.CouplingMixture

variable {X I : Type*} [MeasurableSpace X] [Fintype I]

lemma diagonal_fst (μ : Measure X) : (diagonal μ).fst = μ := by
  simpa [diagonal] using
    (Measure.fst_map_prodMk (μ := μ) (X := id) (Y := id) measurable_id)

lemma diagonal_snd (μ : Measure X) : (diagonal μ).snd = μ := by
  simpa [diagonal] using
    (Measure.snd_map_prodMk (μ := μ) (X := id) (Y := id) measurable_id)

lemma fst_finsetSum {J : Type*} (s : Finset J) (μ : J → Measure (X × X)) :
    (∑ i ∈ s, μ i).fst = ∑ i ∈ s, (μ i).fst := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih => simp [Finset.sum_insert ha, ih]

lemma snd_finsetSum {J : Type*} (s : Finset J) (μ : J → Measure (X × X)) :
    (∑ i ∈ s, μ i).snd = ∑ i ∈ s, (μ i).snd := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih => simp [Finset.sum_insert ha, ih]

lemma mixture_fst (μ : Measure X) (q : ℝ≥0∞) (p : I → ℝ≥0∞)
    (u v : I → Measure X) [∀ i, IsProbabilityMeasure (v i)] :
    (mixture μ q p u v).fst = q • μ + ∑ i, p i • u i := by
  unfold mixture
  rw [Measure.fst_add, fst_finsetSum]
  simp only [Measure.fst, Measure.map_smul,
    Measure.map_fst_prod, measure_univ, one_smul]
  rw [← Measure.fst, diagonal_fst]

lemma mixture_snd (μ : Measure X) (q : ℝ≥0∞) (p : I → ℝ≥0∞)
    (u v : I → Measure X) [∀ i, IsProbabilityMeasure (u i)]
    [∀ i, IsProbabilityMeasure (v i)] :
    (mixture μ q p u v).snd = q • μ + ∑ i, p i • v i := by
  unfold mixture
  rw [Measure.snd_add, snd_finsetSum]
  simp only [Measure.snd, Measure.map_smul,
    Measure.map_snd_prod, measure_univ, one_smul]
  rw [← Measure.snd, diagonal_snd]

lemma withDensity_finite_mixture (μ : Measure X) (q : ℝ≥0∞)
    (p : I → ℝ≥0∞) (g : I → X → ℝ≥0∞) (hg : ∀ i, Measurable (g i)) :
    μ.withDensity (fun x => q + ∑ i, p i * g i x) =
      q • μ + ∑ i, p i • μ.withDensity (g i) := by
  classical
  have hsum : μ.withDensity (fun x => ∑ i, p i * g i x) =
      ∑ i, p i • μ.withDensity (g i) := by
    have hfin : ∀ s : Finset I, μ.withDensity (fun x => ∑ i ∈ s, p i * g i x) =
        ∑ i ∈ s, p i • μ.withDensity (g i) := by
      intro s
      induction s using Finset.induction_on with
      | empty => simp
      | @insert a s ha ih =>
        simp only [Finset.sum_insert ha]
        rw [show (fun x => p a * g a x + ∑ i ∈ s, p i * g i x) =
          (fun x => p a * g a x) + (fun x => ∑ i ∈ s, p i * g i x) from rfl,
          withDensity_add_left (show Measurable (fun x => p a * g a x) from measurable_const.mul (hg a)), ih]
        congr 1
        exact withDensity_smul (p a) (hg a)
    exact hfin Finset.univ
  rw [show (fun x => q + ∑ i, p i * g i x) =
    (fun _ => q) + (fun x => ∑ i, p i * g i x) from rfl,
    withDensity_add_left measurable_const, withDensity_const, hsum]

lemma intervalLaw_ae_mem (a b : ℝ) : ∀ᵐ x ∂intervalLaw a b, x ∈ Ico a b :=
  ae_cond_mem measurableSet_Ico

omit [Fintype I] in
lemma map_label_event [DecidableEq I] [MeasurableSpace (Option I)] [MeasurableSingletonClass (Option I)]
    (ν : Measure (X × X)) (l j : Option I) :
    ν.map (fun z => (l, z)) {z | z.1 = j} = if l = j then ν Set.univ else 0 := by
  classical
  have hs : MeasurableSet {z : Option I × (X × X) | z.1 = j} :=
    measurable_fst (measurableSet_singleton j)
  rw [Measure.map_apply (show Measurable (fun z : X × X => (l, z)) from
    measurable_const.prodMk measurable_id) hs]
  by_cases h : l = j <;> simp [h]

lemma labelledMixture_some_mass [MeasurableSpace (Option I)] [MeasurableSingletonClass (Option I)]
    (μ : Measure X) (q : ℝ≥0∞) (p : I → ℝ≥0∞)
    (u v : I → Measure X) [∀ i, IsProbabilityMeasure (u i)]
    [∀ i, IsProbabilityMeasure (v i)] (i : I) :
    labelledMixture μ q p u v {z | z.1 = some i} = p i := by
  classical
  simp only [labelledMixture, Measure.add_apply, Measure.smul_apply,
    Measure.finsetSum_apply, smul_eq_mul, map_label_event]
  simp

lemma cond_eq_withDensity_uniformDensity {μ : Measure X} [IsFiniteMeasure μ]
    {s : Set X} (hs : MeasurableSet s) (hpos : 0 < μ.real s) :
    μ[|s] = μ.withDensity (fun x =>
      ENNReal.ofReal (CouplingMarginalBounds.uniformDensity μ s x)) := by
  have hc : ENNReal.ofReal ((μ.real s)⁻¹) = (μ s)⁻¹ := by
    rw [ENNReal.ofReal_inv_of_pos hpos, measureReal_def,
      ENNReal.ofReal_toReal (measure_ne_top μ s)]
  have hfun : (fun x => ENNReal.ofReal (CouplingMarginalBounds.uniformDensity μ s x)) =
      s.indicator (fun _ => (μ s)⁻¹) := by
    ext x
    by_cases hx : x ∈ s <;> simp [CouplingMarginalBounds.uniformDensity, hx, hc]
  rw [hfun, withDensity_indicator hs, withDensity_const]
  rfl

omit [MeasurableSpace X] in
lemma ofReal_mixture_density (q : ℝ) (p : I → ℝ) (g : I → X → ℝ)
    (hq : 0 ≤ q) (hp : ∀ i, 0 ≤ p i) (hg : ∀ i x, 0 ≤ g i x) (x : X) :
    ENNReal.ofReal (q + ∑ i, p i * g i x) =
      ENNReal.ofReal q + ∑ i, ENNReal.ofReal (p i) * ENNReal.ofReal (g i x) := by
  rw [ENNReal.ofReal_add hq (Finset.sum_nonneg (fun i _ => mul_nonneg (hp i) (hg i x))),
    ENNReal.ofReal_sum_of_nonneg (fun i _ => mul_nonneg (hp i) (hg i x))]
  congr 1
  exact Finset.sum_congr rfl (fun i _ => ENNReal.ofReal_mul (hp i))

lemma mixture_fst_real_density (μ : Measure X) (q : ℝ) (p : I → ℝ)
    (u v : I → Measure X) [∀ i, IsProbabilityMeasure (v i)]
    (g : I → X → ℝ) (hq : 0 ≤ q) (hp : ∀ i, 0 ≤ p i)
    (hg0 : ∀ i x, 0 ≤ g i x) (hgm : ∀ i, Measurable (g i))
    (hu : ∀ i, u i = μ.withDensity (fun x => ENNReal.ofReal (g i x))) :
    (mixture μ (ENNReal.ofReal q) (fun i => ENNReal.ofReal (p i)) u v).fst =
      μ.withDensity (fun x => ENNReal.ofReal (q + ∑ i, p i * g i x)) := by
  rw [mixture_fst]
  simp_rw [hu, ofReal_mixture_density q p g hq hp hg0]
  exact (withDensity_finite_mixture μ _ _ _ (fun i => (hgm i).ennreal_ofReal)).symm

lemma mixture_snd_real_density (μ : Measure X) (q : ℝ) (p : I → ℝ)
    (u v : I → Measure X) [∀ i, IsProbabilityMeasure (u i)]
    [∀ i, IsProbabilityMeasure (v i)]
    (g : I → X → ℝ) (hq : 0 ≤ q) (hp : ∀ i, 0 ≤ p i)
    (hg0 : ∀ i x, 0 ≤ g i x) (hgm : ∀ i, Measurable (g i))
    (hv : ∀ i, v i = μ.withDensity (fun x => ENNReal.ofReal (g i x))) :
    (mixture μ (ENNReal.ofReal q) (fun i => ENNReal.ofReal (p i)) u v).snd =
      μ.withDensity (fun x => ENNReal.ofReal (q + ∑ i, p i * g i x)) := by
  rw [mixture_snd]
  simp_rw [hv, ofReal_mixture_density q p g hq hp hg0]
  exact (withDensity_finite_mixture μ _ _ _ (fun i => (hgm i).ennreal_ofReal)).symm

end Invariant233.CouplingMixture

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Couplings_OneCoordinateCoupling
attribute [-instance] _root_.OAI.Invariant233.OrderedProductCoupling.coordinateLaw_isProbabilityMeasure _root_.OAI.Invariant233.OrderedProductCoupling.law_isProbabilityMeasure _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

namespace Invariant233.OneCoordinateCoupling

open CouplingMarginalBounds CouplingMixture

lemma baseLaw_eq_restrict : baseLaw = volume.restrict (Ico (0 : ℝ) 1) := by
  simp [baseLaw, intervalLaw, ProbabilityTheory.cond, Real.volume_Ico]

lemma interval_subset_unit {a b : ℝ} (ha : 0 ≤ a) (hb : b ≤ 1) :
    Ico a b ⊆ Ico (0 : ℝ) 1 := by
  intro x hx
  exact ⟨ha.trans hx.1, hx.2.trans_le hb⟩

lemma baseLaw_interval_measure {a b : ℝ} (ha : 0 ≤ a) (hb : b ≤ 1) (hab : a ≤ b) :
    baseLaw.real (Ico a b) = b - a := by
  rw [measureReal_def, baseLaw_eq_restrict, Measure.restrict_apply measurableSet_Ico,
    inter_eq_left.mpr (interval_subset_unit ha hb), Real.volume_Ico,
    ENNReal.toReal_ofReal (sub_nonneg.mpr hab)]

lemma intervalLaw_eq_base_cond {a b : ℝ} (ha : 0 ≤ a) (hb : b ≤ 1) :
    intervalLaw a b = baseLaw[|Ico a b] := by
  rw [baseLaw_eq_restrict]
  simp only [intervalLaw, ProbabilityTheory.cond,
    Measure.restrict_apply measurableSet_Ico,
    Measure.restrict_restrict measurableSet_Ico,
    inter_eq_left.mpr (interval_subset_unit ha hb)]

lemma intervalLaw_eq_base_withDensity {a b : ℝ}
    (ha : 0 ≤ a) (hb : b ≤ 1) (hab : a < b) :
    intervalLaw a b = baseLaw.withDensity (fun x =>
      ENNReal.ofReal (uniformDensity baseLaw (Ico a b) x)) := by
  rw [intervalLaw_eq_base_cond ha hb]
  apply cond_eq_withDensity_uniformDensity measurableSet_Ico
  rw [baseLaw_interval_measure ha hb hab.le]
  exact sub_pos.mpr hab

lemma labelledLaw_tag_mass {κ m a b t : ℝ} (hm : 2 ≤ m)
    (ha0 : 0 < a) (ha1 : a ≤ 1 / 4) (hb0 : 0 < b) (hb1 : b ≤ 1 / 4) :
    labelledLaw κ m a b t {z | z.1 = some (4 : Fin 5)} = ENNReal.ofReal (t / m) := by
  have : ∀ i, IsProbabilityMeasure (leftLaw m a b i) :=
    leftLaw_isProbabilityMeasure (by linarith) ha0 ha1 hb0 hb1
  have : ∀ i, IsProbabilityMeasure (rightLaw m a b i) :=
    rightLaw_isProbabilityMeasure hm ha0 ha1 hb0 hb1
  exact labelledMixture_some_mass _ _ _ _ _ (4 : Fin 5)

end Invariant233.OneCoordinateCoupling

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Product_OneCoordinateDensity
attribute [-instance] _root_.OAI.Invariant233.OrderedProductCoupling.sourcePairLaw_isProbabilityMeasure _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

namespace Invariant233.OneCoordinateCoupling

open CouplingMarginalBounds CouplingMixture

lemma intervalDensity_measurable (a b : ℝ) : Measurable (intervalDensity a b) :=
  measurable_const.indicator measurableSet_Ico

lemma intervalDensity_nonneg (a b x : ℝ) : 0 ≤ intervalDensity a b x := by
  by_cases hx : x ∈ Ico a b
  · simp [intervalDensity, uniformDensity, hx, inv_nonneg.mpr (measureReal_nonneg)]
  · simp [intervalDensity, uniformDensity, hx]

lemma intervalDensity_memLp (a b : ℝ) (p : ℝ≥0∞) :
    MemLp (intervalDensity a b) p baseLaw :=
  uniformDensity_memLp measurableSet_Ico p

lemma intervalDensity_integral {a b : ℝ} (ha : 0 ≤ a) (hb : b ≤ 1) (hab : a < b) :
    (∫ x, intervalDensity a b x ∂baseLaw) = 1 := by
  apply uniformDensity_integral measurableSet_Ico
  rw [baseLaw_interval_measure ha hb hab.le]
  exact sub_pos.mpr hab

lemma intervalDensity_variance {a b : ℝ} (ha : 0 ≤ a) (hb : b ≤ 1) (hab : a < b) :
    (∫ x, (intervalDensity a b x - 1) ^ 2 ∂baseLaw) = (b - a)⁻¹ - 1 := by
  have hpos : 0 < baseLaw.real (Ico a b) := by
    rw [baseLaw_interval_measure ha hb hab.le]
    exact sub_pos.mpr hab
  rw [intervalDensity, uniformDensity_variance measurableSet_Ico hpos,
    baseLaw_interval_measure ha hb hab.le]

lemma intervalDensity_le_inv_length {a b : ℝ}
    (ha : 0 ≤ a) (hb : b ≤ 1) (hab : a < b) (x : ℝ) :
    intervalDensity a b x ≤ (b - a)⁻¹ := by
  by_cases hx : x ∈ Ico a b
  · simp [intervalDensity, uniformDensity, hx, baseLaw_interval_measure ha hb hab.le]
  · simp [intervalDensity, uniformDensity, hx, inv_nonneg.mpr (sub_nonneg.mpr hab.le)]

lemma intervalDensity_le_width {a b w : ℝ}
    (ha : 0 ≤ a) (hb : b ≤ 1) (hw : 0 < w) (hlen : w / 2 ≤ b - a) (x : ℝ) :
    intervalDensity a b x ≤ 2 / w := by
  have hab : a < b := by linarith
  apply (intervalDensity_le_inv_length ha hb hab x).trans
  rw [inv_eq_one_div]
  apply (div_le_div_iff₀ (sub_pos.mpr hab) hw).2
  linarith

lemma leftLaw_eq_withDensity {m a b : ℝ} (hm : 2 ≤ m)
    (ha0 : 0 < a) (ha1 : a ≤ 1 / 4) (hb0 : 0 < b) (hb1 : b ≤ 1 / 4)
    (i : Fin 5) :
    leftLaw m a b i = baseLaw.withDensity (fun x => ENNReal.ofReal (leftDensity m a b i x)) := by
  have hm0 : 0 < m := by linarith
  have hinv0 : 0 < 1 / m := one_div_pos.mpr hm0
  have hinv1 : 1 / m ≤ 1 / 2 := (div_le_iff₀ hm0).2 (by linarith)
  fin_cases i <;> simp only [leftLaw, leftDensity] <;>
    apply intervalLaw_eq_base_withDensity <;> linarith

lemma rightLaw_eq_withDensity {m a b : ℝ} (hm : 2 ≤ m)
    (ha0 : 0 < a) (ha1 : a ≤ 1 / 4) (hb0 : 0 < b) (hb1 : b ≤ 1 / 4)
    (i : Fin 5) :
    rightLaw m a b i = baseLaw.withDensity (fun x => ENNReal.ofReal (rightDensity m a b i x)) := by
  have hm0 : 0 < m := by linarith
  have hinv0 : 0 < 1 / m := one_div_pos.mpr hm0
  have hinv1 : 1 / m ≤ 1 / 2 := (div_le_iff₀ hm0).2 (by linarith)
  fin_cases i <;> simp only [rightLaw, rightDensity] <;>
    apply intervalLaw_eq_base_withDensity <;> linarith

lemma leftDensity_bound {m a b : ℝ} (hm : 2 ≤ m)
    (ha0 : 0 < a) (ha1 : a ≤ 1 / 4) (hb0 : 0 < b) (hb1 : b ≤ 1 / 4)
    (i : Fin 5) (x : ℝ) :
    0 ≤ leftDensity m a b i x ∧ leftDensity m a b i x ≤ componentVarianceBounds m a b i := by
  have hm0 : 0 < m := by linarith
  have hinv0 : 0 < 1 / m := one_div_pos.mpr hm0
  have hinv1 : 1 / m ≤ 1 / 2 := (div_le_iff₀ hm0).2 (by linarith)
  constructor
  · fin_cases i <;> exact intervalDensity_nonneg _ _ _
  · fin_cases i <;> simp only [leftDensity, componentVarianceBounds]
    · apply intervalDensity_le_width <;> linarith
    · apply intervalDensity_le_width <;> linarith
    · apply intervalDensity_le_width <;> linarith
    · apply intervalDensity_le_width <;> linarith
    · simpa using intervalDensity_le_inv_length (a := 0) (b := 1 / m)
        (by norm_num) (by linarith) hinv0 x

lemma rightDensity_bound {m a b : ℝ} (hm : 2 ≤ m)
    (ha0 : 0 < a) (ha1 : a ≤ 1 / 4) (hb0 : 0 < b) (hb1 : b ≤ 1 / 4)
    (i : Fin 5) (x : ℝ) :
    0 ≤ rightDensity m a b i x ∧ rightDensity m a b i x ≤ componentVarianceBounds m a b i := by
  have hm0 : 0 < m := by linarith
  have hinv0 : 0 < 1 / m := one_div_pos.mpr hm0
  have hinv1 : 1 / m ≤ 1 / 2 := (div_le_iff₀ hm0).2 (by linarith)
  constructor
  · fin_cases i <;> exact intervalDensity_nonneg _ _ _
  · fin_cases i <;> simp only [rightDensity, componentVarianceBounds]
    · apply intervalDensity_le_width <;> linarith
    · apply intervalDensity_le_width <;> linarith
    · apply intervalDensity_le_width <;> linarith
    · apply intervalDensity_le_width <;> linarith
    · simpa using intervalDensity_le_inv_length (a := 1 - 1 / m) (b := 1)
        (by linarith) (by norm_num) (by linarith) x

lemma pairLaw_fst_density {κ m a b t : ℝ}
    (hκ0 : 0 ≤ κ) (hκ : κ ≤ 1 / 100) (hm : 100 ≤ m)
    (ha : 1 / m ≤ a) (ha' : a ≤ 1 / 4)
    (hb : 1 / m ≤ b) (hb' : b ≤ 1 / 4)
    (ht0 : 0 ≤ t) (ht : t ≤ 1) :
    (pairLaw κ m a b t).fst = baseLaw.withDensity
      (fun x => ENNReal.ofReal (leftMarginalDensity κ m a b t x)) := by
  have hm0 : 0 < m := by linarith
  have hm2 : 2 ≤ m := by linarith
  have ha0 := width_pos hm0 ha
  have hb0 := width_pos hm0 hb
  have : ∀ i, IsProbabilityMeasure (rightLaw m a b i) :=
    rightLaw_isProbabilityMeasure hm2 ha0 ha' hb0 hb'
  apply mixture_fst_real_density
  · exact le_trans (by norm_num) (diagonalMass_bounds hκ0 hκ hm ha ha' hb hb' ht0 ht).1
  · exact componentProbabilities_nonneg hκ0 hm0 ht0
  · intro i x
    exact (leftDensity_bound hm2 ha0 ha' hb0 hb' i x).1
  · intro i
    fin_cases i <;> exact intervalDensity_measurable _ _
  · exact leftLaw_eq_withDensity hm2 ha0 ha' hb0 hb'

lemma pairLaw_snd_density {κ m a b t : ℝ}
    (hκ0 : 0 ≤ κ) (hκ : κ ≤ 1 / 100) (hm : 100 ≤ m)
    (ha : 1 / m ≤ a) (ha' : a ≤ 1 / 4)
    (hb : 1 / m ≤ b) (hb' : b ≤ 1 / 4)
    (ht0 : 0 ≤ t) (ht : t ≤ 1) :
    (pairLaw κ m a b t).snd = baseLaw.withDensity
      (fun x => ENNReal.ofReal (rightMarginalDensity κ m a b t x)) := by
  have hm0 : 0 < m := by linarith
  have hm2 : 2 ≤ m := by linarith
  have ha0 := width_pos hm0 ha
  have hb0 := width_pos hm0 hb
  have : ∀ i, IsProbabilityMeasure (leftLaw m a b i) :=
    leftLaw_isProbabilityMeasure hm0 ha0 ha' hb0 hb'
  have : ∀ i, IsProbabilityMeasure (rightLaw m a b i) :=
    rightLaw_isProbabilityMeasure hm2 ha0 ha' hb0 hb'
  apply mixture_snd_real_density
  · exact le_trans (by norm_num) (diagonalMass_bounds hκ0 hκ hm ha ha' hb hb' ht0 ht).1
  · exact componentProbabilities_nonneg hκ0 hm0 ht0
  · intro i x
    exact (rightDensity_bound hm2 ha0 ha' hb0 hb' i x).1
  · intro i
    fin_cases i <;> exact intervalDensity_measurable _ _
  · exact rightLaw_eq_withDensity hm2 ha0 ha' hb0 hb'

lemma leftMarginalDensity_bounds {κ m a b t : ℝ}
    (hκ0 : 0 ≤ κ) (hκ : κ ≤ 1 / 100) (hm : 100 ≤ m)
    (ha : 1 / m ≤ a) (ha' : a ≤ 1 / 4)
    (hb : 1 / m ≤ b) (hb' : b ≤ 1 / 4)
    (ht0 : 0 ≤ t) (ht : t ≤ 1) (x : ℝ) :
    49 / 50 ≤ leftMarginalDensity κ m a b t x ∧
      leftMarginalDensity κ m a b t x ≤ 2 + 8 * κ ∧
      leftMarginalDensity κ m a b t x < 10 := by
  have hm0 : 0 < m := by linarith
  have hd := leftDensity_bound (m := m) (by linarith) (width_pos hm0 ha) ha'
    (width_pos hm0 hb) hb'
  have h := marginal_density_bounds hκ0 hκ hm ha ha' hb hb' ht0 ht
    (hd 0 x) (hd 1 x) (hd 2 x) (hd 3 x) (hd 4 x)
  simpa [leftMarginalDensity, componentProbabilities, Fin.sum_univ_succ, leftDensity, add_assoc] using h

lemma rightMarginalDensity_bounds {κ m a b t : ℝ}
    (hκ0 : 0 ≤ κ) (hκ : κ ≤ 1 / 100) (hm : 100 ≤ m)
    (ha : 1 / m ≤ a) (ha' : a ≤ 1 / 4)
    (hb : 1 / m ≤ b) (hb' : b ≤ 1 / 4)
    (ht0 : 0 ≤ t) (ht : t ≤ 1) (x : ℝ) :
    49 / 50 ≤ rightMarginalDensity κ m a b t x ∧
      rightMarginalDensity κ m a b t x ≤ 2 + 8 * κ ∧
      rightMarginalDensity κ m a b t x < 10 := by
  have hm0 : 0 < m := by linarith
  have hd := rightDensity_bound (m := m) (by linarith) (width_pos hm0 ha) ha'
    (width_pos hm0 hb) hb'
  have h := marginal_density_bounds hκ0 hκ hm ha ha' hb hb' ht0 ht
    (hd 0 x) (hd 1 x) (hd 2 x) (hd 3 x) (hd 4 x)
  simpa [rightMarginalDensity, componentProbabilities, Fin.sum_univ_succ, rightDensity, add_assoc] using h

lemma intervalDensity_variance_le_width {a b w : ℝ}
    (ha : 0 ≤ a) (hb : b ≤ 1) (hw : 0 < w) (hlen : w / 2 ≤ b - a) :
    (∫ x, (intervalDensity a b x - 1) ^ 2 ∂baseLaw) ≤ 2 / w := by
  apply uniformDensity_variance_le measurableSet_Ico hw
  rw [baseLaw_interval_measure ha hb (by linarith)]
  exact hlen

lemma leftDensity_variance_bound {m a b : ℝ} (hm : 2 ≤ m)
    (ha0 : 0 < a) (ha1 : a ≤ 1 / 4) (hb0 : 0 < b) (hb1 : b ≤ 1 / 4)
    (i : Fin 5) :
    (∫ x, (leftDensity m a b i x - 1) ^ 2 ∂baseLaw) ≤ componentVarianceBounds m a b i := by
  have hm0 : 0 < m := by linarith
  have hinv0 : 0 < 1 / m := one_div_pos.mpr hm0
  have hinv1 : 1 / m ≤ 1 / 2 := (div_le_iff₀ hm0).2 (by linarith)
  fin_cases i <;> simp only [leftDensity, componentVarianceBounds]
  · apply intervalDensity_variance_le_width <;> linarith
  · apply intervalDensity_variance_le_width <;> linarith
  · apply intervalDensity_variance_le_width <;> linarith
  · apply intervalDensity_variance_le_width <;> linarith
  · change (∫ x, (intervalDensity 0 (1 / m) x - 1) ^ 2 ∂baseLaw) ≤ m
    rw [intervalDensity_variance (by norm_num) (by linarith) hinv0]
    simp

lemma rightDensity_variance_bound {m a b : ℝ} (hm : 2 ≤ m)
    (ha0 : 0 < a) (ha1 : a ≤ 1 / 4) (hb0 : 0 < b) (hb1 : b ≤ 1 / 4)
    (i : Fin 5) :
    (∫ x, (rightDensity m a b i x - 1) ^ 2 ∂baseLaw) ≤ componentVarianceBounds m a b i := by
  have hm0 : 0 < m := by linarith
  have hinv0 : 0 < 1 / m := one_div_pos.mpr hm0
  have hinv1 : 1 / m ≤ 1 / 2 := (div_le_iff₀ hm0).2 (by linarith)
  fin_cases i <;> simp only [rightDensity, componentVarianceBounds]
  · apply intervalDensity_variance_le_width <;> linarith
  · apply intervalDensity_variance_le_width <;> linarith
  · apply intervalDensity_variance_le_width <;> linarith
  · apply intervalDensity_variance_le_width <;> linarith
  · change (∫ x, (intervalDensity (1 - 1 / m) 1 x - 1) ^ 2 ∂baseLaw) ≤ m
    rw [intervalDensity_variance (by linarith) (by norm_num) (by linarith)]
    simp

lemma marginalDensity_sub_one (κ m a b t : ℝ) (d : Fin 5 → ℝ) :
    diagonalMass κ m a b t + ∑ i, componentProbabilities κ m a b t i * d i - 1 =
      ∑ i, componentProbabilities κ m a b t i * (d i - 1) := by
  simp only [componentProbabilities, Fin.sum_univ_succ, Matrix.cons_val_zero,
    Matrix.cons_val_succ, Fin.sum_univ_zero, add_zero, diagonalMass]
  ring

lemma leftMarginalDensity_energy {κ m a b t : ℝ} (hm : 2 ≤ m)
    (ha0 : 0 < a) (ha1 : a ≤ 1 / 4) (hb0 : 0 < b) (hb1 : b ≤ 1 / 4)
    (ht0 : 0 ≤ t) (ht : t ≤ 1) :
    (∫ x, (leftMarginalDensity κ m a b t x - 1) ^ 2 ∂baseLaw) ≤
      20 * (2 * κ ^ 2 / m + t / m) := by
  have hf : ∀ i, MemLp (fun x => leftDensity m a b i x - 1) 2 baseLaw := by
    intro i
    fin_cases i <;> exact (intervalDensity_memLp _ _ 2).sub (memLp_const 1)
  have h := five_component_energy_bound hf (κ := κ) (by linarith) ha0 hb0 ht0 ht
    (leftDensity_variance_bound hm ha0 ha1 hb0 hb1)
  simpa only [leftMarginalDensity, marginalDensity_sub_one] using h

lemma rightMarginalDensity_energy {κ m a b t : ℝ} (hm : 2 ≤ m)
    (ha0 : 0 < a) (ha1 : a ≤ 1 / 4) (hb0 : 0 < b) (hb1 : b ≤ 1 / 4)
    (ht0 : 0 ≤ t) (ht : t ≤ 1) :
    (∫ x, (rightMarginalDensity κ m a b t x - 1) ^ 2 ∂baseLaw) ≤
      20 * (2 * κ ^ 2 / m + t / m) := by
  have hf : ∀ i, MemLp (fun x => rightDensity m a b i x - 1) 2 baseLaw := by
    intro i
    fin_cases i <;> exact (intervalDensity_memLp _ _ 2).sub (memLp_const 1)
  have h := five_component_energy_bound hf (κ := κ) (by linarith) ha0 hb0 ht0 ht
    (rightDensity_variance_bound hm ha0 ha1 hb0 hb1)
  simpa only [rightMarginalDensity, marginalDensity_sub_one] using h

lemma leftMarginalDensity_memLp (κ m a b t : ℝ) :
    MemLp (leftMarginalDensity κ m a b t) 2 baseLaw := by
  apply (memLp_const (diagonalMass κ m a b t)).add
  apply memLp_finsetSum Finset.univ
  intro i _
  apply MemLp.const_mul
  fin_cases i <;> exact intervalDensity_memLp _ _ 2

lemma rightMarginalDensity_memLp (κ m a b t : ℝ) :
    MemLp (rightMarginalDensity κ m a b t) 2 baseLaw := by
  apply (memLp_const (diagonalMass κ m a b t)).add
  apply memLp_finsetSum Finset.univ
  intro i _
  apply MemLp.const_mul
  fin_cases i <;> exact intervalDensity_memLp _ _ 2

lemma leftMarginalDensity_integral {κ m a b t : ℝ} (hm : 2 ≤ m)
    (ha0 : 0 < a) (ha1 : a ≤ 1 / 4) (hb0 : 0 < b) (hb1 : b ≤ 1 / 4) :
    (∫ x, leftMarginalDensity κ m a b t x ∂baseLaw) = 1 := by
  have hm0 : 0 < m := by linarith
  have hinv0 : 0 < 1 / m := one_div_pos.mpr hm0
  have hinv1 : 1 / m ≤ 1 / 2 := (div_le_iff₀ hm0).2 (by linarith)
  have hi : ∀ i, Integrable (fun x => componentProbabilities κ m a b t i * leftDensity m a b i x) baseLaw := by
    intro i
    apply Integrable.const_mul
    fin_cases i <;> exact (intervalDensity_memLp _ _ 2).integrable (by first | (simp; all_goals first | (norm_num; done) | rfl | decide) | (norm_num; done) | norm_num)
  have hmean : ∀ i, (∫ x, leftDensity m a b i x ∂baseLaw) = 1 := by
    intro i
    fin_cases i <;> apply intervalDensity_integral <;> linarith
  have hs := integrable_finsetSum Finset.univ (fun i _ => hi i)
  change (∫ x, diagonalMass κ m a b t + ∑ i, componentProbabilities κ m a b t i * leftDensity m a b i x ∂baseLaw) = 1
  rw [integral_add (integrable_const _) hs,
    integral_finsetSum Finset.univ (fun i _ => hi i)]
  simp only [integral_const, probReal_univ, one_smul,
    integral_const_mul, hmean, mul_one]
  simp only [componentProbabilities, Fin.sum_univ_succ, Matrix.cons_val_zero,
    Matrix.cons_val_succ, Fin.sum_univ_zero, add_zero, diagonalMass]
  ring

lemma rightMarginalDensity_integral {κ m a b t : ℝ} (hm : 2 ≤ m)
    (ha0 : 0 < a) (ha1 : a ≤ 1 / 4) (hb0 : 0 < b) (hb1 : b ≤ 1 / 4) :
    (∫ x, rightMarginalDensity κ m a b t x ∂baseLaw) = 1 := by
  have hm0 : 0 < m := by linarith
  have hinv0 : 0 < 1 / m := one_div_pos.mpr hm0
  have hinv1 : 1 / m ≤ 1 / 2 := (div_le_iff₀ hm0).2 (by linarith)
  have hi : ∀ i, Integrable (fun x => componentProbabilities κ m a b t i * rightDensity m a b i x) baseLaw := by
    intro i
    apply Integrable.const_mul
    fin_cases i <;> exact (intervalDensity_memLp _ _ 2).integrable (by first | (simp; all_goals first | (norm_num; done) | rfl | decide) | (norm_num; done) | norm_num)
  have hmean : ∀ i, (∫ x, rightDensity m a b i x ∂baseLaw) = 1 := by
    intro i
    fin_cases i <;> apply intervalDensity_integral <;> linarith
  have hs := integrable_finsetSum Finset.univ (fun i _ => hi i)
  change (∫ x, diagonalMass κ m a b t + ∑ i, componentProbabilities κ m a b t i * rightDensity m a b i x ∂baseLaw) = 1
  rw [integral_add (integrable_const _) hs,
    integral_finsetSum Finset.univ (fun i _ => hi i)]
  simp only [integral_const, probReal_univ, one_smul,
    integral_const_mul, hmean, mul_one]
  simp only [componentProbabilities, Fin.sum_univ_succ, Matrix.cons_val_zero,
    Matrix.cons_val_succ, Fin.sum_univ_zero, add_zero, diagonalMass]
  ring

lemma pairLaw_fst_le_ten {κ m a b t : ℝ}
    (hκ0 : 0 ≤ κ) (hκ : κ ≤ 1 / 100) (hm : 100 ≤ m)
    (ha : 1 / m ≤ a) (ha' : a ≤ 1 / 4)
    (hb : 1 / m ≤ b) (hb' : b ≤ 1 / 4)
    (ht0 : 0 ≤ t) (ht : t ≤ 1) :
    (pairLaw κ m a b t).fst ≤ (10 : ℝ≥0∞) • baseLaw := by
  rw [pairLaw_fst_density hκ0 hκ hm ha ha' hb hb' ht0 ht, ← withDensity_const]
  apply withDensity_mono
  apply Filter.Eventually.of_forall
  intro x
  exact (ENNReal.ofReal_le_ofReal
    (leftMarginalDensity_bounds hκ0 hκ hm ha ha' hb hb' ht0 ht x).2.2.le).trans_eq (by norm_num)

lemma pairLaw_snd_le_ten {κ m a b t : ℝ}
    (hκ0 : 0 ≤ κ) (hκ : κ ≤ 1 / 100) (hm : 100 ≤ m)
    (ha : 1 / m ≤ a) (ha' : a ≤ 1 / 4)
    (hb : 1 / m ≤ b) (hb' : b ≤ 1 / 4)
    (ht0 : 0 ≤ t) (ht : t ≤ 1) :
    (pairLaw κ m a b t).snd ≤ (10 : ℝ≥0∞) • baseLaw := by
  rw [pairLaw_snd_density hκ0 hκ hm ha ha' hb hb' ht0 ht, ← withDensity_const]
  apply withDensity_mono
  apply Filter.Eventually.of_forall
  intro x
  exact (ENNReal.ofReal_le_ofReal
    (rightMarginalDensity_bounds hκ0 hκ hm ha ha' hb hb' ht0 ht x).2.2.le).trans_eq (by norm_num)

end Invariant233.OneCoordinateCoupling

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Analysis_ConcreteTagEvent
attribute [-instance] _root_.OAI.Invariant233.OrderedProductCoupling.coordinateLaw_isProbabilityMeasure _root_.OAI.Invariant233.OrderedProductCoupling.law_isProbabilityMeasure _root_.OAI.Invariant233.OrderedProductCoupling.sourcePairLaw_isProbabilityMeasure _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal ProbabilityTheory

namespace Invariant233.OneCoordinateCoupling

open CouplingMixture CouplingMarginalBounds

theorem labelledLaw_ae_tag_interval (κ m a b t : ℝ) :
    ∀ᵐ z ∂labelledLaw κ m a b t, z.1 = some (4 : Fin 5) →
      z.2.1 < 1 / m ∧ 1 - 1 / m ≤ z.2.2 := by
  let P : Option (Fin 5) × (ℝ × ℝ) → Prop := fun z =>
    z.1 = some (4 : Fin 5) → z.2.1 < 1 / m ∧ 1 - 1 / m ≤ z.2.2
  have hP : MeasurableSet {z | P z} := by
    simp only [P, imp_iff_not_or]
    change MeasurableSet ({z : Option (Fin 5) × (ℝ × ℝ) | z.1 = some (4 : Fin 5)}ᶜ ∪
      {z : Option (Fin 5) × (ℝ × ℝ) | z.2.1 < 1 / m ∧ 1 - 1 / m ≤ z.2.2})
    exact (measurable_fst (measurableSet_singleton _)).compl.union
      ((measurableSet_lt (measurable_fst.comp measurable_snd) measurable_const).inter
       (measurableSet_le measurable_const (measurable_snd.comp measurable_snd)))
  change ∀ᵐ z ∂labelledLaw κ m a b t, P z
  rw [labelledLaw, labelledMixture, ae_add_measure_iff, ae_finsetSum_measure_iff]
  constructor
  · apply Measure.ae_smul_measure
    apply (ae_map_iff (measurable_const.prodMk measurable_id).aemeasurable hP).2
    exact Filter.Eventually.of_forall (by intro z; simp [P])
  · intro i _
    apply Measure.ae_smul_measure
    apply (ae_map_iff (measurable_const.prodMk measurable_id).aemeasurable hP).2
    by_cases hi : i = 4
    · subst i
      change ∀ᵐ z ∂(intervalLaw 0 (1 / m)).prod (intervalLaw (1 - 1 / m) 1),
        P (some 4, z)
      have : IsZeroOrProbabilityMeasure (intervalLaw 0 (1 / m)) := inferInstanceAs
        (IsZeroOrProbabilityMeasure (volume[|Ico 0 (1 / m)]))
      have : IsZeroOrProbabilityMeasure (intervalLaw (1 - 1 / m) 1) := inferInstanceAs
        (IsZeroOrProbabilityMeasure (volume[|Ico (1 - 1 / m) 1]))
      have hs : MeasurableSet {z : ℝ × ℝ | P (some 4, z)} :=
        hP.preimage (measurable_const.prodMk measurable_id)
      rw [Measure.ae_prod_iff_ae_ae hs]
      filter_upwards [intervalLaw_ae_mem 0 (1 / m)] with x hx
      filter_upwards [intervalLaw_ae_mem (1 - 1 / m) 1] with y hy
      exact fun _ => ⟨hx.2, hy.1⟩
    · exact Filter.Eventually.of_forall (by intro z; simp [P, hi])

theorem labelledLaw_left_map (κ m a b t : ℝ) :
    (labelledLaw κ m a b t).map (fun z => z.2.1) = (pairLaw κ m a b t).fst := by
  change _ = (pairLaw κ m a b t).map Prod.fst
  rw [← labelledLaw_map_snd, Measure.map_map measurable_fst measurable_snd]
  rfl

theorem labelledLaw_right_map (κ m a b t : ℝ) :
    (labelledLaw κ m a b t).map (fun z => z.2.2) = (pairLaw κ m a b t).snd := by
  change _ = (pairLaw κ m a b t).map Prod.snd
  rw [← labelledLaw_map_snd, Measure.map_map measurable_snd measurable_snd]
  rfl

theorem concrete_product_currentBlock_mass (m : ℕ) (hm : 100 ≤ m)
    (κ : ℝ) (hκ0 : 0 ≤ κ) (hκ : κ ≤ 1 / 100)
    (a b : Fin m → ℝ)
    (ha : ∀ i, 1 / (m : ℝ) ≤ a i) (ha' : ∀ i, a i ≤ 1 / 4)
    (hb : ∀ i, 1 / (m : ℝ) ≤ b i) (hb' : ∀ i, b i ≤ 1 / 4) :
    Real.exp (-82) ≤
      (Measure.pi (fun i => labelledLaw κ m (a i) (b i) 1)).real
        {z | (∃ i, (z i).1 = some (4 : Fin 5)) ∧
          ∀ i, (z i).2.1 < 1 - 2 / (m : ℝ) ∧ 2 / (m : ℝ) < (z i).2.2} := by
  have hmR : (100 : ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : (0 : ℝ) < m := by linarith
  have hm2 : (2 : ℝ) ≤ m := by linarith
  let μ := fun i : Fin m => labelledLaw κ m (a i) (b i) 1
  have : ∀ i, IsProbabilityMeasure (μ i) := fun i =>
    labelledLaw_isProbabilityMeasure hκ0 hκ hmR (ha i) (ha' i) (hb i) (hb' i)
      (by norm_num) (by norm_num)
  let T : Fin m → Set (Option (Fin 5) × (ℝ × ℝ)) :=
    fun _ => {z | z.1 = some (4 : Fin 5)}
  have hT : ∀ i, MeasurableSet (T i) := fun _ =>
    measurable_fst (measurableSet_singleton _)
  have hTag : ∀ i, (μ i).real (T i) = 1 / (m : ℝ) := by
    intro i
    change (labelledLaw κ m (a i) (b i) 1).real {z | z.1 = some (4 : Fin 5)} = _
    rw [measureReal_def, labelledLaw_tag_mass hm2 (width_pos hm0 (ha i)) (ha' i)
      (width_pos hm0 (hb i)) (hb' i), ENNReal.toReal_ofReal (by positivity)]
  have hinv : 1 / (m : ℝ) ≤ 1 / 100 :=
    (div_le_div_iff₀ hm0 (by norm_num)).2 (by linarith)
  have hSafe : ∀ i, ∀ᵐ z ∂μ i, z ∈ T i →
      z.2.1 < 1 - 2 / (m : ℝ) ∧ 2 / (m : ℝ) < z.2.2 := by
    intro i
    filter_upwards [labelledLaw_ae_tag_interval κ m (a i) (b i) 1] with z hz
    intro ht
    obtain ⟨hx, hy⟩ := hz ht
    rw [show (2 : ℝ) / m = 2 * (1 / (m : ℝ)) by ring]
    constructor <;> linarith
  have hdomX : ∀ i, (μ i).map (fun z => z.2.1) ≤
      ENNReal.ofReal 10 • volume.restrict (Ico (0 : ℝ) 1) := by
    intro i
    change (labelledLaw κ m (a i) (b i) 1).map _ ≤ _
    rw [labelledLaw_left_map, ← baseLaw_eq_restrict]
    simpa using pairLaw_fst_le_ten hκ0 hκ hmR (ha i) (ha' i) (hb i) (hb' i)
      (t := 1) (by norm_num) (by norm_num)
  have hdomY : ∀ i, (μ i).map (fun z => z.2.2) ≤
      ENNReal.ofReal 10 • volume.restrict (Ico (0 : ℝ) 1) := by
    intro i
    change (labelledLaw κ m (a i) (b i) 1).map _ ≤ _
    rw [labelledLaw_right_map, ← baseLaw_eq_restrict]
    simpa using pairLaw_snd_le_ten hκ0 hκ hmR (ha i) (ha' i) (hb i) (hb' i)
      (t := 1) (by norm_num) (by norm_num)
  have hbudget : 0 ≤ 1 - (1 + 2 * ((10 : ℝ) * 2)) / (m : ℝ) := by
    apply sub_nonneg.mpr
    exact (div_le_one hm0).mpr (by linarith)
  have h := InvariantRotation.TruncationEvent.currentBlock_mass_lower_bound_ae m
    (by omega) μ T hT (fun _ => measurable_fst.comp measurable_snd)
    (fun _ => measurable_snd.comp measurable_snd) (C := 10) (a := 2)
    (by norm_num) (by norm_num) hbudget hTag hSafe hdomX hdomY
  norm_num only [show (1 : ℝ) + 2 * (10 * 2) = 41 by norm_num] at h
  exact (InvariantRotation.TaggedEventBounds.product_tag_bound m hm).trans h

end Invariant233.OneCoordinateCoupling

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Couplings_BlockedProductCoupling
attribute [-instance] _root_.OAI.Invariant233.OrderedProductCoupling.coordinateLaw_isProbabilityMeasure _root_.OAI.Invariant233.OrderedProductCoupling.law_isProbabilityMeasure _root_.OAI.Invariant233.OrderedProductCoupling.sourcePairLaw_isProbabilityMeasure _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.BlockedProductCoupling.unflatten_flatten _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal

namespace Invariant233.BlockedProductCoupling

open OneCoordinateCoupling

variable {m : ℕ → ℕ} {κ : ℕ → ℝ}
  {a b : (s : ℕ) → Fin (m s) → ℝ}
  (hm : ∀ s, 100 ≤ m s) (hκ0 : ∀ s, 0 ≤ κ s) (hκ : ∀ s, κ s ≤ 1 / 100)
  (ha : ∀ s i, 1 / (m s : ℝ) ≤ a s i) (ha' : ∀ s i, a s i ≤ 1 / 4)
  (hb : ∀ s i, 1 / (m s : ℝ) ≤ b s i) (hb' : ∀ s i, b s i ≤ 1 / 4)

include hm hκ0 hκ ha ha' hb hb'

theorem coordinate_isProbabilityMeasure (j s : ℕ) (i : Fin (m s)) :
    IsProbabilityMeasure (labelledLaw (κ s) (m s) (a s i) (b s i)
      (if s = j then 1 else 0)) := by
  apply labelledLaw_isProbabilityMeasure (hκ0 s) (hκ s)
    (by exact_mod_cast hm s) (ha s i) (ha' s i) (hb s i) (hb' s i)
  all_goals split_ifs <;> norm_num

theorem blockLaw_isProbabilityMeasure (j s : ℕ) :
    IsProbabilityMeasure (blockLaw m κ a b j s) := by
  have := coordinate_isProbabilityMeasure hm hκ0 hκ ha ha' hb hb' j s
  unfold blockLaw
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

theorem law_isProbabilityMeasure (j : ℕ) :
    IsProbabilityMeasure (law m κ a b j) := by
  have := blockLaw_isProbabilityMeasure hm hκ0 hκ ha ha' hb hb' j
  unfold law
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

theorem law_map_block (j s : ℕ) :
    (law m κ a b j).map (fun z => z s) = blockLaw m κ a b j s := by
  have := blockLaw_isProbabilityMeasure hm hκ0 hκ ha ha' hb hb' j
  exact Measure.infinitePi_map_eval _ s

theorem law_map_coordinate (j s : ℕ) (i : Fin (m s)) :
    (law m κ a b j).map (fun z => z s i) =
      labelledLaw (κ s) (m s) (a s i) (b s i) (if s = j then 1 else 0) := by
  have := coordinate_isProbabilityMeasure hm hκ0 hκ ha ha' hb hb' j s
  change (law m κ a b j).map ((fun z => z i) ∘ (fun z => z s)) = _
  rw [← Measure.map_map (measurable_pi_apply i) (measurable_pi_apply s),
    law_map_block hm hκ0 hκ ha ha' hb hb']
  exact (measurePreserving_eval _ i).map_eq

theorem currentEvent_mass (j : ℕ) :
    Real.exp (-82) ≤ (law m κ a b j).real (currentEvent m j) := by
  let E : Set (Fin (m j) → Coordinate) :=
    {z | (∃ i, (z i).1 = some (4 : Fin 5)) ∧
      ∀ i, (z i).2.1 < 1 - 2 / (m j : ℝ) ∧ 2 / (m j : ℝ) < (z i).2.2}
  have hE : MeasurableSet E := by
    change MeasurableSet ({z : Fin (m j) → Coordinate | ∃ i, (z i).1 = some (4 : Fin 5)} ∩
      {z | ∀ i, (z i).2.1 < 1 - 2 / (m j : ℝ) ∧ 2 / (m j : ℝ) < (z i).2.2})
    rw [Set.ofPred_exists, Set.ofPred_forall]
    apply MeasurableSet.inter
    ·
      apply MeasurableSet.iUnion
      intro i
      exact (measurable_fst.comp (measurable_pi_apply i)) (measurableSet_singleton _)
    ·
      apply MeasurableSet.iInter
      intro i
      have hx : Measurable (fun z : Fin (m j) → Coordinate => (z i).2.1) := by fun_prop
      have hy : Measurable (fun z : Fin (m j) → Coordinate => (z i).2.2) := by fun_prop
      exact (measurableSet_lt hx measurable_const).inter
        (measurableSet_lt measurable_const hy)
  have heq : (law m κ a b j).real (currentEvent m j) =
      (blockLaw m κ a b j j).real E := by
    rw [← law_map_block hm hκ0 hκ ha ha' hb hb' j j,
      map_measureReal_apply (measurable_pi_apply j) hE]
    rfl
  rw [heq]
  simpa only [blockLaw, ite_true, if_true, E] using
    concrete_product_currentBlock_mass (m j) (hm j) (κ j) (hκ0 j) (hκ j)
      (a j) (b j) (ha j) (ha' j) (hb j) (hb' j)

theorem law_map_uncurry (j : ℕ) :
    (law m κ a b j).map (fun z (p : Σ s, Fin (m s)) => z p.1 p.2) =
      Measure.infinitePi (fun p : Σ s, Fin (m s) =>
        labelledLaw (κ p.1) (m p.1) (a p.1 p.2) (b p.1 p.2)
          (if p.1 = j then 1 else 0)) := by
  have := coordinate_isProbabilityMeasure hm hκ0 hκ ha ha' hb hb' j
  unfold law blockLaw
  have h := Measure.infinitePi_map_piCurry_symm
    (fun s i => labelledLaw (κ s) (m s) (a s i) (b s i)
      (if s = j then 1 else 0))
  simp only [Measure.infinitePi_eq_pi] at h
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  congr 1

theorem law_left_marginal_le_ten (j s : ℕ) (i : Fin (m s)) :
    (law m κ a b j).map (fun z => (z s i).2.1) ≤
      (10 : ℝ≥0∞) • volume.restrict (Ico (0 : ℝ) 1) := by
  change (law m κ a b j).map ((Prod.fst ∘ Prod.snd) ∘
    (fun z => z s i)) ≤ _
  rw [← Measure.map_map (measurable_fst.comp measurable_snd)
      ((measurable_pi_apply i).comp (measurable_pi_apply s)),
    law_map_coordinate hm hκ0 hκ ha ha' hb hb']
  change (labelledLaw (κ s) (m s) (a s i) (b s i) _).map
    (fun z => z.2.1) ≤ _
  rw [labelledLaw_left_map, ← baseLaw_eq_restrict]
  apply pairLaw_fst_le_ten (hκ0 s) (hκ s) (by exact_mod_cast hm s)
    (ha s i) (ha' s i) (hb s i) (hb' s i)
  all_goals split_ifs <;> norm_num

theorem law_right_marginal_le_ten (j s : ℕ) (i : Fin (m s)) :
    (law m κ a b j).map (fun z => (z s i).2.2) ≤
      (10 : ℝ≥0∞) • volume.restrict (Ico (0 : ℝ) 1) := by
  change (law m κ a b j).map ((Prod.snd ∘ Prod.snd) ∘
    (fun z => z s i)) ≤ _
  rw [← Measure.map_map (measurable_snd.comp measurable_snd)
      ((measurable_pi_apply i).comp (measurable_pi_apply s)),
    law_map_coordinate hm hκ0 hκ ha ha' hb hb']
  change (labelledLaw (κ s) (m s) (a s i) (b s i) _).map
    (fun z => z.2.2) ≤ _
  rw [labelledLaw_right_map, ← baseLaw_eq_restrict]
  apply pairLaw_snd_le_ten (hκ0 s) (hκ s) (by exact_mod_cast hm s)
    (ha s i) (ha' s i) (hb s i) (hb' s i)
  all_goals split_ifs <;> norm_num

theorem futureBad_mass_le {K : ℕ → ℝ} (hK : ∀ s, 0 < K s)
    (j : ℕ) (hsum : Summable (fun n : ℕ => 1 / K (j + 1 + n))) :
    (law m κ a b j).real (futureBad m K j) ≤
      40 * K j * ∑' n : ℕ, 1 / K (j + 1 + n) := by
  have := law_isProbabilityMeasure hm hκ0 hκ ha ha' hb hb' j
  have h := InvariantRotation.EndpointIntervalBounds.blocked_future_endpoint_loss_le
    (law m κ a b j) (fun n => m (j + 1 + n)) (fun n => by have := hm (j + 1 + n); omega)
    (K := fun n => K (j + 1 + n)) (fun n => hK _) hsum
    (X := fun n i z => (z (j + 1 + n) i).2.1)
    (Y := fun n i z => (z (j + 1 + n) i).2.2)
    (by intros; fun_prop) (by intros; fun_prop)
    (C := 10) (a := 2) (W := K j) (by norm_num) (by norm_num) (hK j).le
    (fun n i => by simpa using law_left_marginal_le_ten hm hκ0 hκ ha ha' hb hb' j _ i)
    (fun n i => by simpa using law_right_marginal_le_ten hm hκ0 hκ ha ha' hb hb' j _ i)
  norm_num only [show (2 : ℝ) * 10 * 2 = 40 by norm_num] at h
  exact h

end Invariant233.BlockedProductCoupling

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Analysis_BlockedEventConditions
attribute [-instance] _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set

namespace Invariant233.BlockedProductCoupling

theorem not_mem_futureBad_iff {m : ℕ → ℕ} {K : ℕ → ℝ}
    {j : ℕ} {z : Sample m} :
    z ∉ futureBad m K j ↔
      ∀ s, j < s → ∀ i : Fin (m s),
        (z s i).2.1 < 1 - 2 * K j / ((m s : ℝ) * K s) ∧
        2 * K j / ((m s : ℝ) * K s) < (z s i).2.2 := by
  simp only [futureBad, mem_iUnion, mem_ofPred_eq, not_exists, not_or, not_le]
  constructor
  · intro h s hs
    obtain ⟨n, hn⟩ := Nat.exists_eq_add_of_le (Nat.succ_le_of_lt hs)
    subst s
    exact h n
  · intro h n i
    exact h (j + 1 + n) (by omega) i

theorem mem_retainedEvent_iff {X : Type*} {m : ℕ → ℕ} {K : ℕ → ℝ}
    {r : X → ℝ} {x y : Sample m → X} {j : ℕ} {z : Sample m} :
    z ∈ retainedEvent m K r x y j ↔
      (∃ i, (z j i).1 = some (4 : Fin 5)) ∧
      (∀ i, (z j i).2.1 < 1 - 2 / (m j : ℝ) ∧
        2 / (m j : ℝ) < (z j i).2.2) ∧
      (∀ s, j < s → ∀ i : Fin (m s),
        (z s i).2.1 < 1 - 2 * K j / ((m s : ℝ) * K s) ∧
        2 * K j / ((m s : ℝ) * K s) < (z s i).2.2) ∧
      1 / (j : ℝ) ≤ r (x z) ∧ 1 / (j : ℝ) ≤ 1 - r (y z) := by
  simp only [retainedEvent, mem_sdiff, mem_union, not_or, not_mem_futureBad_iff,
    currentEvent, mem_ofPred_eq, not_lt]
  tauto

end Invariant233.BlockedProductCoupling

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Analysis_EndpointLoss
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Filter MeasureTheory Set
open scoped Topology RealInnerProductSpace

namespace Invariant233.EndpointLoss

variable {X : Type*} [MeasurableSpace X]

theorem sqrt_integral_sq_eq_norm {μ : Measure X} (f : Lp ℝ 2 μ) :
    Real.sqrt (∫ x, f x ^ 2 ∂μ) = ‖f‖ := by
  have hs : (∫ x, f x ^ 2 ∂μ) = ‖f‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq f, L2.inner_def]
    simp only [real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs]
  rw [hs, Real.sqrt_sq (norm_nonneg f)]

theorem sqrt_integral_sq_eq_toReal_eLpNorm {μ : Measure X} {h : X → ℝ} (hh : MemLp h 2 μ) :
    Real.sqrt (∫ x, h x ^ 2 ∂μ) = (eLpNorm h 2 μ).toReal := by
  rw [← Lp.norm_toLp h hh, ← sqrt_integral_sq_eq_norm]
  congr 1
  apply integral_congr_ae
  filter_upwards [hh.coeFn_toLp] with x hx
  rw [hx]

theorem tendsto_measure_sublevel_zero
    (μ : Measure X) [IsFiniteMeasure μ] {r : X → ℝ}
    (hr : Measurable r) (hpos : ∀ᵐ x ∂μ, 0 < r x)
    {t : ℕ → ℝ} (ht_mono : Antitone t)
    (ht_zero : Tendsto t atTop (𝓝 0)) :
    Tendsto (fun n => μ {x | r x < t n}) atTop (𝓝 0) := by
  let s : ℕ → Set X := fun n => {x | r x < t n}
  have hs : ∀ n, MeasurableSet (s n) := fun n => measurableSet_lt hr measurable_const
  have hm : Antitone s := by
    intro n m hnm x hx
    exact lt_of_lt_of_le hx (ht_mono hnm)
  have hnull : μ (⋂ n, s n) = 0 := by
    apply measure_mono_null (t := {x | ¬ 0 < r x})
    · intro x hx
      simp only [mem_iInter, mem_ofPred_eq, s] at hx ⊢
      have hle : r x ≤ 0 := ge_of_tendsto' ht_zero (fun n => (hx n).le)
      exact not_lt.mpr hle
    · exact ae_iff.mp hpos
  have hlim := tendsto_measure_iInter_atTop
    (fun n => (hs n).nullMeasurableSet) hm ⟨0, measure_ne_top μ _⟩
  simpa only [hnull, Function.comp_def, s] using hlim

theorem tendsto_measureReal_sublevel_zero
    (μ : Measure X) [IsFiniteMeasure μ] {r : X → ℝ}
    (hr : Measurable r) (hpos : ∀ᵐ x ∂μ, 0 < r x)
    {t : ℕ → ℝ} (ht_mono : Antitone t)
    (ht_zero : Tendsto t atTop (𝓝 0)) :
    Tendsto (fun n => μ.real {x | r x < t n}) atTop (𝓝 0) := by
  exact (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp
    (tendsto_measure_sublevel_zero μ hr hpos ht_mono ht_zero)

theorem tendsto_measureReal_reciprocal_sublevel_zero
    (μ : Measure X) [IsFiniteMeasure μ] {r : X → ℝ}
    (hr : Measurable r) (hpos : ∀ᵐ x ∂μ, 0 < r x) :
    Tendsto (fun n : ℕ => μ.real {x | r x < 1 / ((n : ℝ) + 1)})
      atTop (𝓝 0) := by
  apply tendsto_measureReal_sublevel_zero μ hr hpos
  · intro n m hnm
    exact one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hnm 1)
  · exact tendsto_one_div_add_atTop_nhds_zero_nat

theorem setIntegral_density_le_sqrt
    (μ : Measure X) [IsFiniteMeasure μ] {h : X → ℝ}
    (hh : MemLp h 2 μ) (h_nonneg : 0 ≤ᵐ[μ] h)
    {s : Set X} (hs : MeasurableSet s) :
    (∫ x in s, h x ∂μ) ≤
      Real.sqrt (∫ x, h x ^ 2 ∂μ) * Real.sqrt (μ.real s) := by
  have hCS := integral_mul_le_Lp_mul_Lq_of_nonneg
    Real.HolderConjugate.two_two h_nonneg
    (show 0 ≤ᵐ[μ] s.indicator (fun _ : X => (1 : ℝ)) from
      Filter.Eventually.of_forall (fun x => by
        change 0 ≤ s.indicator (fun _ : X => (1 : ℝ)) x
        by_cases hx : x ∈ s <;> simp [hx]))
    (by simpa using hh) (by simpa using (MemLp.indicator hs (memLp_const (1 : ℝ))))
  have hmul : (fun x => h x * s.indicator (fun _ : X => (1 : ℝ)) x) =
      s.indicator h := by
    funext x
    by_cases hx : x ∈ s <;> simp [hx]
  have hpow : (fun x => (s.indicator (fun _ : X => (1 : ℝ)) x) ^ (2 : ℝ)) =
      s.indicator (fun _ : X => (1 : ℝ)) := by
    funext x
    by_cases hx : x ∈ s <;> simp [hx]
  rw [hmul, integral_indicator hs, hpow] at hCS
  simp only [Real.rpow_two, ← Real.sqrt_eq_rpow] at hCS
  have hmass : (∫ x, s.indicator (fun _ : X => (1 : ℝ)) x ∂μ) = μ.real s := by
    rw [integral_indicator hs]
    simp
  simpa only [hmass] using hCS

theorem withDensity_measureReal_le_sqrt
    (μ : Measure X) [IsFiniteMeasure μ] {h : X → ℝ}
    (hh : MemLp h 2 μ) (h_nonneg : 0 ≤ᵐ[μ] h)
    {s : Set X} (hs : MeasurableSet s) :
    (μ.withDensity (fun x => ENNReal.ofReal (h x))).real s ≤
      Real.sqrt (∫ x, h x ^ 2 ∂μ) * Real.sqrt (μ.real s) := by
  rw [measureReal_def, withDensity_apply _ hs]
  rw [← integral_eq_lintegral_of_nonneg_ae
    (ae_restrict_of_ae h_nonneg) hh.aestronglyMeasurable.restrict]
  exact setIntegral_density_le_sqrt μ hh h_nonneg hs

theorem tendsto_measureReal_of_uniform_sqrt_bound
    (μ : Measure X) (ν : ℕ → Measure X) (H : ℝ) {s : ℕ → Set X}
    (hbound : ∀ n, (ν n).real (s n) ≤ H * Real.sqrt (μ.real (s n)))
    (hzero : Tendsto (fun n => μ.real (s n)) atTop (𝓝 0)) :
    Tendsto (fun n => (ν n).real (s n)) atTop (𝓝 0) := by
  apply squeeze_zero (fun _ => measureReal_nonneg) hbound
  simpa using tendsto_const_nhds.mul (Real.continuous_sqrt.continuousAt.tendsto.comp hzero)

theorem tendsto_measureReal_one_div_sublevel_zero
    (μ : Measure X) [IsFiniteMeasure μ] {r : X → ℝ}
    (hr : Measurable r) (hpos : ∀ᵐ x ∂μ, 0 < r x) :
    Tendsto (fun n : ℕ => μ.real {x | r x < 1 / (n : ℝ)})
      atTop (𝓝 0) := by
  apply (tendsto_add_atTop_iff_nat 1).mp
  simpa only [Nat.cast_add, Nat.cast_one] using
    tendsto_measureReal_reciprocal_sublevel_zero μ hr hpos

theorem tendsto_withDensity_sublevel_zero
    (μ : Measure X) [IsFiniteMeasure μ] {r : X → ℝ}
    (hr : Measurable r) (hpos : ∀ᵐ x ∂μ, 0 < r x)
    (h : ℕ → X → ℝ) (hh : ∀ n, MemLp (h n) 2 μ)
    (h_nonneg : ∀ n, 0 ≤ᵐ[μ] h n) (H : ℝ)
    (hbound : ∀ n, Real.sqrt (∫ x, h n x ^ 2 ∂μ) ≤ H) :
    Tendsto (fun n : ℕ =>
      (μ.withDensity (fun x => ENNReal.ofReal (h n x))).real
        {x | r x < 1 / (n : ℝ)}) atTop (𝓝 0) := by
  apply tendsto_measureReal_of_uniform_sqrt_bound μ _ H
  · intro n
    exact (withDensity_measureReal_le_sqrt μ (hh n) (h_nonneg n)
      (measurableSet_lt hr measurable_const)).trans
      (mul_le_mul_of_nonneg_right (hbound n) (Real.sqrt_nonneg _))
  · exact tendsto_measureReal_one_div_sublevel_zero μ hr hpos

theorem tendsto_pullback_sublevel_zero
    (μ : Measure X) [IsFiniteMeasure μ] {r : X → ℝ}
    (hr : Measurable r) (hpos : ∀ᵐ x ∂μ, 0 < r x)
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (P : (n : ℕ) → Measure (Ω n)) (x : (n : ℕ) → Ω n → X)
    (hx : ∀ n, Measurable (x n))
    (h : ℕ → X → ℝ) (hh : ∀ n, MemLp (h n) 2 μ)
    (hn : ∀ n, 0 ≤ᵐ[μ] h n) (H : ℝ)
    (hb : ∀ n, Real.sqrt (∫ z, h n z ^ 2 ∂μ) ≤ H)
    (hmap : ∀ n, (P n).map (x n) =
      μ.withDensity (fun z => ENNReal.ofReal (h n z))) :
    Tendsto (fun n : ℕ => (P n).real {ω | r (x n ω) < 1 / (n : ℝ)})
      atTop (𝓝 0) := by
  have ht := tendsto_withDensity_sublevel_zero μ hr hpos h hh hn H hb
  convert ht using 1
  all_goals try with_reducible_and_instances rfl
  funext n
  rw [← hmap n, map_measureReal_apply (hx n) (measurableSet_lt hr measurable_const)]
  rfl

theorem tendsto_endpoint_bad_union_zero
    (μ : Measure X) [IsFiniteMeasure μ] {r : X → ℝ}
    (hr : Measurable r) (hi : ∀ᵐ z ∂μ, 0 < r z ∧ r z < 1)
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (P : (n : ℕ) → Measure (Ω n))
    (x y : (n : ℕ) → Ω n → X)
    (hx : ∀ n, Measurable (x n)) (hy : ∀ n, Measurable (y n))
    (h₁ h₂ : ℕ → X → ℝ)
    (hh₁ : ∀ n, MemLp (h₁ n) 2 μ) (hh₂ : ∀ n, MemLp (h₂ n) 2 μ)
    (hn₁ : ∀ n, 0 ≤ᵐ[μ] h₁ n) (hn₂ : ∀ n, 0 ≤ᵐ[μ] h₂ n)
    (H₁ H₂ : ℝ)
    (hb₁ : ∀ n, Real.sqrt (∫ z, h₁ n z ^ 2 ∂μ) ≤ H₁)
    (hb₂ : ∀ n, Real.sqrt (∫ z, h₂ n z ^ 2 ∂μ) ≤ H₂)
    (hm₁ : ∀ n, (P n).map (x n) =
      μ.withDensity (fun z => ENNReal.ofReal (h₁ n z)))
    (hm₂ : ∀ n, (P n).map (y n) =
      μ.withDensity (fun z => ENNReal.ofReal (h₂ n z))) :
    Tendsto (fun n : ℕ => (P n).real
      ({ω | r (x n ω) < 1 / (n : ℝ)} ∪
       {ω | 1 - r (y n ω) < 1 / (n : ℝ)})) atTop (𝓝 0) := by
  apply squeeze_zero (fun _ => measureReal_nonneg)
    (fun _ => measureReal_union_le _ _)
  have hp : ∀ᵐ z ∂μ, 0 < r z := hi.mono (fun _ hz => hz.1)
  have hq : ∀ᵐ z ∂μ, 0 < 1 - r z := hi.mono (fun _ hz => sub_pos.mpr hz.2)
  simpa only [zero_add, Pi.sub_apply] using
    (tendsto_pullback_sublevel_zero μ hr hp P x hx h₁ hh₁ hn₁ H₁ hb₁ hm₁).add
      (tendsto_pullback_sublevel_zero μ (measurable_const.sub hr) hq
        P y hy h₂ hh₂ hn₂ H₂ hb₂ hm₂)

end Invariant233.EndpointLoss

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Analysis_ParameterTails
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Filter
open scoped Topology

namespace Invariant233.ParameterTails

theorem tsum_tail_le_of_half_decay {a : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n)
    (hstep : ∀ n, a (n + 1) ≤ a n / 2) (j : ℕ) :
    (∑' n : ℕ, a (j + n)) ≤ 2 * a j := by
  have hs : Summable (fun n : ℕ => a (j + n)) :=
    summable_of_half_decay (fun n => ha (j + n))
      (fun n => by simpa only [Nat.add_assoc] using hstep (j + n))
  calc
    (∑' n : ℕ, a (j + n)) ≤ ∑' n : ℕ, a j * (1 / 2 : ℝ) ^ n :=
      hs.tsum_le_tsum (half_decay_iterate hstep j)
        (summable_geometric_two.mul_left (a j))
    _ = 2 * a j := by rw [tsum_mul_left, tsum_geometric_two]; ring

theorem reciprocal_tail_bound {K : ℕ → ℝ} (hK : ∀ n, 0 < K n)
    (hdouble : ∀ n, 2 * K n ≤ K (n + 1)) (j : ℕ) :
    (∑' n : ℕ, 1 / K (j + 1 + n)) ≤ 2 / K (j + 1) := by
  simpa only [div_eq_mul_inv, one_mul] using
    tsum_tail_le_of_half_decay (fun n => le_of_lt (one_div_pos.mpr (hK n)))
      (reciprocal_half_decay hK hdouble) (j + 1)

end Invariant233.ParameterTails

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Couplings_ProductDensity
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory
open scoped BigOperators ENNReal

namespace Invariant233.ProductDensity

theorem integral_sq_eq_one_add_centered_sq
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {h : Ω → ℝ} (hh : MemLp h 2 μ) (hmean : ∫ x, h x ∂μ = 1) :
    (∫ x, h x ^ 2 ∂μ) = 1 + ∫ x, (h x - 1) ^ 2 ∂μ := by
  have hv := ProbabilityTheory.variance_eq_sub hh
  rw [ProbabilityTheory.variance_eq_integral hh.aemeasurable, hmean] at hv
  norm_num at hv
  linarith

theorem integral_finite_product_sq
    {ι : Type*} [Fintype ι] {Ω : ι → Type*}
    [∀ i, MeasurableSpace (Ω i)] {μ : (i : ι) → Measure (Ω i)}
    [∀ i, IsProbabilityMeasure (μ i)] {h : (i : ι) → Ω i → ℝ}
    (hh : ∀ i, MemLp (h i) 2 (μ i))
    (hmean : ∀ i, ∫ x, h i x ∂μ i = 1) :
    (∫ x, (∏ i, h i (x i)) ^ 2 ∂Measure.pi μ) =
      ∏ i, (1 + ∫ x, (h i x - 1) ^ 2 ∂μ i) := by
  calc
    _ = ∫ x, ∏ i, (h i (x i)) ^ 2 ∂Measure.pi μ := by
      congr 1
      funext x
      exact (Finset.prod_pow _ _ _).symm
    _ = ∏ i, ∫ x, (h i x) ^ 2 ∂μ i := integral_fintype_prod_eq_prod (μ := μ) (fun i x => h i x ^ 2)
    _ = _ := Finset.prod_congr rfl fun i _ =>
      integral_sq_eq_one_add_centered_sq (hh i) (hmean i)

theorem integral_finite_product_sq_le_exp
    {ι : Type*} [Fintype ι] {Ω : ι → Type*}
    [∀ i, MeasurableSpace (Ω i)] {μ : (i : ι) → Measure (Ω i)}
    [∀ i, IsProbabilityMeasure (μ i)] {h : (i : ι) → Ω i → ℝ}
    (hh : ∀ i, MemLp (h i) 2 (μ i))
    (hmean : ∀ i, ∫ x, h i x ∂μ i = 1) :
    (∫ x, (∏ i, h i (x i)) ^ 2 ∂Measure.pi μ) ≤
      Real.exp (∑ i, ∫ x, (h i x - 1) ^ 2 ∂μ i) := by
  rw [integral_finite_product_sq hh hmean]
  exact Real.prod_one_add_le_exp_sum _ fun i => integral_nonneg fun x => sq_nonneg _

theorem integral_finite_product_sq_le_exp_of_sum_le
    {ι : Type*} [Fintype ι] {Ω : ι → Type*}
    [∀ i, MeasurableSpace (Ω i)] {μ : (i : ι) → Measure (Ω i)}
    [∀ i, IsProbabilityMeasure (μ i)] {h : (i : ι) → Ω i → ℝ} {C : ℝ}
    (hh : ∀ i, MemLp (h i) 2 (μ i))
    (hmean : ∀ i, ∫ x, h i x ∂μ i = 1)
    (hC : (∑ i, ∫ x, (h i x - 1) ^ 2 ∂μ i) ≤ C) :
    (∫ x, (∏ i, h i (x i)) ^ 2 ∂Measure.pi μ) ≤ Real.exp C :=
  (integral_finite_product_sq_le_exp hh hmean).trans (Real.exp_le_exp.mpr hC)

theorem eLpNorm_finite_product_le_exp_half
    {ι : Type*} [Fintype ι] {Ω : ι → Type*}
    [∀ i, MeasurableSpace (Ω i)] {μ : (i : ι) → Measure (Ω i)}
    [∀ i, IsProbabilityMeasure (μ i)] {h : (i : ι) → Ω i → ℝ} {C : ℝ}
    (hh : ∀ i, MemLp (h i) 2 (μ i))
    (hmean : ∀ i, ∫ x, h i x ∂μ i = 1)
    (hC : (∑ i, ∫ x, (h i x - 1) ^ 2 ∂μ i) ≤ C) :
    eLpNorm (fun x => ∏ i, h i (x i)) 2 (Measure.pi μ) ≤
      ENNReal.ofReal (Real.exp (C / 2)) := by
  rw [MemLp.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)
    (memLp_finite_product hh)]
  norm_num only [ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_eq_abs, sq_abs]
  apply ENNReal.ofReal_le_ofReal
  calc
    _ ≤ (Real.exp C) ^ (1 / 2 : ℝ) :=
      Real.rpow_le_rpow (integral_nonneg fun _ => sq_nonneg _)
        (integral_finite_product_sq_le_exp_of_sum_le hh hmean hC) (by positivity)
    _ = Real.exp (C / 2) := by
      rw [← Real.exp_mul]
      congr 1
      ring

theorem eLpNorm_partial_product_le_exp_half
    {ι : Type*} {Ω : ι → Type*} [∀ i, MeasurableSpace (Ω i)]
    {μ : (i : ι) → Measure (Ω i)} [∀ i, IsProbabilityMeasure (μ i)]
    {h : (i : ι) → Ω i → ℝ} {C : ℝ} (s : Finset ι)
    (hh : ∀ i, MemLp (h i) 2 (μ i))
    (hmean : ∀ i, ∫ x, h i x ∂μ i = 1)
    (hC : (∑ i ∈ s, ∫ x, (h i x - 1) ^ 2 ∂μ i) ≤ C) :
    eLpNorm (fun x => ∏ i ∈ s, h i (x i)) 2 (Measure.infinitePi μ) ≤
      ENNReal.ofReal (Real.exp (C / 2)) := by
  have heq := eLpNorm_comp_measurePreserving
    (memLp_finite_product (fun i : s => hh i)).aestronglyMeasurable
    (measurePreserving_restrict_infinitePi μ s) (p := (2 : ℝ≥0∞))
  have hbound := eLpNorm_finite_product_le_exp_half (fun i : s => hh i)
    (fun i : s => hmean i) (C := C) (by
      exact (Finset.sum_coe_sort s (fun i => ∫ x, (h i x - 1) ^ 2 ∂μ i)).le.trans hC)
  rw [partial_product_eq_restrict h s]
  exact heq.le.trans hbound

theorem eLpNorm_partial_product_le_exp_half_of_tsum_le
    {ι : Type*} {Ω : ι → Type*} [∀ i, MeasurableSpace (Ω i)]
    {μ : (i : ι) → Measure (Ω i)} [∀ i, IsProbabilityMeasure (μ i)]
    {h : (i : ι) → Ω i → ℝ} {C : ℝ} (s : Finset ι)
    (hh : ∀ i, MemLp (h i) 2 (μ i))
    (hmean : ∀ i, ∫ x, h i x ∂μ i = 1)
    (hsum : Summable (fun i => ∫ x, (h i x - 1) ^ 2 ∂μ i))
    (hC : (∑' i, ∫ x, (h i x - 1) ^ 2 ∂μ i) ≤ C) :
    eLpNorm (fun x => ∏ i ∈ s, h i (x i)) 2 (Measure.infinitePi μ) ≤
      ENNReal.ofReal (Real.exp (C / 2)) := by
  apply eLpNorm_partial_product_le_exp_half s hh hmean
  exact (hsum.sum_le_tsum s fun i _ => integral_nonneg fun x => sq_nonneg _).trans hC

theorem integral_partial_product
    {ι : Type*} {Ω : ι → Type*} [∀ i, MeasurableSpace (Ω i)]
    {μ : (i : ι) → Measure (Ω i)} [∀ i, IsProbabilityMeasure (μ i)]
    {h : (i : ι) → Ω i → ℝ} (s : Finset ι)
    (hh : ∀ i, Integrable (h i) (μ i)) :
    (∫ x, ∏ i ∈ s, h i (x i) ∂Measure.infinitePi μ) =
      ∏ i ∈ s, ∫ x, h i x ∂μ i := by
  rw [partial_product_eq_restrict h s]
  change (∫ x, (fun y : (i : s) → Ω i => ∏ i : s, h i (y i)) (s.restrict x)
    ∂Measure.infinitePi μ) = _
  rw [integral_restrict_infinitePi (μ := μ) (s := s)
    (f := fun y : (i : s) → Ω i => ∏ i : s, h i (y i))
    (Integrable.fintype_prod_dep (fun i : s => hh i)).aestronglyMeasurable]
  rw [integral_fintype_prod_eq_prod]
  exact Finset.prod_coe_sort s (fun i => ∫ x, h i x ∂μ i)

theorem partial_product_mul_of_subset
    {ι : Type*} [DecidableEq ι] {Ω : ι → Type*}
    (h : (i : ι) → Ω i → ℝ) {s t : Finset ι} (hst : s ⊆ t) (x : (i : ι) → Ω i) :
    (∏ i ∈ s, h i (x i)) * (∏ i ∈ t, h i (x i)) =
      ∏ i ∈ t, if i ∈ s then h i (x i) ^ 2 else h i (x i) := by
  have heq : (∏ i ∈ t, if i ∈ s then h i (x i) else 1) =
      ∏ i ∈ s, h i (x i) := by
    rw [Finset.prod_ite_mem, Finset.inter_eq_right.mpr hst]
  rw [← heq, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i hi
  split_ifs <;> ring

theorem integral_partial_product_mul_of_subset
    {ι : Type*} [DecidableEq ι] {Ω : ι → Type*} [∀ i, MeasurableSpace (Ω i)]
    {μ : (i : ι) → Measure (Ω i)} [∀ i, IsProbabilityMeasure (μ i)]
    {h : (i : ι) → Ω i → ℝ} {s t : Finset ι} (hst : s ⊆ t)
    (hh : ∀ i, MemLp (h i) 2 (μ i))
    (hmean : ∀ i, ∫ x, h i x ∂μ i = 1) :
    (∫ x, (∏ i ∈ s, h i (x i)) * (∏ i ∈ t, h i (x i)) ∂Measure.infinitePi μ) =
      ∫ x, (∏ i ∈ s, h i (x i)) ^ 2 ∂Measure.infinitePi μ := by
  have hmixed : ∀ i, Integrable (fun x => if i ∈ s then h i x ^ 2 else h i x) (μ i) := by
    intro i
    by_cases hi : i ∈ s
    · simpa only [ite_eq_left hi] using (hh i).integrable_sq
    · simpa only [ite_eq_right hi] using (hh i).integrable (by norm_num)
  have hleft : (∫ x, (∏ i ∈ s, h i (x i)) * (∏ i ∈ t, h i (x i)) ∂Measure.infinitePi μ) =
      ∏ i ∈ s, ∫ x, h i x ^ 2 ∂μ i := by
    simp_rw [partial_product_mul_of_subset h hst]
    rw [integral_partial_product t hmixed]
    calc
      _ = ∏ i ∈ t, if i ∈ s then ∫ x, h i x ^ 2 ∂μ i else 1 := by
        apply Finset.prod_congr rfl
        intro i hi
        by_cases his : i ∈ s
        · simp only [ite_eq_left his]
        · simp only [ite_eq_right his, hmean]
      _ = _ := by rw [Finset.prod_ite_mem, Finset.inter_eq_right.mpr hst]
  rw [hleft]
  symm
  calc
    _ = ∫ x, ∏ i ∈ s, h i (x i) ^ 2 ∂Measure.infinitePi μ := by
      congr 1
      funext x
      exact (Finset.prod_pow _ _ _).symm
    _ = _ := integral_partial_product s (fun i => (hh i).integrable_sq)

theorem indicator_partial_product
    {ι : Type*} [DecidableEq ι] {Ω : ι → Type*}
    (h : (i : ι) → Ω i → ℝ) {s t : Finset ι} (hst : s ⊆ t)
    (a : (i : ι) → Set (Ω i)) (x : (i : ι) → Ω i) :
    (Set.pi (s : Set ι) a).indicator (fun y => ∏ i ∈ t, h i (y i)) x =
      ∏ i ∈ t, if i ∈ s then (a i).indicator (h i) (x i) else h i (x i) := by
  classical
  by_cases hx : x ∈ Set.pi (s : Set ι) a
  · rw [Set.indicator_of_mem hx]
    apply Finset.prod_congr rfl
    intro i hi
    by_cases his : i ∈ s
    · rw [ite_eq_left his, Set.indicator_of_mem ((Set.mem_pi.mp hx) i his)]
    · rw [ite_eq_right his]
  · rw [Set.indicator_of_notMem hx]
    symm
    have hex : ∃ i ∈ s, x i ∉ a i := by
      by_contra hnone
      apply hx
      apply Set.mem_pi.mpr
      intro i hi
      by_contra hix
      exact hnone ⟨i, hi, hix⟩
    obtain ⟨i, his, hix⟩ := hex
    apply Finset.prod_eq_zero (hst his)
    rw [ite_eq_left his, Set.indicator_of_notMem hix]

theorem setIntegral_partial_product_pi
    {ι : Type*} [DecidableEq ι] {Ω : ι → Type*} [∀ i, MeasurableSpace (Ω i)]
    {μ : (i : ι) → Measure (Ω i)} [∀ i, IsProbabilityMeasure (μ i)]
    {h : (i : ι) → Ω i → ℝ} {s t : Finset ι} (hst : s ⊆ t)
    (hh : ∀ i, Integrable (h i) (μ i))
    (hmean : ∀ i, ∫ x, h i x ∂μ i = 1)
    (a : (i : ι) → Set (Ω i)) (ha : ∀ i, MeasurableSet (a i)) :
    (∫ x in Set.pi (s : Set ι) a, ∏ i ∈ t, h i (x i) ∂Measure.infinitePi μ) =
      ∏ i ∈ s, ∫ x in a i, h i x ∂μ i := by
  classical
  have hmeas : MeasurableSet (Set.pi (s : Set ι) a) :=
    MeasurableSet.pi s.countable_toSet (fun i _ => ha i)
  rw [← integral_indicator hmeas]
  simp_rw [indicator_partial_product h hst a]
  have hmixed : ∀ i, Integrable (fun x => if i ∈ s then (a i).indicator (h i) x else h i x) (μ i) := by
    intro i
    by_cases his : i ∈ s
    · simpa only [ite_eq_left his] using (hh i).indicator (ha i)
    · simpa only [ite_eq_right his] using hh i
  rw [integral_partial_product t hmixed]
  calc
    _ = ∏ i ∈ t, if i ∈ s then ∫ x in a i, h i x ∂μ i else 1 := by
      apply Finset.prod_congr rfl
      intro i hi
      by_cases his : i ∈ s
      · simp only [ite_eq_left his, integral_indicator (ha i)]
      · simp only [ite_eq_right his, hmean]
    _ = _ := by rw [Finset.prod_ite_mem, Finset.inter_eq_right.mpr hst]

end Invariant233.ProductDensity

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Sampling_OrthogonalPrefixLimit
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Filter
open scoped Topology

namespace Invariant233.ProductDensity

theorem cauchySeq_of_prefix_inner
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (f : ℕ → E)
    (hinner : ∀ n m, n ≤ m → inner ℝ (f n) (f m) = ‖f n‖ ^ 2)
    (hbound : BddAbove (Set.range fun n => ‖f n‖ ^ 2)) : CauchySeq f := by
  have hdist : ∀ n m, n ≤ m → dist (f n) (f m) ^ 2 = ‖f m‖ ^ 2 - ‖f n‖ ^ 2 := by
    intro n m hnm
    rw [dist_eq_norm, norm_sub_sq_real, hinner n m hnm]
    ring
  have hmono : Monotone (fun n => ‖f n‖ ^ 2) := by
    intro n m hnm
    have := sq_nonneg (dist (f n) (f m))
    rw [hdist n m hnm] at this
    linarith
  have hc : CauchySeq (fun n => ‖f n‖ ^ 2) :=
    (tendsto_atTop_ciSup hmono hbound).cauchySeq
  apply Metric.cauchySeq_iff.2
  intro ε hε
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.1 hc (ε ^ 2) (sq_pos_of_pos hε)
  refine ⟨N, fun n hn m hm => ?_⟩
  have hreal := hN n hn m hm
  rw [Real.dist_eq] at hreal
  rcases le_total n m with hnm | hmn
  · have hs := hdist n m hnm
    have hl := (abs_lt.mp hreal).1
    nlinarith [dist_nonneg (x := f n) (y := f m)]
  · have hs := hdist m n hmn
    have hl := (abs_lt.mp hreal).2
    rw [dist_comm (f m) (f n)] at hs
    nlinarith [dist_nonneg (x := f n) (y := f m)]

theorem exists_limit_of_prefix_inner
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (f : ℕ → E)
    (hinner : ∀ n m, n ≤ m → inner ℝ (f n) (f m) = ‖f n‖ ^ 2)
    (hbound : BddAbove (Set.range fun n => ‖f n‖ ^ 2)) :
    ∃ g : E, Tendsto f atTop (𝓝 g) :=
  cauchySeq_tendsto_of_complete (cauchySeq_of_prefix_inner f hinner hbound)

end Invariant233.ProductDensity

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Couplings_ProductDensityLimit
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Filter
open scoped BigOperators ENNReal Topology

namespace Invariant233.ProductDensity

theorem inner_toLp_eq_integral_mul
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {f g : Ω → ℝ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    inner ℝ (hf.toLp f) (hg.toLp g) = ∫ x, f x * g x ∂μ := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x hfx hgx
  simp [hfx, hgx, mul_comm]

theorem partialDensityLp_inner
    {Ω : ℕ → Type*} [∀ i, MeasurableSpace (Ω i)]
    {μ : (i : ℕ) → Measure (Ω i)} [∀ i, IsProbabilityMeasure (μ i)]
    {h : (i : ℕ) → Ω i → ℝ} (hh : ∀ i, MemLp (h i) 2 (μ i))
    (hmean : ∀ i, ∫ x, h i x ∂μ i = 1) {n m : ℕ} (hnm : n ≤ m) :
    inner ℝ (partialDensityLp hh n) (partialDensityLp hh m) =
      ‖partialDensityLp hh n‖ ^ 2 := by
  calc
    _ = ∫ x, (∏ i ∈ Finset.range n, h i (x i)) *
        (∏ i ∈ Finset.range m, h i (x i)) ∂Measure.infinitePi μ :=
      inner_toLp_eq_integral_mul _ _
    _ = ∫ x, (∏ i ∈ Finset.range n, h i (x i)) ^ 2 ∂Measure.infinitePi μ :=
      integral_partial_product_mul_of_subset (Finset.range_mono hnm) hh hmean
    _ = inner ℝ (partialDensityLp hh n) (partialDensityLp hh n) := by
      rw [partialDensityLp, inner_toLp_eq_integral_mul]
      congr 1
      funext x
      ring
    _ = _ := real_inner_self_eq_norm_sq _

theorem exists_partialDensityLp_limit
    {Ω : ℕ → Type*} [∀ i, MeasurableSpace (Ω i)]
    {μ : (i : ℕ) → Measure (Ω i)} [∀ i, IsProbabilityMeasure (μ i)]
    {h : (i : ℕ) → Ω i → ℝ} {C : ℝ}
    (hh : ∀ i, MemLp (h i) 2 (μ i))
    (hmean : ∀ i, ∫ x, h i x ∂μ i = 1)
    (hsum : Summable (fun i => ∫ x, (h i x - 1) ^ 2 ∂μ i))
    (hC : (∑' i, ∫ x, (h i x - 1) ^ 2 ∂μ i) ≤ C) :
    ∃ g : Lp ℝ 2 (Measure.infinitePi μ),
      Tendsto (partialDensityLp hh) atTop (𝓝 g) ∧ ‖g‖ ≤ Real.exp (C / 2) := by
  have hb : ∀ n, ‖partialDensityLp hh n‖ ≤ Real.exp (C / 2) := by
    intro n
    rw [partialDensityLp, Lp.norm_toLp]
    have hnorm := eLpNorm_partial_product_le_exp_half_of_tsum_le
      (Finset.range n) hh hmean hsum hC
    have := ENNReal.toReal_mono (ENNReal.ofReal_ne_top) hnorm
    simpa only [ENNReal.toReal_ofReal (Real.exp_pos _).le] using this
  obtain ⟨g, hg⟩ := exists_limit_of_prefix_inner (partialDensityLp hh)
    (fun n m hnm => partialDensityLp_inner hh hmean hnm)
    ⟨(Real.exp (C / 2)) ^ 2, by
      rintro _ ⟨n, rfl⟩
      exact pow_le_pow_left₀ (norm_nonneg _) (hb n) 2⟩
  exact ⟨g, hg, le_of_tendsto hg.norm (Filter.Eventually.of_forall hb)⟩

theorem tendsto_eLpNorm_one_partialDensity_sub
    {Ω : ℕ → Type*} [∀ i, MeasurableSpace (Ω i)]
    {μ : (i : ℕ) → Measure (Ω i)} [∀ i, IsProbabilityMeasure (μ i)]
    {h : (i : ℕ) → Ω i → ℝ} (hh : ∀ i, MemLp (h i) 2 (μ i))
    {g : Lp ℝ 2 (Measure.infinitePi μ)}
    (hg : Tendsto (partialDensityLp hh) atTop (𝓝 g)) :
    Tendsto (fun n => eLpNorm
      ((fun x => ∏ i ∈ Finset.range n, h i (x i)) - (g : ((i : ℕ) → Ω i) → ℝ))
      1 (Measure.infinitePi μ)) atTop (𝓝 0) := by
  have h2 : Tendsto (fun n => eLpNorm
      ((fun x => ∏ i ∈ Finset.range n, h i (x i)) - (g : ((i : ℕ) → Ω i) → ℝ))
      2 (Measure.infinitePi μ)) atTop (𝓝 0) := by
    have ht := hg.edist (tendsto_const_nhds (x := g))
    simp only [edist_self] at ht
    apply ht.congr
    intro n
    rw [Lp.edist_def]
    apply eLpNorm_congr_ae
    exact (memLp_partial_product (Finset.range n) hh).coeFn_toLp.sub Filter.EventuallyEq.rfl
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h2
    (fun _ => bot_le)
  intro n
  exact eLpNorm_le_eLpNorm_of_exponent_le (hf := by first | exact (memLp_partial_product (Finset.range n) hh).aestronglyMeasurable.sub (Lp.aestronglyMeasurable g) | fun_prop | assumption | solve_by_elim | exact Lp.aestronglyMeasurable _ | (apply Measurable.aestronglyMeasurable; solve_by_elim) | (apply Continuous.aestronglyMeasurable; solve_by_elim) | (apply Measurable.aestronglyMeasurable; measurability) | measurability) (by norm_num)

theorem partialDensityLp_limit_nonneg
    {Ω : ℕ → Type*} [∀ i, MeasurableSpace (Ω i)]
    {μ : (i : ℕ) → Measure (Ω i)} [∀ i, IsProbabilityMeasure (μ i)]
    {h : (i : ℕ) → Ω i → ℝ} (hh : ∀ i, MemLp (h i) 2 (μ i))
    (hnonneg : ∀ i x, 0 ≤ h i x)
    {g : Lp ℝ 2 (Measure.infinitePi μ)}
    (hg : Tendsto (partialDensityLp hh) atTop (𝓝 g)) :
    0 ≤ᵐ[Measure.infinitePi μ] (g : ((i : ℕ) → Ω i) → ℝ) := by
  apply ae_nonneg_of_forall_setIntegral_nonneg ((Lp.memLp g).integrable (by norm_num))
  intro s hs hsf
  have hi := tendsto_setIntegral_of_L1' (g : ((i : ℕ) → Ω i) → ℝ) (Lp.aestronglyMeasurable g)
    (Filter.Eventually.of_forall fun n =>
      (memLp_partial_product (Finset.range n) hh).integrable (by norm_num))
    (tendsto_eLpNorm_one_partialDensity_sub hh hg) s
  exact ge_of_tendsto hi (Filter.Eventually.of_forall fun n =>
    integral_nonneg fun x => Finset.prod_nonneg fun i _ => hnonneg i (x i))

theorem partialDensityLp_limit_integral
    {Ω : ℕ → Type*} [∀ i, MeasurableSpace (Ω i)]
    {μ : (i : ℕ) → Measure (Ω i)} [∀ i, IsProbabilityMeasure (μ i)]
    {h : (i : ℕ) → Ω i → ℝ} (hh : ∀ i, MemLp (h i) 2 (μ i))
    (hmean : ∀ i, ∫ x, h i x ∂μ i = 1)
    {g : Lp ℝ 2 (Measure.infinitePi μ)}
    (hg : Tendsto (partialDensityLp hh) atTop (𝓝 g)) :
    (∫ x, g x ∂Measure.infinitePi μ) = 1 := by
  have hi := tendsto_integral_of_L1' (hfi := by first | fun_prop | assumption | solve_by_elim | exact Lp.aestronglyMeasurable _ | (apply Measurable.aestronglyMeasurable; solve_by_elim) | (apply Continuous.aestronglyMeasurable; solve_by_elim) | (apply Measurable.aestronglyMeasurable; measurability) | measurability) (g : ((i : ℕ) → Ω i) → ℝ)
    (Filter.Eventually.of_forall fun n =>
      (memLp_partial_product (Finset.range n) hh).integrable (by norm_num))
    (tendsto_eLpNorm_one_partialDensity_sub hh hg)
  have heq : ∀ n, (∫ x, ∏ i ∈ Finset.range n, h i (x i) ∂Measure.infinitePi μ) = 1 := by
    intro n
    rw [integral_partial_product (Finset.range n) (fun i => (hh i).integrable (by norm_num))]
    simp [hmean]
  simp_rw [heq] at hi
  exact tendsto_nhds_unique hi tendsto_const_nhds

theorem partialDensityLp_limit_setIntegral_pi
    {Ω : ℕ → Type*} [∀ i, MeasurableSpace (Ω i)]
    {μ : (i : ℕ) → Measure (Ω i)} [∀ i, IsProbabilityMeasure (μ i)]
    {h : (i : ℕ) → Ω i → ℝ} (hh : ∀ i, MemLp (h i) 2 (μ i))
    (hmean : ∀ i, ∫ x, h i x ∂μ i = 1)
    {g : Lp ℝ 2 (Measure.infinitePi μ)}
    (hg : Tendsto (partialDensityLp hh) atTop (𝓝 g))
    (s : Finset ℕ) (a : (i : ℕ) → Set (Ω i)) (ha : ∀ i, MeasurableSet (a i)) :
    (∫ x in Set.pi (s : Set ℕ) a, g x ∂Measure.infinitePi μ) =
      ∏ i ∈ s, ∫ x in a i, h i x ∂μ i := by
  have hi := tendsto_setIntegral_of_L1' (g : ((i : ℕ) → Ω i) → ℝ) (Lp.aestronglyMeasurable g)
    (Filter.Eventually.of_forall fun n =>
      (memLp_partial_product (Finset.range n) hh).integrable (by norm_num))
    (tendsto_eLpNorm_one_partialDensity_sub hh hg) (Set.pi (s : Set ℕ) a)
  obtain ⟨N, hN⟩ := Finset.exists_nat_subset_range s
  have heq : (fun n => ∫ x in Set.pi (s : Set ℕ) a,
      ∏ i ∈ Finset.range n, h i (x i) ∂Measure.infinitePi μ) =ᶠ[atTop]
      (fun _ => ∏ i ∈ s, ∫ x in a i, h i x ∂μ i) := by
    apply Filter.eventually_atTop.2
    refine ⟨N, fun n hn => ?_⟩
    exact setIntegral_partial_product_pi (hN.trans (Finset.range_mono hn))
      (fun i => (hh i).integrable (by norm_num)) hmean a ha
  exact tendsto_nhds_unique hi (tendsto_const_nhds.congr' heq.symm)

theorem isProbabilityMeasure_withDensity_ofReal
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {h : Ω → ℝ} (hh : Integrable h μ) (hnonneg : 0 ≤ᵐ[μ] h)
    (hmean : ∫ x, h x ∂μ = 1) :
    IsProbabilityMeasure (μ.withDensity (fun x => ENNReal.ofReal (h x))) := by
  constructor
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal hh hnonneg, hmean]
  simp

theorem partialDensityLp_limit_withDensity
    {Ω : ℕ → Type*} [∀ i, MeasurableSpace (Ω i)]
    {μ : (i : ℕ) → Measure (Ω i)} [∀ i, IsProbabilityMeasure (μ i)]
    {h : (i : ℕ) → Ω i → ℝ} (hh : ∀ i, MemLp (h i) 2 (μ i))
    (hnonneg : ∀ i x, 0 ≤ h i x)
    (hmean : ∀ i, ∫ x, h i x ∂μ i = 1)
    {g : Lp ℝ 2 (Measure.infinitePi μ)}
    (hg : Tendsto (partialDensityLp hh) atTop (𝓝 g)) :
    (Measure.infinitePi μ).withDensity (fun x => ENNReal.ofReal (g x)) =
      Measure.infinitePi (fun i => (μ i).withDensity (fun x => ENNReal.ofReal (h i x))) := by
  let : ∀ i, IsProbabilityMeasure ((μ i).withDensity (fun x => ENNReal.ofReal (h i x))) :=
    fun i => isProbabilityMeasure_withDensity_ofReal ((hh i).integrable (by norm_num))
      (Filter.Eventually.of_forall (hnonneg i)) (hmean i)
  have hgnonneg := partialDensityLp_limit_nonneg hh hnonneg hg
  have hgi := (Lp.memLp g).integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  apply Measure.eq_infinitePi
  intro s a ha
  have hmeas : MeasurableSet (Set.pi (s : Set ℕ) a) :=
    MeasurableSet.pi s.countable_toSet (fun i _ => ha i)
  rw [withDensity_apply _ hmeas,
    ← ofReal_integral_eq_lintegral_ofReal hgi.restrict (ae_restrict_of_ae hgnonneg),
    partialDensityLp_limit_setIntegral_pi hh hmean hg s a ha]
  rw [ENNReal.ofReal_prod_of_nonneg (fun i _ => integral_nonneg (hnonneg i))]
  apply Finset.prod_congr rfl
  intro i hi
  rw [withDensity_apply _ (ha i)]
  exact ofReal_integral_eq_lintegral_ofReal ((hh i).integrable (by norm_num)).restrict
    (Filter.Eventually.of_forall (hnonneg i))

theorem exists_product_density
    {Ω : ℕ → Type*} [∀ i, MeasurableSpace (Ω i)]
    {μ : (i : ℕ) → Measure (Ω i)} [∀ i, IsProbabilityMeasure (μ i)]
    {h : (i : ℕ) → Ω i → ℝ} {C : ℝ}
    (hh : ∀ i, MemLp (h i) 2 (μ i))
    (hnonneg : ∀ i x, 0 ≤ h i x)
    (hmean : ∀ i, ∫ x, h i x ∂μ i = 1)
    (hsum : Summable (fun i => ∫ x, (h i x - 1) ^ 2 ∂μ i))
    (hC : (∑' i, ∫ x, (h i x - 1) ^ 2 ∂μ i) ≤ C) :
    ∃ H : ((i : ℕ) → Ω i) → ℝ,
      MemLp H 2 (Measure.infinitePi μ) ∧
      (0 ≤ᵐ[Measure.infinitePi μ] H) ∧
      (∫ x, H x ∂Measure.infinitePi μ) = 1 ∧
      eLpNorm H 2 (Measure.infinitePi μ) ≤ ENNReal.ofReal (Real.exp (C / 2)) ∧
      (Measure.infinitePi μ).withDensity (fun x => ENNReal.ofReal (H x)) =
        Measure.infinitePi (fun i => (μ i).withDensity (fun x => ENNReal.ofReal (h i x))) := by
  obtain ⟨g, hg, hgbound⟩ := exists_partialDensityLp_limit hh hmean hsum hC
  refine ⟨g, Lp.memLp g, partialDensityLp_limit_nonneg hh hnonneg hg,
    partialDensityLp_limit_integral hh hmean hg, ?_,
    partialDensityLp_limit_withDensity hh hnonneg hmean hg⟩
  rw [← Lp.enorm_def, ← ofReal_norm]
  exact ENNReal.ofReal_le_ofReal hgbound

theorem exists_hybrid_product_density
    {Ω : ℕ → Type*} [∀ i, MeasurableSpace (Ω i)]
    {μ : (i : ℕ) → Measure (Ω i)} [∀ i, IsProbabilityMeasure (μ i)]
    {h : Bool → (i : ℕ) → Ω i → ℝ} {b : ℕ → ℝ} {C : ℝ}
    (ε : ℕ → Bool)
    (hh : ∀ a i, MemLp (h a i) 2 (μ i))
    (hnonneg : ∀ a i x, 0 ≤ h a i x)
    (hmean : ∀ a i, ∫ x, h a i x ∂μ i = 1)
    (hb : ∀ a i, (∫ x, (h a i x - 1) ^ 2 ∂μ i) ≤ b i)
    (hsum : Summable b) (hC : (∑' i, b i) ≤ C) :
    ∃ H : ((i : ℕ) → Ω i) → ℝ,
      MemLp H 2 (Measure.infinitePi μ) ∧
      (0 ≤ᵐ[Measure.infinitePi μ] H) ∧
      (∫ x, H x ∂Measure.infinitePi μ) = 1 ∧
      eLpNorm H 2 (Measure.infinitePi μ) ≤ ENNReal.ofReal (Real.exp (C / 2)) ∧
      (Measure.infinitePi μ).withDensity (fun x => ENNReal.ofReal (H x)) =
        Measure.infinitePi (fun i => (μ i).withDensity (fun x => ENNReal.ofReal (h (ε i) i x))) := by
  have hsel : Summable (fun i => ∫ x, (h (ε i) i x - 1) ^ 2 ∂μ i) :=
    Summable.of_nonneg_of_le (fun i => integral_nonneg fun x => sq_nonneg _)
      (fun i => hb (ε i) i) hsum
  exact exists_product_density (fun i => hh (ε i) i)
    (fun i => hnonneg (ε i) i) (fun i => hmean (ε i) i) hsel
    ((hsel.tsum_le_tsum (fun i => hb (ε i) i) hsum).trans hC)

end Invariant233.ProductDensity

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Couplings_ProductCoupling
attribute [-instance] _root_.OAI.Invariant233.OrderedProductCoupling.circlePairLaw_probability _root_.OAI.Invariant233.OrderedProductCoupling.leftTailLaw_isProbabilityMeasure _root_.OAI.Invariant233.OrderedProductCoupling.sourcePairLaw_isProbabilityMeasure _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.BlockedProductCoupling.circleLeftEndpoint_unflatten _root_.OAI.Invariant233.BlockedProductCoupling.circleRightEndpoint_unflatten _root_.OAI.Invariant233.BlockedProductCoupling.flatten_unflatten _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal

namespace Invariant233.OrderedProductCoupling

open OneCoordinateCoupling

lemma hybridEndpoint_measurable (ε : ℕ → Bool) : Measurable (hybridEndpoint ε) := by
  apply Measurable.of_eval
  intro i
  unfold hybridEndpoint rightEndpoint leftEndpoint
  split_ifs <;> fun_prop

lemma coordinateLaw_map_pair (P : Parameters) (i : ℕ) :
    (coordinateLaw P i).map Prod.snd = pairLaw (P.κ i) (P.m i) (P.a i) (P.b i) (P.t i) :=
  labelledLaw_map_snd _ _ _ _ _

lemma coordinateLaw_map_left (P : Parameters) (i : ℕ) :
    (coordinateLaw P i).map (fun z => z.2.1) = baseLaw.withDensity
      (fun x => ENNReal.ofReal (marginalDensity P false i x)) := by
  have h := pairLaw_fst_density (P.κ_nonneg i) (P.κ_le i) (P.m_ge i)
    (P.a_lower i) (P.a_upper i) (P.b_lower i) (P.b_upper i) (P.t_nonneg i) (P.t_le i)
  rw [← coordinateLaw_map_pair P i, Measure.fst,
    Measure.map_map measurable_fst measurable_snd] at h
  exact h

lemma coordinateLaw_map_right (P : Parameters) (i : ℕ) :
    (coordinateLaw P i).map (fun z => z.2.2) = baseLaw.withDensity
      (fun x => ENNReal.ofReal (marginalDensity P true i x)) := by
  have h := pairLaw_snd_density (P.κ_nonneg i) (P.κ_le i) (P.m_ge i)
    (P.a_lower i) (P.a_upper i) (P.b_lower i) (P.b_upper i) (P.t_nonneg i) (P.t_le i)
  rw [← coordinateLaw_map_pair P i, Measure.snd,
    Measure.map_map measurable_snd measurable_snd] at h
  exact h

lemma hybridEndpoint_map (P : Parameters) (ε : ℕ → Bool) :
    (law P).map (hybridEndpoint ε) = Measure.infinitePi (fun i => baseLaw.withDensity
      (fun x => ENNReal.ofReal (marginalDensity P (ε i) i x))) := by
  let f : ℕ → CoordinateSample → ℝ :=
    fun i z => if ε i then z.2.2 else z.2.1
  have hf : ∀ i, Measurable (f i) := by
    intro i
    dsimp [f]
    split_ifs <;> fun_prop
  calc
    _ = Measure.infinitePi (fun i => (coordinateLaw P i).map (f i)) :=
      Measure.infinitePi_map_pi (coordinateLaw P) hf
    _ = _ := by
      congr 1
      funext i
      cases h : ε i
      · simpa only [f, h, Bool.false_eq_true, ite_false, if_false] using coordinateLaw_map_left P i
      · simpa only [f, h, ite_true, if_true] using coordinateLaw_map_right P i

lemma marginalDensity_memLp (P : Parameters) (side : Bool) (i : ℕ) :
    MemLp (marginalDensity P side i) 2 baseLaw := by
  cases side
  · exact leftMarginalDensity_memLp _ _ _ _ _
  · exact rightMarginalDensity_memLp _ _ _ _ _

lemma marginalDensity_nonneg (P : Parameters) (side : Bool) (i : ℕ) (x : ℝ) :
    0 ≤ marginalDensity P side i x := by
  cases side
  · exact le_trans (by norm_num) (leftMarginalDensity_bounds (P.κ_nonneg i) (P.κ_le i)
      (P.m_ge i) (P.a_lower i) (P.a_upper i) (P.b_lower i) (P.b_upper i)
      (P.t_nonneg i) (P.t_le i) x).1
  · exact le_trans (by norm_num) (rightMarginalDensity_bounds (P.κ_nonneg i) (P.κ_le i)
      (P.m_ge i) (P.a_lower i) (P.a_upper i) (P.b_lower i) (P.b_upper i)
      (P.t_nonneg i) (P.t_le i) x).1

lemma marginalDensity_integral (P : Parameters) (side : Bool) (i : ℕ) :
    (∫ x, marginalDensity P side i x ∂baseLaw) = 1 := by
  have hm0 : 0 < P.m i := by linarith [P.m_ge i]
  have ha0 := CouplingMarginalBounds.width_pos hm0 (P.a_lower i)
  have hb0 := CouplingMarginalBounds.width_pos hm0 (P.b_lower i)
  cases side
  · exact leftMarginalDensity_integral (by linarith [P.m_ge i]) ha0 (P.a_upper i) hb0 (P.b_upper i)
  · exact rightMarginalDensity_integral (by linarith [P.m_ge i]) ha0 (P.a_upper i) hb0 (P.b_upper i)

lemma marginalDensity_variance_le (P : Parameters) (side : Bool) (i : ℕ) :
    (∫ x, (marginalDensity P side i x - 1) ^ 2 ∂baseLaw) ≤ energyBound P i := by
  have hm0 : 0 < P.m i := by linarith [P.m_ge i]
  have ha0 := CouplingMarginalBounds.width_pos hm0 (P.a_lower i)
  have hb0 := CouplingMarginalBounds.width_pos hm0 (P.b_lower i)
  cases side
  · exact leftMarginalDensity_energy (by linarith [P.m_ge i]) ha0 (P.a_upper i) hb0 (P.b_upper i)
      (P.t_nonneg i) (P.t_le i)
  · exact rightMarginalDensity_energy (by linarith [P.m_ge i]) ha0 (P.a_upper i) hb0 (P.b_upper i)
      (P.t_nonneg i) (P.t_le i)

lemma exists_hybrid_density (P : Parameters) (ε : ℕ → Bool) {C : ℝ}
    (hsum : Summable (energyBound P)) (hC : (∑' i, energyBound P i) ≤ C) :
    ∃ H : Endpoint → ℝ, MemLp H 2 baseMeasure ∧ (0 ≤ᵐ[baseMeasure] H) ∧
      (∫ x, H x ∂baseMeasure) = 1 ∧
      eLpNorm H 2 baseMeasure ≤ ENNReal.ofReal (Real.exp (C / 2)) ∧
      (law P).map (hybridEndpoint ε) = baseMeasure.withDensity (fun x => ENNReal.ofReal (H x)) := by
  obtain ⟨H, hH, hnonneg, hmean, hnorm, hlaw⟩ :=
    ProductDensity.exists_hybrid_product_density ε
      (marginalDensity_memLp P) (marginalDensity_nonneg P) (marginalDensity_integral P)
      (marginalDensity_variance_le P) hsum hC
  exact ⟨H, hH, hnonneg, hmean, hnorm, (hybridEndpoint_map P ε).trans hlaw.symm⟩

end Invariant233.OrderedProductCoupling

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Couplings_BlockedCouplingEnergy
attribute [-instance] _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory
open scoped BigOperators

namespace Invariant233.BlockedProductCoupling

theorem sum_block_energy (m : ℕ) (hm : 0 < m) (κ t : ℝ) :
    (∑' _i : Fin m, 20 * (2 * κ ^ 2 / (m : ℝ) + t / (m : ℝ))) =
      20 * (2 * κ ^ 2 + t) := by
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  simp only [tsum_fintype, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  field_simp

theorem full_energy_sum (m : ℕ → ℕ) (hm : ∀ s, 0 < m s)
    (κ : ℕ → ℝ) (hκ : Summable (fun s => κ s ^ 2)) (j : ℕ) :
    Summable (fun p : Σ s, Fin (m s) =>
      20 * (2 * κ p.1 ^ 2 / (m p.1 : ℝ) +
        (if p.1 = j then 1 else 0) / (m p.1 : ℝ))) ∧
    (∑' p : Σ s, Fin (m s),
      20 * (2 * κ p.1 ^ 2 / (m p.1 : ℝ) +
        (if p.1 = j then 1 else 0) / (m p.1 : ℝ))) =
      20 * (2 * (∑' s, κ s ^ 2) + 1) := by
  classical
  have htag : Summable (fun s : ℕ => if s = j then (1 : ℝ) else 0) :=
    summable_of_ne_finset_zero (s := {j}) (by simp)
  have he (s : ℕ) :
      (∑' _i : Fin (m s), 20 * (2 * κ s ^ 2 / (m s : ℝ) +
        (if s = j then 1 else 0) / (m s : ℝ))) =
      20 * (2 * κ s ^ 2 + (if s = j then 1 else 0)) :=
    sum_block_energy _ (hm s) _ _
  have hblock : Summable (fun s => 20 * (2 * κ s ^ 2 +
      (if s = j then (1 : ℝ) else 0))) :=
    ((hκ.mul_left 2).add htag).mul_left 20
  have hs : Summable (fun p : Σ s, Fin (m s) =>
      20 * (2 * κ p.1 ^ 2 / (m p.1 : ℝ) +
        (if p.1 = j then 1 else 0) / (m p.1 : ℝ))) := by
    apply (summable_sigma_of_nonneg (fun p => by positivity)).2
    refine ⟨fun s => (hasSum_fintype _).summable, ?_⟩
    simpa only [he] using hblock
  refine ⟨hs, ?_⟩
  rw [hs.tsum_sigma' (fun s => (hasSum_fintype _).summable)]
  simp only [he]
  rw [tsum_mul_left, (hκ.mul_left 2).tsum_add htag, tsum_mul_left]
  simp

theorem enumerated_energy_sum (m : ℕ → ℕ) (hm : ∀ s, 0 < m s)
    (κ : ℕ → ℝ) (hκ : Summable (fun s => κ s ^ 2))
    (e : ℕ ≃ Σ s, Fin (m s)) (j : ℕ) :
    Summable (fun i : ℕ => 20 * (2 * κ (e i).1 ^ 2 / (m (e i).1 : ℝ) +
      (if (e i).1 = j then 1 else 0) / (m (e i).1 : ℝ))) ∧
    (∑' i : ℕ, 20 * (2 * κ (e i).1 ^ 2 / (m (e i).1 : ℝ) +
      (if (e i).1 = j then 1 else 0) / (m (e i).1 : ℝ))) =
      20 * (2 * (∑' s, κ s ^ 2) + 1) := by
  obtain ⟨hs, hv⟩ := full_energy_sum m hm κ hκ j
  exact ⟨e.summable_iff.mpr hs, (e.tsum_eq _).trans hv⟩

end Invariant233.BlockedProductCoupling

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Couplings_BlockedCouplingDensity
attribute [-instance] _root_.OAI.Invariant233.OrderedProductCoupling.circlePairLaw_probability _root_.OAI.Invariant233.OrderedProductCoupling.leftTailLaw_isProbabilityMeasure _root_.OAI.Invariant233.OrderedProductCoupling.sourcePairLaw_isProbabilityMeasure _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.BlockedProductCoupling.circleLeftEndpoint_unflatten _root_.OAI.Invariant233.BlockedProductCoupling.circleRightEndpoint_unflatten _root_.OAI.Invariant233.BlockedProductCoupling.flatten_unflatten _root_.OAI.Invariant233.BlockedProductCoupling.unflatten_flatten _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory
open scoped ENNReal

namespace Invariant233.BlockedProductCoupling

variable {m : ℕ → ℕ} {κ : ℕ → ℝ}
  {a b : (s : ℕ) → Fin (m s) → ℝ}
  (hm : ∀ s, 100 ≤ m s) (hκ0 : ∀ s, 0 ≤ κ s) (hκ : ∀ s, κ s ≤ 1 / 100)
  (ha : ∀ s i, 1 / (m s : ℝ) ≤ a s i) (ha' : ∀ s i, a s i ≤ 1 / 4)
  (hb : ∀ s i, 1 / (m s : ℝ) ≤ b s i) (hb' : ∀ s i, b s i ≤ 1 / 4)

include hm hκ0 hκ ha ha' hb hb'

theorem law_map_flatten (e : ℕ ≃ Σ s, Fin (m s)) (j : ℕ) :
    (law m κ a b j).map (flatten e) =
      OrderedProductCoupling.law (parameters hm hκ0 hκ ha ha' hb hb' e j) := by
  let P := parameters hm hκ0 hκ ha ha' hb hb' e j
  change (law m κ a b j).map
    ((fun z : (Σ s, Fin (m s)) → Coordinate => fun i => z (e i)) ∘
      (fun z p => z p.1 p.2)) = OrderedProductCoupling.law P
  rw [← Measure.map_map (by fun_prop) (by fun_prop),
    law_map_uncurry hm hκ0 hκ ha ha' hb hb']
  have h := Measure.infinitePi_map_piCongrLeft
    (OrderedProductCoupling.coordinateLaw P) e.symm
  simp only [OrderedProductCoupling.coordinateLaw, P, parameters,
    Equiv.apply_symm_apply] at h
  unfold OrderedProductCoupling.law
  convert h using 1 <;> first | (with_reducible_and_instances rfl) | (congr 1)
  · funext z i
    simp [MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft]
  · congr 1
    funext p
    rw [e.apply_symm_apply]

theorem exists_hybrid_density_of_blocks
    (hsq : Summable (fun s => κ s ^ 2))
    (e : ℕ ≃ Σ s, Fin (m s)) (j : ℕ) (sel : ℕ → Bool) :
    ∃ H : OrderedProductCoupling.Endpoint → ℝ,
      MemLp H 2 OrderedProductCoupling.baseMeasure ∧
      (0 ≤ᵐ[OrderedProductCoupling.baseMeasure] H) ∧
      (∫ x, H x ∂OrderedProductCoupling.baseMeasure) = 1 ∧
      eLpNorm H 2 OrderedProductCoupling.baseMeasure ≤
        ENNReal.ofReal (Real.exp (10 * (2 * (∑' s, κ s ^ 2) + 1))) ∧
      (law m κ a b j).map (OrderedProductCoupling.hybridEndpoint sel ∘ flatten e) =
        OrderedProductCoupling.baseMeasure.withDensity (fun x => ENNReal.ofReal (H x)) := by
  let P := parameters hm hκ0 hκ ha ha' hb hb' e j
  obtain ⟨hs, he⟩ := enumerated_energy_sum m (fun s => by have := hm s; omega) κ hsq e j
  have hs' : Summable (OrderedProductCoupling.energyBound P) := hs
  have he' : (∑' i, OrderedProductCoupling.energyBound P i) ≤
      20 * (2 * (∑' s, κ s ^ 2) + 1) := he.le
  obtain ⟨H, hH, hn, hmean, hnorm, hmap⟩ :=
    OrderedProductCoupling.exists_hybrid_density P sel hs' he'
  refine ⟨H, hH, hn, hmean, ?_, ?_⟩
  · convert hnorm using 1
    all_goals try with_reducible_and_instances rfl
    congr 2
    ring
  · rw [← Measure.map_map (OrderedProductCoupling.hybridEndpoint_measurable sel)
      (by unfold flatten; fun_prop), law_map_flatten hm hκ0 hκ ha ha' hb hb']
    exact hmap

theorem exists_left_density_of_blocks
    (hsq : Summable (fun s => κ s ^ 2))
    (e : ℕ ≃ Σ s, Fin (m s)) (j : ℕ) :
    ∃ H : OrderedProductCoupling.Endpoint → ℝ,
      MemLp H 2 OrderedProductCoupling.baseMeasure ∧
      (0 ≤ᵐ[OrderedProductCoupling.baseMeasure] H) ∧
      Real.sqrt (∫ x, H x ^ 2 ∂OrderedProductCoupling.baseMeasure) ≤
        Real.exp (10 * (2 * (∑' s, κ s ^ 2) + 1)) ∧
      (law m κ a b j).map (leftEndpoint e) =
        OrderedProductCoupling.baseMeasure.withDensity (fun x => ENNReal.ofReal (H x)) := by
  obtain ⟨H, hH, hn, _, hnorm, hmap⟩ :=
    exists_hybrid_density_of_blocks hm hκ0 hκ ha ha' hb hb' hsq e j (fun _ => false)
  refine ⟨H, hH, hn, ?_, ?_⟩
  · rw [EndpointLoss.sqrt_integral_sq_eq_toReal_eLpNorm hH]
    have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hnorm
    simpa only [ENNReal.toReal_ofReal (Real.exp_pos _).le] using h
  · have hf : OrderedProductCoupling.hybridEndpoint (fun _ => false) ∘ flatten e =
        leftEndpoint e := by
      funext z i
      rfl
    rw [hf] at hmap
    exact hmap

theorem exists_right_density_of_blocks
    (hsq : Summable (fun s => κ s ^ 2))
    (e : ℕ ≃ Σ s, Fin (m s)) (j : ℕ) :
    ∃ H : OrderedProductCoupling.Endpoint → ℝ,
      MemLp H 2 OrderedProductCoupling.baseMeasure ∧
      (0 ≤ᵐ[OrderedProductCoupling.baseMeasure] H) ∧
      Real.sqrt (∫ x, H x ^ 2 ∂OrderedProductCoupling.baseMeasure) ≤
        Real.exp (10 * (2 * (∑' s, κ s ^ 2) + 1)) ∧
      (law m κ a b j).map (rightEndpoint e) =
        OrderedProductCoupling.baseMeasure.withDensity (fun x => ENNReal.ofReal (H x)) := by
  obtain ⟨H, hH, hn, _, hnorm, hmap⟩ :=
    exists_hybrid_density_of_blocks hm hκ0 hκ ha ha' hb hb' hsq e j (fun _ => true)
  refine ⟨H, hH, hn, ?_, ?_⟩
  · rw [EndpointLoss.sqrt_integral_sq_eq_toReal_eLpNorm hH]
    have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hnorm
    simpa only [ENNReal.toReal_ofReal (Real.exp_pos _).le] using h
  · have hf : OrderedProductCoupling.hybridEndpoint (fun _ => true) ∘ flatten e =
        rightEndpoint e := by
      funext z i
      rfl
    rw [hf] at hmap
    exact hmap

end Invariant233.BlockedProductCoupling

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Analysis_BlockedPositiveEvent
attribute [-instance] _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.BlockedProductCoupling.unflatten_flatten _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Filter MeasureTheory Set
open scoped Topology

namespace Invariant233.BlockedProductCoupling

variable {m : ℕ → ℕ} {κ : ℕ → ℝ}
  {a b : (s : ℕ) → Fin (m s) → ℝ}
  (hm : ∀ s, 100 ≤ m s) (hκ0 : ∀ s, 0 ≤ κ s) (hκ : ∀ s, κ s ≤ 1 / 100)
  (ha : ∀ s i, 1 / (m s : ℝ) ≤ a s i) (ha' : ∀ s i, a s i ≤ 1 / 4)
  (hb : ∀ s i, 1 / (m s : ℝ) ≤ b s i) (hb' : ∀ s i, b s i ≤ 1 / 4)

include hm hκ0 hκ ha ha' hb hb'

theorem futureBad_mass_le_ratio {K : ℕ → ℝ} (hK : ∀ s, 0 < K s)
    (hd : ∀ s, 2 * K s ≤ K (s + 1)) (j : ℕ) :
    (law m κ a b j).real (futureBad m K j) ≤ 80 * (K j / K (j + 1)) := by
  have hs : Summable (fun n : ℕ => 1 / K (j + 1 + n)) := by
    simpa only [Function.comp_def, Nat.add_comm] using
      (ParameterTails.summable_reciprocal hK hd).comp_injective
        (show Function.Injective (fun n : ℕ => n + (j + 1)) from
          fun _ _ h => Nat.add_right_cancel h)
  calc
    _ ≤ 40 * K j * ∑' n : ℕ, 1 / K (j + 1 + n) :=
      futureBad_mass_le hm hκ0 hκ ha ha' hb hb' hK j hs
    _ ≤ 40 * K j * (2 / K (j + 1)) :=
      mul_le_mul_of_nonneg_left (ParameterTails.reciprocal_tail_bound hK hd j)
        (mul_nonneg (by norm_num) (hK j).le)
    _ = 80 * (K j / K (j + 1)) := by ring

theorem tendsto_futureBad_mass_zero {K : ℕ → ℝ} (hK : ∀ s, 0 < K s)
    (hd : ∀ s, 2 * K s ≤ K (s + 1))
    (hratio : Tendsto (fun j => K j / K (j + 1)) atTop (𝓝 0)) :
    Tendsto (fun j => (law m κ a b j).real (futureBad m K j)) atTop (𝓝 0) := by
  apply squeeze_zero (fun _ => measureReal_nonneg)
    (futureBad_mass_le_ratio hm hκ0 hκ ha ha' hb hb' hK hd)
  simpa using tendsto_const_nhds.mul hratio

theorem eventually_retainedEvent_mass
    {K : ℕ → ℝ} (hK : ∀ s, 0 < K s)
    (hd : ∀ s, 2 * K s ≤ K (s + 1))
    (hratio : Tendsto (fun j => K j / K (j + 1)) atTop (𝓝 0))
    {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]
    {r : X → ℝ} (hr : Measurable r) (hi : ∀ᵐ x ∂μ, 0 < r x ∧ r x < 1)
    (x y : Sample m → X) (hx : Measurable x) (hy : Measurable y)
    (h₁ h₂ : ℕ → X → ℝ)
    (hh₁ : ∀ j, MemLp (h₁ j) 2 μ) (hh₂ : ∀ j, MemLp (h₂ j) 2 μ)
    (hn₁ : ∀ j, 0 ≤ᵐ[μ] h₁ j) (hn₂ : ∀ j, 0 ≤ᵐ[μ] h₂ j)
    (H₁ H₂ : ℝ)
    (hH₁ : ∀ j, Real.sqrt (∫ z, h₁ j z ^ 2 ∂μ) ≤ H₁)
    (hH₂ : ∀ j, Real.sqrt (∫ z, h₂ j z ^ 2 ∂μ) ≤ H₂)
    (hmap₁ : ∀ j, (law m κ a b j).map x =
      μ.withDensity (fun z => ENNReal.ofReal (h₁ j z)))
    (hmap₂ : ∀ j, (law m κ a b j).map y =
      μ.withDensity (fun z => ENNReal.ofReal (h₂ j z))) :
    ∀ᶠ j in atTop, Real.exp (-82) / 2 ≤
      (law m κ a b j).real (retainedEvent m K r x y j) := by
  have := law_isProbabilityMeasure hm hκ0 hκ ha ha' hb hb'
  have hdiag := EndpointLoss.tendsto_endpoint_bad_union_zero μ hr hi
    (law m κ a b) (fun _ => x) (fun _ => y) (fun _ => hx) (fun _ => hy)
    h₁ h₂ hh₁ hh₂ hn₁ hn₂ H₁ H₂ hH₁ hH₂ hmap₁ hmap₂
  have hfuture := tendsto_futureBad_mass_zero hm hκ0 hκ ha ha' hb hb' hK hd hratio
  have hloss : Tendsto (fun j => (law m κ a b j).real
      (futureBad m K j ∪ ({z | r (x z) < 1 / (j : ℝ)} ∪
        {z | 1 - r (y z) < 1 / (j : ℝ)}))) atTop (𝓝 0) := by
    apply squeeze_zero (fun _ => measureReal_nonneg) (fun _ => measureReal_union_le _ _)
    simpa only [zero_add] using hfuture.add hdiag
  exact InvariantRotation.TaggedEventBounds.eventually_half_le_measureReal_sdiff
    (law m κ a b) (currentEvent m) _ (Real.exp_pos _)
    (Eventually.of_forall (currentEvent_mass hm hκ0 hκ ha ha' hb hb')) hloss

theorem eventually_actual_retainedEvent_mass
    (hsq : Summable (fun s => κ s ^ 2))
    (e : ℕ ≃ Σ s, Fin (m s))
    {K : ℕ → ℝ} (hK : ∀ s, 0 < K s)
    (hd : ∀ s, 2 * K s ≤ K (s + 1))
    (hratio : Tendsto (fun j => K j / K (j + 1)) atTop (𝓝 0))
    {r : OrderedProductCoupling.Endpoint → ℝ} (hr : Measurable r)
    (hi : ∀ᵐ x ∂OrderedProductCoupling.baseMeasure, 0 < r x ∧ r x < 1) :
    ∀ᶠ j in atTop, Real.exp (-82) / 2 ≤
      (law m κ a b j).real
        (retainedEvent m K r (leftEndpoint e) (rightEndpoint e) j) := by
  choose h₁ hh₁ hn₁ hH₁ hmap₁ using
    exists_left_density_of_blocks hm hκ0 hκ ha ha' hb hb' hsq e
  choose h₂ hh₂ hn₂ hH₂ hmap₂ using
    exists_right_density_of_blocks hm hκ0 hκ ha ha' hb hb' hsq e
  apply eventually_retainedEvent_mass hm hκ0 hκ ha ha' hb hb' hK hd hratio
    OrderedProductCoupling.baseMeasure hr hi (leftEndpoint e) (rightEndpoint e)
    (by unfold leftEndpoint flatten OrderedProductCoupling.leftEndpoint; fun_prop)
    (by unfold rightEndpoint flatten OrderedProductCoupling.rightEndpoint; fun_prop)
    h₁ h₂ hh₁ hh₂ hn₁ hn₂ _ _ hH₁ hH₂ hmap₁ hmap₂

end Invariant233.BlockedProductCoupling

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Sampling_SamplingHorizon
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Invariant233.SamplingHorizon

open Filter
open scoped Topology

theorem rpow_ratio_le_inv {x a b : ℝ} (hx : 1 ≤ x)
    (hgap : 1 ≤ (b - a) * x) :
    x ^ (a * x) / x ^ (b * x) ≤ x⁻¹ := by
  have hxpos : 0 < x := lt_of_lt_of_le zero_lt_one hx
  rw [← Real.rpow_sub hxpos, ← Real.rpow_neg_one]
  apply Real.rpow_le_rpow_of_exponent_le hx
  linarith

theorem horizon_ratio_le_inv {m K : ℝ} (hm : 20 ≤ m)
    (hK : m ^ ((3 / 4 : ℝ) * m) ≤ K) :
    m ^ ((7 / 10 : ℝ) * m) / K ≤ m⁻¹ := by
  have hmpos : 0 < m := by linarith
  have hpowpos : 0 < m ^ ((3 / 4 : ℝ) * m) := Real.rpow_pos_of_pos hmpos _
  calc
    m ^ ((7 / 10 : ℝ) * m) / K ≤
        m ^ ((7 / 10 : ℝ) * m) / m ^ ((3 / 4 : ℝ) * m) :=
      div_le_div_of_nonneg_left (Real.rpow_nonneg hmpos.le _) hpowpos hK
    _ ≤ m⁻¹ := rpow_ratio_le_inv (by linarith) (by linarith)

theorem tendsto_horizon_ratio {m K : ℕ → ℝ}
    (hm : Tendsto m atTop atTop)
    (hK : ∀ n, m n ^ ((3 / 4 : ℝ) * m n) ≤ K n) :
    Tendsto (fun n => m n ^ ((7 / 10 : ℝ) * m n) / K n) atTop (𝓝 0) := by
  have hlarge : ∀ᶠ n in atTop, 20 ≤ m n := hm.eventually_ge_atTop 20
  apply squeeze_zero' _ _ (tendsto_inv_atTop_zero.comp hm)
  · filter_upwards [hlarge] with n hn
    have hpos : 0 < m n := by linarith
    exact div_nonneg (Real.rpow_nonneg hpos.le _)
      (le_trans (Real.rpow_nonneg hpos.le _) (hK n))
  · filter_upwards [hlarge] with n hn
    exact horizon_ratio_le_inv hn (hK n)

theorem tendsto_horizon_ratio_of_pow_two_le {m K : ℕ → ℝ}
    (hm : ∀ n, (2 : ℝ) ^ n ≤ m n)
    (hK : ∀ n, m n ^ ((3 / 4 : ℝ) * m n) ≤ K (n + 1)) :
    Tendsto (fun n => m n ^ ((7 / 10 : ℝ) * m n) / K (n + 1))
      atTop (𝓝 0) := by
  apply tendsto_horizon_ratio _ hK
  exact tendsto_atTop_mono hm (tendsto_pow_atTop_atTop_of_one_lt (by norm_num))

end Invariant233.SamplingHorizon

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Product_ProductScaleConsequences
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Topology
open Filter
namespace Invariant233.ProductScaleLaws

variable {p : ProductScaleData} (hp : ProductScaleLaws p)
include hp

theorem real_K_pos (n : ℕ) : 0 < (p.K n : ℝ) := by exact_mod_cast hp.K_pos n

theorem real_K_double (n : ℕ) : 2 * (p.K n : ℝ) ≤ (p.K (n + 1) : ℝ) := by
  exact_mod_cast (hp.K_double n).le

theorem m_ge_pow_self (n : ℕ) : 2 ^ n ≤ p.m n := by
  have h := hp.m_ge_pow n
  have hpow : 2 ^ n ≤ 2 ^ (n + 1) := by
    rw [pow_succ]
    omega
  exact hpow.trans h

end Invariant233.ProductScaleLaws

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Rotation_BlockedCircleEvent
attribute [-instance] _root_.OAI.Invariant233.CircleParameterData.circleFiniteBase_probability _root_.OAI.Invariant233.OrderedProductCoupling.circlePairLaw_probability _root_.OAI.Invariant233.ProductModel.IdealSampling.law_finite _root_.OAI.Invariant233.ProductModel.IdealSampling.sourceMeasure_finite _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.ProductModel.prefixPairLaw_finite _root_.OAI.Invariant233.Rotation.circleMeasure_probability _root_.OAI.Invariant233.TrialSampling.spatialLaw_probability _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Filter MeasureTheory Set
open scoped Topology

namespace Invariant233.BlockedProductCoupling

theorem measurePreserving_toCircle : MeasurePreserving toCircle
    OrderedProductCoupling.baseMeasure ProductModel.baseMeasure := by
  have hc : MeasurePreserving (fun t : ℝ => (t : Circle))
      OneCoordinateCoupling.baseLaw circleMeasure := by
    rw [OneCoordinateCoupling.baseLaw_eq_restrict, circleMeasure,
      restrict_Ico_eq_restrict_Ioc]
    simpa only [zero_add] using AddCircle.measurePreserving_mk (1 : ℝ) 0
  refine ⟨by unfold toCircle; fun_prop, ?_⟩
  unfold OrderedProductCoupling.baseMeasure ProductModel.baseMeasure toCircle
  rw [Measure.infinitePi_map_pi _ (fun _ => hc.measurable)]
  simp only [hc.map_eq]

theorem eventually_circle_retainedEvent_mass
    {m : ℕ → ℕ} {κ : ℕ → ℝ} {a b : (s : ℕ) → Fin (m s) → ℝ}
    (hm : ∀ s, 100 ≤ m s) (hκ0 : ∀ s, 0 ≤ κ s) (hκ : ∀ s, κ s ≤ 1 / 100)
    (ha : ∀ s i, 1 / (m s : ℝ) ≤ a s i) (ha' : ∀ s i, a s i ≤ 1 / 4)
    (hb : ∀ s i, 1 / (m s : ℝ) ≤ b s i) (hb' : ∀ s i, b s i ≤ 1 / 4)
    (hsq : Summable (fun s => κ s ^ 2)) (e : ℕ ≃ Σ s, Fin (m s))
    {K : ℕ → ℝ} (hK : ∀ s, 0 < K s)
    (hd : ∀ s, 2 * K s ≤ K (s + 1))
    (hratio : Tendsto (fun j => K j / K (j + 1)) atTop (𝓝 0))
    {r : ProductModel.Base → ℝ} (hr : Measurable r)
    (hi : ∀ᵐ x ∂ProductModel.baseMeasure, 0 < r x ∧ r x < 1) :
    ∀ᶠ j in atTop, Real.exp (-82) / 2 ≤
      (law m κ a b j).real
        (retainedEvent m K r (circleLeftEndpoint e) (circleRightEndpoint e) j) := by
  have hir : ∀ᵐ x ∂OrderedProductCoupling.baseMeasure,
      0 < (r ∘ toCircle) x ∧ (r ∘ toCircle) x < 1 :=
    measurePreserving_toCircle.quasiMeasurePreserving.ae hi
  have h := eventually_actual_retainedEvent_mass
    (m := m) (κ := κ) (a := a) (b := b)
    hm hκ0 hκ ha ha' hb hb' hsq e hK hd hratio
    (r := r ∘ toCircle) (hr.comp measurePreserving_toCircle.measurable) hir
  simpa only [retainedEvent, circleLeftEndpoint, circleRightEndpoint,
    Function.comp_apply] using h

end Invariant233.BlockedProductCoupling

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Analysis_BlockedSourceEvent
attribute [-instance] _root_.OAI.Invariant233.CircleParameterData.circleFiniteBase_probability _root_.OAI.Invariant233.OrderedProductCoupling.circlePairLaw_probability _root_.OAI.Invariant233.ProductModel.IdealSampling.law_finite _root_.OAI.Invariant233.ProductModel.IdealSampling.sourceMeasure_finite _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.ProductModel.prefixPairLaw_finite _root_.OAI.Invariant233.Rotation.circleMeasure_probability _root_.OAI.Invariant233.TrialSampling.spatialLaw_probability _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped Topology

namespace Invariant233.BlockedProductCoupling

theorem mem_sourceRetainedEvent_iff {X : Type*} {m : ℕ → ℕ} {K : ℕ → ℝ}
    {r : X → ℝ} {x y : Sample m → X} {j : ℕ} {z : Sample m} :
    z ∈ sourceRetainedEvent m K r x y j ↔
      (∃ i, (z j i).1 = some (4 : Fin 5)) ∧
      (∀ i, (z j i).2.1 < 1 - 2 / (m j : ℝ) ∧
        2 / (m j : ℝ) < (z j i).2.2) ∧
      (∀ s, j < s → ∀ i : Fin (m s),
        (z s i).2.1 < 1 - 2 * K j / ((m s : ℝ) * K s) ∧
        2 * K j / ((m s : ℝ) * K s) < (z s i).2.2) ∧
      1 / ((j + 1 : ℕ) : ℝ) ≤ r (x z) ∧
      1 / ((j + 1 : ℕ) : ℝ) ≤ 1 - r (y z) := by
  simp only [sourceRetainedEvent, Set.mem_sdiff, mem_union, not_or,
    not_mem_futureBad_iff, currentEvent, mem_ofPred_eq, not_lt]
  tauto

theorem retainedEvent_subset_sourceRetainedEvent {X : Type*}
    (m : ℕ → ℕ) (K : ℕ → ℝ) (r : X → ℝ) (x y : Sample m → X)
    (j : ℕ) (hj : 1 ≤ j) :
    retainedEvent m K r x y j ⊆ sourceRetainedEvent m K r x y j := by
  intro z hz
  obtain ⟨htag, hcur, hfuture, hx, hy⟩ := mem_retainedEvent_iff.mp hz
  have hdiv : 1 / ((j + 1 : ℕ) : ℝ) ≤ 1 / (j : ℝ) :=
    one_div_le_one_div_of_le (by exact_mod_cast (by omega : 0 < j))
      (by exact_mod_cast Nat.le_succ j)
  exact mem_sourceRetainedEvent_iff.mpr ⟨htag, hcur, hfuture, hdiv.trans hx, hdiv.trans hy⟩

theorem source_kappa_nonneg (j : ℕ) : 0 ≤ ProductScaleData.kappa j := by
  unfold ProductScaleData.kappa
  positivity

theorem source_kappa_le (j : ℕ) : ProductScaleData.kappa j ≤ 1 / 100 := by
  apply one_div_le_one_div_of_le (by norm_num)
  have hj : (1 : ℝ) ≤ ((j + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos j
  linarith

theorem source_kappa_sq_summable : Summable (fun j => ProductScaleData.kappa j ^ 2) := by
  have hs : Summable (fun j : ℕ => 1 / (j : ℝ) ^ 2) :=
    Real.summable_one_div_nat_pow.mpr (by norm_num)
  have ht := (summable_nat_add_iff 1).mpr hs
  apply (ht.mul_left (1 / (100 : ℝ) ^ 2)).congr
  intro j
  dsimp [ProductScaleData.kappa]
  ring

theorem sourceLaw_isProbabilityMeasure {p : ProductScaleData}
    (hp : ProductScaleLaws p) (j : ℕ) : IsProbabilityMeasure (sourceLaw p j) :=
  law_isProbabilityMeasure hp.m_ge_100 source_kappa_nonneg source_kappa_le
    (fun s _ => (hp.a_bounds s).1) (fun s _ => (hp.a_bounds s).2)
    (fun s _ => (hp.b_bounds s).1) (fun s _ => (hp.b_bounds s).2) j

theorem source_cutoff_ratio_tendsto {p : ProductScaleData} (hp : ProductScaleLaws p) :
    Tendsto (fun j => (p.K j : ℝ) / p.K (j + 1)) atTop (𝓝 0) := by
  have hH := SamplingHorizon.tendsto_horizon_ratio_of_pow_two_le
    (m := fun j => (p.m j : ℝ)) (K := fun j => (p.K j : ℝ))
    (fun j => by exact_mod_cast hp.m_ge_pow_self j)
    (fun j => by rw [hp.next_K j]; exact Nat.le_ceil _)
  apply squeeze_zero (fun j => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) _ hH
  intro j
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  calc
    (p.K j : ℝ) ≤ p.m j := by exact_mod_cast hp.m_ge_K j
    _ ≤ (p.m j : ℝ) ^ ((7 / 10 : ℝ) * p.m j) := by
      have hm : (100 : ℝ) ≤ p.m j := by exact_mod_cast hp.m_ge_100 j
      simpa only [Real.rpow_one] using
        Real.rpow_le_rpow_of_exponent_le (by linarith : (1 : ℝ) ≤ p.m j)
          (by linarith : (1 : ℝ) ≤ (7 / 10 : ℝ) * p.m j)

theorem eventually_sourceEvent_mass {p : ProductScaleData} (hp : ProductScaleLaws p)
    (e : ℕ ≃ Σ s, Fin (p.m s)) {r : ProductModel.Base → ℝ}
    (hr : Measurable r) (hi : ∀ᵐ x ∂ProductModel.baseMeasure, 0 < r x ∧ r x < 1) :
    ∀ᶠ j in atTop, Real.exp (-82) / 2 ≤ (sourceLaw p j).real (sourceEvent p e r j) := by
  have h := eventually_circle_retainedEvent_mass hp.m_ge_100
    source_kappa_nonneg source_kappa_le
    (fun s _ => (hp.a_bounds s).1) (fun s _ => (hp.a_bounds s).2)
    (fun s _ => (hp.b_bounds s).1) (fun s _ => (hp.b_bounds s).2)
    source_kappa_sq_summable e hp.real_K_pos hp.real_K_double
    (source_cutoff_ratio_tendsto hp) hr hi
  filter_upwards [h, eventually_ge_atTop 1] with j hj hjpos
  have := sourceLaw_isProbabilityMeasure hp j
  change Real.exp (-82) / 2 ≤ (sourceLaw p j).real _ at hj
  exact hj.trans (measureReal_mono
    (retainedEvent_subset_sourceRetainedEvent _ _ _ _ _ j hjpos))

end Invariant233.BlockedProductCoupling

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Sampling_MixedRadixCircle
attribute [-instance] _root_.OAI.Invariant233.MixedRadix.digitLaw_isProbability _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Filter
open scoped Topology

namespace Invariant233.MixedRadix

@[simp] theorem hybrid_apply_lt {r : ℕ → ℕ} (d e : Digits r) {N n : ℕ} (hn : n < N) :
    hybrid d e N n = e n := ite_eq_left hn

end Invariant233.MixedRadix

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Operators_BlockedProjectionWindow
attribute [-instance] _root_.OAI.Invariant233.CircleParameterData.circleFiniteBase_probability _root_.OAI.Invariant233.OrderedProductCoupling.circlePairLaw_probability _root_.OAI.Invariant233.ProductModel.IdealSampling.law_finite _root_.OAI.Invariant233.ProductModel.IdealSampling.sourceMeasure_finite _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.ProductModel.prefixPairLaw_finite _root_.OAI.Invariant233.Rotation.circleMeasure_probability _root_.OAI.Invariant233.TrialSampling.spatialLaw_probability _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped Topology BigOperators ComplexConjugate lp

namespace Invariant233.BlockedProductCoupling

theorem measurable_sourceEvent (p : ProductScaleData)
    (e : ℕ ≃ Σ s, Fin (p.m s)) {r : ProductModel.Base → ℝ}
    (hr : Measurable r) (j : ℕ) : MeasurableSet (sourceEvent p e r j) := by
  have hx : Measurable (circleLeftEndpoint e) := by
    unfold circleLeftEndpoint toCircle leftEndpoint flatten OrderedProductCoupling.leftEndpoint
    fun_prop
  have hy : Measurable (circleRightEndpoint e) := by
    unfold circleRightEndpoint toCircle rightEndpoint flatten OrderedProductCoupling.rightEndpoint
    fun_prop
  have hc : MeasurableSet (currentEvent p.m j) := by
    change MeasurableSet ({z : Sample p.m | ∃ i, (z j i).1 = some (4 : Fin 5)} ∩
      {z | ∀ i, (z j i).2.1 < 1 - 2 / (p.m j : ℝ) ∧
        2 / (p.m j : ℝ) < (z j i).2.2})
    apply MeasurableSet.inter
    · simp only [ofPred_exists]
      exact MeasurableSet.iUnion fun i => (by fun_prop :
        Measurable (fun z : Sample p.m => (z j i).1)) (measurableSet_singleton _)
    · simp only [ofPred_forall]
      apply MeasurableSet.iInter
      intro i
      have hxi : Measurable (fun z : Sample p.m => (z j i).2.1) := by fun_prop
      have hyi : Measurable (fun z : Sample p.m => (z j i).2.2) := by fun_prop
      exact (measurableSet_lt hxi measurable_const).inter
        (measurableSet_lt measurable_const hyi)
  have hf : MeasurableSet (futureBad p.m (fun s => (p.K s : ℝ)) j) := by
    apply MeasurableSet.iUnion
    intro n
    apply MeasurableSet.iUnion
    intro i
    have hxi : Measurable (fun z : Sample p.m => (z (j + 1 + n) i).2.1) := by fun_prop
    have hyi : Measurable (fun z : Sample p.m => (z (j + 1 + n) i).2.2) := by fun_prop
    exact (measurableSet_le measurable_const hxi).union
      (measurableSet_le hyi measurable_const)
  exact hc.diff (hf.union
    ((measurableSet_lt (hr.comp hx) measurable_const).union
      (measurableSet_lt (measurable_const.sub (hr.comp hy)) measurable_const)))

end Invariant233.BlockedProductCoupling

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Analysis_BlockedSourceTransport
attribute [-instance] _root_.OAI.Invariant233.CircleParameterData.circleFiniteBase_probability _root_.OAI.Invariant233.OrderedProductCoupling.circlePairLaw_probability _root_.OAI.Invariant233.OrderedProductCoupling.leftTailLaw_isProbabilityMeasure _root_.OAI.Invariant233.OrderedProductCoupling.sourcePairLaw_isProbabilityMeasure _root_.OAI.Invariant233.ProductModel.IdealSampling.law_finite _root_.OAI.Invariant233.ProductModel.IdealSampling.sourceMeasure_finite _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.ProductModel.prefixPairLaw_finite _root_.OAI.Invariant233.Rotation.circleMeasure_probability _root_.OAI.Invariant233.TrialSampling.spatialLaw_probability _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators

noncomputable section
open MeasureTheory Set Filter

namespace Invariant233.BlockedProductCoupling

theorem measurable_unflatten {m : ℕ → ℕ} (e : ℕ ≃ Σ s, Fin (m s)) :
    Measurable (unflatten e) := by unfold unflatten; fun_prop

theorem measurable_flatten {m : ℕ → ℕ} (e : ℕ ≃ Σ s, Fin (m s)) :
    Measurable (flatten e) := by unfold flatten; fun_prop

theorem source_measurePreserving_flatten {p : ProductScaleData}
    (hp : ProductScaleLaws p) (e : ℕ ≃ Σ s, Fin (p.m s)) (j : ℕ) :
    MeasurePreserving (flatten e) (sourceLaw p j)
      (OrderedProductCoupling.law (OrderedProductCoupling.sourceBlocks p.m p.a p.b
        hp.m_ge_100 (fun s => (hp.a_bounds s).1) (fun s => (hp.a_bounds s).2)
        (fun s => (hp.b_bounds s).1) (fun s => (hp.b_bounds s).2) e j)) := by
  refine ⟨measurable_flatten e, ?_⟩
  change (law _ _ _ _ _).map _ = _
  rw [law_map_flatten hp.m_ge_100 source_kappa_nonneg source_kappa_le
    (fun s _ => (hp.a_bounds s).1) (fun s _ => (hp.a_bounds s).2)
    (fun s _ => (hp.b_bounds s).1) (fun s _ => (hp.b_bounds s).2)]
  congr 1
  simp [parameters, OrderedProductCoupling.sourceBlocks, OrderedProductCoupling.ofBlocks,
    OrderedProductCoupling.sourceKappa, ProductScaleData.kappa, Nat.cast_add, Nat.cast_one]

theorem source_measurePreserving_unflatten {p : ProductScaleData}
    (hp : ProductScaleLaws p) (e : ℕ ≃ Σ s, Fin (p.m s)) (j : ℕ) :
    MeasurePreserving (unflatten e)
      (OrderedProductCoupling.law (OrderedProductCoupling.sourceBlocks p.m p.a p.b
        hp.m_ge_100 (fun s => (hp.a_bounds s).1) (fun s => (hp.a_bounds s).2)
        (fun s => (hp.b_bounds s).1) (fun s => (hp.b_bounds s).2) e j))
      (sourceLaw p j) := by
  refine ⟨measurable_unflatten e, ?_⟩
  rw [← (source_measurePreserving_flatten hp e j).map_eq,
    Measure.map_map (measurable_unflatten e) (measurable_flatten e)]
  rw [show unflatten e ∘ flatten e = id from funext (unflatten_flatten e)]
  exact Measure.map_id

theorem flatSourceEvent_mass_eq {p : ProductScaleData} (hp : ProductScaleLaws p)
    (e : ℕ ≃ Σ s, Fin (p.m s)) {r : ProductModel.Base → ℝ} (hr : Measurable r) (j : ℕ) :
    (OrderedProductCoupling.law (OrderedProductCoupling.sourceBlocks p.m p.a p.b
      hp.m_ge_100 (fun s => (hp.a_bounds s).1) (fun s => (hp.a_bounds s).2)
      (fun s => (hp.b_bounds s).1) (fun s => (hp.b_bounds s).2) e j)).real
      (flatSourceEvent p e r j) = (sourceLaw p j).real (sourceEvent p e r j) := by
  rw [← (source_measurePreserving_unflatten hp e j).map_eq,
    map_measureReal_apply (measurable_unflatten e) (measurable_sourceEvent p e hr j)]
  rfl

theorem eventually_flatSourceEvent_mass_oai {p : ProductScaleData} (hp : ProductScaleLaws p)
    (e : ℕ ≃ Σ s, Fin (p.m s)) {r : ProductModel.Base → ℝ} (hr : Measurable r)
    (hi : ∀ᵐ x ∂ProductModel.baseMeasure, 0 < r x ∧ r x < 1) :
    ∀ᶠ j in atTop, Real.exp (-82) / 2 ≤
      (OrderedProductCoupling.law (OrderedProductCoupling.sourceBlocks p.m p.a p.b
        hp.m_ge_100 (fun s => (hp.a_bounds s).1) (fun s => (hp.a_bounds s).2)
        (fun s => (hp.b_bounds s).1) (fun s => (hp.b_bounds s).2) e j)).real
        (flatSourceEvent p e r j) := by
  filter_upwards [eventually_sourceEvent_mass hp e hr hi] with j hj
  rwa [flatSourceEvent_mass_eq hp e hr j]

end Invariant233.BlockedProductCoupling

end

end OAI
end

theorem solution : type_of% @OAI.Invariant233.BlockedProductCoupling.eventually_flatSourceEvent_mass_oai := @OAI.Invariant233.BlockedProductCoupling.eventually_flatSourceEvent_mass_oai
