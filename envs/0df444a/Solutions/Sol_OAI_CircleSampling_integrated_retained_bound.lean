-- Prove2me | solution 1 for OAI.CircleSampling.integrated_retained_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-25T22:15:26.905546+00:00
-- url     : https://prove2.me/submissions/5fcf9c48-d54e-4211-9d62-3a4000ef4618

import Mathlib
import Definitions.Def_OAIQ2Rw002

section
-- module Solutions.OAIQ2_Rot.RotationWeights_Fibers
attribute [-instance] _root_.OAI.CircleCoupling.labelMeasurableSpace _root_.OAI.ContinuousCircleWeight.fiberSeparable _root_.OAI.ContinuousCircleWeight.realCutoffRange_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uι

noncomputable section
open MeasureTheory
open scoped ENNReal NNReal ComplexInnerProductSpace BigOperators

namespace ContinuousCircleWeight

theorem fiberCocycleShift_pow_apply (F : ℤ → ℝ) (hF : ∀ k, 0 < F k)
    (hmono : Antitone F) (n : ℕ) (f : FiberHilbert) (k : ℤ) :
    (fiberCocycleShift F hF hmono ^ n) f k =
      (F k / F (k-n) : ℝ) * f (k-n) := by
  induction n generalizing f k with
  | zero => simp [ne_of_gt (hF k)]
  | succ n ih =>
    rw [pow_succ', mul_apply_eq_comp, fiberCocycleShift_apply, ih]
    have hk : k - 1 - (n : ℤ) = k - ((n+1 : ℕ) : ℤ) := by omega
    rw [hk, ← mul_assoc, ← Complex.ofReal_mul]
    have hr : F k / F (k-1) * (F (k-1) / F (k - ((n+1 : ℕ) : ℤ))) =
        F k / F (k - ((n+1 : ℕ) : ℤ)) := by
      field_simp [ne_of_gt (hF (k-1))]
    rw [hr]

theorem invariant_fixed_vector {T q : FiberOperator}
    (hinv : (1-q) * T * q = 0) {v : FiberHilbert} (hv : q v = v) :
    q (T v) = T v := by
  have h := congrArg (fun A : FiberOperator => A v) hinv
  have heq : T v - q (T v) = 0 := by
    simpa only [mul_apply_eq_comp, hv, sub_apply,
      one_apply_eq_self, zero_apply] using h
  exact (sub_eq_zero.mp heq).symm

theorem invariant_fixed_vector_pow {T q : FiberOperator}
    (hinv : (1-q) * T * q = 0) {v : FiberHilbert} (hv : q v = v) (n : ℕ) :
    q ((T ^ n) v) = (T ^ n) v := by
  induction n with
  | zero => simpa using hv
  | succ n ih =>
    rw [pow_succ', mul_apply_eq_comp]
    exact invariant_fixed_vector hinv ih

theorem projection_complement_inner {q : FiberOperator} (hq : IsStarProjection q)
    {v : FiberHilbert} (hv : q v = v) (e : FiberHilbert) :
    inner ℂ ((1-q) e) v = 0 := by
  rw [← (hq.one_sub.isSelfAdjoint.adjoint_eq),
    ContinuousLinearMap.adjoint_inner_left]
  simp [hv]

theorem cocycle_action_coordinate (F G : ℤ → ℝ) (hF : ∀ k, 0 < F k)
    (hG : ∀ k, 0 < G k) (hmono : Antitone G) (horder : ∀ k, G k ≤ F k)
    (ξ : FiberHilbert) (n : ℕ) (k : ℤ) :
    ((fiberCocycleShift G hG hmono ^ n)
      (cocycleRatioDiagonal F G hF hG horder ξ)) (n+k) =
      (G (n+k) / F k : ℝ) * ξ k := by
  rw [fiberCocycleShift_pow_apply]
  simp only [add_sub_cancel_left, cocycleRatioDiagonal_apply]
  rw [← mul_assoc, ← Complex.ofReal_mul]
  congr 2
  field_simp [ne_of_gt (hG k)]

theorem fiber_full_convolution (F G : ℤ → ℝ) (hF : ∀ k, 0 < F k)
    (hG : ∀ k, 0 < G k) (hmono : Antitone G) (horder : ∀ k, G k ≤ F k)
    (q : FiberOperator) (hq : IsStarProjection q)
    (hinv : (1-q) * fiberCocycleShift G hG hmono * q = 0)
    (ξ e : FiberHilbert)
    (hξ : q (cocycleRatioDiagonal F G hF hG horder ξ) =
      cocycleRatioDiagonal F G hF hG horder ξ) (n : ℕ) :
    Summable (fun v : ℤ => (G (n+v) / F v : ℝ) * ξ v *
        starRingEnd ℂ (((1-q) e) (n+v))) ∧
      (∑' v : ℤ, (G (n+v) / F v : ℝ) * ξ v *
        starRingEnd ℂ (((1-q) e) (n+v))) = 0 := by
  let η := (fiberCocycleShift G hG hmono ^ n)
    (cocycleRatioDiagonal F G hF hG horder ξ)
  let g := (1-q) e
  have hcoord (k : ℤ) : inner ℂ (g (n+k)) (η (n+k)) =
      (G (n+k) / F k : ℝ) * ξ k * starRingEnd ℂ (g (n+k)) := by
    rw [RCLike.inner_apply]
    rw [show η (n+k) = (G (n+k) / F k : ℝ) * ξ k from
      cocycle_action_coordinate F G hF hG hmono horder ξ n k]
  constructor
  · have hs := (Equiv.addLeft (n : ℤ)).summable_iff.mpr (lp.summable_inner (𝕜 := ℂ) g η)
    change Summable (fun k : ℤ => inner ℂ (g (n+k)) (η (n+k))) at hs
    simpa only [hcoord] using hs
  · have hzero : inner ℂ g η = 0 := projection_complement_inner hq
      (invariant_fixed_vector_pow hinv hξ n) e
    rw [lp.inner_eq_tsum] at hzero
    rw [← (Equiv.addLeft (n : ℤ)).tsum_eq (fun k => inner ℂ (g k) (η k))] at hzero
    change (∑' k : ℤ, inner ℂ (g (n+k)) (η (n+k))) = 0 at hzero
    simpa only [hcoord] using hzero

theorem cocycle_two_ratio_bounds (F G : ℤ → ℝ) (hF : ∀ k, 0 < F k)
    (hG : ∀ k, 0 < G k) (hFmono : Antitone F) (hGmono : Antitone G)
    (horder : ∀ k, G k ≤ F k) (n : ℕ) (k : ℤ) :
    0 < G (n+k) / F k ∧
    G (n+k) / F k ≤ G k / F k ∧
    G (n+k) / F k ≤ G (n+k) / F (n+k) ∧
    G k / F k ≤ 1 ∧ G (n+k) / F (n+k) ≤ 1 := by
  have hkn : k ≤ (n : ℤ) + k := by omega
  exact ⟨div_pos (hG _) (hF _),
    div_le_div_of_nonneg_right (hGmono hkn) (hF _).le,
    div_le_div_of_nonneg_left (hG _).le (hF _) (hFmono hkn),
    (div_le_one (hF _)).mpr (horder _),
    (div_le_one (hF _)).mpr (horder _)⟩

end ContinuousCircleWeight

end

end OAI
end

section
-- module Solutions.OAIQ2_Rot.RotationWeights_Parameters
attribute [-instance] _root_.OAI.CircleCoupling.labelMeasurableSpace _root_.OAI.CircleSampling.stageSample_nonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CircleSampling

open MeasureTheory
open scoped ENNReal NNReal ComplexInnerProductSpace BigOperators
open MeasureTheory Filter Set Submodule
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ComplexInnerProductSpace
open MeasureTheory Filter Set
open Set
open scoped ComplexInnerProductSpace
open Set
open scoped ComplexInnerProductSpace
open MeasureTheory Set Filter Topology
open scoped BigOperators ComplexConjugate
open MeasureTheory Set Filter
open scoped BigOperators ENNReal
open Filter Set
open scoped Topology
open Filter Set
open scoped Topology
open Set MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter Set
open scoped Topology
open Set MeasureTheory
open scoped ENNReal Classical
open Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Topology
open scoped BigOperators
open scoped BigOperators
open Set
open Set
open Set

section
open Set Filter MeasureTheory ContinuousCircleWeight.Sampling
open scoped Topology

lemma polynomialWindow_growth (j : ℕ) : 2*polynomialWindow j<polynomialWindow (j+1) :=
  (scaleStep j).numeric.2.2.2.2.2.2.1

lemma polynomialWindow_geometric (j n : ℕ) : 2^n*polynomialWindow j≤polynomialWindow (j+n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hg := (polynomialWindow_growth (j+n)).le
    calc
      2^(n+1)*polynomialWindow j = 2*(2^n*polynomialWindow j) := by ring
      _ ≤ 2*polynomialWindow (j+n) := Nat.mul_le_mul_left _ ih
      _ ≤ polynomialWindow (j+(n+1)) := by simpa only [Nat.add_assoc] using hg

end

open Set Filter MeasureTheory
open scoped Topology BigOperators

lemma window_inverse_bound (j n : ℕ) :
    1/(polynomialWindow (j+n):ℝ) ≤ (1/(polynomialWindow j:ℝ))*(1/2:ℝ)^n := by
  have hK : 0<(polynomialWindow j:ℝ) := Nat.cast_pos.mpr (polynomialWindow_pos j)
  have hg : (2:ℝ)^n*(polynomialWindow j:ℝ) ≤ polynomialWindow (j+n) := by
    exact_mod_cast polynomialWindow_geometric j n
  calc
    1/(polynomialWindow (j+n):ℝ) ≤ 1/((2:ℝ)^n*(polynomialWindow j:ℝ)) :=
      one_div_le_one_div_of_le (by positivity) hg
    _ = (1/(polynomialWindow j:ℝ))*(1/2:ℝ)^n := by rw [div_pow,one_pow]; field_simp

lemma summable_window_inverse (j : ℕ) : Summable (fun n => 1/(polynomialWindow (j+n):ℝ)) := by
  apply Summable.of_nonneg_of_le (fun _ => by positivity) (window_inverse_bound j)
  exact (summable_geometric_of_norm_lt_one (x:=(1/2:ℝ)) (by norm_num)).mul_left _

lemma tsum_window_inverse (j : ℕ) :
    (∑' n,1/(polynomialWindow (j+n):ℝ)) ≤ 2/(polynomialWindow j:ℝ) := by
  have hs := (summable_geometric_of_norm_lt_one (x:=(1/2:ℝ)) (by norm_num)).mul_left (1/(polynomialWindow j:ℝ))
  calc
    _ ≤ ∑' n,(1/(polynomialWindow j:ℝ))*(1/2:ℝ)^n :=
      (summable_window_inverse j).tsum_le_tsum (window_inverse_bound j) hs
    _ = 2/(polynomialWindow j:ℝ) := by
      rw [tsum_mul_left,tsum_geometric_of_norm_lt_one (by norm_num : ‖(1/2:ℝ)‖<1)]
      ring

lemma sum_phase_block (j : ℕ) :
    (∑ i : Fin (blockLength j), coordinatePhase (blocks.equiv ⟨j,i⟩)) ≤ 2/(polynomialWindow j:ℝ) := by
  have hm : (blockLength j:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (scaleStep j).mpos.ne'
  calc
    _ ≤ ∑ _i : Fin (blockLength j),2/((blockLength j:ℝ)*polynomialWindow j) :=
      Finset.sum_le_sum (fun i _ => (coordinatePhase_block j i).2.le)
    _ = 2/(polynomialWindow j:ℝ) := by simp; field_simp

lemma summable_coordinatePhase : Summable coordinatePhase := by
  have hs : Summable (fun j => 2/(polynomialWindow j:ℝ)) := by
    simpa only [Nat.zero_add,div_eq_mul_inv,one_mul] using (summable_window_inverse 0).mul_left 2
  have ht : Summable (fun j => ∑ i : Fin (blockLength j), coordinatePhase (blocks.equiv ⟨j,i⟩)) :=
    Summable.of_nonneg_of_le (fun _ => Finset.sum_nonneg (fun _ _ => (coordinatePhase_pos _).le))
      sum_phase_block hs
  apply blocks.equiv.summable_iff.mp
  apply (summable_sigma_of_nonneg (fun x : Σ j, Fin (blocks.m j) => (coordinatePhase_pos (blocks.equiv x)).le)).mpr
  refine ⟨fun _ => Summable.of_finite,?_⟩
  convert ht using 1
  ext j
  rw [tsum_fintype]
  rfl


end CircleSampling

end

end OAI
end

section
-- module Solutions.OAIQ2_Rot.RotationWeights_MeasurableWeight
attribute [-instance] _root_.OAI.CircleCoupling.labelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CircleModel

open MeasureTheory
open scoped ENNReal NNReal ComplexInnerProductSpace BigOperators
open MeasureTheory Filter Set Submodule
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ComplexInnerProductSpace
open MeasureTheory Filter Set
open Set
open scoped ComplexInnerProductSpace
open Set
open scoped ComplexInnerProductSpace
open MeasureTheory Set Filter Topology
open scoped BigOperators ComplexConjugate
open MeasureTheory Set Filter
open scoped BigOperators ENNReal
open Filter Set
open scoped Topology
open Filter Set
open scoped Topology
open Set MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter Set
open scoped Topology
open Set MeasureTheory
open scoped ENNReal Classical
open Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Topology
open scoped BigOperators
open scoped BigOperators
open Set
open Set
open Set

open Set MeasureTheory Filter
open scoped BigOperators ENNReal Topology Classical
section
lemma repr_coe (x : CircleX) : ((repr x : ℝ) : CircleX) = x := by
  exact (AddCircle.measurableEquivIco 1 0).symm_apply_apply x

lemma Xi_shift (q : ℕ → ℕ) (θ : CircleX) (k : ℤ) (i : ℕ) (x : CircleX) :
    Xi q i (shift θ k x) = Int.fract (Xi q i x + k*beta q θ i) := by
  rw [← repr_mk]
  have hk : (((k:ℝ)*repr (q i • θ) : ℝ) : CircleX) = k • (q i • θ) := by
    rw [← zsmul_eq_mul,AddCircle.coe_zsmul,repr_coe]
  change repr (q i • (x+k•θ)) = repr ((repr (q i • x)+(k:ℝ)*repr (q i • θ) : ℝ) : CircleX)
  rw [AddCircle.coe_add,repr_coe,hk,nsmul_add,smul_comm]

lemma floor_cocycle (x a : ℝ) (k n : ℤ) :
    ⌊x+(k+n)*a⌋ = ⌊x+k*a⌋ + ⌊Int.fract (x+k*a)+n*a⌋ := by
  have h : x+(k+n)*a = Int.fract (x+k*a)+n*a+(⌊x+k*a⌋:ℝ) := by
    rw [Int.fract]; ring
  rw [h,Int.floor_add_intCast]
  omega

lemma shift_add (θ : CircleX) (k n : ℤ) (x : CircleX) :
    shift θ n (shift θ k x) = shift θ (k+n) x := by
  simp [shift,add_zsmul,add_assoc]
lemma good_shift (q : ℕ → ℕ) (θ : CircleX) (k : ℤ) (x : CircleX) :
    shift θ k x ∈ good q θ ↔ x ∈ good q θ := by
  constructor
  · intro h a
    have := h (a-k)
    simpa [shift_add] using this
  · intro h a
    simpa [shift_add] using h (k+a)

lemma floorTerm_add (q : ℕ → ℕ) (θ : CircleX) (k n : ℤ) (x : CircleX) (i : ℕ) :
    floorTerm q θ (k+n) x i = floorTerm q θ k x i + floorTerm q θ n (shift θ k x) i := by
  simp only [floorTerm,Xi_shift,floor_cocycle,Int.cast_add]

lemma exponent_add {q : ℕ → ℕ} {θ : CircleX} (c : ℕ → ℝ) (k n : ℤ) {x : CircleX}
    (hx : x∈good q θ) :
    exponent q θ c (k+n) x = exponent q θ c n (shift θ k x)+exponent q θ c k x := by
  simp only [exponent,floorTerm_add,Int.cast_add,mul_add]
  rw [(summable_exponent c k hx).tsum_add (summable_exponent c n ((good_shift q θ k x).mpr hx)),add_comm]

lemma cocycle_add (q : ℕ → ℕ) (θ : CircleX) (c : ℕ → ℝ) (k n : ℤ) (x : CircleX) :
    cocycle q θ c (k+n) x = cocycle q θ c n (shift θ k x)*cocycle q θ c k x := by
  unfold cocycle
  by_cases hx : x∈good q θ
  · rw [ite_eq_left hx,ite_eq_left hx,ite_eq_left ((good_shift q θ k x).mpr hx),exponent_add c k n hx,neg_add,Real.exp_add]
  · rw [ite_eq_right hx,ite_eq_right hx,ite_eq_right (mt (good_shift q θ k x).mp hx),one_mul]

lemma measurePreserving_XiMap {q : ℕ → ℕ} (hq : ∀ i, q i≠0) (i : ℕ) :
    MeasurePreserving (fun x : CircleX ↦ q i • x) volume volume := by
  simpa only [natCast_zsmul] using
    (Measure.measurePreserving_zsmul (volume : Measure CircleX) (by exact_mod_cast hq i : (q i:ℤ)≠0))

lemma measure_repr_lower {r : ℝ} : volume {x : CircleX | repr x < r} ≤ ENNReal.ofReal r := by
  change volume (repr ⁻¹' Iio r) ≤ _
  rw [AddCircle.add_projection_respects_measure 1 0 (measurable_repr measurableSet_Iio)]
  have hs : ((↑) : ℝ → CircleX) ⁻¹' {x | repr x < r} ∩ Ioc 0 (0+1) ⊆ Ioo 0 r ∪ {1} := by
    rintro s ⟨hs,hsI⟩
    by_cases he : s=1
    · exact Or.inr (by simpa using he)
    · left
      refine ⟨hsI.1,?_⟩
      change repr (s : CircleX)<r at hs
      rw [repr_mk,Int.fract_eq_self.mpr ⟨hsI.1.le,lt_of_le_of_ne (by simpa using hsI.2) he⟩] at hs
      exact hs
  calc
    _ ≤ volume (Ioo 0 r ∪ {1}) := measure_mono hs
    _ ≤ volume (Ioo 0 r) + volume ({1}:Set ℝ) := measure_union_le _ _
    _ = ENNReal.ofReal r := by simp

lemma measure_repr_upper {r : ℝ} : volume {x : CircleX | 1-r≤repr x} ≤ ENNReal.ofReal r := by
  change volume (repr ⁻¹' Ici (1-r)) ≤ _
  rw [AddCircle.add_projection_respects_measure 1 0 (measurable_repr measurableSet_Ici)]
  have hs : ((↑) : ℝ → CircleX) ⁻¹' {x | 1-r≤repr x} ∩ Ioc 0 (0+1) ⊆ Icc (1-r) 1 ∪ {1} := by
    rintro s ⟨hs,hsI⟩
    by_cases he : s=1
    · exact Or.inr (by simpa using he)
    · left
      refine ⟨?_,by simpa using hsI.2⟩
      change 1-r≤repr (s : CircleX) at hs
      rw [repr_mk,Int.fract_eq_self.mpr ⟨hsI.1.le,lt_of_le_of_ne (by simpa using hsI.2) he⟩] at hs
      exact hs
  calc
    _ ≤ volume (Icc (1-r) 1 ∪ {1}) := measure_mono hs
    _ ≤ volume (Icc (1-r) 1)+volume ({1}:Set ℝ) := measure_union_le _ _
    _ = ENNReal.ofReal r := by simp

lemma floorTerm_event_bound {q : ℕ → ℕ} (hq : ∀ i, q i≠0) (θ : CircleX) (k : ℤ) (i : ℕ) :
    volume {x : CircleX | floorTerm q θ k x i≠0} ≤ ENNReal.ofReal (2 * |(k:ℝ)| * beta q θ i) := by
  let t := |(k:ℝ)| * beta q θ i
  have ht : 0≤t := mul_nonneg (abs_nonneg _) (repr_mem _).1
  have hs : {x : CircleX | floorTerm q θ k x i≠0} ⊆
      {x | Xi q i x<t} ∪ {x | 1-t≤Xi q i x} := by
    intro x hx
    by_contra! hh
    simp only [Set.mem_union,Set.mem_ofPred_eq,not_or,not_lt,not_le] at hh
    apply hx
    apply Int.floor_eq_iff.mpr
    have hβ : 0 ≤ beta q θ i := (repr_mem (q i • θ)).1
    have ha : -(t) ≤ (k:ℝ)*beta q θ i := by
      dsimp [t]; nlinarith [neg_abs_le (k:ℝ)]
    have hb : (k:ℝ)*beta q θ i ≤ t := by
      dsimp [t]; nlinarith [le_abs_self (k:ℝ)]
    constructor <;> push_cast <;> linarith
  have h1 : volume {x : CircleX | Xi q i x<t} ≤ ENNReal.ofReal t := by
    rw [show {x : CircleX | Xi q i x<t} = (fun x : CircleX ↦ q i • x) ⁻¹' (repr ⁻¹' Iio t) from rfl,
      (measurePreserving_XiMap hq i).measure_preimage (measurable_repr measurableSet_Iio).nullMeasurableSet]
    exact measure_repr_lower
  have h2 : volume {x : CircleX | 1-t≤Xi q i x} ≤ ENNReal.ofReal t := by
    rw [show {x : CircleX | 1-t≤Xi q i x} = (fun x : CircleX ↦ q i • x) ⁻¹' (repr ⁻¹' Ici (1-t)) from rfl,
      (measurePreserving_XiMap hq i).measure_preimage (measurable_repr measurableSet_Ici).nullMeasurableSet]
    exact measure_repr_upper
  calc
    _ ≤ volume {x : CircleX | Xi q i x<t}+volume {x : CircleX | 1-t≤Xi q i x} :=
      (measure_mono hs).trans (measure_union_le _ _)
    _ ≤ ENNReal.ofReal t+ENNReal.ofReal t := add_le_add h1 h2
    _ = _ := by rw [← ENNReal.ofReal_add ht ht]; congr 1; dsimp [t]; ring

lemma ae_good0 {q : ℕ → ℕ} (hq : ∀ i, q i≠0) (θ : CircleX)
    (hβ : Summable (beta q θ)) : ∀ᵐ x : CircleX ∂volume, x∈good0 q θ := by
  apply ae_all_iff.mpr
  intro k
  apply ae_finite_setOfPred_mem
  apply ne_of_lt
  apply lt_of_le_of_lt (ENNReal.tsum_le_tsum (floorTerm_event_bound hq θ k))
  exact (hβ.mul_left (2*|(k:ℝ)|)).tsum_ofReal_lt_top

lemma ae_good {q : ℕ → ℕ} (hq : ∀ i, q i≠0) (θ : CircleX)
    (hβ : Summable (beta q θ)) : ∀ᵐ x : CircleX ∂volume, x∈good q θ := by
  apply ae_all_iff.mpr
  intro a
  exact (measurePreserving_add_right (volume : Measure CircleX) (a•θ)).quasiMeasurePreserving.ae (ae_good0 hq θ hβ)

end
open Set MeasureTheory Filter
open scoped BigOperators

lemma floor_unit_interval_bounds {s a : ℝ} (hs : s∈Ico 0 1) :
    ⌊a⌋ ≤ ⌊s+a⌋ ∧ ⌊s+a⌋ ≤ ⌊a⌋+1 := by
  constructor
  · exact Int.floor_mono (by linarith [hs.1])
  · have hlt : s+a < (⌊a⌋+1:ℤ)+1 := by
      push_cast
      linarith [Int.lt_floor_add_one a,hs.2]
    exact Int.lt_add_one_iff.mp ((Int.floor_lt).mpr (by simpa only [Int.cast_add,Int.cast_one] using hlt))

lemma floorTerm_difference_le_one (q : ℕ → ℕ) (θ : CircleX) (k : ℤ) (x y : CircleX) (i : ℕ) :
    floorTerm q θ k x i ≤ floorTerm q θ k y i+1 := by
  have hx := floor_unit_interval_bounds (a:=(k:ℝ)*beta q θ i) (repr_mem (q i • x))
  have hy := floor_unit_interval_bounds (a:=(k:ℝ)*beta q θ i) (repr_mem (q i • y))
  change ⌊Xi q i x+(k:ℝ)*beta q θ i⌋ ≤ ⌊Xi q i y+(k:ℝ)*beta q θ i⌋+1
  dsimp [Xi] at *
  omega

lemma cocycle_ratio_tail_bound {q : ℕ → ℕ} {θ : CircleX} (c : ℕ → ℝ)
    (hc : ∀ i,0≤c i) (D : ℕ) (k : ℤ) {x y : CircleX}
    (hx : x∈good q θ) (hy : y∈good q θ) (hxy : ∀ i, D ≤ i → Xi q i x≤Xi q i y) :
    cocycle q θ c k y/cocycle q θ c k x ≤ Real.exp (∑ i∈Finset.range D,c i) := by
  have hf : Summable (fun i : ℕ => if i<D then c i else 0) :=
    summable_of_ne_finset_zero (s:=Finset.range D) (by intro i hi; simp_all)
  have hsum : (∑' i : ℕ, if i<D then c i else 0) = ∑ i∈Finset.range D,c i := by
    rw [tsum_eq_sum (s:=Finset.range D) (by intro i hi; simp_all)]
    apply Finset.sum_congr rfl
    intro i hi
    simp [Finset.mem_range.mp hi]
  have hb : exponent q θ c k x ≤ exponent q θ c k y+∑ i∈Finset.range D,c i := by
    rw [← hsum,exponent,exponent,← (summable_exponent c k hy).tsum_add hf]
    apply (summable_exponent c k hx).tsum_le_tsum _ ((summable_exponent c k hy).add hf)
    intro i
    by_cases hi : i<D
    · simp only [ite_eq_left hi]
      have h := floorTerm_difference_le_one q θ k x y i
      have h' : (floorTerm q θ k x i:ℝ) ≤ (floorTerm q θ k y i:ℝ)+1 := by exact_mod_cast h
      nlinarith [mul_le_mul_of_nonneg_left h' (hc i)]
    · simp only [ite_eq_right hi,add_zero]
      exact mul_le_mul_of_nonneg_left (Int.cast_le.mpr (floorTerm_ordered k (hxy i (by omega)))) (hc i)
  rw [cocycle_ratio_exp c k hx hy]
  exact Real.exp_le_exp.mpr (by linarith)

lemma cocycle_ratio_ordered {q : ℕ → ℕ} {θ : CircleX} (c : ℕ → ℝ)
    (hc : ∀ i,0≤c i) (k : ℤ) {x y : CircleX}
    (hx : x∈good q θ) (hy : y∈good q θ) (hxy : ∀ i,Xi q i x≤Xi q i y) :
    cocycle q θ c k y/cocycle q θ c k x ≤ 1 := by
  simpa using cocycle_ratio_tail_bound c hc 0 k hx hy (fun i _ => hxy i)


end CircleModel

end

end OAI
end

section
-- module Solutions.OAIQ2_Rot.RotationWeights_OrbitBounds
attribute [-instance] _root_.OAI.CircleCoupling.labelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CircleSampling

universe uX uY uι

open MeasureTheory
open scoped ENNReal NNReal ComplexInnerProductSpace BigOperators
open MeasureTheory Filter Set Submodule
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ComplexInnerProductSpace
open MeasureTheory Filter Set
open Set
open scoped ComplexInnerProductSpace
open Set
open scoped ComplexInnerProductSpace
open MeasureTheory Set Filter Topology
open scoped BigOperators ComplexConjugate
open MeasureTheory Set Filter
open scoped BigOperators ENNReal
open Filter Set
open scoped Topology
open Filter Set
open scoped Topology
open Set MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter Set
open scoped Topology
open Set MeasureTheory
open scoped ENNReal Classical
open Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Topology
open scoped BigOperators
open scoped BigOperators
open Set
open Set
open Set
open Set MeasureTheory Filter
open scoped BigOperators ENNReal Topology Classical

section
open CircleModel Set Filter MeasureTheory
open scoped Topology BigOperators

lemma model_beta_sum : Summable (CircleModel.beta modelFrequency modelAngle) := by
  have he : CircleModel.beta modelFrequency modelAngle = coordinatePhase := funext model_beta
  rw [he]
  exact summable_coordinatePhase
lemma model_good_ae : ∀ᵐ x : CircleModel.CircleX, x∈modelGood :=
  CircleModel.ae_good (fun i => (frequency_pos (i+1)).ne') modelAngle model_beta_sum
lemma modelF_add (k n : ℤ) (x : CircleModel.CircleX) :
    modelF (k+n) x=modelF n (CircleModel.shift modelAngle k x)*modelF k x :=
  CircleModel.cocycle_add _ _ _ _ _ _
lemma modelGood_shift (k : ℤ) (x : CircleModel.CircleX) : CircleModel.shift modelAngle k x∈modelGood ↔ x∈modelGood :=
  CircleModel.good_shift _ _ _ _
lemma modelF_ratio_ordered {x y : CircleModel.CircleX} (hx : x∈modelGood) (hy : y∈modelGood)
    (hxy : ∀ i,CircleModel.Xi modelFrequency i x≤CircleModel.Xi modelFrequency i y) (k : ℤ) :
    modelF k y/modelF k x≤1 :=
  CircleModel.cocycle_ratio_ordered coordinateDrop (fun i => dropSize_nonneg (coordinateBlock i)) k hx hy hxy
lemma modelF_ratio_tail {x y : CircleModel.CircleX} (D : ℕ) (hx : x∈modelGood) (hy : y∈modelGood)
    (hxy : ∀ i,D ≤ i → CircleModel.Xi modelFrequency i x≤CircleModel.Xi modelFrequency i y) (k : ℤ) :
    modelF k y/modelF k x≤Real.exp (∑ i∈Finset.range D,coordinateDrop i) :=
  CircleModel.cocycle_ratio_tail_bound coordinateDrop (fun i => dropSize_nonneg (coordinateBlock i)) D k hx hy hxy

lemma phase_orbit (i : ℕ) (n : ℤ) :
    modelFrequency i • (n•modelAngle)=((n*coordinatePhase i:ℝ):CircleModel.CircleX) := by
  rw [smul_comm,←model_beta]
  unfold CircleModel.beta CircleModel.Xi
  rw [←zsmul_eq_mul,AddCircle.coe_zsmul,CircleModel.repr_coe]

end

open MeasureTheory Set Filter
open scoped ENNReal Topology
section

lemma weightedMeasure_real_apply {X : Type uX} [MeasurableSpace X] (μ : Measure X) {f : X → ℝ}
    (hf : Integrable f μ) (hn : ∀ x,0≤f x) {A : Set X} (hA : MeasurableSet A) :
    (weightedMeasure μ f).real A=∫ x in A,f x ∂μ := by
  rw [Measure.real,weightedMeasure,withDensity_apply _ hA,
    ←ofReal_integral_eq_lintegral_ofReal hf.restrict (ae_of_all _ hn),ENNReal.toReal_ofReal]
  exact integral_nonneg hn
lemma weightedMeasure_integral {X : Type uX} [MeasurableSpace X] (μ : Measure X) {f : X → ℝ}
    (hf : Measurable f) (hn : ∀ x,0≤f x) (g : X → ℝ) :
    (∫ x,g x ∂weightedMeasure μ f)=∫ x,f x*g x ∂μ := by
  rw [weightedMeasure,integral_withDensity_eq_integral_toReal_smul hf.ennreal_ofReal
    (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (hn _),smul_eq_mul]

lemma weightedMeasure_map_equiv {X : Type uX} [MeasurableSpace X] (μ : Measure X)
    (T : X ≃ᵐ X) (hT : MeasurePreserving T μ μ) (f : X → ℝ) (hf : Measurable f) :
    Measure.map T (weightedMeasure μ f)=weightedMeasure μ (fun y => f (T.symm y)) := by
  ext A hA
  rw [Measure.map_apply T.measurable hA,weightedMeasure,weightedMeasure,
    withDensity_apply _ (T.measurable hA),withDensity_apply _ hA]
  have hgm : Measurable (A.indicator (fun y => ENNReal.ofReal (f (T.symm y)))) :=
    (hf.ennreal_ofReal.comp T.symm.measurable).indicator hA
  rw [←lintegral_indicator (T.measurable hA),←lintegral_indicator hA]
  calc
    _ = ∫⁻ x, A.indicator (fun y => ENNReal.ofReal (f (T.symm y))) (T x) ∂μ := by
      apply lintegral_congr
      intro x
      by_cases hx : T x∈A <;> simp [hx]
    _ = ∫⁻ y, A.indicator (fun y => ENNReal.ofReal (f (T.symm y))) y ∂Measure.map T μ :=
      (lintegral_map' hgm.aemeasurable T.measurable.aemeasurable).symm
    _ = _ := by rw [hT.map_eq]

lemma weightedGraph_fst {X : Type uX} {Y : Type uY} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (f : X → ℝ) (T : X → Y) (hT : Measurable T) :
    Measure.map Prod.fst (weightedGraph μ f T)=weightedMeasure μ f := by
  rw [weightedGraph,Measure.map_map measurable_fst (show Measurable (fun x => (x,T x)) from measurable_id.prodMk hT)]
  exact Measure.map_id
lemma weightedGraph_snd {X : Type uX} [MeasurableSpace X] (μ : Measure X)
    (T : X ≃ᵐ X) (hT : MeasurePreserving T μ μ) (f : X → ℝ) (hf : Measurable f) :
    Measure.map Prod.snd (weightedGraph μ f T)=weightedMeasure μ (fun y => f (T.symm y)) := by
  rw [weightedGraph,Measure.map_map measurable_snd (show Measurable (fun x => (x,T x)) from measurable_id.prodMk T.measurable)]
  exact weightedMeasure_map_equiv μ T hT f hf

open MeasureTheory Set Filter
open scoped ENNReal Topology BigOperators

lemma weightedMeasure_add {X : Type uX} [MeasurableSpace X] (μ : Measure X) {f g : X → ℝ}
    (hf : Measurable f) (hfn : ∀ x,0≤f x) (hgn : ∀ x,0≤g x) :
    weightedMeasure μ (fun x => f x+g x)=weightedMeasure μ f+weightedMeasure μ g := by
  unfold weightedMeasure
  simp only [ENNReal.ofReal_add (hfn _) (hgn _)]
  exact withDensity_add_left hf.ennreal_ofReal _
lemma weightedMeasure_mul {X : Type uX} [MeasurableSpace X] (μ : Measure X) (f : X → ℝ)
    (hf : Measurable f) {c : ℝ} (hc : 0≤c) :
    weightedMeasure μ (fun x => c*f x)=ENNReal.ofReal c • weightedMeasure μ f := by
  unfold weightedMeasure
  simp only [ENNReal.ofReal_mul hc]
  exact withDensity_smul _ hf.ennreal_ofReal
lemma weightedMeasure_sum {X : Type uX} {ι : Type uι} [MeasurableSpace X] (μ : Measure X)
    (s : Finset ι) (f : ι → X → ℝ) (hf : ∀ i∈s,Measurable (f i))
    (hn : ∀ i∈s,∀ x,0≤f i x) :
    weightedMeasure μ (fun x => ∑ i∈s,f i x)=∑ i∈s,weightedMeasure μ (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [weightedMeasure]
  | @insert i s hi ih =>
    simp only [Finset.mem_insert] at hf hn
    simp only [Finset.sum_insert hi]
    rw [weightedMeasure_add μ (hf i (Or.inl rfl)) (hn i (Or.inl rfl))
      (fun x => Finset.sum_nonneg (fun k hk => hn k (Or.inr hk) x))]
    rw [ih (fun k hk => hf k (Or.inr hk)) (fun k hk => hn k (Or.inr hk))]

lemma map_finsetSum {X : Type uX} {Y : Type uY} {ι : Type uι} [MeasurableSpace X] [MeasurableSpace Y]
    (s : Finset ι) (μ : ι → Measure X) {T : X → Y} (hT : Measurable T) :
    Measure.map T (∑ i∈s,μ i)=∑ i∈s,Measure.map T (μ i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp only [Finset.sum_insert hi,Measure.map_add _ _ hT,ih]

lemma finiteGraphAverage_fst {X : Type uX} {ι : Type uι} [MeasurableSpace X] [Fintype ι]
    (μ : Measure X) (w : ι → X → ℝ) (T : ι → X → X)
    (hw : ∀ i,Measurable (w i)) (hn : ∀ i x,0≤w i x) (hT : ∀ i,Measurable (T i)) :
    Measure.map Prod.fst (finiteGraphAverage μ w T)=weightedMeasure μ (finiteAverage w) := by
  rw [finiteGraphAverage,Measure.map_smul,
    map_finsetSum _ _ measurable_fst]
  simp_rw [weightedGraph_fst μ _ _ (hT _)]
  change _ = weightedMeasure μ (fun x => (Fintype.card ι:ℝ)⁻¹ * ∑ i, w i x)
  rw [weightedMeasure_mul _ _ (by fun_prop) (by positivity),
    weightedMeasure_sum _ _ _ (fun i _ => hw i) (fun i _ => hn i)]
lemma finiteGraphAverage_snd {X : Type uX} {ι : Type uι} [MeasurableSpace X] [Fintype ι]
    (μ : Measure X) (T : ι → X ≃ᵐ X) (hT : ∀ i,MeasurePreserving (T i) μ μ)
    (w : ι → X → ℝ) (hw : ∀ i,Measurable (w i)) (hn : ∀ i x,0≤w i x) :
    Measure.map Prod.snd (finiteGraphAverage μ w (fun i => T i))=
      weightedMeasure μ (finiteAverage (fun i y => w i ((T i).symm y))) := by
  rw [finiteGraphAverage,Measure.map_smul,
    map_finsetSum _ _ measurable_snd]
  simp_rw [weightedGraph_snd μ _ (hT _) _ (hw _)]
  change _ = weightedMeasure μ (fun y => (Fintype.card ι:ℝ)⁻¹ * ∑ i, w i ((T i).symm y))
  rw [weightedMeasure_mul _ _ (by fun_prop) (by positivity),
    weightedMeasure_sum μ Finset.univ (fun i y => w i ((T i).symm y)) (fun i _ => (hw i).comp (T i).symm.measurable) (fun i _ x => hn i _)]

lemma finiteGraphAverage_ae {X : Type uX} {ι : Type uι} [MeasurableSpace X] [Fintype ι]
    (μ : Measure X) (w : ι → X → ℝ) (T : ι → X → X)
    (hw : ∀ i,Measurable (w i)) (hT : ∀ i,Measurable (T i))
    (P : X×X → Prop) (hP : MeasurableSet {z | P z})
    (hp : ∀ i,∀ᵐ x ∂μ,w i x≠0 → P (x,T i x)) :
    ∀ᵐ z ∂finiteGraphAverage μ w T,P z := by
  unfold finiteGraphAverage
  apply Measure.ae_smul_measure
  apply ae_finsetSum_measure_iff.mpr
  intro i _
  rw [weightedGraph]
  apply (ae_map_iff (show Measurable (fun x => (x,T i x)) from measurable_id.prodMk (hT i)).aemeasurable hP).mpr
  rw [weightedMeasure,ae_withDensity_iff (hw i).ennreal_ofReal]
  filter_upwards [hp i] with x hx hne
  apply hx
  intro hz
  exact hne (by simp [hz])
end

section
open ContinuousCircleWeight.Sampling MeasureTheory Set CircleModel
open scoped BigOperators

lemma stageEll_lt (j : ℕ) : scaleEll (blockLength j) < 1 := by
  apply Real.rpow_lt_one_of_one_lt_of_neg
  · exact_mod_cast (by have := blockLength_ge j; omega : 1 < blockLength j)
  · norm_num

lemma stage_frequency (j : ℕ) (i : Fin (blockLength j)) :
    modelFrequency (blocks.equiv ⟨j,i⟩)=(scaleStep j).q (i+1) := by
  change frequency (blockEnd j+i.val+1)=_
  rw [show blockEnd j+i.val+1=blockEnd j+(i.val+1) by omega,frequency_block j (by omega)]
lemma stage_phase (j : ℕ) (i : Fin (blockLength j)) :
    coordinatePhase (blocks.equiv ⟨j,i⟩) = Int.fract (((scaleStep j).q (i+1):ℝ)*parameterAngle) := by
  unfold coordinatePhase
  rw [stage_frequency]
lemma stageFactor_model (positive : Bool) (j : ℕ) (n : ℤ) (i : Fin (blockLength j)) (x : CircleModel.CircleX) :
    stageFactor positive j n i x = orientedWeight positive (scaleEll (blockLength j)) (scaleAlpha (blockLength j))
      (modelFrequency (blocks.equiv ⟨j,i⟩) • x) (modelFrequency (blocks.equiv ⟨j,i⟩) • (n • modelAngle)) := by
  rw [phase_orbit,stage_phase,stage_frequency]
  rfl
lemma stageWeight_negative (j : ℕ) (n : ℤ) (x : CircleModel.CircleX) :
    stageWeight false j n x = stageWeight true j n (CircleModel.shift modelAngle (-n) x) := by
  apply Finset.prod_congr rfl
  intro i _
  simp only [stageFactor_model,orientedWeight,Bool.false_eq_true,↓reduceIte,uNeg,CircleModel.shift,neg_smul]
  rw [smul_add,smul_neg,sub_eq_add_neg]

lemma stageDensity_measurable (positive : Bool) (j : ℕ) (t : Fin ((scaleState j).1.q (scaleState j).1.d)) :
    Measurable (stageDensity positive j t) := by
  unfold stageDensity finiteAverage
  exact (Finset.measurable_sum _ (fun n _ => stageWeight_measurable positive j n.val)).const_mul _
lemma stageDensity_nonneg (positive : Bool) (j : ℕ) (t : Fin ((scaleState j).1.q (scaleState j).1.d)) (x : CircleModel.CircleX) :
    0 ≤ stageDensity positive j t x := by
  apply mul_nonneg (by positivity)
  exact Finset.sum_nonneg (fun n _ => (stageWeight_bounds positive j n.val x).1)
lemma stageDensity_memLp (positive : Bool) (j : ℕ) (t : Fin ((scaleState j).1.q (scaleState j).1.d)) :
    MemLp (stageDensity positive j t) 2 := by
  have h : MemLp (fun x => ∑ n : (scaleStep j).samples t, stageWeight positive j n.val x) 2 :=
    memLp_finsetSum Finset.univ (fun n _ => stageWeight_memLp positive j n.val)
  exact h.const_mul _
lemma stageDensity_energy (positive : Bool) (j : ℕ) (t : Fin ((scaleState j).1.q (scaleState j).1.d)) :
    (∫ x, (stageDensity positive j t x-1)^2) < 1/((j:ℝ)+1)^2 := by
  exact (scaleStep j).energies parameterAngle (parameterAngle_spec.2.2.2 j) t positive
end

open CircleModel Set MeasureTheory
open scoped BigOperators

lemma graphBad_measurable (j : ℕ) : MeasurableSet (graphBad j) :=
  (MeasurableSet.iUnion (fun _ => measurableSet_le measurable_const (CircleModel.measurable_Xi _ _))).union
    (MeasurableSet.iUnion (fun _ => measurableSet_le measurable_const (CircleModel.measurable_Xi _ _)))
lemma sampleBound_pos (j : ℕ) : 0  <  sampleBound j :=
  Real.rpow_pos_of_pos (Nat.cast_pos.mpr (scaleStep j).mpos) _
lemma sample_bound (j : ℕ) {t : Fin ((scaleState j).1.q (scaleState j).1.d)} {n : ℤ}
    (hn : n∈(scaleStep j).samples t) : 0  <  n ∧ (n:ℝ) ≤ sampleBound j := by
  have h := (scaleStep j).samples_bounds t n hn
  refine ⟨?_,h.2⟩
  have hh : (0:ℝ) < n := lt_of_lt_of_le (half_pos (sampleBound_pos j)) h.1
  exact_mod_cast hh
lemma coordinate_add_nowrap (q : ℕ) (x y : CircleX) (t : ℝ)
    (he : q•y=(t:CircleX)) (ht : 0 ≤ t)
    (hu : CircleModel.repr (q•x)+t < 1) :
    CircleModel.repr (q • (x+y))=CircleModel.repr (q•x)+t := by
  have he' : q • (x+y)=((CircleModel.repr (q • x)+t:ℝ):CircleX) := by
    rw [nsmul_add,he,AddCircle.coe_add,CircleModel.repr_coe]
  rw [he',CircleModel.repr_mk]
  exact Int.fract_eq_self.mpr ⟨add_nonneg (CircleModel.repr_mem _).1 ht,hu⟩
lemma positive_weight_order {ℓ α : ℝ} (hℓ : ℓ < 1) (hα : 0 < α) (s t : CircleX)
    (hw : uPos ℓ α s t ≠ 0) : CircleModel.repr s  ≤  CircleModel.repr (s+t) := by
  have hh : α ≤ delta (repr s) ∧ 0 < repr t ∧ repr t < ℓ*delta (repr s) := by
    by_cases hh : α ≤ delta (repr s) ∧ 0 < repr t ∧ repr t < ℓ*delta (repr s)
    · exact hh
    · exact False.elim (hw (by simp only [uPos,weight,ite_eq_right hh]))
  have hd : 0 < delta (repr s) := lt_of_lt_of_le hα hh.1
  have hst : repr s+repr t < 1 := by
    have : ℓ*delta (repr s) < delta (repr s) := (mul_lt_iff_lt_one_left hd).mpr hℓ
    have := min_le_right (repr s) (1-repr s)
    unfold delta at *
    linarith [hh.2.2]
  have he : CircleModel.repr (s+t)=CircleModel.repr s+CircleModel.repr t := by
    simpa only [one_nsmul] using coordinate_add_nowrap 1 s t (CircleModel.repr t)
      (by simpa using (CircleModel.repr_coe t).symm) hh.2.1.le (by simpa only [one_nsmul,repr,CircleModel.repr] using hst)
  rw [he]
  exact le_add_of_nonneg_right hh.2.1.le
lemma stageWeight_order (j : ℕ) (n : ℤ) (x : CircleX)
    (hw : stageWeight true j n x ≠ 0) (i : Fin (blockLength j)) :
    CircleModel.Xi modelFrequency (blocks.equiv ⟨j,i⟩) x  ≤
      CircleModel.Xi modelFrequency (blocks.equiv ⟨j,i⟩) (CircleModel.shift modelAngle n x) := by
  have hfactor : stageFactor true j n i x ≠ 0 := (Finset.prod_ne_zero_iff.mp hw) i (Finset.mem_univ _)
  rw [stageFactor_model] at hfactor
  change uPos _ _ _ _ ≠ 0 at hfactor
  have h := positive_weight_order (stageEll_lt j) (stageAlpha_pos j) _ _ hfactor
  simpa only [CircleModel.Xi,CircleModel.shift,nsmul_add] using h

lemma restricted_orbit_order (j D : ℕ) (h : CircleX)
    (hperiod : ∀ i, D ≤ i  →  modelFrequency i•h=0)
    (t : Fin ((scaleState j).1.q (scaleState j).1.d))
    (ht : gridPoint (scaleState j).1 t=h)
    (n : ℤ) (hn : n∈(scaleStep j).samples t) (x : CircleX)
    (hx : x∉graphBad j) (hw : stageWeight true j n x ≠ 0) :
    ∀ i, D ≤ i  →  CircleModel.Xi modelFrequency i x ≤
      CircleModel.Xi modelFrequency i (CircleModel.shift modelAngle n x) := by
  have ho := (scaleStep j).orbits parameterAngle (parameterAngle_spec.2.2.2 j) t n hn
  rw [ht] at ho
  obtain ⟨δ,hδ,hδeq⟩ := ho
  have hδn : n•modelAngle=h+(δ:CircleX) := by
    change (δ:CircleX)=n•modelAngle-h at hδeq
    exact (sub_eq_iff_eq_add.mp hδeq.symm).trans (add_comm _ _)
  intro i hi
  by_cases hold : i < blockEnd j
  · have hbad : CircleModel.Xi modelFrequency i x < 1-(modelFrequency i:ℝ)*gridTolerance j (scaleState j).1 := by
      by_contra! hh
      exact hx (Or.inl (mem_iUnion.mpr ⟨⟨i,hold⟩,hh⟩))
    have he : modelFrequency i•(n•modelAngle)=(((modelFrequency i:ℝ)*δ:ℝ):CircleX) := by
      rw [hδn,nsmul_add,hperiod i hi,zero_add,←AddCircle.coe_nsmul,nsmul_eq_mul]
    have hval := coordinate_add_nowrap (modelFrequency i) x (n•modelAngle)
      ((modelFrequency i:ℝ)*δ) he (mul_nonneg (Nat.cast_nonneg _) hδ.1.le)
      (by change CircleModel.Xi modelFrequency i x+_ < 1
          have hdiff : (modelFrequency i:ℝ)*δ < (modelFrequency i:ℝ)*gridTolerance j (scaleState j).1 :=
            mul_lt_mul_of_pos_left hδ.2 (Nat.cast_pos.mpr (frequency_pos (i+1)))
          linarith)
    change CircleModel.Xi modelFrequency i x  ≤  CircleModel.repr (modelFrequency i•(x+n•modelAngle))
    rw [hval]
    exact le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg _) hδ.1.le)
  · by_cases htail : blockEnd (j+1) ≤ i
    · have hbad : CircleModel.Xi modelFrequency i x < 1-sampleBound j*coordinatePhase i := by
        by_contra! hh
        exact hx (Or.inr (mem_iUnion.mpr ⟨⟨i,htail⟩,hh⟩))
      have hn0 : 0 ≤ (n:ℝ) := by exact_mod_cast (sample_bound j hn).1.le
      have hval := coordinate_add_nowrap (modelFrequency i) x (n•modelAngle)
        ((n:ℝ)*coordinatePhase i) (phase_orbit i n)
        (mul_nonneg hn0 (coordinatePhase_pos i).le)
        (by change CircleModel.Xi modelFrequency i x+_ < 1
            nlinarith [mul_le_mul_of_nonneg_right (sample_bound j hn).2 (coordinatePhase_pos i).le])
      change CircleModel.Xi modelFrequency i x  ≤  CircleModel.repr (modelFrequency i•(x+n•modelAngle))
      rw [hval]
      exact le_add_of_nonneg_right (mul_nonneg hn0 (coordinatePhase_pos i).le)
    · have hem : blockEnd (j+1)=blockEnd j+blockLength j := rfl
      let k : Fin (blockLength j) := ⟨i-blockEnd j,by omega⟩
      have he : blocks.equiv ⟨j,k⟩=i := by change blockEnd j+(i-blockEnd j)=i; omega
      simpa only [he] using stageWeight_order j n x hw k


end CircleSampling

end

end OAI
end

section
-- module Solutions.OAIQ2_Rot.RotationWeights_RationalGraphs
attribute [-instance] _root_.OAI.CircleCoupling.labelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

universe uι uX uY

open MeasureTheory
open scoped ENNReal NNReal ComplexInnerProductSpace BigOperators
open MeasureTheory Filter Set Submodule
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ComplexInnerProductSpace
open MeasureTheory Filter Set
open Set
open scoped ComplexInnerProductSpace
open Set
open scoped ComplexInnerProductSpace
open MeasureTheory Set Filter Topology
open scoped BigOperators ComplexConjugate
open MeasureTheory Set Filter
open scoped BigOperators ENNReal
open Filter Set
open scoped Topology
open Filter Set
open scoped Topology
open Set MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter Set
open scoped Topology
open Set MeasureTheory
open scoped ENNReal Classical
open Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Topology
open scoped BigOperators
open scoped BigOperators
open Set
open Set
open Set
open Set MeasureTheory Filter
open scoped BigOperators ENNReal Topology Classical
open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace CircleModel
open MeasureTheory Set
open scoped ENNReal

lemma measure_Xi_upper {q : ℕ → ℕ} (hq : ∀ i, q i≠0) (i : ℕ) (r : ℝ) :
    volume {x : CircleX | 1-r ≤ Xi q i x} ≤ ENNReal.ofReal r := by
  change volume ((fun x : CircleX => q i • x) ⁻¹' (repr ⁻¹' Ici (1-r))) ≤ _
  rw [(measurePreserving_XiMap hq i).measure_preimage (measurable_repr measurableSet_Ici).nullMeasurableSet]
  exact measure_repr_upper
end CircleModel

namespace CircleSampling

section
open CircleModel Set MeasureTheory Filter
open scoped ENNReal Topology BigOperators

lemma graphTolerance_pos (j : ℕ) : 0 < gridTolerance j (scaleState j).1 := by
  unfold gridTolerance
  have := (scaleState j).2.qpos (scaleState j).1.d le_rfl
  positivity
lemma oldGraphBad_bound (j : ℕ) :
    volume.real (oldGraphBad j) ≤ 1/(10*((j:ℝ)+1)^2) := by
  have htol := (graphTolerance_pos j).le
  have hq : 0 < ((scaleState j).1.q (scaleState j).1.d:ℝ) := Nat.cast_pos.mpr ((scaleState j).2.qpos _ le_rfl)
  calc
    _ ≤ ∑ i : Fin (blockEnd j), volume.real {x : CircleX | 1-(modelFrequency i:ℝ)*gridTolerance j (scaleState j).1 ≤ CircleModel.Xi modelFrequency i x} := measureReal_iUnion_fintype_le _
    _ ≤ ∑ i : Fin (blockEnd j), (modelFrequency i:ℝ)*gridTolerance j (scaleState j).1 := by
      apply Finset.sum_le_sum
      intro i _
      exact ENNReal.toReal_le_of_le_ofReal (mul_nonneg (Nat.cast_nonneg _) htol)
        (CircleModel.measure_Xi_upper (fun i => (frequency_pos (i+1)).ne') i _)
    _ ≤ ∑ _i : Fin (blockEnd j), ((scaleState j).1.q (scaleState j).1.d:ℝ)*gridTolerance j (scaleState j).1 := by
      apply Finset.sum_le_sum
      intro i _
      apply mul_le_mul_of_nonneg_right _ htol
      have hf := frequency_strictMono.monotone (show i.val+1 ≤ blockEnd j by omega)
      rw [frequency_eq_state (j:=j) le_rfl] at hf
      exact_mod_cast hf
    _ = (blockEnd j:ℝ)*(((scaleState j).1.q (scaleState j).1.d:ℝ)*gridTolerance j (scaleState j).1) := by simp
    _ ≤ _ := by
      unfold gridTolerance blockEnd
      have hd : 0 ≤ ((scaleState j).1.d:ℝ) := Nat.cast_nonneg _
      have hj : 0 < (j:ℝ)+1 := by positivity
      field_simp
      nlinarith [sq_pos_of_pos hj]

lemma measure_iUnion_le_ofReal_tsum {ι : Type uι} {X : Type uX} [Countable ι] [MeasurableSpace X]
    (μ : Measure X) (A : ι → Set X) (b : ι → ℝ) (hb : ∀ i, 0 ≤ b i)
    (hs : Summable b) (h : ∀ i, μ (A i) ≤ ENNReal.ofReal (b i)) :
    μ (⋃ i, A i) ≤ ENNReal.ofReal (∑' i, b i) := by
  calc
    _ ≤ ∑' i, μ (A i) := measure_iUnion_le _
    _ ≤ ∑' i, ENNReal.ofReal (b i) := ENNReal.tsum_le_tsum h
    _ = _ := (ENNReal.ofReal_tsum_of_nonneg hb hs).symm
lemma tailGraphBad_subset (j : ℕ) : tailGraphBad j ⊆
    ⋃ s : ℕ, ⋃ k : Fin (blockLength (j+1+s)),
      {x | 1-sampleBound j*coordinatePhase (blocks.equiv ⟨j+1+s,k⟩) ≤ CircleModel.Xi modelFrequency (blocks.equiv ⟨j+1+s,k⟩) x} := by
  rintro x hx
  obtain ⟨i,hi⟩ := mem_iUnion.mp hx
  obtain ⟨⟨b,k⟩,he⟩ := blocks.equiv.surjective i.val
  have hi' : i.val < blockEnd (b+1) := by
    rw [←he]
    change blockEnd b+k.val < blockEnd b+blockLength b
    exact Nat.add_lt_add_left k.isLt _
  have hb : j+1 ≤ b := by
    by_contra! hb
    have := blockEnd_strictMono.monotone (show b+1 ≤ j+1 by omega)
    omega
  have heq : j+1+(b-(j+1))=b := by omega
  apply mem_iUnion.mpr
  refine ⟨b-(j+1),?_⟩
  rw [heq]
  exact mem_iUnion.mpr ⟨k,by simpa only [he] using hi⟩
lemma tailGraphBad_bound (j : ℕ) :
    volume.real (tailGraphBad j) ≤ 4*sampleBound j/(polynomialWindow (j+1):ℝ) := by
  have hQ := (sampleBound_pos j).le
  have hq : ∀ i, modelFrequency i ≠ 0 := fun i => (frequency_pos (i+1)).ne'
  have hs : Summable (fun s => 2*sampleBound j/(polynomialWindow (j+1+s):ℝ)) := by
    simpa only [div_eq_mul_inv,one_mul] using (summable_window_inverse (j+1)).mul_left (2*sampleBound j)
  have hblock (s : ℕ) : volume (⋃ k : Fin (blockLength (j+1+s)),
      {x : CircleX | 1-sampleBound j*coordinatePhase (blocks.equiv ⟨j+1+s,k⟩) ≤ CircleModel.Xi modelFrequency (blocks.equiv ⟨j+1+s,k⟩) x}) ≤
      ENNReal.ofReal (2*sampleBound j/(polynomialWindow (j+1+s):ℝ)) := by
    apply (measure_iUnion_le_ofReal_tsum volume _ _ (fun k => mul_nonneg (sampleBound_pos j).le (coordinatePhase_pos _).le)
      (Summable.of_finite) (fun k => CircleModel.measure_Xi_upper hq _ _)).trans
    apply ENNReal.ofReal_le_ofReal
    rw [tsum_fintype,←Finset.mul_sum]
    calc
      _ ≤ sampleBound j*(2/(polynomialWindow (j+1+s):ℝ)) :=
        mul_le_mul_of_nonneg_left (sum_phase_block _) (sampleBound_pos j).le
      _ = _ := by ring
  have hm : volume (tailGraphBad j) ≤ ENNReal.ofReal (∑' s, 2*sampleBound j/(polynomialWindow (j+1+s):ℝ)) :=
    (measure_mono (tailGraphBad_subset j)).trans (measure_iUnion_le_ofReal_tsum volume _ _ (fun _ => by positivity) hs hblock)
  apply (ENNReal.toReal_le_of_le_ofReal (tsum_nonneg (fun _ => by positivity)) hm).trans
  simp_rw [div_eq_mul_inv]
  rw [tsum_mul_left]
  calc
    _ ≤ 2*sampleBound j*(2/(polynomialWindow (j+1):ℝ)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      simpa only [one_div] using tsum_window_inverse (j+1)
    _ = _ := by ring

lemma sampleBound_div_window (j : ℕ) : sampleBound j/(polynomialWindow (j+1):ℝ) ≤ 1/(blockLength j:ℝ) := by
  have hm : 0 < (blockLength j:ℝ) := Nat.cast_pos.mpr (scaleStep j).mpos
  have hm1 : 1 ≤ (blockLength j:ℝ) := by exact_mod_cast (scaleStep j).mpos
  have hm20 : (20:ℝ) ≤ blockLength j := by exact_mod_cast (show 20 ≤ blockLength j from (by have := blockLength_ge j; omega))
  have hk : (blockLength j:ℝ)^((3:ℝ)/4*blockLength j) ≤ (polynomialWindow (j+1):ℝ) := Nat.le_ceil _
  calc
    _ ≤ sampleBound j/((blockLength j:ℝ)^((3:ℝ)/4*blockLength j)) :=
      div_le_div_of_nonneg_left (sampleBound_pos j).le (Real.rpow_pos_of_pos hm _) hk
    _ = (blockLength j:ℝ)^(-(1:ℝ)/20*blockLength j) := by
      rw [sampleBound,←Real.rpow_sub hm]
      congr 1
      ring
    _ ≤ (blockLength j:ℝ)^(-(1:ℝ)) := Real.rpow_le_rpow_of_exponent_le hm1 (by linarith)
    _ = _ := by rw [Real.rpow_neg_one,one_div]
lemma graphBad_bound (j : ℕ) : volume.real (graphBad j) ≤ 1/(10*((j:ℝ)+1)^2)+4/(blockLength j:ℝ) := by
  calc
    _ ≤ volume.real (oldGraphBad j)+volume.real (tailGraphBad j) := measureReal_union_le _ _
    _ ≤ 1/(10*((j:ℝ)+1)^2)+4*sampleBound j/(polynomialWindow (j+1):ℝ) := add_le_add (oldGraphBad_bound j) (tailGraphBad_bound j)
    _ ≤ _ := by
      have h := mul_le_mul_of_nonneg_left (sampleBound_div_window j) (by norm_num : (0:ℝ) ≤ 4)
      apply add_le_add le_rfl
      simpa only [div_eq_mul_inv,mul_one,one_mul,mul_assoc] using h
lemma graphBad_tendsto : Tendsto (fun j => volume.real (graphBad j)) atTop (𝓝 0) := by
  have ha : Tendsto (fun j : ℕ => 1/(10*((j:ℝ)+1)^2)) atTop (𝓝 0) := by
    have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜:=ℝ)).pow 2
    convert h.div_const 10 using 1
    · ext j
      field_simp
    · norm_num
  have hb : Tendsto (fun j => 4/(blockLength j:ℝ)) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv,one_mul,mul_zero,Function.comp_def] using ((tendsto_one_div_atTop_nhds_zero_nat (𝕜:=ℝ)).comp blockLength_strictMono.tendsto_atTop).const_mul 4
  exact squeeze_zero (fun _ => measureReal_nonneg) graphBad_bound (by simpa using ha.add hb)
end
open Set
lemma circle_nat_zero (a : ℕ) : ((a:ℝ):CircleX)=0 := by
  rw [←mul_one (a:ℝ),←nsmul_eq_mul,AddCircle.coe_nsmul,AddCircle.coe_period,nsmul_zero]
lemma rational_annihilated {N P : ℕ} (hN : 0 < N) (hNP : N ∣ P) (a : ℕ) :
    P • (((a:ℝ)/(N:ℝ):ℝ):CircleX)=0 := by
  obtain ⟨c,rfl⟩ := hNP
  rw [←AddCircle.coe_nsmul,nsmul_eq_mul]
  have he : ((N*c:ℕ):ℝ)*((a:ℝ)/(N:ℝ))=((c*a:ℕ):ℝ) := by
    push_cast
    field_simp
  rw [he,circle_nat_zero]
lemma rational_tail_period (D : ℕ) (a : Fin (frequency (D+1))) (i : ℕ) (hi : D ≤ i) :
    modelFrequency i • (((a.val:ℝ)/(frequency (D+1):ℝ):ℝ):CircleX)=0 :=
  rational_annihilated (frequency_pos (D+1)) (frequency_dvd_of_le (Nat.add_le_add_right hi 1)) _
end CircleSampling

open MeasureTheory Set
namespace CircleSampling

section

lemma integral_norm_le_sqrt {X : Type uX} [MeasurableSpace X] (μ : Measure X)
    [IsProbabilityMeasure μ] {f : X → ℝ} (hf : MemLp f 2 μ) :
    (∫ x, ‖f x‖ ∂μ) ≤ Real.sqrt (∫ x, (f x)^2 ∂μ) := by
  have hh := integral_mul_norm_le_Lp_mul_Lq
    (show Real.HolderConjugate 2 2 by norm_num [Real.holderConjugate_iff])
    (by simpa using hf) (show MemLp (fun _ : X => (1:ℝ)) (ENNReal.ofReal 2) μ from memLp_const 1)
  simpa [Real.rpow_two,Real.sqrt_eq_rpow,Real.norm_eq_abs,sq_abs] using hh

lemma setIntegral_norm_le_sqrt {X : Type uX} [MeasurableSpace X] (μ : Measure X)
    [IsFiniteMeasure μ] {f : X → ℝ} (hf : MemLp f 2 μ) (A : Set X) (hA : MeasurableSet A) :
    (∫ x in A, ‖f x‖ ∂μ) ≤ Real.sqrt (∫ x, (f x)^2 ∂μ)*Real.sqrt (μ.real A) := by
  have hi := (memLp_const (1:ℝ) (μ:=μ) (p:=2)).indicator hA
  have hh := integral_mul_norm_le_Lp_mul_Lq
    (show Real.HolderConjugate 2 2 by norm_num [Real.holderConjugate_iff])
    (by simpa using hf) (by simpa using hi)
  have he (x : X) : ‖f x‖*‖A.indicator (fun _ => (1:ℝ)) x‖ = A.indicator (fun x => ‖f x‖) x := by
    by_cases hx : x∈A <;> simp [hx]
  have he2 (x : X) : ‖A.indicator (fun _ => (1:ℝ)) x‖^(2:ℝ) = A.indicator (fun _ => (1:ℝ)) x := by
    by_cases hx : x∈A <;> simp [hx]
  have hl : (∫ x, ‖f x‖*‖A.indicator (fun _ => (1:ℝ)) x‖ ∂μ) = ∫ x in A, ‖f x‖ ∂μ := by
    simp_rw [he]
    exact integral_indicator hA
  have hr : (∫ x, ‖A.indicator (fun _ => (1:ℝ)) x‖^(2:ℝ) ∂μ) = μ.real A := by
    simp_rw [he2]
    rw [integral_indicator hA]
    simp
  rw [hl,hr] at hh
  simpa only [Real.rpow_two,Real.norm_eq_abs,sq_abs,Real.sqrt_eq_rpow,one_div] using hh

lemma setIntegral_nonneg_le_sqrt {X : Type uX} [MeasurableSpace X] (μ : Measure X)
    [IsFiniteMeasure μ] {f : X → ℝ} (hf : MemLp f 2 μ) (hn : ∀ x,0≤f x)
    (A : Set X) (hA : MeasurableSet A) :
    (∫ x in A, f x ∂μ) ≤ Real.sqrt (∫ x, (f x)^2 ∂μ)*Real.sqrt (μ.real A) := by
  simpa only [Real.norm_of_nonneg (hn _)] using setIntegral_norm_le_sqrt μ hf A hA

lemma integral_sq_le_of_error {X : Type uX} [MeasurableSpace X] (μ : Measure X)
    [IsProbabilityMeasure μ] {f : X → ℝ} (hf : MemLp f 2 μ) {ε : ℝ}
    (hε : 0≤ε) (he : (∫ x,(f x-1)^2 ∂μ) ≤ ε^2) :
    (∫ x,(f x)^2 ∂μ) ≤ (1+ε)^2 := by
  have hg : MemLp (fun x => f x-1) 2 μ := hf.sub (memLp_const 1)
  have hin : Integrable f μ := hf.integrable (by norm_num)
  have hgs := hg.integrable_sq
  have hL := integral_norm_le_sqrt μ hg
  have herr : (∫ x,f x-1 ∂μ) ≤ ε := by
    calc
      _ ≤ ∫ x,‖f x-1‖ ∂μ := integral_mono (hg.integrable (by norm_num)) (hg.norm.integrable (by norm_num)) (fun _ => le_abs_self _)
      _ ≤ Real.sqrt (∫ x,(f x-1)^2 ∂μ) := hL
      _ ≤ ε := (Real.sqrt_le_left hε).mpr he
  have hid : (∫ x,(f x)^2 ∂μ) = (∫ x,(f x-1)^2 ∂μ)+2*(∫ x,f x-1 ∂μ)+1 := by
    have hp (x : X) : (f x)^2=(f x-1)^2+2*(f x-1)+1 := by ring
    simp_rw [hp]
    have hmid : Integrable (fun x => (f x-1)^2+2*(f x-1)) μ := hgs.add ((hg.integrable (by norm_num)).const_mul 2)
    rw [integral_add hmid (integrable_const 1)]
    rw [integral_add hgs ((hg.integrable (by norm_num)).const_mul 2),integral_const_mul]
    simp
  rw [hid]
  nlinarith

open MeasureTheory Set Filter
open scoped Topology ENNReal BoundedContinuousFunction
variable {X : Type uX} [MeasurableSpace X]

lemma weightedMeasure_le_sqrt (μ : Measure X) [IsFiniteMeasure μ]
    {f : X → ℝ} (hf : MemLp f 2 μ) (hn : ∀ x, 0 ≤ f x) {C : ℝ}
    (hC : 0 ≤ C) (hb : (∫ x, (f x)^2 ∂μ) ≤ C^2)
    (A : Set X) (hA : MeasurableSet A) :
    (weightedMeasure μ f).real A ≤ C*Real.sqrt (μ.real A) := by
  rw [weightedMeasure_real_apply μ (hf.integrable (by norm_num)) hn hA]
  exact (setIntegral_nonneg_le_sqrt μ hf hn A hA).trans
    (mul_le_mul_of_nonneg_right ((Real.sqrt_le_left hC).mpr hb) (Real.sqrt_nonneg _))

lemma finiteMeasure_sqrt_uc {Y : Type uY} [MeasurableSpace Y]
    (μ : Measure X) [IsFiniteMeasure μ] (ν : ℕ → Measure Y) [∀ j, IsFiniteMeasure (ν j)]
    (T : Y → X) (_hT : Measurable T) {C : ℝ} (hC : 0 < C)
    (hb : ∀ j A, MeasurableSet A → (ν j).real (T ⁻¹' A) ≤ C*Real.sqrt (μ.real A)) :
    ∀ ε : ℝ≥0∞, ε ≠ 0 → ∃ δ : ℝ≥0∞, δ ≠ 0 ∧
      ∀ A : Set X, μ A < δ → ∀ j, ν j (T ⁻¹' A) ≤ ε := by
  intro ε hε
  by_cases htop : ε=⊤
  · exact ⟨1,by norm_num,fun _ _ _ => htop.symm ▸ le_top⟩
  have he : 0 < ε.toReal := ENNReal.toReal_pos hε htop
  refine ⟨ENNReal.ofReal ((ε.toReal/C)^2), ENNReal.ofReal_ne_zero_iff.mpr (sq_pos_of_pos (div_pos he hC)), ?_⟩
  intro A hA j
  let B := toMeasurable μ A
  have hB : MeasurableSet B := measurableSet_toMeasurable μ A
  have hμ : μ B=μ A := measure_toMeasurable A
  have hBr : μ.real B ≤ (ε.toReal/C)^2 := by
    apply (ENNReal.toReal_le_of_le_ofReal (sq_nonneg _))
    rw [hμ]
    exact hA.le
  apply le_trans (measure_mono (preimage_mono (subset_toMeasurable μ A)))
  apply (ENNReal.toReal_le_toReal (measure_ne_top _ _) htop).mp
  calc
    _ ≤ C*Real.sqrt (μ.real B) := hb j B hB
    _ ≤ C*(ε.toReal/C) := mul_le_mul_of_nonneg_left ((Real.sqrt_le_left (div_pos he hC).le).mpr hBr) hC.le
    _ = ε.toReal := mul_div_cancel₀ _ hC.ne'

lemma weightedMeasure_l1_test [TopologicalSpace X] [BorelSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] {f : X → ℝ}
    (hf : MemLp f 2 μ) (hm : Measurable f) (hn : ∀ x, 0 ≤ f x)
    (φ : X →ᵇ ℝ) :
    |(∫ x, φ x ∂weightedMeasure μ f)-(∫ x, φ x ∂μ)| ≤
      ‖φ‖*Real.sqrt (∫ x, (f x-1)^2 ∂μ) := by
  have hfi := hf.integrable (by norm_num)
  have hfg : Integrable (fun x => f x*φ x) μ := hfi.mul_bdd φ.continuous.aestronglyMeasurable (ae_of_all _ φ.norm_coe_le_norm)
  have hg : MemLp (fun x => f x-1) 2 μ := hf.sub (memLp_const 1)
  rw [weightedMeasure_integral μ hm hn φ, ←integral_sub hfg (φ.integrable μ)]
  have he : (fun x => f x*φ x-φ x) = (fun x => (f x-1)*φ x) := by ext x; ring
  rw [he]
  calc
    _ ≤ ∫ x, ‖(f x-1)*φ x‖ ∂μ := norm_integral_le_integral_norm _
    _ ≤ ∫ x, ‖φ‖*‖f x-1‖ ∂μ := by
      apply integral_mono ((hfg.sub (φ.integrable μ)).congr (ae_of_all _ (fun x => by dsimp; ring))).norm
        ((hg.norm.integrable (by norm_num)).const_mul ‖φ‖)
      intro x
      dsimp only
      rw [norm_mul,mul_comm]
      exact mul_le_mul_of_nonneg_right (φ.norm_coe_le_norm x) (norm_nonneg _)
    _ = ‖φ‖*(∫ x, ‖f x-1‖ ∂μ) := integral_const_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left (integral_norm_le_sqrt μ hg) (norm_nonneg _)

lemma weightedMeasure_test_restrict [TopologicalSpace X] [BorelSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] {f : X → ℝ}
    (hf : Integrable f μ) (_hm : Measurable f) (hn : ∀ x, 0 ≤ f x)
    (A : Set X) (hA : MeasurableSet A) (φ : X →ᵇ ℝ) :
    |(∫ x, φ x ∂(weightedMeasure μ f).restrict Aᶜ)-(∫ x, φ x ∂weightedMeasure μ f)| ≤
      ‖φ‖*(weightedMeasure μ f).real A := by
  have := weightedMeasure_finite μ hf hn
  have hi : Integrable φ (weightedMeasure μ f) := φ.integrable _
  have he := integral_add_compl hA hi
  have hsub : (∫ x, φ x ∂(weightedMeasure μ f).restrict Aᶜ)-(∫ x, φ x ∂weightedMeasure μ f) =
      -(∫ x in A, φ x ∂weightedMeasure μ f) := by linarith [he]
  rw [hsub,abs_neg]
  calc
    _ ≤ ∫ x in A, ‖φ x‖ ∂weightedMeasure μ f := norm_integral_le_integral_norm _
    _ ≤ ∫ _x in A, ‖φ‖ ∂weightedMeasure μ f := integral_mono hi.restrict.norm (integrable_const _) φ.norm_coe_le_norm
    _ = _ := by simp [mul_comm]
end

open MeasureTheory Filter Set
open scoped Topology BoundedContinuousFunction

lemma tendsto_integral_graph_error {X : Type uX} [PseudoMetricSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X]
    (ν : ℕ → FiniteMeasure (X×X)) (T : C(X,X)) (r : ℕ → ℝ)
    (hr : Tendsto r atTop (𝓝 0)) {M : ℝ} (hM : 0≤M)
    (hmass : ∀ j, (ν j : Measure (X×X)).real univ≤M)
    (hsupport : ∀ j, ∀ᵐ z ∂(ν j : Measure (X×X)), dist z.2 (T z.1)≤r j)
    (φ : (X×X) →ᵇ ℝ) :
    Tendsto (fun j => ∫ z, φ z-φ (z.1,T z.1) ∂(ν j : Measure (X×X))) atTop (𝓝 0) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  have he : 0<ε/(M+1) := div_pos hε (by linarith)
  obtain ⟨δ,hδ,hclose⟩ := Metric.uniformContinuous_iff.mp (CompactSpace.uniformContinuous_of_continuous φ.continuous) (ε/(M+1)) he
  obtain ⟨N,hN⟩ := (eventually_atTop.mp (hr.eventually_lt_const hδ))
  refine ⟨N,fun n hn => ?_⟩
  have hb : ∀ᵐ z ∂(ν n : Measure (X×X)), ‖φ z-φ (z.1,T z.1)‖≤ε/(M+1) := by
    filter_upwards [hsupport n] with z hz
    have hd : dist z (z.1,T z.1)<δ := by
      simpa only [Prod.dist_eq,dist_self, max_eq_right (dist_nonneg)] using hz.trans_lt (hN n hn)
    simpa only [dist_eq_norm] using (hclose hd).le
  calc
    _ = ‖∫ z, φ z-φ (z.1,T z.1) ∂(ν n : Measure (X×X))‖ := dist_zero_right _
    _ ≤ (ε/(M+1))*(ν n : Measure (X×X)).real univ := norm_integral_le_of_norm_le_const hb
    _ ≤ (ε/(M+1))*M := mul_le_mul_of_nonneg_left (hmass n) he.le
    _ < ε := by
      have hh : (ε/(M+1))*(M+1)=ε := div_mul_cancel₀ _ (by linarith)
      nlinarith

lemma tendsto_graph_of_fst {X : Type uX} [MetricSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X]
    (ν : ℕ → FiniteMeasure (X×X)) (μ : FiniteMeasure X) (T : C(X,X)) (r : ℕ → ℝ)
    (hr : Tendsto r atTop (𝓝 0)) {M : ℝ} (hM : 0≤M)
    (hmass : ∀ j, (ν j : Measure (X×X)).real univ≤M)
    (hsupport : ∀ j, ∀ᵐ z ∂(ν j : Measure (X×X)), dist z.2 (T z.1)≤r j)
    (hfst : Tendsto (fun j => (ν j).map Prod.fst) atTop (𝓝 μ)) :
    Tendsto ν atTop (𝓝 (μ.map (fun x => (x,T x)))) := by
  apply FiniteMeasure.tendsto_iff_forall_integral_tendsto.mpr
  intro φ
  let ψ : X →ᵇ ℝ := BoundedContinuousFunction.mkOfCompact ⟨fun x => φ (x,T x),by fun_prop⟩
  have hf := FiniteMeasure.tendsto_iff_forall_integral_tendsto.mp hfst ψ
  have hcomp : ∀ j, (∫ x, ψ x ∂((ν j).map Prod.fst : Measure X))=
      ∫ z, φ (z.1,T z.1) ∂(ν j : Measure (X×X)) := by
    intro j
    exact integral_map measurable_fst.aemeasurable ψ.continuous.measurable.aestronglyMeasurable
  have htgt : (∫ z, φ z ∂(μ.map (fun x => (x,T x)) : Measure (X×X)))=∫ x, ψ x ∂(μ : Measure X) := by
    exact integral_map (by fun_prop) φ.continuous.measurable.aestronglyMeasurable
  simp_rw [hcomp] at hf
  rw [htgt]
  have hd := tendsto_integral_graph_error ν T r hr hM hmass hsupport φ
  have hi2 (j : ℕ) : Integrable (fun z : X×X => φ (z.1,T z.1)) (ν j : Measure (X×X)) :=
    (show Continuous (fun z : X×X => φ (z.1,T z.1)) by fun_prop).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hid (j : ℕ) : (∫ z,φ z-φ (z.1,T z.1) ∂(ν j : Measure (X×X)))+
      (∫ z,φ (z.1,T z.1) ∂(ν j : Measure (X×X)))=∫ z,φ z ∂(ν j : Measure (X×X)) := by
    rw [integral_sub (φ.integrable _) (hi2 j)]
    ring
  simpa only [hid,zero_add] using hd.add hf
end CircleSampling

end

end OAI
end

section
-- module Solutions.OAIQ2_Rot.RotationWeights_GraphTransfer
attribute [-instance] _root_.OAI.CircleCoupling.labelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

universe uX uY uι uE

open MeasureTheory
open scoped ENNReal NNReal ComplexInnerProductSpace BigOperators
open MeasureTheory Filter Set Submodule
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ComplexInnerProductSpace
open MeasureTheory Filter Set
open Set
open scoped ComplexInnerProductSpace
open Set
open scoped ComplexInnerProductSpace
open MeasureTheory Set Filter Topology
open scoped BigOperators ComplexConjugate
open MeasureTheory Set Filter
open scoped BigOperators ENNReal
open Filter Set
open scoped Topology
open Filter Set
open scoped Topology
open Set MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter Set
open scoped Topology
open Set MeasureTheory
open scoped ENNReal Classical
open Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Topology
open scoped BigOperators
open scoped BigOperators
open Set
open Set
open Set
open Set MeasureTheory Filter
open scoped BigOperators ENNReal Topology Classical
open MeasureTheory Set Filter
open scoped ENNReal Topology
open MeasureTheory Set
open MeasureTheory Filter Set
open scoped Topology BoundedContinuousFunction

namespace CircleSampling

section
open MeasureTheory Set Filter
open scoped Topology ENNReal BoundedContinuousFunction
variable {X : Type uX} [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]

lemma graph_restriction_convergence
    (μ : ProbabilityMeasure X) (ν : ℕ → FiniteMeasure (X×X))
    (f g : ℕ → X → ℝ) (hf : ∀ j, MemLp (f j) 2 (μ:Measure X))
    (hg : ∀ j, MemLp (g j) 2 (μ:Measure X))
    (hfm : ∀ j, Measurable (f j)) (_hgm : ∀ j, Measurable (g j))
    (hfn : ∀ j x, 0 ≤ f j x) (hgn : ∀ j x, 0 ≤ g j x)
    (hfst : ∀ j, Measure.map Prod.fst (ν j : Measure (X×X))=weightedMeasure (μ:Measure X) (f j))
    (hsnd : ∀ j, Measure.map Prod.snd (ν j : Measure (X×X))=weightedMeasure (μ:Measure X) (g j))
    (δ : ℕ → ℝ) (hδ : Tendsto δ atTop (𝓝 0)) (hδb : ∀ j, 0 ≤ δ j ∧ δ j ≤ 1)
    (hfe : ∀ j, (∫ x, (f j x-1)^2 ∂(μ:Measure X)) ≤ (δ j)^2)
    (hge : ∀ j, (∫ x, (g j x-1)^2 ∂(μ:Measure X)) ≤ (δ j)^2)
    (A : ℕ → Set X) (hA : ∀ j, MeasurableSet (A j))
    (hAlim : Tendsto (fun j => (μ:Measure X).real (A j)) atTop (𝓝 0))
    (T : C(X,X)) (r : ℕ → ℝ) (hr : Tendsto r atTop (𝓝 0))
    (hsupport : ∀ j, ∀ᵐ z ∂(ν j:Measure (X×X)), dist z.2 (T z.1) ≤ r j) :
    let ν' := fun j => (ν j).restrict (Prod.fst ⁻¹' (A j)ᶜ)
    Tendsto ν' atTop (𝓝 ((μ.toFiniteMeasure).map (fun x => (x,T x)))) ∧
    (∀ ε : ℝ≥0∞, ε ≠ 0 → ∃ d : ℝ≥0∞, d ≠ 0 ∧
      ∀ B : Set X, (μ:Measure X) B < d → ∀ j,
      (ν' j : Measure (X×X)) (Prod.fst ⁻¹' B) ≤ ε ∧
      (ν' j : Measure (X×X)) (Prod.snd ⁻¹' B) ≤ ε) := by
  let ν' := fun j => (ν j).restrict (Prod.fst ⁻¹' (A j)ᶜ)
  have hf2 (j) : (∫ x, (f j x)^2 ∂(μ:Measure X)) ≤ 2^2 := by
    exact (integral_sq_le_of_error _ (hf j) (hδb j).1 (hfe j)).trans (by nlinarith [(hδb j).1,(hδb j).2])
  have hg2 (j) : (∫ x, (g j x)^2 ∂(μ:Measure X)) ≤ 2^2 := by
    exact (integral_sq_le_of_error _ (hg j) (hδb j).1 (hge j)).trans (by nlinarith [(hδb j).1,(hδb j).2])
  have hfle (j) (B : Set X) (hB : MeasurableSet B) :
      (ν' j:Measure (X×X)).real (Prod.fst ⁻¹' B) ≤ 2*Real.sqrt ((μ:Measure X).real B) := by
    have hm : (ν' j:Measure (X×X)) (Prod.fst ⁻¹' B) ≤ (ν j:Measure (X×X)) (Prod.fst ⁻¹' B) := Measure.restrict_le_self _
    apply le_trans (ENNReal.toReal_mono (measure_ne_top _ _) hm)
    change ((ν j:Measure (X×X)) (Prod.fst ⁻¹' B)).toReal ≤ _
    rw [←Measure.map_apply measurable_fst hB,hfst j]
    exact weightedMeasure_le_sqrt _ (hf j) (hfn j) (by norm_num) (hf2 j) B hB
  have hgle (j) (B : Set X) (hB : MeasurableSet B) :
      (ν' j:Measure (X×X)).real (Prod.snd ⁻¹' B) ≤ 2*Real.sqrt ((μ:Measure X).real B) := by
    have hm : (ν' j:Measure (X×X)) (Prod.snd ⁻¹' B) ≤ (ν j:Measure (X×X)) (Prod.snd ⁻¹' B) := Measure.restrict_le_self _
    apply le_trans (ENNReal.toReal_mono (measure_ne_top _ _) hm)
    change ((ν j:Measure (X×X)) (Prod.snd ⁻¹' B)).toReal ≤ _
    rw [←Measure.map_apply measurable_snd hB,hsnd j]
    exact weightedMeasure_le_sqrt _ (hg j) (hgn j) (by norm_num) (hg2 j) B hB
  constructor
  · have hmap (j) : Measure.map Prod.fst (ν' j:Measure (X×X))=
        (weightedMeasure (μ:Measure X) (f j)).restrict (A j)ᶜ := by
      rw [←hfst j,Measure.restrict_map measurable_fst (hA j).compl]
      rfl
    apply tendsto_graph_of_fst ν' μ.toFiniteMeasure T r hr (by norm_num : (0:ℝ) ≤ 2) ?_ ?_ ?_
    · intro j
      simpa using hfle j univ MeasurableSet.univ
    · intro j
      exact ae_restrict_of_ae (hsupport j)
    · apply FiniteMeasure.tendsto_iff_forall_integral_tendsto.mpr
      intro φ
      have hbound (j) : |(∫ x, φ x ∂((ν' j).map Prod.fst : Measure X))-(∫ x, φ x ∂(μ:Measure X))| ≤
          ‖φ‖*(δ j+2*Real.sqrt ((μ:Measure X).real (A j))) := by
        change |(∫ x, φ x ∂Measure.map Prod.fst (ν' j:Measure (X×X)))-_| ≤ _
        rw [hmap j]
        calc
          _ ≤ |(∫ x, φ x ∂(weightedMeasure (μ:Measure X) (f j)).restrict (A j)ᶜ)-
                (∫ x, φ x ∂weightedMeasure (μ:Measure X) (f j))|+
              |(∫ x, φ x ∂weightedMeasure (μ:Measure X) (f j))-(∫ x, φ x ∂(μ:Measure X))| := abs_sub_le _ _ _
          _ ≤ ‖φ‖*(weightedMeasure (μ:Measure X) (f j)).real (A j)+
              ‖φ‖*Real.sqrt (∫ x, (f j x-1)^2 ∂(μ:Measure X)) :=
            add_le_add (weightedMeasure_test_restrict _ ((hf j).integrable (by norm_num)) (hfm j) (hfn j) _ (hA j) φ)
              (weightedMeasure_l1_test _ (hf j) (hfm j) (hfn j) φ)
          _ ≤ ‖φ‖*(2*Real.sqrt ((μ:Measure X).real (A j)))+‖φ‖*δ j := by
            gcongr
            · exact weightedMeasure_le_sqrt _ (hf j) (hfn j) (by norm_num) (hf2 j) _ (hA j)
            · exact (Real.sqrt_le_left (hδb j).1).mpr (hfe j)
          _ = _ := by ring
      have ht : Tendsto (fun j => ‖φ‖*(δ j+2*Real.sqrt ((μ:Measure X).real (A j)))) atTop (𝓝 0) := by
        simpa using (hδ.add (hAlim.sqrt.const_mul 2)).const_mul ‖φ‖
      exact tendsto_iff_norm_sub_tendsto_zero.mpr (squeeze_zero (fun _ => abs_nonneg _) hbound ht)
  · intro ε hε
    obtain ⟨d,hd,hdf⟩ := finiteMeasure_sqrt_uc (μ:Measure X) (fun j => (ν' j:Measure (X×X))) Prod.fst measurable_fst (by norm_num : (0:ℝ)<2) hfle ε hε
    obtain ⟨e,he,heg⟩ := finiteMeasure_sqrt_uc (μ:Measure X) (fun j => (ν' j:Measure (X×X))) Prod.snd measurable_snd (by norm_num : (0:ℝ)<2) hgle ε hε
    exact ⟨min d e,ne_of_gt (lt_min (pos_iff_ne_zero.mpr hd) (pos_iff_ne_zero.mpr he)),
      fun B hB j => ⟨hdf B (hB.trans_le (min_le_left _ _)) j,heg B (hB.trans_le (min_le_right _ _)) j⟩⟩
end
open MeasureTheory Set Filter
open scoped ENNReal Topology

lemma orbitEquiv_symm_apply (n : ℤ) (x : CircleX) : (orbitEquiv n).symm x=CircleModel.shift modelAngle (-n) x := by
  simp [orbitEquiv,CircleModel.shift]
lemma orbitEquiv_preserving (n : ℤ) : MeasurePreserving (orbitEquiv n) volume volume := measurePreserving_add_right volume _

lemma stageGraph_fst (j : ℕ) (t : Fin ((scaleState j).1.q (scaleState j).1.d)) :
    Measure.map Prod.fst (stageGraph j t : Measure (CircleX×CircleX))=weightedMeasure volume (stageDensity true j t) :=
  finiteGraphAverage_fst _ _ _ (fun n => stageWeight_measurable true j n.val) (fun n x => (stageWeight_bounds true j n.val x).1)
    (fun n => (orbitEquiv n.val).measurable)
lemma stageGraph_snd (j : ℕ) (t : Fin ((scaleState j).1.q (scaleState j).1.d)) :
    Measure.map Prod.snd (stageGraph j t : Measure (CircleX×CircleX))=weightedMeasure volume (stageDensity false j t) := by
  have he := finiteGraphAverage_snd volume (fun n : (scaleStep j).samples t => orbitEquiv n.val)
    (fun n => orbitEquiv_preserving n.val) (fun n => stageWeight true j n.val)
    (fun n => stageWeight_measurable true j n.val) (fun n x => (stageWeight_bounds true j n.val x).1)
  change Measure.map Prod.snd (stageGraph j t : Measure (CircleX×CircleX))=_ at he
  rw [he]
  congr 1
  funext x
  apply congrArg ((Fintype.card ((scaleStep j).samples t):ℝ)⁻¹ * ·)
  apply Finset.sum_congr rfl
  intro n _
  change stageWeight true j n.val ((orbitEquiv n.val).symm x)=stageWeight false j n.val x
  rw [orbitEquiv_symm_apply,stageWeight_negative]

lemma quotient_norm_le (δ : ℝ) : ‖(δ:CircleX)‖ ≤ |δ| := by
  exact QuotientAddGroup.norm_mk_le_norm
lemma stageGraph_support (j : ℕ) (t : Fin ((scaleState j).1.q (scaleState j).1.d)) :
    ∀ᵐ z ∂(stageGraph j t:Measure (CircleX×CircleX)),
      dist z.2 (translation (gridPoint (scaleState j).1 t) z.1) ≤ gridTolerance j (scaleState j).1 := by
  have hP : MeasurableSet {z : CircleX×CircleX | dist z.2 (translation (gridPoint (scaleState j).1 t) z.1) ≤ gridTolerance j (scaleState j).1} :=
    measurableSet_le (measurable_snd.dist ((translation (gridPoint (scaleState j).1 t)).continuous.measurable.comp measurable_fst)) measurable_const
  apply finiteGraphAverage_ae volume
    (fun n : (scaleStep j).samples t => stageWeight true j n.val)
    (fun n => orbitEquiv n.val) (fun n => stageWeight_measurable true j n.val)
    (fun n => (orbitEquiv n.val).measurable) _ hP
  intro n
  apply ae_of_all
  intro x _
  obtain ⟨δ,hδ,he⟩ := (scaleStep j).orbits parameterAngle (parameterAngle_spec.2.2.2 j) t n.val n.property
  have hn : n.val•modelAngle=gridPoint (scaleState j).1 t+(δ:CircleX) := by
    change (δ:CircleX)=n.val•modelAngle-gridPoint (scaleState j).1 t at he
    exact (sub_eq_iff_eq_add.mp he.symm).trans (add_comm _ _)
  change dist (x+n.val•modelAngle) (x+gridPoint (scaleState j).1 t) ≤ _
  rw [hn,←add_assoc,dist_eq_norm,add_sub_cancel_left]
  exact ((quotient_norm_le δ).trans_eq (abs_of_pos hδ.1)).trans hδ.2.le
lemma gridTolerance_bound (j : ℕ) : 0 < gridTolerance j (scaleState j).1 ∧
    gridTolerance j (scaleState j).1 ≤ 1/((j:ℝ)+1) := by
  have hj : 0 < (j:ℝ)+1 := by positivity
  have hq : (1:ℝ) ≤ (scaleState j).1.q (scaleState j).1.d := by exact_mod_cast (scaleState j).2.qpos _ le_rfl
  have hd : 1 ≤ 1+((scaleState j).1.d:ℝ) := le_add_of_nonneg_right (Nat.cast_nonneg _)
  constructor
  · unfold gridTolerance; positivity
  · unfold gridTolerance
    apply one_div_le_one_div_of_le hj
    calc
      _ ≤ 10*((j:ℝ)+1)^2 := by nlinarith [sq_nonneg (j:ℝ)]
      _ ≤ 10*((j:ℝ)+1)^2*(1+((scaleState j).1.d:ℝ)) := le_mul_of_one_le_right (by positivity) hd
      _ ≤ _ := le_mul_of_one_le_right (by positivity) hq
lemma gridTolerance_tendsto : Tendsto (fun j => gridTolerance j (scaleState j).1) atTop (𝓝 0) :=
  squeeze_zero (fun j => (gridTolerance_bound j).1.le) (fun j => (gridTolerance_bound j).2)
    tendsto_one_div_add_atTop_nhds_zero_nat

lemma rationalIndex_spec (D : ℕ) (a : Fin (frequency (D+1))) (j : ℕ) :
    gridPoint (scaleState (D+1+j)).1 (rationalIndex D a j)=rationalPoint D a :=
  (rational_stage_index D (D+1+j) a (le_trans (by omega) (blockEnd_ge _))).choose_spec

lemma rationalGraph_convergence (D : ℕ) (a : Fin (frequency (D+1))) :
    Tendsto (rationalGraph D a) atTop (𝓝 (circleProbability.toFiniteMeasure.map (fun x => (x,translation (rationalPoint D a) x)))) ∧
    (∀ ε : ℝ≥0∞, ε≠0 → ∃ d : ℝ≥0∞, d≠0 ∧ ∀ B : Set CircleX, volume B<d → ∀ j,
      (rationalGraph D a j:Measure (CircleX×CircleX)) (Prod.fst ⁻¹' B) ≤ ε ∧
      (rationalGraph D a j:Measure (CircleX×CircleX)) (Prod.snd ⁻¹' B) ≤ ε) := by
  have hs : Tendsto (fun j : ℕ => D+1+j) atTop atTop := by simpa only [Nat.add_comm] using tendsto_add_atTop_nat (D+1)
  apply graph_restriction_convergence circleProbability
    (fun j => stageGraph (D+1+j) (rationalIndex D a j))
    (fun j => stageDensity true (D+1+j) (rationalIndex D a j))
    (fun j => stageDensity false (D+1+j) (rationalIndex D a j))
    (fun j => stageDensity_memLp _ _ _) (fun j => stageDensity_memLp _ _ _)
    (fun j => stageDensity_measurable _ _ _) (fun j => stageDensity_measurable _ _ _)
    (fun j => stageDensity_nonneg _ _ _) (fun j => stageDensity_nonneg _ _ _)
    (fun j => stageGraph_fst _ _) (fun j => stageGraph_snd _ _)
    (fun j => 1/(((D+1+j:ℕ):ℝ)+1)) ?_ ?_ ?_ ?_
    (fun j => graphBad (D+1+j)) (fun j => graphBad_measurable _) (graphBad_tendsto.comp hs)
    (translation (rationalPoint D a)) (fun j => gridTolerance (D+1+j) (scaleState (D+1+j)).1)
    (gridTolerance_tendsto.comp hs) ?_
  · exact (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜:=ℝ)).comp hs
  · intro j
    refine ⟨by positivity, ?_⟩
    simpa using (one_div_le_one_div_of_le (by norm_num : (0:ℝ)<1) (le_add_of_nonneg_left (Nat.cast_nonneg (D+1+j))))
  · intro j
    simpa only [one_div_pow,circleProbability,ProbabilityMeasure.coe_mk] using (stageDensity_energy true (D+1+j) (rationalIndex D a j)).le
  · intro j
    simpa only [one_div_pow,circleProbability,ProbabilityMeasure.coe_mk] using (stageDensity_energy false (D+1+j) (rationalIndex D a j)).le
  · intro j
    simpa only [rationalIndex_spec] using stageGraph_support (D+1+j) (rationalIndex D a j)
end CircleSampling

open MeasureTheory Set Filter Topology TopologicalSpace
namespace ContinuousCircleWeight

section

theorem continuousOn_compact_graph {X : Type uX} {Y : Type uY} [TopologicalSpace X]
    [TopologicalSpace Y] [T2Space X] (f : X → Y) {K : Set (X × Y)}
    (hK : IsCompact K) (hgraph : ∀ p ∈ K, p.2 = f p.1) :
    ContinuousOn f (Prod.fst '' K) := by
  let E : Set X := Prod.fst '' K
  have hpoint : ∀ x ∈ E, (x, f x) ∈ K := by
    rintro x ⟨p, hp, rfl⟩
    simpa only [← hgraph p hp, Prod.eta] using hp
  let e : K ≃ E :=
    { toFun := fun p => ⟨p.1.1, ⟨p.1, p.2, rfl⟩⟩
      invFun := fun x => ⟨(x.1, f x.1), hpoint x.1 x.2⟩
      left_inv := by
        intro p
        apply Subtype.ext
        exact Prod.ext rfl (hgraph p.1 p.2).symm
      right_inv := by intro x; rfl }
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have he : Continuous e := (continuous_fst.comp continuous_subtype_val).subtype_mk _
  have he' : Continuous e.symm := he.continuous_symm_of_equiv_compact_to_t2
  rw [continuousOn_iff_continuous_domRestrict]
  exact continuous_snd.comp (continuous_subtype_val.comp he')

theorem measurable_lusin_compact {X : Type uX} {Y : Type uY} [TopologicalSpace X]
    [TopologicalSpace Y] [PolishSpace X] [PolishSpace Y]
    [MeasurableSpace X] [MeasurableSpace Y] [BorelSpace X] [BorelSpace Y]
    {μ : Measure X} [IsFiniteMeasure μ] {f : X → Y} (hf : Measurable f)
    {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ E : Set X, IsCompact E ∧ μ Eᶜ < ε ∧ ContinuousOn f E := by
  let g : X → X × Y := fun x => (x, f x)
  have hg : Measurable g := measurable_id.prodMk hf
  let G : Set (X × Y) := {p | p.2 = f p.1}
  have hG : MeasurableSet G := measurableSet_eq_fun measurable_snd (hf.comp measurable_fst)
  let ν := μ.map g
  obtain ⟨K, hKG, hK, hsmall⟩ := hG.exists_isCompact_sdiff_lt (measure_ne_top ν G) hε
  have hpre : g ⁻¹' (G \ K) = (Prod.fst '' K)ᶜ := by
    ext x
    simp only [mem_preimage, Set.mem_sdiff, mem_ofPred_eq, g, G, mem_compl_iff,
      true_and]
    constructor
    · intro hx hproj
      obtain ⟨p, hp, hpx⟩ := hproj
      apply hx
      convert hp using 1
      exact Prod.ext hpx.symm (by simpa only [mem_ofPred_eq, G, hpx] using (hKG hp).symm)
    · intro hx hxp
      exact hx ⟨(x, f x), hxp, rfl⟩
  rw [Measure.map_apply hg (hG.diff hK.isClosed.measurableSet), hpre] at hsmall
  refine ⟨Prod.fst '' K, hK.image continuous_fst, hsmall, ?_⟩
  exact continuousOn_compact_graph f hK (fun _ hp => hKG hp)

theorem finiteMeasure_compl_le_of_tendsto {X : Type uX} [TopologicalSpace X]
    [MeasurableSpace X] [OpensMeasurableSpace X] [HasOuterApproxClosed X]
    {ν : FiniteMeasure X} {νs : ℕ → FiniteMeasure X}
    (hlim : Tendsto νs atTop (𝓝 ν)) {K : Set X} (hK : IsClosed K)
    {ε : ℝ≥0∞} (hsmall : ∀ n, (νs n : Measure X) Kᶜ ≤ ε) :
    (ν : Measure X) Kᶜ ≤ ε := by
  have hmass : Tendsto (fun n => (νs n : Measure X) univ) atTop
      (𝓝 ((ν : Measure X) univ)) := by
    simpa only [← FiniteMeasure.ennreal_mass, Function.comp_def] using
      (ENNReal.continuous_coe.tendsto ν.mass).comp hlim.mass
  have hpoint : ∀ n, (νs n : Measure X) univ ≤ (νs n : Measure X) K + ε := by
    intro n
    calc
      _ = (νs n : Measure X) K + (νs n : Measure X) Kᶜ :=
        (measure_add_measure_compl hK.measurableSet).symm
      _ ≤ _ := add_le_add le_rfl (hsmall n)
  have hbound : (ν : Measure X) univ ≤ (ν : Measure X) K + ε := by
    calc
      _ = atTop.limsup (fun n => (νs n : Measure X) univ) := hmass.limsup_eq.symm
      _ ≤ atTop.limsup (fun n => (νs n : Measure X) K + ε) :=
        limsup_le_limsup (Eventually.of_forall hpoint)
      _ = atTop.limsup (fun n => (νs n : Measure X) K) + ε :=
        limsup_add_const _ _ _ (by isBoundedDefault) (by isBoundedDefault)
      _ ≤ _ := add_le_add
        (FiniteMeasure.limsup_measure_closed_le_of_tendsto hlim hK) le_rfl
  rw [measure_compl hK.measurableSet (measure_ne_top _ _)]
  exact tsub_le_iff_right.mpr (by simpa only [add_comm] using hbound)

theorem compact_relation_transfer {X : Type uX} [TopologicalSpace X] [T2Space X]
    [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X] [HasOuterApproxClosed (X × X)]
    {μ : Measure X} {ν : FiniteMeasure (X × X)} {νs : ℕ → FiniteMeasure (X × X)}
    (hlim : Tendsto νs atTop (𝓝 ν)) {Z : Set (X × X)}
    (hgood : ∀ n, (νs n : Measure (X × X)) Zᶜ = 0)
    (huc : ∀ ε : ℝ≥0∞, ε ≠ 0 → ∃ δ : ℝ≥0∞, δ ≠ 0 ∧
      ∀ A : Set X, μ A < δ → ∀ n,
        (νs n : Measure (X × X)) (Prod.fst ⁻¹' A) ≤ ε ∧
        (νs n : Measure (X × X)) (Prod.snd ⁻¹' A) ≤ ε)
    (happrox : ∀ δ : ℝ≥0∞, δ ≠ 0 → ∃ E : Set X,
      μ Eᶜ < δ ∧ IsCompact ((E ×ˢ E) ∩ Z)) :
    (ν : Measure (X × X)) Zᶜ = 0 := by
  apply le_antisymm ?_ bot_le
  apply ENNReal.le_of_forall_pos_le_add
  intro ε hε _
  have heps : (ε : ℝ≥0∞) / 2 ≠ 0 :=
    (ENNReal.half_pos (ENNReal.coe_ne_zero.mpr hε.ne.symm)).ne.symm
  obtain ⟨δ, hδ, hδsmall⟩ := huc ((ε : ℝ≥0∞) / 2) heps
  obtain ⟨E, hEμ, hEK⟩ := happrox δ hδ
  let K := (E ×ˢ E) ∩ Z
  have hKsmall : ∀ n, (νs n : Measure (X × X)) Kᶜ ≤ ε := by
    intro n
    have hsub : Kᶜ ⊆ (Prod.fst ⁻¹' Eᶜ) ∪ (Prod.snd ⁻¹' Eᶜ) ∪ Zᶜ := by
      intro p hp
      simp only [K, mem_compl_iff, mem_inter_iff, mem_prod] at hp
      simp only [mem_union, mem_preimage, mem_compl_iff]
      tauto
    calc
      _ ≤ (νs n : Measure (X × X))
          ((Prod.fst ⁻¹' Eᶜ) ∪ (Prod.snd ⁻¹' Eᶜ) ∪ Zᶜ) := measure_mono hsub
      _ ≤ (νs n : Measure (X × X)) ((Prod.fst ⁻¹' Eᶜ) ∪ (Prod.snd ⁻¹' Eᶜ)) +
          (νs n : Measure (X × X)) Zᶜ := measure_union_le _ _
      _ ≤ ((νs n : Measure (X × X)) (Prod.fst ⁻¹' Eᶜ) +
          (νs n : Measure (X × X)) (Prod.snd ⁻¹' Eᶜ)) + 0 :=
        add_le_add (measure_union_le _ _) (hgood n).le
      _ ≤ ((ε : ℝ≥0∞) / 2 + (ε : ℝ≥0∞) / 2) + 0 :=
        add_le_add (add_le_add (hδsmall Eᶜ hEμ n).1 (hδsmall Eᶜ hEμ n).2) le_rfl
      _ = ε := by simp
  have hlimK := finiteMeasure_compl_le_of_tendsto hlim hEK.isClosed hKsmall
  simpa only [ENNReal.bot_eq_zero, zero_add] using (measure_mono (compl_subset_compl.mpr
    (show K ⊆ Z from inter_subset_right))).trans hlimK

lemma continuous_bounded_field_apply {X : Type uX} [TopologicalSpace X]
    {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (A : X → (E →L[ℂ] E)) {C : ℝ} (_hC : 0 ≤ C)
    (hb : ∀ x, ‖A x‖ ≤ C) (hA : ∀ u, Continuous (fun x ↦ A x u))
    {v : X → E} (hv : Continuous v) : Continuous (fun x ↦ A x (v x)) := by
  rw [continuous_iff_continuousAt]
  intro x
  have hzero : Tendsto (fun y ↦ A y (v y-v x)) (𝓝 x) (𝓝 0) := by
    apply squeeze_zero_norm (a := fun y ↦ C * ‖v y-v x‖)
    · intro y
      exact (A y).le_opNorm _ |>.trans (mul_le_mul_of_nonneg_right (hb y) (norm_nonneg _))
    · have ht : Tendsto (fun y ↦ ‖v y-v x‖) (𝓝 x) (𝓝 0) := by
        simpa only [sub_self, norm_zero] using ((hv.tendsto x).sub_const (v x)).norm
      simpa only [mul_zero] using tendsto_const_nhds.mul ht
  have hsum := hzero.add (hA (v x)).continuousAt
  change Tendsto (fun y ↦ A y (v y)) (𝓝 x) (𝓝 (A x (v x)))
  simpa only [map_sub, sub_add_cancel, zero_add] using hsum

lemma continuous_cappedDiagonal {X : Type uX} [TopologicalSpace X]
    (F : ℤ → X → ℝ) (hF : ∀ k, Continuous (F k)) (hp : ∀ k x, 0 < F k x)
    (B : ℝ≥0) (u : FiberHilbert) :
    Continuous (fun z : X × X ↦ cappedDiagonal F B z.1 z.2 u) := by
  apply continuous_bounded_lp_field _ B.coe_nonneg (fun _ ↦ lpDiagonal_norm_le _ _) _ u
  intro k
  have he : (fun z : X × X ↦ cappedDiagonal F B z.1 z.2 (lp.single 2 k 1)) =
      (fun z ↦ (cappedRatio F B z.1 z.2 k : ℂ) • lp.single 2 k 1) := by
    funext z
    ext i
    simp only [cappedDiagonal, lpDiagonal_apply, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
    by_cases hi : i=k
    · subst i; simp
    · simp [lp.single_apply, hi]
  change Continuous (fun z : X × X ↦ cappedDiagonal F B z.1 z.2 (lp.single 2 k 1))
  rw [he]
  have hr : Continuous (fun z : X × X ↦ cappedRatio F B z.1 z.2 k) :=
    continuous_const.min (continuous_const.max
      (((hF k).comp continuous_snd).div ((hF k).comp continuous_fst) (fun z ↦ (hp k z.1).ne')))
  exact (Complex.continuous_ofReal.comp hr).smul
    (continuous_const : Continuous (fun _ : X × X ↦ (lp.single 2 k 1 : FiberHilbert)))

attribute [local instance] OAI.ContinuousCircleWeight.fiberMeasurable
local instance fiberBorel : BorelSpace FiberHilbert := ⟨rfl⟩

lemma cappedPairRelation_iff {X : Type uX} (p : X → FiberOperator) (F : ℤ → X → ℝ)
    (B : ℝ≥0) (x y : X) :
    (x,y) ∈ cappedPairRelation p F B ↔ (1-p y)*cappedDiagonal F B x y*p x=0 := by
  constructor
  · intro h
    apply lp.ext_continuousLinearMap (by norm_num)
    intro k
    apply ContinuousLinearMap.ext
    intro a
    have he : lp.single (E := fun _ : ℤ ↦ ℂ) 2 k a = a • lp.single 2 k (1 : ℂ) := by
      simpa using (lp.single_smul (E := fun _ : ℤ ↦ ℂ) 2 k a (1 : ℂ))
    change (1-p y) (cappedDiagonal F B x y (p x (lp.single 2 k a))) = 0
    simp only [he, map_smul]
    change a • ((1-p y) (cappedDiagonal F B x y (p x (lp.single 2 k 1)))) = 0
    rw [h k, smul_zero]
  · intro h k
    have he := congrArg (fun a : FiberOperator ↦ a (lp.single 2 k 1)) h
    exact he

lemma cappedPairRelation_compact_approx {X : Type uX} [TopologicalSpace X] [PolishSpace X]
    [MeasurableSpace X] [BorelSpace X] {μ : Measure X} [IsFiniteMeasure μ]
    (p : X → FiberOperator) (hp : ∀ x, ‖p x‖ ≤ 1)
    (hpm : ∀ k : ℤ, Measurable (fun x ↦ p x (lp.single 2 k 1)))
    (F : ℤ → X → ℝ) (hFm : ∀ k, Measurable (F k)) (hFp : ∀ k x, 0 < F k x)
    (B : ℝ≥0) {δ : ℝ≥0∞} (hδ : δ ≠ 0) :
    ∃ E : Set X, μ Eᶜ < δ ∧ IsCompact ((E ×ˢ E) ∩ cappedPairRelation p F B) := by
  let f : X → (ℤ → FiberHilbert) × (ℤ → ℝ) :=
    fun x ↦ ((fun k ↦ p x (lp.single 2 k 1)), fun k ↦ F k x)
  have hfm : Measurable f := (Measurable.of_eval hpm).prodMk (Measurable.of_eval hFm)
  obtain ⟨E,hEc,hEμ,hEf⟩ := measurable_lusin_compact hfm (μ := μ) hδ
  refine ⟨E,hEμ,?_⟩
  let : CompactSpace E := isCompact_iff_compactSpace.mp hEc
  have hfc : Continuous (fun x : E ↦ f x) := continuousOn_iff_continuous_domRestrict.mp hEf
  have hpc : ∀ k, Continuous (fun x : E ↦ p x (lp.single 2 k 1)) :=
    fun k ↦ (continuous_apply k).comp hfc.fst
  have hFc : ∀ k, Continuous (fun x : E ↦ F k x) :=
    fun k ↦ (continuous_apply k).comp hfc.snd
  have hpstrong : ∀ u : FiberHilbert, Continuous (fun x : E ↦ p x u) :=
    continuous_bounded_lp_field (fun x : E ↦ p x) zero_le_one (fun x ↦ hp x) hpc
  have hDc : ∀ u : FiberHilbert, Continuous (fun z : E × E ↦ cappedDiagonal F B z.1 z.2 u) :=
    continuous_cappedDiagonal (fun k (x : E) ↦ F k x) hFc (fun k x ↦ hFp k x) B
  have hqc : ∀ u : FiberHilbert, Continuous (fun z : E × E ↦ (1-p z.2) u) := by
    intro u
    change Continuous (fun z : E × E ↦ u-p z.2 u)
    exact continuous_const.sub ((hpstrong u).comp continuous_snd)
  have hqb : ∀ z : E × E, ‖1-p z.2‖ ≤ 2 := by
    intro z
    calc
      ‖1-p z.2‖ ≤ ‖(1 : FiberOperator)‖ + ‖p z.2‖ := norm_sub_le _ _
      _ ≤ 1 + 1 := add_le_add (ContinuousLinearMap.norm_id_le) (hp z.2)
      _ = 2 := by norm_num
  let T : ℤ → E × E → FiberHilbert :=
    fun k z ↦ (1-p z.2) (cappedDiagonal F B z.1 z.2 (p z.1 (lp.single 2 k 1)))
  have hTc : ∀ k, Continuous (T k) := by
    intro k
    apply continuous_bounded_field_apply (fun z : E × E ↦ 1-p z.2) (by norm_num) hqb hqc
    apply continuous_bounded_field_apply (fun z : E × E ↦ cappedDiagonal F B z.1 z.2)
      B.coe_nonneg (fun _ ↦ lpDiagonal_norm_le _ _) hDc
    exact (hpc k).comp continuous_fst
  have hK : IsCompact {z : E × E | ∀ k, T k z=0} := by
    have hc : IsClosed {z : E × E | ∀ k, T k z=0} := by
      simpa only [funext_iff, Pi.zero_apply] using
        (isClosed_eq (continuous_pi hTc)
          (continuous_const : Continuous (fun _ : E × E ↦ (0 : ℤ → FiberHilbert))))
    exact hc.isCompact
  let e : E × E → X × X := fun z ↦ (z.1.val,z.2.val)
  have he : Continuous e :=
    (continuous_subtype_val.comp continuous_fst).prodMk (continuous_subtype_val.comp continuous_snd)
  have hset : (E ×ˢ E) ∩ cappedPairRelation p F B = e '' {z : E × E | ∀ k,T k z=0} := by
    ext z
    constructor
    · rintro ⟨⟨hx,hy⟩,hz⟩
      exact ⟨(⟨z.1,hx⟩,⟨z.2,hy⟩),hz,rfl⟩
    · rintro ⟨⟨x,y⟩,hxy,rfl⟩
      exact ⟨⟨x.property,y.property⟩,hxy⟩
  rw [hset]
  exact hK.image he

theorem capped_pair_identity_transfer {X : Type uX} [TopologicalSpace X] [PolishSpace X]
    [MeasurableSpace X] [BorelSpace X] {μ : Measure X} [IsFiniteMeasure μ]
    (p : X → FiberOperator) (hp : ∀ x, ‖p x‖ ≤ 1)
    (hpm : ∀ k : ℤ, Measurable (fun x ↦ p x (lp.single 2 k 1)))
    (F : ℤ → X → ℝ) (hFm : ∀ k, Measurable (F k)) (hFp : ∀ k x, 0 < F k x)
    (B : ℝ≥0) {ν : FiniteMeasure (X × X)} {νs : ℕ → FiniteMeasure (X × X)}
    (hlim : Tendsto νs atTop (𝓝 ν))
    (hgood : ∀ n, ∀ᵐ z ∂(νs n : Measure (X × X)),
      (1-p z.2)*cappedDiagonal F B z.1 z.2*p z.1=0)
    (huc : ∀ ε : ℝ≥0∞, ε ≠ 0 → ∃ δ : ℝ≥0∞, δ ≠ 0 ∧
      ∀ A : Set X, μ A < δ → ∀ n,
        (νs n : Measure (X × X)) (Prod.fst ⁻¹' A) ≤ ε ∧
        (νs n : Measure (X × X)) (Prod.snd ⁻¹' A) ≤ ε) :
    ∀ᵐ z ∂(ν : Measure (X × X)), (1-p z.2)*cappedDiagonal F B z.1 z.2*p z.1=0 := by
  have hr : (ν : Measure (X × X)) (cappedPairRelation p F B)ᶜ=0 := by
    apply compact_relation_transfer hlim (μ := μ) ?_ huc
      (fun _ hδ ↦ cappedPairRelation_compact_approx p hp hpm F hFm hFp B hδ)
    intro n
    have hg : ∀ᵐ z ∂(νs n : Measure (X × X)), z ∈ cappedPairRelation p F B :=
      (hgood n).mono fun z hz ↦ (cappedPairRelation_iff p F B z.1 z.2).mpr hz
    exact ae_iff.mp hg
  have hg : ∀ᵐ z ∂(ν : Measure (X × X)), z ∈ cappedPairRelation p F B := ae_iff.mpr hr
  exact hg.mono fun z hz ↦ (cappedPairRelation_iff p F B z.1 z.2).mp hz

end

open MeasureTheory Set
open scoped ComplexConjugate

lemma cappedDiagonal_apply_of_bound {X : Type uX} (F : ℤ → X → ℝ) (hF : ∀ k x, 0 < F k x)
    (B : ℝ≥0) (x y : X) (hb : ∀ k, F k y/F k x ≤ B) (v : FiberHilbert) (k : ℤ) :
    cappedDiagonal F B x y v k=(F k y/F k x:ℝ)*v k := by
  change (cappedRatio F B x y k:ℂ)*v k=_
  rw [cappedRatio,max_eq_right (div_pos (hF k y) (hF k x)).le,min_eq_right (hb k)]

lemma positive_orbit_capped_pair {X : Type uX} (F : ℤ → X → ℝ) (hF : ∀ k x,0 < F k x)
    (hmono : ∀ x,Antitone (fun k => F k x)) (x y : X) (n : ℕ)
    (hrel : ∀ k, F (k+n) x=F k y*F n x)
    (p q : FiberOperator) (hp : IsStarProjection p)
    (hinv : (1-p)*fiberCocycleShift (fun k => F k x) (fun k => hF k x) (hmono x)*p=0)
    (hcov : p*(fiberShift n).toContinuousLinearEquiv.toContinuousLinearMap=
      (fiberShift n).toContinuousLinearEquiv.toContinuousLinearMap*q)
    (B : ℝ≥0) (hb : ∀ k,F k y/F k x ≤ B) :
    (1-q)*cappedDiagonal F B x y*p=0 := by
  have he (v : FiberHilbert) : fiberShift n (cappedDiagonal F B x y v)=
      ((F n x)⁻¹:ℂ) • (fiberCocycleShift (fun k => F k x) (fun k => hF k x) (hmono x)^n) v := by
    apply lp.ext
    funext k
    rw [fiberShift_apply,cappedDiagonal_apply_of_bound F hF B x y hb,lp.coeFn_smul,Pi.smul_apply,smul_eq_mul,
      fiberCocycleShift_pow_apply]
    have hr := hrel (k-n)
    rw [sub_add_cancel] at hr
    rw [hr]
    push_cast
    field_simp [Complex.ofReal_ne_zero.mpr (hF (n:ℤ) x).ne', Complex.ofReal_ne_zero.mpr (hF (k-n) x).ne']
  apply ContinuousLinearMap.ext
  intro v
  change cappedDiagonal F B x y (p v)-q (cappedDiagonal F B x y (p v))=0
  apply sub_eq_zero.mpr
  apply (fiberShift n).injective
  have hv : p (p v)=p v := by
    have h := congrArg (fun A : FiberOperator => A v) hp.isIdempotentElem
    exact h
  have hfix := invariant_fixed_vector_pow hinv hv n
  have hc := congrArg (fun A : FiberOperator => A (cappedDiagonal F B x y (p v))) hcov
  change p (fiberShift n (cappedDiagonal F B x y (p v)))=
    fiberShift n (q (cappedDiagonal F B x y (p v))) at hc
  rw [he,map_smul,hfix] at hc
  exact (he (p v)).trans hc
end ContinuousCircleWeight

end

end OAI
end

section
-- module Solutions.OAIQ2_Rot.RotationWeights_ProjectionIdentity
attribute [-instance] _root_.OAI.CircleCoupling.labelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

universe uX uE

open MeasureTheory
open scoped ENNReal NNReal ComplexInnerProductSpace BigOperators
open MeasureTheory Filter Set Submodule
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ComplexInnerProductSpace
open MeasureTheory Filter Set
open Set
open scoped ComplexInnerProductSpace
open Set
open scoped ComplexInnerProductSpace
open MeasureTheory Set Filter Topology
open scoped BigOperators ComplexConjugate
open MeasureTheory Set Filter
open scoped BigOperators ENNReal
open Filter Set
open scoped Topology
open Filter Set
open scoped Topology
open Set MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter Set
open scoped Topology
open Set MeasureTheory
open scoped ENNReal Classical
open Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Topology
open scoped BigOperators
open scoped BigOperators
open Set
open Set
open Set
open Set MeasureTheory Filter
open scoped BigOperators ENNReal Topology Classical
open MeasureTheory Set Filter
open scoped ENNReal Topology
open MeasureTheory Set
open MeasureTheory Filter Set
open scoped Topology BoundedContinuousFunction
open MeasureTheory Set Filter Topology TopologicalSpace

namespace CircleSampling
open MeasureTheory Set Filter ContinuousCircleWeight
open scoped ComplexInnerProductSpace Topology ENNReal
lemma rationalCap_ge_one (D : ℕ) : (1:ℝ) ≤ rationalCap D := by
  apply Real.one_le_exp_iff.mpr
  exact Finset.sum_nonneg (fun i _ => dropSize_nonneg _)

lemma stageGraph_ae (j : ℕ) (t : Fin ((scaleState j).1.q (scaleState j).1.d))
    (P : CircleX×CircleX → Prop)
    (hP : ∀ n : (scaleStep j).samples t, ∀ᵐ x,stageWeight true j n.val x≠0 → P (x,orbitEquiv n.val x)) :
    ∀ᵐ z ∂(stageGraph j t:Measure (CircleX×CircleX)), P z := by
  change ∀ᵐ z ∂finiteGraphAverage volume (fun n : (scaleStep j).samples t => stageWeight true j n.val) (fun n => orbitEquiv n.val), P z
  unfold finiteGraphAverage
  apply Measure.ae_smul_measure
  apply ae_finsetSum_measure_iff.mpr
  intro n _
  rw [weightedGraph]
  have he : MeasurableEmbedding (fun x : CircleX => (x,orbitEquiv n.val x)) :=
    (measurable_id.prodMk (orbitEquiv n.val).measurable).measurableEmbedding (fun _ _ h => congrArg Prod.fst h)
  apply he.ae_map_iff.mpr
  rw [weightedMeasure,ae_withDensity_iff (stageWeight_measurable true j n.val).ennreal_ofReal]
  filter_upwards [hP n] with x hx hn
  apply hx
  intro hz
  exact hn (by simp [hz])

lemma rationalGraph_pair (P : ModelProjectionField) (D : ℕ) (a : Fin (frequency (D+1))) (j : ℕ) :
    ∀ᵐ z ∂(rationalGraph D a j:Measure (CircleX×CircleX)),
      (1-P.p z.2)*cappedDiagonal modelF (rationalCap D) z.1 z.2*P.p z.1=0 := by
  let N := D+1+j
  let t := rationalIndex D a j
  have hg : ∀ᵐ z ∂(stageGraph N t:Measure (CircleX×CircleX)), z.1∉graphBad N →
      (1-P.p z.2)*cappedDiagonal modelF (rationalCap D) z.1 z.2*P.p z.1=0 := by
    apply stageGraph_ae N t
    intro n
    filter_upwards [model_good_ae,P.invariant,P.covariance n.val] with x hx hi hc hw hbad
    have hn : (n.val.toNat:ℤ)=n.val := Int.toNat_of_nonneg (sample_bound N n.property).1.le
    have hb (k : ℤ) : modelF k (CircleModel.shift modelAngle n.val x)/modelF k x ≤ rationalCap D :=
      modelF_ratio_tail D hx ((modelGood_shift n.val x).mpr hx)
        (restricted_orbit_order N D (rationalPoint D a) (rational_tail_period D a) t
          (rationalIndex_spec D a j) n.val n.property x hbad hw) k
    have hr (k : ℤ) : modelF (k+(n.val.toNat:ℤ)) x=modelF k (CircleModel.shift modelAngle (n.val.toNat:ℤ) x)*modelF (n.val.toNat:ℤ) x := by
      simpa only [add_comm k] using modelF_add (n.val.toNat:ℤ) k x
    have hh := positive_orbit_capped_pair modelF modelF_pos modelF_antitone x (CircleModel.shift modelAngle n.val x) n.val.toNat
      (by simpa only [hn] using hr) (P.p x) (P.p (CircleModel.shift modelAngle n.val x)) (P.projection x) hi
      (by simpa only [hn] using hc) (rationalCap D) hb
    exact hh
  change ∀ᵐ z ∂(stageGraph N t:Measure (CircleX×CircleX)).restrict (Prod.fst ⁻¹' (graphBad N)ᶜ), _
  rw [ae_restrict_iff' ((graphBad_measurable N).compl.preimage measurable_fst)]
  exact hg

lemma rational_pair_graph (P : ModelProjectionField) (D : ℕ) (a : Fin (frequency (D+1))) :
    ∀ᵐ z ∂(circleProbability.toFiniteMeasure.map (fun x => (x,translation (rationalPoint D a) x)) : Measure (CircleX×CircleX)),
      (1-P.p z.2)*cappedDiagonal modelF (rationalCap D) z.1 z.2*P.p z.1=0 := by
  exact capped_pair_identity_transfer (μ := volume) (νs := rationalGraph D a) P.p P.norm_le P.measurable modelF modelF_measurable modelF_pos
    (rationalCap D) (rationalGraph_convergence D a).1 (rationalGraph_pair P D a) (rationalGraph_convergence D a).2

lemma rational_pair (P : ModelProjectionField) (D : ℕ) (a : Fin (frequency (D+1))) :
    ∀ᵐ x, (1-P.p (x+rationalPoint D a))*cappedDiagonal modelF (rationalCap D) x (x+rationalPoint D a)*P.p x=0 := by
  have hh := rational_pair_graph P D a
  change ∀ᵐ z ∂Measure.map (fun x : CircleX => (x,x+rationalPoint D a)) volume, _ at hh
  exact ae_of_ae_map (p := fun z : CircleX×CircleX =>
    (1-P.p z.2)*cappedDiagonal modelF (rationalCap D) z.1 z.2*P.p z.1=0) (show AEMeasurable (fun x : CircleX => (x,x+rationalPoint D a)) volume from
    (measurable_id.prodMk (measurable_id.add_const _)).aemeasurable) hh
end CircleSampling

namespace ContinuousCircleWeight
open MeasureTheory Filter Set
open scoped Topology ComplexInnerProductSpace
attribute [local instance] OAI.ContinuousCircleWeight.instMeasurableSpaceSubtypePreLpIntComplexMemAddSubgroupFiberHilbert_1
local instance instBorelSpaceSubtypePreLpIntComplexMemAddSubgroupFiberHilbert_1 : BorelSpace FiberHilbert := ⟨rfl⟩

lemma stronglyMeasurable_lp_field {X : Type uX} [MeasurableSpace X]
    (A : X → FiberOperator)
    (hc : ∀ k : ℤ, Measurable (fun x ↦ A x (lp.single 2 k 1)))
    (u : FiberHilbert) : StronglyMeasurable (fun x ↦ A x u) := by
  classical
  let v : Finset ℤ → FiberHilbert := fun s ↦ ∑ k ∈ s, lp.single 2 k (u k)
  have hv : Tendsto v atTop (𝓝 u) := lp.hasSum_single (by norm_num) u
  apply stronglyMeasurable_of_tendsto atTop (f := fun s x => A x (v s))
  · intro s
    simp only [v,map_sum]
    apply Finset.stronglyMeasurable_fun_sum
    intro k _
    have he : lp.single (E := fun _ : ℤ ↦ ℂ) 2 k (u k) = (u k) • lp.single 2 k (1 : ℂ) := by
      simpa using (lp.single_smul (E := fun _ : ℤ ↦ ℂ) 2 k (u k) (1 : ℂ))
    simp only [he,map_smul]
    exact (hc k).stronglyMeasurable.const_smul (u k)
  · exact tendsto_pi_nhds.mpr (fun x => (A x).continuous.tendsto u |>.comp hv)

lemma stronglyMeasurable_field_simple {X : Type uX} {E : Type uE} [MeasurableSpace X]
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    (T : X → (E →L[ℂ] E)) (hT : ∀ v, StronglyMeasurable (fun x ↦ T x v)) (s : SimpleFunc X E) :
    StronglyMeasurable (fun x ↦ T x (s x)) := by
  classical
  have he : (fun x ↦ T x (s x)) = ∑ a ∈ s.range, (s ⁻¹' {a}).indicator (fun x ↦ T x a) := by
    funext x
    simp [Set.indicator, s.mem_range_self]
  rw [he]
  exact s.range.stronglyMeasurable_sum fun a _ ↦ (hT a).indicator (s.measurableSet_fiber a)

lemma stronglyMeasurable_field_apply {X : Type uX} {E : Type uE} [MeasurableSpace X]
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    (T : X → (E →L[ℂ] E)) (hT : ∀ v, StronglyMeasurable (fun x ↦ T x v))
    (f : X → E) (hf : StronglyMeasurable f) : StronglyMeasurable (fun x ↦ T x (f x)) := by
  apply stronglyMeasurable_of_tendsto atTop
    (fun n ↦ stronglyMeasurable_field_simple T hT (hf.approx n))
  exact tendsto_pi_nhds.mpr fun x ↦ ((T x).continuous.tendsto (f x)).comp (hf.tendsto_approx x)

lemma measurable_cappedDiagonal {X : Type uX} [MeasurableSpace X]
    (F : ℤ → X → ℝ) (hF : ∀ k,Measurable (F k))
    (B : ℝ≥0) (u : FiberHilbert) :
    Measurable (fun z : X×X => cappedDiagonal F B z.1 z.2 u) := by
  apply (stronglyMeasurable_lp_field _ ?_ u).measurable
  intro k
  have he : (fun z : X × X ↦ cappedDiagonal F B z.1 z.2 (lp.single 2 k 1)) =
      (fun z ↦ (cappedRatio F B z.1 z.2 k : ℂ) • lp.single 2 k 1) := by
    funext z
    ext i
    simp only [cappedDiagonal,lpDiagonal_apply,lp.coeFn_smul,Pi.smul_apply,smul_eq_mul]
    by_cases hi : i=k
    · subst i; simp
    · simp [lp.single_apply,hi]
  rw [he]
  have hr : Measurable (fun z : X×X => cappedRatio F B z.1 z.2 k) :=
    measurable_const.min (measurable_const.max (((hF k).comp measurable_snd).div ((hF k).comp measurable_fst)))
  exact hr.complex_ofReal.smul measurable_const

lemma measurableSet_cappedPairRelation {X : Type uX} [MeasurableSpace X]
    (p : X → FiberOperator) (hp : ∀ k : ℤ,Measurable (fun x => p x (lp.single 2 k 1)))
    (F : ℤ → X → ℝ) (hF : ∀ k,Measurable (F k)) (B : ℝ≥0) :
    MeasurableSet (cappedPairRelation p F B) := by
  unfold cappedPairRelation
  simp only [Set.ofPred_forall]
  apply MeasurableSet.iInter
  intro k
  have hp' : ∀ u,StronglyMeasurable (fun z : X×X => p z.2 u) := fun u =>
    (stronglyMeasurable_lp_field p hp u).comp_measurable measurable_snd
  have hD : ∀ u,StronglyMeasurable (fun z : X×X => cappedDiagonal F B z.1 z.2 u) := fun u =>
    (measurable_cappedDiagonal F hF B u).stronglyMeasurable
  have hu : StronglyMeasurable (fun z : X×X => cappedDiagonal F B z.1 z.2 (p z.1 (lp.single 2 k 1))) :=
    stronglyMeasurable_field_apply _ hD _ ((hp k).comp measurable_fst).stronglyMeasurable
  have hd := hu.sub (stronglyMeasurable_field_apply _ hp' _ hu)
  exact measurableSet_eq_fun hd.measurable measurable_const
end ContinuousCircleWeight

end

end OAI
end

section
-- module Solutions.OAIQ2_Rot.RotationWeights_CouplingMoments
attribute [-instance] _root_.OAI.CircleCoupling.CoordinateParameters.instIsProbabilityMeasureSampleLaw _root_.OAI.CircleCoupling.DigitSystem.instIsProbabilityMeasureSampleLaw _root_.OAI.CircleCoupling.DigitSystem.instIsProbabilityMeasureSamplesProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CircleCoupling

universe uD uA uι uΩ

open MeasureTheory
open scoped ENNReal NNReal ComplexInnerProductSpace BigOperators
open MeasureTheory Filter Set Submodule
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ComplexInnerProductSpace
open MeasureTheory Filter Set
open Set
open scoped ComplexInnerProductSpace
open Set
open scoped ComplexInnerProductSpace
open MeasureTheory Set Filter Topology
open scoped BigOperators ComplexConjugate
open MeasureTheory Set Filter
open scoped BigOperators ENNReal
open Filter Set
open scoped Topology
open Filter Set
open scoped Topology
open Set MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter Set
open scoped Topology
open Set MeasureTheory
open scoped ENNReal Classical
open Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Topology
open scoped BigOperators
open scoped BigOperators
open Set
open Set
open Set
open Set MeasureTheory Filter
open scoped BigOperators ENNReal Topology Classical
open MeasureTheory Set Filter
open scoped ENNReal Topology
open MeasureTheory Set
open MeasureTheory Filter Set
open scoped Topology BoundedContinuousFunction
open MeasureTheory Set Filter Topology TopologicalSpace
open MeasureTheory Set
open scoped ENNReal BigOperators Classical
open MeasureTheory Set
open scoped BigOperators ENNReal Classical
section

lemma sum_sq_le_card_mul {D : Type uD} [Fintype D] (f : D → ℝ) :
    (∑ d, f d)^2 ≤ (Fintype.card D : ℝ) * ∑ d, (f d)^2 := by
  simpa [mul_comm] using Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset D) f (fun _ => (1 : ℝ))

lemma centered_density_squares {D : Type uD} [Fintype D] (g : D → ℝ) (M : ℝ)
    (hg : ∀ d, 0 ≤ g d) (hM : ∀ d, g d ≤ M)
    (hmean : ∑ d, g d = (Fintype.card D : ℝ)) :
    ∑ d, (g d - 1)^2 ≤ (Fintype.card D : ℝ) * M := by
  have hsq : ∑ d, (g d)^2 ≤ M * ∑ d, g d := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro d _
    nlinarith [mul_le_mul_of_nonneg_right (hM d) (hg d)]
  have heq : ∑ d, (g d - 1)^2 = (∑ d, (g d)^2) - (Fintype.card D : ℝ) := by
    simp_rw [sub_sq]
    simp only [Finset.sum_add_distrib,Finset.sum_sub_distrib,Finset.sum_const,
      Finset.card_univ,nsmul_eq_mul,one_pow,mul_one]
    rw [← Finset.mul_sum, hmean]
    ring
  rw [heq]
  rw [hmean] at hsq
  have : (0 : ℝ) ≤ Fintype.card D := Nat.cast_nonneg _
  nlinarith

lemma mixture_density_squares {D : Type uD} {A : Type uA} [Fintype D] [Fintype A]
    (g : A → D → ℝ) (p M : A → ℝ)
    (hg : ∀ a d, 0 ≤ g a d) (hM : ∀ a d, g a d ≤ M a)
    (hmean : ∀ a, ∑ d, g a d = (Fintype.card D : ℝ)) :
    ∑ d, (1 + ∑ a, p a * (g a d - 1))^2 ≤
      (Fintype.card D : ℝ) * (1 + (Fintype.card A : ℝ) * ∑ a, (p a)^2 * M a) := by
  let v : D → ℝ := fun d => ∑ a, p a * (g a d - 1)
  have hvmean : ∑ d, v d = 0 := by
    simp only [v]
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro a _
    rw [← Finset.mul_sum,Finset.sum_sub_distrib,hmean]
    simp
  have hv : ∑ d, (v d)^2 ≤ (Fintype.card D : ℝ) *
      ((Fintype.card A : ℝ) * ∑ a, (p a)^2 * M a) := by
    calc
      ∑ d, (v d)^2 ≤ ∑ d, (Fintype.card A : ℝ) * ∑ a, (p a * (g a d-1))^2 :=
        Finset.sum_le_sum (fun d _ => sum_sq_le_card_mul _)
      _ = (Fintype.card A : ℝ) * ∑ a, (p a)^2 * ∑ d, (g a d-1)^2 := by
        simp_rw [mul_pow]
        rw [← Finset.mul_sum,Finset.sum_comm]
        simp_rw [← Finset.mul_sum]
      _ ≤ (Fintype.card A : ℝ) * ∑ a, (p a)^2 * ((Fintype.card D : ℝ) * M a) := by
        gcongr with a
        exact centered_density_squares (g a) (M a) (hg a) (hM a) (hmean a)
      _ = _ := by simp_rw [mul_left_comm ((p _)^2) (Fintype.card D : ℝ)]; rw [← Finset.mul_sum]; ring
  have heq : ∑ d, (1+v d)^2 = (Fintype.card D : ℝ) + ∑ d, (v d)^2 := by
    simp_rw [add_sq]
    simp only [Finset.sum_add_distrib,one_pow,Finset.sum_const,
      Finset.card_univ,nsmul_eq_mul,mul_one,← Finset.mul_sum,hvmean,mul_zero,add_zero]
  change ∑ d, (1+v d)^2 ≤ _
  rw [heq]
  nlinarith

lemma uniform_l2_set_bound {D : Type uD} [Fintype D] [Nonempty D]
    [MeasurableSpace D] [MeasurableSingletonClass D]
    (μ ν : Measure D) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : ∀ d, μ.real {d} = (Fintype.card D : ℝ)⁻¹) {H : ℝ} (hH : 0 ≤ H)
    (hL2 : (Fintype.card D : ℝ) * ∑ d, (ν.real {d})^2 ≤ H^2)
    (A : Set D) : ν.real A ≤ H * Real.sqrt (μ.real A) := by
  classical
  let s := A.toFinite.toFinset
  have hs : (s : Set D) = A := by simp [s]
  have hνA : ν.real A = ∑ d ∈ s, ν.real {d} := by rw [← hs, sum_measureReal_singleton]
  have hμA : μ.real A = (s.card : ℝ) / (Fintype.card D : ℝ) := by
    rw [← hs, ← sum_measureReal_singleton]
    simp only [hμ,Finset.sum_const,nsmul_eq_mul,div_eq_mul_inv]
  have hc : (0 : ℝ) < Fintype.card D := Nat.cast_pos.mpr Fintype.card_pos
  have hsq : (ν.real A)^2 ≤ H^2 * μ.real A := by
    rw [hνA,hμA]
    have hh := Finset.sum_mul_sq_le_sq_mul_sq s (fun d => ν.real {d}) (fun _ => (1 : ℝ))
    simp only [mul_one,one_pow,Finset.sum_const,nsmul_eq_mul,mul_one] at hh
    have hsub : ∑ d ∈ s, (ν.real {d})^2 ≤ ∑ d, (ν.real {d})^2 :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ => sq_nonneg _)
    have hcard : (0 : ℝ) ≤ s.card := Nat.cast_nonneg _
    have hbound := mul_le_mul_of_nonneg_right hsub hcard
    have hbound2 := mul_le_mul_of_nonneg_left ((le_div_iff₀ hc).mpr (by nlinarith :
      (∑ d, (ν.real {d})^2) * (Fintype.card D : ℝ) ≤ H^2)) hcard
    calc
      _ ≤ (∑ d, (ν.real {d})^2) * (s.card : ℝ) := hh.trans hbound
      _ ≤ (s.card : ℝ) * (H^2 / (Fintype.card D : ℝ)) := by simpa [mul_comm] using hbound2
      _ = _ := by ring
  apply (sq_le_sq₀ measureReal_nonneg (mul_nonneg hH (Real.sqrt_nonneg _))).mp
  simpa [mul_pow,Real.sq_sqrt measureReal_nonneg] using hsq

lemma pi_second_moment {ι : Type uι} [Fintype ι] [DecidableEq ι] {D : ι → Type uD}
    [∀ i, Fintype (D i)] [∀ i, MeasurableSpace (D i)]
    [∀ i, MeasurableSingletonClass (D i)] (μ : ∀ i, Measure (D i))
    [∀ i, IsProbabilityMeasure (μ i)] :
    (Fintype.card (∀ i, D i) : ℝ) * ∑ d, ((Measure.pi μ).real {d})^2 =
      ∏ i, (Fintype.card (D i) : ℝ) * ∑ d, ((μ i).real {d})^2 := by
  classical
  simp only [Measure.real,Measure.pi_singleton,ENNReal.toReal_prod,← Finset.prod_pow]
  rw [← Fintype.prod_sum (fun i (d : D i) => ((μ i) {d}).toReal^2),
    Fintype.card_pi,Nat.cast_prod,Finset.prod_mul_distrib]

lemma pi_uniform_singleton_real {ι : Type uι} [Fintype ι] [DecidableEq ι] {D : ι → Type uD}
    [∀ i, Fintype (D i)] [∀ i, Nonempty (D i)] [∀ i, MeasurableSpace (D i)]
    [∀ i, MeasurableSingletonClass (D i)] (d : ∀ i, D i) :
    (Measure.pi (fun i => (PMF.uniformOfFintype (D i)).toMeasure)).real {d} =
      (Fintype.card (∀ i, D i) : ℝ)⁻¹ := by
  classical
  simp [Measure.real,Measure.pi_singleton,ENNReal.toReal_prod,PMF.uniformOfFintype_apply,
    Fintype.card_pi,Finset.prod_inv_distrib]


lemma mixture_endpoint_second_moment {A : Type uA} {D : Type uD} [Fintype A] [Fintype D] [Nonempty D]
    [MeasurableSpace A] [MeasurableSpace D] [MeasurableSingletonClass D]
    (p : A → ℝ≥0∞) (μ₀ : Measure (D × D)) (μ : A → Measure (D × D))
    [IsProbabilityMeasure μ₀] [∀ a, IsProbabilityMeasure (μ a)]
    (hp : ∑ a, p a ≤ 1) (f : D × D → D) (hf : Measurable f)
    (hdiag : ∀ d, μ₀.real (f ⁻¹' {d}) = (Fintype.card D : ℝ)⁻¹)
    (M : A → ℝ) (hM : ∀ a d, (Fintype.card D : ℝ) * (μ a).real (f ⁻¹' {d}) ≤ M a) :
    (Fintype.card D : ℝ) * ∑ d,
      ((mixture p (1-∑ a, p a) μ₀ μ).real {ω | f ω.2 = d})^2 ≤
      1 + (Fintype.card A : ℝ) * ∑ a, (p a).toReal^2 * M a := by
  classical
  let L : ℝ := Fintype.card D
  have hL : 0 < L := Nat.cast_pos.mpr Fintype.card_pos
  have hpfin (a : A) : p a ≠ ∞ := ne_top_of_le_ne_top ENNReal.one_ne_top
    ((Finset.single_le_sum (fun _ _ => bot_le) (Finset.mem_univ a)).trans hp)
  have hsfin : (∑ a, p a) ≠ ∞ := ne_top_of_le_ne_top ENNReal.one_ne_top hp
  have hremfin : 1-∑ a, p a ≠ (∞ : ℝ≥0∞) := ne_top_of_le_ne_top ENNReal.one_ne_top tsub_le_self
  have hrem : (1-∑ a, p a).toReal = 1-∑ a, (p a).toReal := by
    rw [ENNReal.toReal_sub_of_le hp ENNReal.one_ne_top,ENNReal.toReal_one,
      ENNReal.toReal_sum (fun a _ => hpfin a)]
  let g : A → D → ℝ := fun a d => L * (μ a).real (f ⁻¹' {d})
  have hg : ∀ a d, 0 ≤ g a d := fun a d => mul_nonneg hL.le measureReal_nonneg
  have hgmean : ∀ a, ∑ d, g a d = L := by
    intro a
    rw [show (∑ d, g a d) = L * ∑ d, (μ a).real (f ⁻¹' {d}) by
      simp only [g,Finset.mul_sum]]
    rw [sum_measureReal_preimage_singleton Finset.univ (fun d _ => hf (measurableSet_singleton d))]
    simp
  have hden (d : D) : L * (mixture p (1-∑ a, p a) μ₀ μ).real {ω | f ω.2 = d} =
      1 + ∑ a, (p a).toReal * (g a d-1) := by
    rw [mixture_fiber_real p _ μ₀ μ hpfin hremfin f hf d,hdiag d,hrem]
    change L * ((1-∑ a, (p a).toReal)*L⁻¹ + ∑ a, (p a).toReal*(μ a).real (f ⁻¹' {d})) = _
    simp only [g,mul_sub,Finset.sum_sub_distrib,mul_one]
    rw [mul_add,← mul_assoc,mul_comm L (1-∑ a, (p a).toReal),mul_assoc,mul_inv_cancel₀ hL.ne',mul_one]
    rw [Finset.mul_sum]
    simp_rw [mul_left_comm L]
    ring
  have hh := mixture_density_squares g (fun a => (p a).toReal) M hg hM hgmean
  simp_rw [← hden,mul_pow] at hh
  rw [← Finset.mul_sum] at hh
  apply (mul_le_mul_iff_right₀ hL).mp
  nlinarith


lemma sixLaw_second_moment (l t u r : ℕ) [NeZero l]
    (ht : 0 < t ∧ t < l) (hu : 0 < u ∧ u < l) (hr : 0 < r ∧ r < l)
    (a b m κ ρ σ τ I : ℝ) (ha : 0 < a) (hb : 0 < b) (hm : 0 < m)
    (hρ : 0 ≤ ρ) (hσ : 0 ≤ σ) (hτ : 0 ≤ τ)
    (htlo : (l : ℝ)*a/3 ≤ (t : ℝ)) (hthi : (t : ℝ) ≤ (l : ℝ)/2)
    (hulo : (l : ℝ)*b/3 ≤ (u : ℝ)) (huhi : (u : ℝ) ≤ (l : ℝ)/2)
    (hrlo : (l : ℝ)/(2*m) ≤ (r : ℝ)) (hrhi : (r : ℝ) ≤ (l : ℝ)/2)
    (hρsq : ρ^2 = κ^2*a/m) (hσsq : σ^2 = κ^2*b/m) (hτsq : τ^2 ≤ I/m^2)
    (hprob : 2*ENNReal.ofReal ρ+2*ENNReal.ofReal σ+ENNReal.ofReal τ ≤ 1)
    (e : Bool) :
    (l : ℝ) * ∑ d : Fin l,
      ((sixLaw l t u r ht hu hr (ENNReal.ofReal ρ) (ENNReal.ofReal σ) (ENNReal.ofReal τ)).real
        {ω | digitEndpoint e ω.2 = d})^2 ≤ 1+(60*κ^2+10*I)/m := by
  have hh := mixture_endpoint_second_moment (sixWeights (ENNReal.ofReal ρ) (ENNReal.ofReal σ) (ENNReal.ofReal τ))
    (diagonal l) (components l t u r ht hu hr) (by simpa [sum_sixWeights] using hprob)
    (digitEndpoint e) (digitEndpoint_measurable e) (by intro d; simpa using diagonal_endpoint_real l e d)
    (![3/a,3/a,3/b,3/b,2*m])
    (by simpa using sixComponents_density_bound l t u r ht hu hr a b m ha hb hm htlo hthi hulo huhi hrlo hrhi e)
  simp only [Fintype.card_fin,sum_sixWeights] at hh
  change (l : ℝ) * ∑ d : Fin l, _ ≤ _ at hh
  change (l : ℝ) * ∑ d : Fin l, _ ≤ _
  apply hh.trans
  simp only [sixWeights,Fin.sum_univ_succ,Matrix.cons_val_zero,Matrix.cons_val_succ,
    Fin.sum_univ_zero,add_zero,ENNReal.toReal_ofReal hρ,
    ENNReal.toReal_ofReal hσ,ENNReal.toReal_ofReal hτ]
  have heq : 1+(5 : ℝ)*(ρ^2*(3/a)+(ρ^2*(3/a)+(σ^2*(3/b)+(σ^2*(3/b)+τ^2*(2*m))))) =
      1+60*κ^2/m+10*m*τ^2 := by rw [hρsq,hσsq]; field_simp; ring
  norm_num only [Nat.cast_ofNat]
  rw [heq]
  have hτ' := mul_le_mul_of_nonneg_left hτsq (by positivity : 0 ≤ 10*m)
  have hid : 10*m*(I/m^2) = 10*I/m := by field_simp
  rw [hid] at hτ'
  calc
    _ ≤ 1+60*κ^2/m+10*I/m := by linarith
    _ = _ := by ring

end
open MeasureTheory Set
open scoped ENNReal



end CircleCoupling

end

end OAI
end

section
-- module Solutions.OAIQ2_Rot.RotationWeights_CoordinateLaws
attribute [-instance] _root_.OAI.CircleCoupling.DigitSystem.instIsProbabilityMeasureSampleLaw _root_.OAI.CircleCoupling.DigitSystem.instIsProbabilityMeasureSamplesProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

universe uκ uD

open MeasureTheory
open scoped ENNReal NNReal ComplexInnerProductSpace BigOperators
open MeasureTheory Filter Set Submodule
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ComplexInnerProductSpace
open MeasureTheory Filter Set
open Set
open scoped ComplexInnerProductSpace
open Set
open scoped ComplexInnerProductSpace
open MeasureTheory Set Filter Topology
open scoped BigOperators ComplexConjugate
open MeasureTheory Set Filter
open scoped BigOperators ENNReal
open Filter Set
open scoped Topology
open Filter Set
open scoped Topology
open Set MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter Set
open scoped Topology
open Set MeasureTheory
open scoped ENNReal Classical
open Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Topology
open scoped BigOperators
open scoped BigOperators
open Set
open Set
open Set
open Set MeasureTheory Filter
open scoped BigOperators ENNReal Topology Classical
open MeasureTheory Set Filter
open scoped ENNReal Topology
open MeasureTheory Set
open MeasureTheory Filter Set
open scoped Topology BoundedContinuousFunction
open MeasureTheory Set Filter Topology TopologicalSpace
open MeasureTheory Set
open scoped ENNReal BigOperators Classical
open MeasureTheory Set
open scoped BigOperators ENNReal Classical
open MeasureTheory Set
open scoped ENNReal
open MeasureTheory Set
open scoped ENNReal NNReal
namespace CircleCoupling

lemma crossingProbability_sq {κ w m : ℝ} (hw : 0 ≤ w) (hm : 0 ≤ m) :
    (crossingProbability κ w m)^2=κ^2*w/m := by
  rw [crossingProbability,mul_pow,Real.sq_sqrt (div_nonneg hw hm)]
  ring

namespace CoordinateParameters
variable (P : CoordinateParameters)

lemma law_second_moment (tagged e : Bool) :
    (P.l:ℝ)* ∑ d : Fin P.l, ((P.law tagged).real {ω | digitEndpoint e ω.2=d})^2 ≤
      1+(60*P.κ^2+10*(if tagged then (1:ℝ) else 0))/(P.m:ℝ) := by
  apply sixLaw_second_moment _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ P.a_pos P.b_pos P.m_pos
    P.ρ_nonneg P.σ_nonneg (P.τ_nonneg tagged) P.width_a.2.2.1 P.rounded_width_a_half
    P.width_b.2.2.1 P.rounded_width_b_half P.tag_bounds.2.2.1 P.rounded_tag_half
    (crossingProbability_sq P.a_pos.le P.m_pos.le) (crossingProbability_sq P.b_pos.le P.m_pos.le) _ (P.probabilities tagged)
  cases tagged <;> simp [τ,one_div,inv_pow]

end CoordinateParameters
end CircleCoupling

end

end OAI
end

section
-- module Solutions.OAIQ2_Rot.RotationWeights_RadixDigits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CircleDigits

universe uι uX

open MeasureTheory
open scoped ENNReal NNReal ComplexInnerProductSpace BigOperators
open MeasureTheory Filter Set Submodule
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ComplexInnerProductSpace
open MeasureTheory Filter Set
open Set
open scoped ComplexInnerProductSpace
open Set
open scoped ComplexInnerProductSpace
open MeasureTheory Set Filter Topology
open scoped BigOperators ComplexConjugate
open MeasureTheory Set Filter
open scoped BigOperators ENNReal
open Filter Set
open scoped Topology
open Filter Set
open scoped Topology
open Set MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter Set
open scoped Topology
open Set MeasureTheory
open scoped ENNReal Classical
open Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Topology
open scoped BigOperators
open scoped BigOperators
open Set
open Set
open Set
open Set MeasureTheory Filter
open scoped BigOperators ENNReal Topology Classical
open MeasureTheory Set Filter
open scoped ENNReal Topology
open MeasureTheory Set
open MeasureTheory Filter Set
open scoped Topology BoundedContinuousFunction
open MeasureTheory Set Filter Topology TopologicalSpace
open MeasureTheory Set
open scoped ENNReal BigOperators Classical
open MeasureTheory Set
open scoped BigOperators ENNReal Classical
open MeasureTheory Set
open scoped ENNReal
open MeasureTheory Set
open scoped ENNReal NNReal

open MeasureTheory Set Filter
open scoped BigOperators ENNReal Topology
section

lemma denominator_inv_tendsto {b : ℕ → ℕ} (hb : ∀ i, 2≤b i) :
    Tendsto (fun n ↦ (denominator b n : ℝ)⁻¹) atTop (𝓝 0) := by
  apply squeeze_zero (fun n ↦ by positivity) (denominator_inv_bound hb)
  exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)



variable (b : ℕ → ℕ)

lemma integral_digitLaw (i : ℕ) [NeZero (b i)] (f : Fin (b i) → ℂ) :
    ∫ d, f d ∂digitLaw b i = (b i : ℂ)⁻¹*∑ d, f d := by
  rw [digitLaw,PMF.integral_eq_sum]
  simp only [PMF.uniformOfFintype_apply,Fintype.card_fin,ENNReal.toReal_inv,ENNReal.toReal_natCast,
    Complex.real_smul,Complex.ofReal_inv,Complex.ofReal_natCast,← Finset.mul_sum]

omit b in
lemma character_div_eq_one {k : ℤ} {q : ℕ} (hq : q≠0) :
    character k ((1/(q : ℝ) : ℝ) : CircleX) = 1 ↔ (q : ℤ)∣k := by
  change (AddCircle.toCircle (k • ((1/(q : ℝ) : ℝ) : CircleX)) : ℂ) = 1 ↔ _
  rw [show (1 : ℂ) = (1 : Circle) by rfl,Circle.coe_inj,← AddCircle.toCircle_zero,
    (AddCircle.injective_toCircle (by norm_num : (1:ℝ)≠0)).eq_iff]
  rw [← AddCircle.coe_zsmul,AddCircle.coe_eq_zero_iff]
  simp only [zsmul_eq_mul,mul_one,one_div]
  constructor
  · rintro ⟨z,hz⟩
    refine ⟨z,?_⟩
    have hq' : (q:ℝ)≠0 := by exact_mod_cast hq
    have h : (k:ℝ) = (q:ℝ)*z := by rw [hz]; field_simp
    exact_mod_cast h
  · rintro ⟨z,hz⟩
    refine ⟨z,?_⟩
    have hq' : (q:ℝ)≠0 := by exact_mod_cast hq
    rw [hz,Int.cast_mul,Int.cast_natCast]
    field_simp

omit b in
lemma character_div_mul (k : ℤ) (q r : ℕ) (d : ℕ) :
    character k ((d/(q*r : ℕ) : ℝ) : CircleX) =
      (character k ((1/(q*r : ℕ) : ℝ) : CircleX))^d := by
  rw [← AddChar.map_nsmul_eq_pow,← AddCircle.coe_nsmul]
  congr 1
  simp [nsmul_eq_mul,div_eq_mul_inv]

lemma integral_digitLaw_character_zero {b : ℕ → ℕ} (hb : ∀ i, 2≤b i)
    [∀ i, NeZero (b i)] (i : ℕ) (k : ℤ)
    (hdiv : (denominator b i : ℤ)∣k) (hnot : ¬(denominator b (i+1) : ℤ)∣k) :
    (∫ d : Fin (b i), character k ((d/(denominator b (i+1) : ℕ) : ℝ) : CircleX)
      ∂digitLaw b i) = 0 := by
  rw [integral_digitLaw]
  suffices ∑ d : Fin (b i), character k ((d/(denominator b (i+1) : ℕ) : ℝ) : CircleX)=0 by rw [this,mul_zero]
  simp_rw [denominator_succ,character_div_mul]
  rw [Fin.sum_univ_eq_sum_range]
  let z := character k ((1/(denominator b i*b i : ℕ) : ℝ) : CircleX)
  change ∑ d∈Finset.range (b i), z^d = 0
  have hz : z≠1 := by
    apply mt (character_div_eq_one (Nat.mul_ne_zero (denominator_pos hb i).ne' (NeZero.ne _))).mp
    simpa only [denominator_succ] using hnot
  have hpow : z^(b i)=1 := by
    rw [← AddChar.map_nsmul_eq_pow,← AddCircle.coe_nsmul]
    have hq : (denominator b i : ℝ)≠0 := by exact_mod_cast (denominator_pos hb i).ne'
    have hbi : (b i : ℝ)≠0 := by exact_mod_cast (show b i≠0 from NeZero.ne _)
    convert (character_div_eq_one (denominator_pos hb i).ne').mpr hdiv using 1
    congr 1
    simp only [nsmul_eq_mul,Nat.cast_mul]
    field_simp
  rw [geom_sum_eq hz,hpow,sub_self,zero_div]

lemma exists_nondividing_digit {b : ℕ → ℕ} (hb : ∀ i, 2≤b i) {k : ℤ} (hk : k≠0) :
    ∃ i, (denominator b i : ℤ)∣k ∧ ¬(denominator b (i+1) : ℤ)∣k := by
  have hex : ∃ n, ¬(denominator b n : ℤ)∣k := by
    have hlarge : k.natAbs < denominator b (k.natAbs+1) :=
      (lt_of_le_of_lt (by omega : k.natAbs≤k.natAbs+1) (Nat.lt_two_pow_self)).trans_le
        (denominator_geometric hb (k.natAbs+1))
    refine ⟨k.natAbs+1,fun hd ↦ ?_⟩
    have hle := Int.natAbs_le_of_dvd_ne_zero hd hk
    simpa only [Int.natAbs_natCast] using not_le_of_gt hlarge hle
  let n := Nat.find hex
  have hn : n≠0 := by
    intro he
    have hh := Nat.find_spec hex
    change ¬(denominator b n : ℤ)∣k at hh
    simp [he] at hh
  refine ⟨n-1,?_,?_⟩
  · by_contra h
    exact Nat.find_min hex (show n-1<n by omega) h
  · simpa only [Nat.sub_add_cancel (by omega : 1≤n)] using Nat.find_spec hex

end

section

lemma character_sum {ι : Type uι} (k : ℤ) (s : Finset ι) (f : ι → CircleX) :
    character k (∑ i∈s, f i) = ∏ i∈s, character k (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => rw [Finset.sum_insert hi,Finset.prod_insert hi,AddChar.map_add_eq_mul,ih]

lemma integral_digitPartial {b : ℕ → ℕ} [∀ i, NeZero (b i)] (k : ℤ) (n : ℕ) :
    (∫ d : Digits b, character k ((∑ i∈Finset.range n, digitTerm b d i : ℝ) : CircleX)
      ∂uniformDigits b) =
    ∏ i∈Finset.range n, ∫ d : Fin (b i), character k ((d/(denominator b (i+1) : ℕ) : ℝ) : CircleX)
      ∂digitLaw b i := by
  classical
  have hcoe (d : Digits b) :
      ((∑ i∈Finset.range n, digitTerm b d i : ℝ) : CircleX) =
        ∑ i∈Finset.range n, (digitTerm b d i : CircleX) := by
    exact map_sum (QuotientAddGroup.mk' (AddSubgroup.zmultiples (1:ℝ))) _ _
  simp_rw [hcoe,character_sum]
  let f := fun (d : ∀ i : Finset.range n, Fin (b i)) ↦
    ∏ i : Finset.range n, character k ((d i/(denominator b (i.val+1) : ℕ) : ℝ) : CircleX)
  have hf : Measurable f := measurable_of_finite _
  have h := integral_restrict_infinitePi (fun i ↦ digitLaw b i) hf.aestronglyMeasurable
  change (∫ d, f ((Finset.range n).restrict d) ∂uniformDigits b) = _ at h
  simp only [f,Finset.restrict_def] at h
  change (∫ d : Digits b, ∏ i∈Finset.range n,
    character k ((d i/(denominator b (i+1) : ℕ) : ℝ) : CircleX) ∂uniformDigits b) = _
  have hp := integral_fintype_prod_eq_prod (𝕜 := ℂ)
    (fun (i : Finset.range n) (d : Fin (b i)) ↦
      character k ((d/(denominator b (i.val+1) : ℕ) : ℝ) : CircleX))
    (μ := fun i ↦ digitLaw b i)
  calc
    _ = ∫ d : Digits b, ∏ i : Finset.range n,
        character k ((d i/(denominator b (i.val+1) : ℕ) : ℝ) : CircleX) ∂uniformDigits b := by
      apply integral_congr_ae
      exact ae_of_all _ fun d ↦ (Finset.prod_coe_sort (Finset.range n)
        (fun i ↦ character k ((d i/(denominator b (i+1) : ℕ) : ℝ) : CircleX))).symm
    _ = ∏ i : Finset.range n, ∫ d : Fin (b i), character k
        ((d/(denominator b (i.val+1) : ℕ) : ℝ) : CircleX) ∂digitLaw b i := h.trans hp
    _ = _ := Finset.prod_coe_sort (Finset.range n)
      (fun i ↦ ∫ d : Fin (b i), character k
        ((d/(denominator b (i+1) : ℕ) : ℝ) : CircleX) ∂digitLaw b i)

lemma integral_endpoint_character {b : ℕ → ℕ} (hb : ∀ i, 2≤b i)
    [∀ i, NeZero (b i)] (k : ℤ) :
    (∫ d : Digits b, character k (endpoint b d) ∂uniformDigits b) = if k=0 then 1 else 0 := by
  classical
  by_cases hk : k=0
  · subst k
    change (∫ d : Digits b, fourier 0 (endpoint b d) ∂uniformDigits b) = _
    simp
  rw [ite_eq_right hk]
  let F := fun n (d : Digits b) ↦
    character k ((∑ i∈Finset.range n, digitTerm b d i : ℝ) : CircleX)
  have hmeas (n : ℕ) : Measurable (F n) :=
    (fourier k).continuous.measurable.comp ((AddCircle.continuous_mk' 1).measurable.comp
      (Finset.measurable_sum _ fun i _ ↦ measurable_digitTerm b i))
  have hlim := tendsto_integral_of_dominated_convergence (μ := uniformDigits b) (fun _ ↦ (1:ℝ))
    (fun n ↦ (hmeas n).aestronglyMeasurable) (integrable_const 1)
    (fun n ↦ ae_of_all _ fun d ↦ by exact (Circle.norm_coe _).le)
    (ae_of_all _ fun d ↦ ((fourier k).continuous.continuousAt.tendsto.comp
      ((AddCircle.continuous_mk' 1).continuousAt.tendsto.comp
        (digitTerm_summable hb d).hasSum.tendsto_sum_nat)))
  obtain ⟨i,hdiv,hnot⟩ := exists_nondividing_digit hb hk
  have hzero : ∀ᶠ n in atTop, (∫ d, F n d ∂uniformDigits b) = (0:ℂ) := by
    filter_upwards [eventually_gt_atTop i] with n hn
    rw [show (∫ d, F n d ∂uniformDigits b) = _ from integral_digitPartial k n]
    exact Finset.prod_eq_zero (Finset.mem_range.mpr hn) (integral_digitLaw_character_zero hb i k hdiv hnot)
  exact tendsto_nhds_unique hlim (tendsto_const_nhds.congr' (hzero.mono fun _ h ↦ h.symm))

lemma continuous_integral {X : Type uX} [TopologicalSpace X] [CompactSpace X] [MeasurableSpace X]
    [BorelSpace X] (μ : Measure X) [IsProbabilityMeasure μ] :
    Continuous (fun f : C(X,ℂ) ↦ ∫ x, f x ∂μ) := by
  apply LipschitzWith.continuous (K := 1)
  rw [lipschitzWith_iff_dist_le_mul]
  intro f g
  simp only [NNReal.coe_one,one_mul,dist_eq_norm]
  have hi (f : C(X,ℂ)) : Integrable f μ :=
    Integrable.of_bound f.continuous.aestronglyMeasurable ‖f‖ (ae_of_all _ f.norm_coe_le_norm)
  rw [← integral_sub (hi f) (hi g)]
  simpa using norm_integral_le_of_norm_le_const (μ := μ) (ae_of_all _ fun x ↦ (f-g).norm_coe_le_norm x)

lemma circle_measure_eq_of_fourier (μ ν : Measure CircleX) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν]
    (h : ∀ k : ℤ, (∫ x, fourier k x ∂μ) = ∫ x, fourier k x ∂ν) : μ=ν := by
  have hi (m : Measure CircleX) [IsProbabilityMeasure m] (f : C(CircleX,ℂ)) : Integrable f m :=
    Integrable.of_bound f.continuous.aestronglyMeasurable ‖f‖ (ae_of_all _ f.norm_coe_le_norm)
  have hc : IsClosed {f : C(CircleX,ℂ) | (∫ x, f x ∂μ) = ∫ x, f x ∂ν} :=
    isClosed_eq (continuous_integral μ) (continuous_integral ν)
  have hs : (↑(Submodule.span ℂ (Set.range (fourier (T := (1:ℝ))))) : Set C(CircleX,ℂ)) ⊆
      {f | (∫ x, f x ∂μ) = ∫ x, f x ∂ν} := by
    intro f hf
    induction hf using Submodule.span_induction with
    | mem f hf => obtain ⟨k,rfl⟩ := hf; exact h k
    | zero => simp
    | add f g _ _ hf hg =>
      change (∫ x, f x+g x ∂μ) = ∫ x, f x+g x ∂ν
      rw [integral_add (hi μ f) (hi μ g),integral_add (hi ν f) (hi ν g),hf,hg]
    | smul a f _ hf =>
      change (∫ x, a • f x ∂μ) = ∫ x, a • f x ∂ν
      rw [integral_smul,integral_smul,hf]
  have hall := closure_minimal hs hc
  rw [← Submodule.topologicalClosure_coe,span_fourier_closure_eq_top,Submodule.top_coe] at hall
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro f
  let g : C(CircleX,ℂ) := ⟨fun x ↦ (f x:ℂ), Complex.continuous_ofReal.comp f.continuous⟩
  have hfg := hall (a := g) (Set.mem_univ _)
  change (∫ x, (f x:ℂ) ∂μ) = ∫ x, (f x:ℂ) ∂ν at hfg
  simpa only [integral_complex_ofReal,Complex.ofReal_inj] using hfg

lemma endpoint_measurePreserving {b : ℕ → ℕ} (hb : ∀ i, 2≤b i)
    [∀ i, NeZero (b i)] : MeasurePreserving (endpoint b) (uniformDigits b) volume := by
  let : IsProbabilityMeasure (volume : Measure CircleX) := by
    rw [AddCircle.volume_eq_smul_haarAddCircle]
    norm_num
    infer_instance
  refine ⟨measurable_endpoint b,?_⟩
  have : IsProbabilityMeasure ((uniformDigits b).map (endpoint b)) :=
    Measure.isProbabilityMeasure_map (measurable_endpoint b).aemeasurable
  apply circle_measure_eq_of_fourier
  intro k
  rw [integral_map (measurable_endpoint b).aemeasurable (fourier k).continuous.aestronglyMeasurable]
  change (∫ d, character k (endpoint b d) ∂uniformDigits b) = _
  rw [integral_endpoint_character hb]
  have hh := congrFun (fourierCoeff_fourier (T := (1:ℝ)) k) 0
  have hm : (AddCircle.haarAddCircle : Measure CircleX) = volume := by
    rw [AddCircle.volume_eq_smul_haarAddCircle]; norm_num
  simpa [fourierCoeff,Pi.single_apply,eq_comm,hm] using hh.symm

end


lemma ae_gridFree (b : ℕ → ℕ) (hb : ∀ i, 2 ≤ b i) :
    ∀ᵐ x : CircleX ∂volume, x ∈ gridFree b := by
  change ∀ᵐ x : CircleX ∂volume, ∀ n, denominator b n • x ≠ 0
  rw [ae_all_iff]
  intro n
  have hp : MeasurePreserving (fun x : CircleX ↦ denominator b n • x) volume volume := by
    simpa only [natCast_zsmul] using
      (Measure.measurePreserving_zsmul (volume : Measure CircleX)
        (by exact_mod_cast (denominator_pos hb n).ne' : (denominator b n : ℤ) ≠ 0))
  have hz : ∀ᵐ x : CircleX ∂volume, x ≠ 0 := by
    apply ae_iff.mpr
    simp only [not_not, Set.ofPred_eq_eq_singleton]
    rw [← Metric.closedBall_zero,AddCircle.volume_closedBall]
    norm_num
  exact hp.quasiMeasurePreserving.ae (p := fun x : CircleX => x ≠ 0) hz



end CircleDigits

end

end OAI
end

section
-- module Solutions.OAIQ2_Rot.RotationWeights_EndpointMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

universe uX uι uD uΩ

open MeasureTheory
open scoped ENNReal NNReal ComplexInnerProductSpace BigOperators
open MeasureTheory Filter Set Submodule
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ComplexInnerProductSpace
open MeasureTheory Filter Set
open Set
open scoped ComplexInnerProductSpace
open Set
open scoped ComplexInnerProductSpace
open MeasureTheory Set Filter Topology
open scoped BigOperators ComplexConjugate
open MeasureTheory Set Filter
open scoped BigOperators ENNReal
open Filter Set
open scoped Topology
open Filter Set
open scoped Topology
open Set MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter Set
open scoped Topology
open Set MeasureTheory
open scoped ENNReal Classical
open Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Topology
open scoped BigOperators
open scoped BigOperators
open Set
open Set
open Set
open Set MeasureTheory Filter
open scoped BigOperators ENNReal Topology Classical
open MeasureTheory Set Filter
open scoped ENNReal Topology
open MeasureTheory Set
open MeasureTheory Filter Set
open scoped Topology BoundedContinuousFunction
open MeasureTheory Set Filter Topology TopologicalSpace
open MeasureTheory Set
open scoped ENNReal BigOperators Classical
open MeasureTheory Set
open scoped BigOperators ENNReal Classical
open MeasureTheory Set
open scoped ENNReal
open MeasureTheory Set
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped BigOperators ENNReal Topology

open Set MeasureTheory Topology
open scoped symmDiff
namespace CircleCoupling

section

section

lemma continuous_measureReal_of_le {X : Type uX} [MeasurableSpace X]
    (μ ν : Measure X) [IsFiniteMeasure μ] [IsFiniteMeasure ν] (hμν : μ ≤ ν) :
    Continuous (fun s : MeasuredSets ν ↦ μ.real (s : Set X)) := by
  apply LipschitzWith.continuous (K := 1)
  apply LipschitzWith.of_dist_le_mul
  intro s t
  simp only [Real.dist_eq, NNReal.coe_one, one_mul, MeasuredSets.dist_def]
  apply (abs_measureReal_sub_le_measureReal_symmDiff s.2.nullMeasurableSet t.2.nullMeasurableSet).trans
  exact ENNReal.toReal_mono (measure_ne_top _ _) (hμν _)

lemma sq_measure_bound_of_generating_ring {X : Type uX} [mX : MeasurableSpace X]
    (μ ν : Measure X) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {C : Set (Set X)} (hC : IsSetRing C) (hU : univ ∈ C)
    (hgen : mX = MeasurableSpace.generateFrom C) (H : ℝ)
    (hfinite : ∀ A∈C, (ν.real A)^2 ≤ H * μ.real A) :
    ∀ A, MeasurableSet A → (ν.real A)^2 ≤ H * μ.real A := by
  let τ := μ+ν
  have hμ : Continuous (fun s : MeasuredSets τ ↦ μ.real (s : Set X)) :=
    continuous_measureReal_of_le μ τ (Measure.le_add_right le_rfl)
  have hν : Continuous (fun s : MeasuredSets τ ↦ ν.real (s : Set X)) :=
    continuous_measureReal_of_le ν τ (Measure.le_add_left le_rfl)
  have hd : Dense ((SetLike.coe : MeasuredSets τ → Set X) ⁻¹' C) :=
    dense_of_generateFrom_isSetRing hC ⟨{univ}, by simp, by simpa, by simp⟩ hgen
  have hc : IsClosed {s : MeasuredSets τ | (ν.real (s : Set X))^2 ≤ H*μ.real (s : Set X)} :=
    isClosed_le (hν.pow 2) (continuous_const.mul hμ)
  have hh : closure ((SetLike.coe : MeasuredSets τ → Set X) ⁻¹' C) ⊆
      {s : MeasuredSets τ | (ν.real (s : Set X))^2 ≤ H*μ.real (s : Set X)} :=
    closure_minimal (fun s hs ↦ hfinite s hs) hc
  rw [hd.closure_eq] at hh
  intro A hA
  exact hh (show (⟨A,hA⟩ : MeasuredSets τ) ∈ univ from mem_univ _)

lemma sqrt_measure_bound_of_generating_ring {X : Type uX} [mX : MeasurableSpace X]
    (μ ν : Measure X) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {C : Set (Set X)} (hC : IsSetRing C) (hU : univ ∈ C)
    (hgen : mX = MeasurableSpace.generateFrom C) {H : ℝ} (hH : 0 ≤ H)
    (hfinite : ∀ A∈C, ν.real A ≤ H * Real.sqrt (μ.real A)) :
    ∀ A, MeasurableSet A → ν.real A ≤ H * Real.sqrt (μ.real A) := by
  have h : ∀ A, MeasurableSet A → (ν.real A)^2 ≤ H^2 * μ.real A :=
    sq_measure_bound_of_generating_ring μ ν hC hU hgen (H^2) (by
      intro A hA
      have hsq := sq_le_sq₀ (show 0≤ν.real A from measureReal_nonneg)
        (mul_nonneg hH (Real.sqrt_nonneg _)) |>.mpr (hfinite A hA)
      rwa [mul_pow, Real.sq_sqrt measureReal_nonneg] at hsq)
  intro A hA
  apply (sq_le_sq₀ measureReal_nonneg (mul_nonneg hH (Real.sqrt_nonneg _))).mp
  simpa [mul_pow,Real.sq_sqrt measureReal_nonneg] using h A hA

lemma infinitePi_sqrt_bound {ι : Type uι} {X : ι → Type uX}
    [∀ i, MeasurableSpace (X i)] (μ ν : ∀ i, Measure (X i))
    [∀ i, IsProbabilityMeasure (μ i)] [∀ i, IsProbabilityMeasure (ν i)]
    {H : ℝ} (hH : 0≤H)
    (hfinite : ∀ I : Finset ι, ∀ A, MeasurableSet A →
      (Measure.pi (fun i : I ↦ ν i)).real A ≤
        H * Real.sqrt ((Measure.pi (fun i : I ↦ μ i)).real A)) :
    ∀ A, MeasurableSet A → (Measure.infinitePi ν).real A ≤
      H * Real.sqrt ((Measure.infinitePi μ).real A) := by
  have hU : (univ : Set (∀ i, X i)) ∈ measurableCylinders (α := X) := by
    rw [← cylinder_univ (∅ : Finset ι)]
    exact cylinder_mem_measurableCylinders _ _ MeasurableSet.univ
  apply sqrt_measure_bound_of_generating_ring (Measure.infinitePi μ) (Measure.infinitePi ν)
    isSetRing_measurableCylinders hU generateFrom_measurableCylinders.symm hH
  intro A hA
  obtain ⟨I,B,hB,rfl⟩ := (mem_measurableCylinders _).mp hA
  have hν : (Measure.infinitePi ν) (cylinder I B) =
      (Measure.pi (fun i : I ↦ ν i)) B := by
    exact Measure.infinitePi_cylinder _ hB
  have hμ : (Measure.infinitePi μ) (cylinder I B) =
      (Measure.pi (fun i : I ↦ μ i)) B := by
    exact Measure.infinitePi_cylinder _ hB
  simp only [Measure.real,hν,hμ]
  exact hfinite I B hB


lemma infinitePi_l2_bound {ι : Type uι} {D : ι → Type uD}
    [∀ i, Fintype (D i)] [∀ i, Nonempty (D i)] [∀ i, MeasurableSpace (D i)]
    [∀ i, MeasurableSingletonClass (D i)] (ν : ∀ i, Measure (D i))
    [∀ i, IsProbabilityMeasure (ν i)] (e : ι → ℝ) (he : ∀ i, 0 ≤ e i)
    (hs : Summable e)
    (hm : ∀ i, (Fintype.card (D i) : ℝ) * ∑ d, ((ν i).real {d})^2 ≤ 1+e i)
    (A : Set (∀ i, D i)) (hA : MeasurableSet A) :
    (Measure.infinitePi ν).real A ≤ Real.exp ((∑' i, e i)/2) *
      Real.sqrt ((Measure.infinitePi (fun i => (PMF.uniformOfFintype (D i)).toMeasure)).real A) := by
  classical
  apply infinitePi_sqrt_bound _ ν (Real.exp_pos _).le _ A hA
  intro I B _hB
  apply uniform_l2_set_bound _ _ (fun d => by simpa using pi_uniform_singleton_real d) (Real.exp_pos _).le _ B
  rw [pi_second_moment (fun i : I => ν i)]
  calc
    (∏ i : I, (Fintype.card (D i) : ℝ) * ∑ d, ((ν i).real {d})^2) ≤ ∏ i : I, Real.exp (e i) := by
      apply Finset.prod_le_prod
      · intro i _; positivity
      · intro i _; exact (hm i).trans (by simpa [add_comm] using Real.add_one_le_exp (e i))
    _ = Real.exp (∑ i : I, e i) := (Real.exp_sum _ _).symm
    _ ≤ Real.exp (∑' i, e i) := by
      apply Real.exp_le_exp.mpr
      rw [Finset.sum_coe_sort]
      exact hs.sum_le_tsum I (fun i _ => he i)
    _ = Real.exp ((∑' i, e i)/2)^2 := by rw [← Real.exp_nat_mul]; congr 1; ring

open CircleDigits

lemma observedDigits_sqrt_bound {Ω : ℕ → Type uΩ} [∀ i, MeasurableSpace (Ω i)]
    (μ : ∀ i, Measure (Ω i)) [∀ i, IsProbabilityMeasure (μ i)]
    {b : ℕ → ℕ} [∀ i, NeZero (b i)] (f : ∀ i, Ω i → Fin (b i))
    (hf : ∀ i, Measurable (f i)) (e : ℕ → ℝ) (he : ∀ i, 0 ≤ e i) (hs : Summable e)
    (hm : ∀ i, (b i : ℝ)* ∑ d, ((μ i).real (f i ⁻¹' {d}))^2 ≤ 1+e i)
    (A : Set (Digits b)) (hA : MeasurableSet A) :
    (Measure.infinitePi μ).real ((fun ω i => f i (ω i)) ⁻¹' A) ≤
      Real.exp ((∑' i, e i)/2) * Real.sqrt ((uniformDigits b).real A) := by
  let ν : ∀ i, Measure (Fin (b i)) := fun i => Measure.map (f i) (μ i)
  have hν : ∀ i, IsProbabilityMeasure (ν i) := fun i => Measure.isProbabilityMeasure_map (hf i).aemeasurable
  have hmoment (i : ℕ) : (Fintype.card (Fin (b i)) : ℝ) * ∑ d, ((ν i).real {d})^2 ≤ 1+e i := by
    convert hm i using 1
    simp only [Fintype.card_fin,Measure.real,ν,Measure.map_apply (hf i) (measurableSet_singleton _)]
  have hh := infinitePi_l2_bound ν e he hs hmoment A hA
  rw [← Measure.infinitePi_map_pi μ hf] at hh
  have hobs : Measurable (fun ω : ∀ i, Ω i => fun i => f i (ω i)) :=
    Measurable.of_eval (fun i => (hf i).comp (measurable_pi_apply i))
  simp only [Measure.real] at hh ⊢
  rw [Measure.map_apply hobs hA] at hh
  exact hh

lemma hybridEndpoint_sqrt_bound {Ω : ℕ → Type uΩ} [∀ i, MeasurableSpace (Ω i)]
    (μ : ∀ i, Measure (Ω i)) [∀ i, IsProbabilityMeasure (μ i)]
    {b : ℕ → ℕ} (hb : ∀ i, 2 ≤ b i) [∀ i, NeZero (b i)]
    (f : ∀ i, Ω i → Fin (b i)) (hf : ∀ i, Measurable (f i))
    (e : ℕ → ℝ) (he : ∀ i, 0 ≤ e i) (hs : Summable e)
    (hm : ∀ i, (b i : ℝ)* ∑ d, ((μ i).real (f i ⁻¹' {d}))^2 ≤ 1+e i)
    (A : Set CircleDigits.CircleX) (hA : MeasurableSet A) :
    (Measure.infinitePi μ).real ((fun ω => endpoint b (fun i => f i (ω i))) ⁻¹' A) ≤
      Real.exp ((∑' i, e i)/2) * Real.sqrt (volume.real A) := by
  have hh := observedDigits_sqrt_bound μ f hf e he hs hm ((endpoint b) ⁻¹' A)
    ((measurable_endpoint b) hA)
  have hp := (endpoint_measurePreserving hb).measure_preimage hA.nullMeasurableSet
  simp only [Measure.real,hp] at hh
  exact hh

end
open CircleDigits

lemma hybridEndpoint_absolutelyContinuous {Ω : ℕ → Type uΩ} [∀ i, MeasurableSpace (Ω i)]
    (μ : ∀ i, Measure (Ω i)) [∀ i, IsProbabilityMeasure (μ i)]
    {b : ℕ → ℕ} (hb : ∀ i, 2 ≤ b i) [∀ i, NeZero (b i)]
    (f : ∀ i, Ω i → Fin (b i)) (hf : ∀ i, Measurable (f i))
    (e : ℕ → ℝ) (he : ∀ i, 0 ≤ e i) (hs : Summable e)
    (hm : ∀ i, (b i : ℝ)* ∑ d, ((μ i).real (f i ⁻¹' {d}))^2 ≤ 1+e i) :
    Measure.map (fun ω => endpoint b (fun i => f i (ω i))) (Measure.infinitePi μ) ≪ volume := by
  have hobs : Measurable (fun ω : ∀ i, Ω i => endpoint b (fun i => f i (ω i))) :=
    (measurable_endpoint b).comp (Measurable.of_eval (fun i => (hf i).comp (measurable_pi_apply i)))
  apply Measure.AbsolutelyContinuous.mk
  intro A hA hzero
  rw [Measure.map_apply hobs hA]
  apply le_antisymm _ bot_le
  apply (ENNReal.toReal_le_toReal (measure_ne_top _ _) ENNReal.zero_ne_top).mp
  have hh := hybridEndpoint_sqrt_bound μ hb f hf e he hs hm A hA
  simpa only [Measure.real,hzero,ENNReal.toReal_zero,Real.sqrt_zero,mul_zero] using hh

end
open CircleDigits

namespace DigitSystem
variable (S : DigitSystem)
lemma measurable_observe (e : ℕ → Bool) : Measurable (S.observe e) := by
  apply Measurable.of_eval
  intro i
  exact (digitEndpoint_measurable (e i)).comp (measurable_snd.comp (measurable_pi_apply i))
lemma measurable_endpoint (e : ℕ → Bool) : Measurable (S.endpoint e) :=
  (CircleDigits.measurable_endpoint _).comp (S.measurable_observe e)

lemma error_nonneg (tagged : ℕ → Bool) (n : ℕ) : 0 ≤ S.error tagged n := by
  cases n with
  | zero => exact le_refl 0
  | succ n => dsimp [error]; split <;> positivity
lemma moment (tagged : ℕ → Bool) (n : ℕ) (e : Bool) :
    (S.radix n:ℝ)*∑ d : Fin (S.radix n), ((S.law tagged n).real {ω | digitEndpoint e ω.2=d})^2 ≤
      1+S.error tagged n := by
  cases n with
  | zero =>
    have h (d : Fin (S.radix 0)) : (S.law tagged 0).real {ω | digitEndpoint e ω.2=d} = (S.radix 0:ℝ)⁻¹ := by
      rw [Measure.real,law,labelled_fiber _ _ _ (digitEndpoint_measurable e)]
      cases e
      · change ((diagonal (S.radix 0)) {z | z.1=d}).toReal = _
        simpa only [Set.preimage,Set.mem_singleton_iff,ENNReal.toReal_inv,ENNReal.toReal_natCast] using congrArg ENNReal.toReal (diagonal_fiber_fst (S.radix 0) d)
      · change ((diagonal (S.radix 0)) {z | z.2=d}).toReal = _
        simpa only [Set.preimage,Set.mem_singleton_iff,ENNReal.toReal_inv,ENNReal.toReal_natCast] using congrArg ENNReal.toReal (diagonal_fiber_snd (S.radix 0) d)
    simp only [h,error,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,add_zero]
    have hz : (S.radix 0:ℝ) ≠ 0 := by exact_mod_cast NeZero.ne (S.radix 0)
    field_simp
    norm_num
  | succ n => exact (S.coord n).law_second_moment (tagged n) e

lemma hybrid_sqrt_bound (tagged e : ℕ → Bool) (hs : Summable (S.error tagged))
    (A : Set CircleDigits.CircleX) (hA : MeasurableSet A) :
    (S.probability tagged).real (S.endpoint e ⁻¹' A) ≤
      Real.exp ((∑' n, S.error tagged n)/2)*Real.sqrt (volume.real A) :=
  hybridEndpoint_sqrt_bound (S.law tagged) S.radix_ge_two
    (fun i ω => digitEndpoint (e i) ω.2) (fun i => (digitEndpoint_measurable (e i)).comp measurable_snd)
    (S.error tagged) (S.error_nonneg tagged) hs (fun i => S.moment tagged i (e i)) A hA

lemma hybrid_ac (tagged e : ℕ → Bool) (hs : Summable (S.error tagged)) :
    Measure.map (S.endpoint e) (S.probability tagged) ≪ volume :=
  hybridEndpoint_absolutelyContinuous (S.law tagged) S.radix_ge_two
    (fun i ω => digitEndpoint (e i) ω.2) (fun i => (digitEndpoint_measurable (e i)).comp measurable_snd)
    (S.error tagged) (S.error_nonneg tagged) hs (fun i => S.moment tagged i (e i))

lemma ae_hybrid_gridFree (tagged e : ℕ → Bool) (hs : Summable (S.error tagged)) :
    ∀ᵐ ω ∂S.probability tagged, S.endpoint e ω ∈ gridFree S.radix := by
  have h := (S.hybrid_ac tagged e hs).ae_le (ae_gridFree S.radix S.radix_ge_two)
  exact (ae_map_iff (S.measurable_endpoint e).aemeasurable (by
    unfold gridFree
    simp only [Set.ofPred_forall]
    exact MeasurableSet.iInter (fun n => ((measurable_const_smul (denominator S.radix n)) (measurableSet_singleton 0)).compl))).mp h

end DigitSystem
end CircleCoupling

end

end OAI
end

section
-- module Solutions.OAIQ2_Rot.RotationWeights_ActualDigits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

universe uX

open MeasureTheory
open scoped ENNReal NNReal ComplexInnerProductSpace BigOperators
open MeasureTheory Filter Set Submodule
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ComplexInnerProductSpace
open MeasureTheory Filter Set
open Set
open scoped ComplexInnerProductSpace
open Set
open scoped ComplexInnerProductSpace
open MeasureTheory Set Filter Topology
open scoped BigOperators ComplexConjugate
open MeasureTheory Set Filter
open scoped BigOperators ENNReal
open Filter Set
open scoped Topology
open Filter Set
open scoped Topology
open Set MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter Set
open scoped Topology
open Set MeasureTheory
open scoped ENNReal Classical
open Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Topology
open scoped BigOperators
open scoped BigOperators
open Set
open Set
open Set
open Set MeasureTheory Filter
open scoped BigOperators ENNReal Topology Classical
open MeasureTheory Set Filter
open scoped ENNReal Topology
open MeasureTheory Set
open MeasureTheory Filter Set
open scoped Topology BoundedContinuousFunction
open MeasureTheory Set Filter Topology TopologicalSpace
open MeasureTheory Set
open scoped ENNReal BigOperators Classical
open MeasureTheory Set
open scoped BigOperators ENNReal Classical
open MeasureTheory Set
open scoped ENNReal
open MeasureTheory Set
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped BigOperators ENNReal Topology
open Set MeasureTheory Topology
open scoped symmDiff
open MeasureTheory Set
open scoped ENNReal BigOperators
open MeasureTheory Set
open scoped ENNReal

namespace CircleSampling

section

section
open Set Filter MeasureTheory
open scoped Topology BigOperators

lemma stageTagged_finite (j : ℕ) : {i | stageTagged j i=true}.Finite := by
  apply (finite_Iio (blockEnd (j+1))).subset
  intro i hi
  have hb : coordinateBlock i=j := of_decide_eq_true hi
  have hr := (blocks.number_spec i).2
  change i<blockEnd (j+1)
  change i<blockEnd (coordinateBlock i)+blockLength (coordinateBlock i) at hr
  have he (t : ℕ) : blockEnd t+blockLength t=blockEnd (t+1) := rfl
  rw [he] at hr
  exact hr.trans_le (blockEnd_strictMono.monotone (by omega))
lemma summable_stageTagError (j : ℕ) :
    Summable (fun i => (if stageTagged j i then (10:ℝ) else 0)/(blockLength (coordinateBlock i):ℝ)) := by
  apply summable_of_hasFiniteSupport
  apply (stageTagged_finite j).subset
  intro i hi
  simp only [Function.mem_support] at hi
  cases h : stageTagged j i
  · simp [h] at hi
  · exact h

lemma summable_kappa_sq : Summable (fun j => (kappa j)^2) := by
  have hs : Summable (fun j : ℕ => (1:ℝ)/(j:ℝ)^2) := by
    exact Real.summable_one_div_nat_pow.mpr (by norm_num : 1<2)
  have ht := (summable_nat_add_iff 1).mpr hs
  have he : (fun j => (kappa j)^2)=(fun j => (1/(100:ℝ)^2)*(1/((j+1:ℕ):ℝ)^2)) := by
    funext j
    dsimp [kappa]
    push_cast
    field_simp
  rw [he]
  exact ht.mul_left (1/(100:ℝ)^2)

lemma summable_coordinateKappaError :
    Summable (fun i => 60*(kappa (coordinateBlock i))^2/(blockLength (coordinateBlock i):ℝ)) := by
  apply blocks.equiv.summable_iff.mp
  apply (summable_sigma_of_nonneg (fun x : Σ j, Fin (blocks.m j) => (by positivity :
    0≤60*(kappa (coordinateBlock (blocks.equiv x)))^2/(blockLength (coordinateBlock (blocks.equiv x)):ℝ)))).mpr
  refine ⟨fun _ => Summable.of_finite,?_⟩
  have he (j : ℕ) : (∑' i : Fin (blocks.m j),60*(kappa (coordinateBlock (blocks.equiv ⟨j,i⟩)))^2/
    (blockLength (coordinateBlock (blocks.equiv ⟨j,i⟩)):ℝ))=60*(kappa j)^2 := by
    simp_rw [coordinateBlock_equiv]
    rw [tsum_fintype]
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    change (blockLength j:ℝ)*(_/(blockLength j:ℝ))=_
    have hm : (blockLength j:ℝ)≠0 := Nat.cast_ne_zero.mpr (scaleStep j).mpos.ne'
    field_simp
  simp_rw [he]
  exact summable_kappa_sq.mul_left 60
end

open MeasureTheory Set Filter CircleCoupling
open scoped BigOperators ENNReal Topology

lemma actual_error_succ (j i : ℕ) : actualSystem.error (stageTagged j) (i+1)=
    60*(kappa (coordinateBlock i))^2/(blockLength (coordinateBlock i):ℝ)+
    (if stageTagged j i then 10 else 0)/(blockLength (coordinateBlock i):ℝ) := by
  dsimp [DigitSystem.error,actualSystem,actualCoordinate]
  split <;> ring
lemma summable_actual_error (j : ℕ) : Summable (actualSystem.error (stageTagged j)) := by
  apply (summable_nat_add_iff 1).mp
  simp_rw [actual_error_succ]
  exact summable_coordinateKappaError.add (summable_stageTagError j)

end

open MeasureTheory Set Filter CircleCoupling
open scoped BigOperators ENNReal Topology

lemma actual_error_sum (j : ℕ) : (∑' i,actualSystem.error (stageTagged j) i)=
    60*(∑' s,(kappa s)^2)+10 := by
  rw [tsum_eq_zero_add' ((summable_nat_add_iff 1).mpr (summable_actual_error j)),show actualSystem.error (stageTagged j) 0=0 by rfl,zero_add]
  simp_rw [actual_error_succ]
  rw [summable_coordinateKappaError.tsum_add (summable_stageTagError j)]
  have hκ : (∑' i,60*(kappa (coordinateBlock i))^2/(blockLength (coordinateBlock i):ℝ))=
      60*(∑' s,(kappa s)^2) := by
    rw [←blocks.equiv.tsum_eq]
    have hs := blocks.equiv.summable_iff.mpr summable_coordinateKappaError
    simp only [Function.comp_def] at hs
    rw [hs.tsum_sigma]
    have he (s : ℕ) : (∑' i : Fin (blocks.m s),60*(kappa (coordinateBlock (blocks.equiv ⟨s,i⟩)))^2/
        (blockLength (coordinateBlock (blocks.equiv ⟨s,i⟩)):ℝ))=60*(kappa s)^2 := by
      simp_rw [coordinateBlock_equiv]
      rw [tsum_fintype]
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
      change (blockLength s:ℝ)*(_/(blockLength s:ℝ))=_
      have hm : (blockLength s:ℝ)≠0 := Nat.cast_ne_zero.mpr (scaleStep s).mpos.ne'
      field_simp
    simp_rw [he]
    exact tsum_mul_left
  have ht : (∑' i,(if stageTagged j i then (10:ℝ) else 0)/(blockLength (coordinateBlock i):ℝ))=10 := by
    rw [←blocks.equiv.tsum_eq]
    have hs := blocks.equiv.summable_iff.mpr (summable_stageTagError j)
    simp only [Function.comp_def] at hs
    rw [hs.tsum_sigma]
    have he (s : ℕ) : (∑' i : Fin (blocks.m s),
        (if stageTagged j (blocks.equiv ⟨s,i⟩) then (10:ℝ) else 0)/
        (blockLength (coordinateBlock (blocks.equiv ⟨s,i⟩)):ℝ))=if s=j then 10 else 0 := by
      simp only [stageTagged,coordinateBlock_equiv,decide_eq_true_eq]
      split_ifs with hs
      · rw [tsum_fintype]
        simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
        change (blockLength s:ℝ)*(10/(blockLength s:ℝ))=10
        have hm : (blockLength s:ℝ)≠0 := Nat.cast_ne_zero.mpr (scaleStep s).mpos.ne'
        field_simp
      · simp
    simp_rw [he]
    exact tsum_ite_eq j (fun _ => 10)
  rw [hκ,ht]

lemma marginalConstant_pos : 0 < marginalConstant := Real.exp_pos _
lemma actual_hybrid_bound (j : ℕ) (e : ℕ → Bool) (A : Set CircleDigits.CircleX) (hA : MeasurableSet A) :
    (actualSystem.probability (stageTagged j)).real (actualSystem.endpoint e ⁻¹' A) ≤
      marginalConstant*Real.sqrt (volume.real A) := by
  have hh := actualSystem.hybrid_sqrt_bound (stageTagged j) e (summable_actual_error j) A hA
  rw [actual_error_sum] at hh
  convert hh using 1
  unfold marginalConstant
  congr 2
  ring
end CircleSampling

namespace CircleDigits
open Filter Set
open scoped Topology BigOperators

lemma hybrid_order {b : ℕ → ℕ} {d e : Digits b} (h : ∀ i,d i ≤ e i) (D i : ℕ) : d i ≤ hybrid d e D i := by
  unfold hybrid
  split_ifs <;> first | exact h i | rfl
lemma hybrid_tail {b : ℕ → ℕ} (hb : ∀ i,2 ≤ b i) (d e : Digits b) (D : ℕ) :
    scaledTail b (hybrid d e D) D=scaledTail b d D := by
  rw [scaledTail_tsum hb,scaledTail_tsum hb]
  congr 1
  apply tsum_congr
  intro i
  simp only [digitTerm,hybrid,show ¬i+D<D by omega,ite_false]
lemma hybrid_grid {b : ℕ → ℕ} (hb : ∀ i,2 ≤ b i) (d e : Digits b) (D : ℕ) :
    ∃ a : Fin (denominator b D), endpoint b (hybrid d e D)-endpoint b d=(((a.val:ℝ)/(denominator b D:ℝ):ℝ):CircleX) := by
  have hz : denominator b D • (endpoint b (hybrid d e D)-endpoint b d)=0 := by
    rw [nsmul_sub,←scaledTail_coe,←scaledTail_coe,hybrid_tail hb,sub_self]
  obtain ⟨a,ha,he⟩ := (AddCircle.nsmul_eq_zero_iff (denominator_pos hb D)).mp hz
  exact ⟨⟨a,ha⟩,by simpa only [mul_one] using he.symm⟩
lemma hybrid_expansion_tendsto {b : ℕ → ℕ} (hb : ∀ i,2 ≤ b i) (d e : Digits b) :
    Tendsto (fun D => expansion b (hybrid d e D)) atTop (𝓝 (expansion b e)) := by
  have hprefix (D : ℕ) : ∑ i∈Finset.range D,digitTerm b (hybrid d e D) i = ∑ i∈Finset.range D,digitTerm b e i := by
    apply Finset.sum_congr rfl
    intro i hi
    simp only [digitTerm,hybrid,Finset.mem_range.mp hi,ite_true]
  have hbound (D : ℕ) : |expansion b (hybrid d e D)-expansion b e| ≤ (denominator b D:ℝ)⁻¹ := by
    have hh := expansion_tail_bound hb (hybrid d e D) D
    have he := expansion_tail_bound hb e D
    rw [hprefix] at hh
    exact abs_le.mpr ⟨by linarith,by linarith⟩
  apply tendsto_iff_dist_tendsto_zero.mpr
  apply squeeze_zero (fun D => dist_nonneg) (fun D => ?_) (denominator_inv_tendsto hb)
  simpa only [Real.dist_eq] using hbound D
lemma hybrid_endpoint_tendsto {b : ℕ → ℕ} (hb : ∀ i,2 ≤ b i) (d e : Digits b) :
    Tendsto (fun D => endpoint b (hybrid d e D)) atTop (𝓝 (endpoint b e)) :=
  ((AddCircle.continuous_mk' 1).tendsto _).comp (hybrid_expansion_tendsto hb d e)
end CircleDigits

namespace CircleSampling
open MeasureTheory Set Filter ContinuousCircleWeight CircleCoupling
open scoped Topology ENNReal ComplexInnerProductSpace
lemma firstEndpoint_measurable : Measurable firstEndpoint := actualSystem.measurable_endpoint _
lemma lastEndpoint_measurable : Measurable lastEndpoint := actualSystem.measurable_endpoint _
lemma hybridEndpoint_measurable (D : ℕ) : Measurable (hybridEndpoint D) := actualSystem.measurable_endpoint _
lemma hybrid_observe (D : ℕ) (ω : ActualSamples) :
    actualSystem.observe (hybridChoice D) ω = CircleDigits.hybrid
      (actualSystem.observe (fun _ => false) ω) (actualSystem.observe (fun _ => true) ω) (D+1) := by
  funext i
  simp only [DigitSystem.observe,CircleDigits.hybrid,hybridChoice]
  by_cases hi : i<D+1 <;> simp [hi]
lemma actual_hybrid_grid (D : ℕ) (ω : ActualSamples) :
    ∃ a : Fin (frequency (D+1)), hybridEndpoint D ω=firstEndpoint ω+rationalPoint D a := by
  have hh := CircleDigits.hybrid_grid actualSystem.radix_ge_two
    (actualSystem.observe (fun _ => false) ω) (actualSystem.observe (fun _ => true) ω) (D+1)
  rw [←hybrid_observe,actual_denominator] at hh
  obtain ⟨a,ha⟩ := hh
  exact ⟨a,by simpa [hybridEndpoint,firstEndpoint,DigitSystem.endpoint,rationalPoint] using (sub_eq_iff_eq_add.mp ha).trans (add_comm _ _)⟩
lemma actual_hybrid_tendsto (ω : ActualSamples) : Tendsto (fun D => hybridEndpoint D ω) atTop (𝓝 (lastEndpoint ω)) := by
  have hh := (CircleDigits.hybrid_endpoint_tendsto actualSystem.radix_ge_two
    (actualSystem.observe (fun _ => false) ω) (actualSystem.observe (fun _ => true) ω)).comp (tendsto_add_atTop_nat 1)
  simpa only [hybridEndpoint,lastEndpoint,DigitSystem.endpoint,hybrid_observe,Function.comp_def] using hh

lemma ae_endpoint_good (j : ℕ) (e : ℕ → Bool) :
    ∀ᵐ ω ∂actualSystem.probability (stageTagged j), actualSystem.endpoint e ω∈modelGood :=
  ae_of_ae_map (actualSystem.measurable_endpoint e).aemeasurable
    ((actualSystem.hybrid_ac (stageTagged j) e (summable_actual_error j)).ae_le model_good_ae)
local instance instMeasurableSpaceSubtypePreLpIntComplexMemAddSubgroupFiberHilbert_1_r50aa99_1 : MeasurableSpace FiberHilbert := borel FiberHilbert
lemma ae_hybrid_coordinate_order (j D : ℕ) :
    ∀ᵐ ω ∂actualSystem.probability (stageTagged j), ∀ i,
      CircleModel.Xi modelFrequency i (firstEndpoint ω) ≤ CircleModel.Xi modelFrequency i (hybridEndpoint D ω) := by
  filter_upwards [actualSystem.ae_digit_order (stageTagged j),
    actualSystem.ae_hybrid_gridFree (stageTagged j) (fun _ => false) (summable_actual_error j),
    actualSystem.ae_hybrid_gridFree (stageTagged j) (hybridChoice D) (summable_actual_error j)] with ω hω hx hy
  intro i
  change (AddCircle.measurableEquivIco 1 0 (frequency (i+1) • actualSystem.endpoint (fun _ => false) ω)).val ≤
    (AddCircle.measurableEquivIco 1 0 (frequency (i+1) • actualSystem.endpoint (hybridChoice D) ω)).val
  rw [←actual_denominator]
  dsimp only [DigitSystem.endpoint] at hx hy ⊢
  rw [CircleDigits.scaledTail_repr actualSystem.radix_ge_two _ hx,CircleDigits.scaledTail_repr actualSystem.radix_ge_two _ hy]
  apply CircleDigits.scaledTail_mono actualSystem.radix_ge_two
  intro k
  rw [hybrid_observe]
  exact CircleDigits.hybrid_order hω (D+1) k

lemma cappedDiagonal_eq_of_ratio_le {X : Type uX} (F : ℤ → X → ℝ) (hF : ∀ k x,0<F k x)
    {x y : X} (B C : ℝ≥0) (hB : ∀ k,F k y/F k x≤B) (hC : ∀ k,F k y/F k x≤C) :
    cappedDiagonal F B x y=cappedDiagonal F C x y := by
  ext u k
  simp only [cappedDiagonal,lpDiagonal_apply,cappedRatio,max_eq_right (div_pos (hF _ _) (hF _ _)).le,
    min_eq_right (hB _),min_eq_right (hC _)]

lemma ae_hybrid_pair (P : ModelProjectionField) (j D : ℕ) :
    ∀ᵐ ω ∂actualSystem.probability (stageTagged j),
      (1-P.p (hybridEndpoint D ω))*cappedDiagonal modelF 1 (firstEndpoint ω) (hybridEndpoint D ω)*P.p (firstEndpoint ω)=0 := by
  have hg : ∀ᵐ x : CircleX, ∀ a : Fin (frequency (D+1)),
      (1-P.p (x+rationalPoint D a))*cappedDiagonal modelF (rationalCap D) x (x+rationalPoint D a)*P.p x=0 :=
    ae_all_iff.mpr (rational_pair P D)
  have hh := ae_of_ae_map firstEndpoint_measurable.aemeasurable
    ((actualSystem.hybrid_ac (stageTagged j) (fun _ => false) (summable_actual_error j)).ae_le hg)
  filter_upwards [hh,ae_endpoint_good j (fun _ => false),ae_endpoint_good j (hybridChoice D),ae_hybrid_coordinate_order j D] with ω hω hx hy hord
  obtain ⟨a,ha⟩ := actual_hybrid_grid D ω
  have hb (k : ℤ) : modelF k (hybridEndpoint D ω)/modelF k (firstEndpoint ω) ≤ 1 := modelF_ratio_ordered hx hy hord k
  have he := cappedDiagonal_eq_of_ratio_le modelF modelF_pos (rationalCap D) 1
    (fun k => (hb k).trans (rationalCap_ge_one D)) hb
  rw [←he,ha]
  exact hω a

lemma actualPairLaw_uc (j : ℕ) (e : ℕ → ℕ → Bool) :
    ∀ ε : ℝ≥0∞, ε≠0 → ∃ δ : ℝ≥0∞, δ≠0 ∧ ∀ A : Set CircleX, volume A<δ → ∀ D,
      (actualPairLaw j (e D):Measure (CircleX×CircleX)) (Prod.fst ⁻¹' A) ≤ ε ∧
      (actualPairLaw j (e D):Measure (CircleX×CircleX)) (Prod.snd ⁻¹' A) ≤ ε := by
  have hf := finiteMeasure_sqrt_uc volume (fun D => (actualPairLaw j (e D):Measure (CircleX×CircleX))) Prod.fst measurable_fst marginalConstant_pos
    (by
      intro D A hA
      change (Measure.map (fun ω => (firstEndpoint ω,actualSystem.endpoint (e D) ω)) (actualSystem.probability (stageTagged j)) (Prod.fst ⁻¹' A)).toReal ≤ _
      rw [Measure.map_apply (firstEndpoint_measurable.prodMk (actualSystem.measurable_endpoint _)) (hA.preimage measurable_fst)]
      exact actual_hybrid_bound j (fun _ => false) A hA)
  have hs := finiteMeasure_sqrt_uc volume (fun D => (actualPairLaw j (e D):Measure (CircleX×CircleX))) Prod.snd measurable_snd marginalConstant_pos
    (by
      intro D A hA
      change (Measure.map (fun ω => (firstEndpoint ω,actualSystem.endpoint (e D) ω)) (actualSystem.probability (stageTagged j)) (Prod.snd ⁻¹' A)).toReal ≤ _
      rw [Measure.map_apply (firstEndpoint_measurable.prodMk (actualSystem.measurable_endpoint _)) (hA.preimage measurable_snd)]
      exact actual_hybrid_bound j (e D) A hA)
  intro ε hε
  obtain ⟨δ,hδ,hf⟩ := hf ε hε
  obtain ⟨η,hη,hs⟩ := hs ε hε
  refine ⟨min δ η,ne_of_gt (lt_min (pos_iff_ne_zero.mpr hδ) (pos_iff_ne_zero.mpr hη)),?_⟩
  intro A hA D
  exact ⟨hf A (lt_of_lt_of_le hA (min_le_left _ _)) D,hs A (lt_of_lt_of_le hA (min_le_right _ _)) D⟩

lemma actualPairLaw_tendsto (j : ℕ) : Tendsto (fun D => actualPairLaw j (hybridChoice D)) atTop (𝓝 (actualPairLaw j (fun _ => true))) := by
  apply FiniteMeasure.tendsto_iff_forall_integral_tendsto.mpr
  intro φ
  have he (e : ℕ → Bool) : (∫ z,φ z ∂(actualPairLaw j e:Measure (CircleX×CircleX)))=
      ∫ ω,φ (firstEndpoint ω,actualSystem.endpoint e ω) ∂actualSystem.probability (stageTagged j) :=
    integral_map (firstEndpoint_measurable.prodMk (actualSystem.measurable_endpoint e)).aemeasurable φ.continuous.measurable.aestronglyMeasurable
  simp_rw [he]
  apply tendsto_integral_of_dominated_convergence (fun _ => ‖φ‖)
  · intro D; exact (φ.continuous.measurable.comp (firstEndpoint_measurable.prodMk (hybridEndpoint_measurable D))).aestronglyMeasurable
  · exact integrable_const _
  · intro D; exact ae_of_all _ (fun ω => φ.norm_coe_le_norm _)
  · exact ae_of_all _ (fun ω => (φ.continuous.tendsto _).comp (tendsto_const_nhds.prodMk_nhds (actual_hybrid_tendsto ω)))

lemma actual_pair_identity (P : ModelProjectionField) (j : ℕ) :
    ∀ᵐ ω ∂actualSystem.probability (stageTagged j),
      (1-P.p (lastEndpoint ω))*cappedDiagonal modelF 1 (firstEndpoint ω) (lastEndpoint ω)*P.p (firstEndpoint ω)=0 := by
  have hg (D : ℕ) : ∀ᵐ z ∂(actualPairLaw j (hybridChoice D):Measure (CircleX×CircleX)),
      (1-P.p z.2)*cappedDiagonal modelF 1 z.1 z.2*P.p z.1=0 := by
    have hm : MeasurableSet {z : CircleX×CircleX | (1-P.p z.2)*cappedDiagonal modelF 1 z.1 z.2*P.p z.1=0} := by
      convert measurableSet_cappedPairRelation P.p P.measurable modelF modelF_measurable 1 using 1
      ext z; exact (cappedPairRelation_iff P.p modelF 1 z.1 z.2).symm
    exact (ae_map_iff (firstEndpoint_measurable.prodMk (hybridEndpoint_measurable D)).aemeasurable hm).mpr (ae_hybrid_pair P j D)
  have hh := capped_pair_identity_transfer (μ := volume) (νs := fun D => actualPairLaw j (hybridChoice D))
    P.p P.norm_le P.measurable modelF modelF_measurable modelF_pos 1 (actualPairLaw_tendsto j) hg (actualPairLaw_uc j hybridChoice)
  exact ae_of_ae_map (firstEndpoint_measurable.prodMk lastEndpoint_measurable).aemeasurable hh
end CircleSampling

end

end OAI
end

section
-- module Solutions.OAIQ2_Rot.RotationWeights_Thresholds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CircleSampling

open MeasureTheory
open scoped ENNReal NNReal ComplexInnerProductSpace BigOperators
open MeasureTheory Filter Set Submodule
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ComplexInnerProductSpace
open MeasureTheory Filter Set
open Set
open scoped ComplexInnerProductSpace
open Set
open scoped ComplexInnerProductSpace
open MeasureTheory Set Filter Topology
open scoped BigOperators ComplexConjugate
open MeasureTheory Set Filter
open scoped BigOperators ENNReal
open Filter Set
open scoped Topology
open Filter Set
open scoped Topology
open Set MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter Set
open scoped Topology
open Set MeasureTheory
open scoped ENNReal Classical
open Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Topology
open scoped BigOperators
open scoped BigOperators
open Set
open Set
open Set
open Set MeasureTheory Filter
open scoped BigOperators ENNReal Topology Classical
open MeasureTheory Set Filter
open scoped ENNReal Topology
open MeasureTheory Set
open MeasureTheory Filter Set
open scoped Topology BoundedContinuousFunction
open MeasureTheory Set Filter Topology TopologicalSpace
open MeasureTheory Set
open scoped ENNReal BigOperators Classical
open MeasureTheory Set
open scoped BigOperators ENNReal Classical
open MeasureTheory Set
open scoped ENNReal
open MeasureTheory Set
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped BigOperators ENNReal Topology
open Set MeasureTheory Topology
open scoped symmDiff
open MeasureTheory Set
open scoped ENNReal BigOperators
open MeasureTheory Set
open scoped ENNReal
open MeasureTheory Set
open scoped BigOperators ENNReal

section
open MeasureTheory Set Filter CircleCoupling CircleDigits
open scoped ENNReal

lemma ae_regularSamples (j : ℕ) : ∀ᵐ ω ∂actualSystem.probability (stageTagged j),ω∈regularSamples := by
  filter_upwards [actualSystem.ae_supported (stageTagged j),ae_endpoint_good j (fun _ => false),
    ae_endpoint_good j (fun _ => true),actualSystem.ae_hybrid_gridFree (stageTagged j) (fun _ => false) (summable_actual_error j),
    actualSystem.ae_hybrid_gridFree (stageTagged j) (fun _ => true) (summable_actual_error j)] with ω hs hx hy hfx hfy
  exact ⟨hs,hx,hy,hfx,hfy⟩
end

open MeasureTheory Set CircleCoupling CircleDigits
open scoped ENNReal


end CircleSampling

end

end OAI
end

section
-- module Solutions.OAIQ2_Rot.RotationWeights_LaurentCoefficients
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory
open scoped ENNReal NNReal ComplexInnerProductSpace BigOperators
open MeasureTheory Filter Set Submodule
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ComplexInnerProductSpace
open MeasureTheory Filter Set
open Set
open scoped ComplexInnerProductSpace
open Set
open scoped ComplexInnerProductSpace
open MeasureTheory Set Filter Topology
open scoped BigOperators ComplexConjugate
open MeasureTheory Set Filter
open scoped BigOperators ENNReal
open Filter Set
open scoped Topology
open Filter Set
open scoped Topology
open Set MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter Set
open scoped Topology
open Set MeasureTheory
open scoped ENNReal Classical
open Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Topology
open scoped BigOperators
open scoped BigOperators
open Set
open Set
open Set
open Set MeasureTheory Filter
open scoped BigOperators ENNReal Topology Classical
open MeasureTheory Set Filter
open scoped ENNReal Topology
open MeasureTheory Set
open MeasureTheory Filter Set
open scoped Topology BoundedContinuousFunction
open MeasureTheory Set Filter Topology TopologicalSpace
open MeasureTheory Set
open scoped ENNReal BigOperators Classical
open MeasureTheory Set
open scoped BigOperators ENNReal Classical
open MeasureTheory Set
open scoped ENNReal
open MeasureTheory Set
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped BigOperators ENNReal Topology
open Set MeasureTheory Topology
open scoped symmDiff
open MeasureTheory Set
open scoped ENNReal BigOperators
open MeasureTheory Set
open scoped ENNReal
open MeasureTheory Set
open scoped BigOperators ENNReal

namespace ContinuousCircleWeight

section
open MeasureTheory
open scoped ENNReal

lemma fiber_squares (ξ : FiberHilbert) : (∑' i,‖ξ i‖ₑ^2)=ENNReal.ofReal (‖ξ‖^2) := by
  have hs : HasSum (fun i => ‖ξ i‖^2) (‖ξ‖^2) := by
    simpa using lp.hasSum_norm (show (0:ℝ)<(2:ℝ≥0∞).toReal by norm_num) ξ
  rw [←hs.tsum_eq,ENNReal.ofReal_tsum_of_nonneg (fun i => sq_nonneg _) hs.summable]
  apply tsum_congr
  intro i
  rw [ENNReal.ofReal_pow (norm_nonneg _),ofReal_norm]
lemma fiber_squares_le {ξ : FiberHilbert} (hξ : ‖ξ‖ ≤ 1) : (∑' i,‖ξ i‖ₑ^2) ≤ 1 := by
  rw [fiber_squares]
  have hh : ‖ξ‖^2 ≤ (1:ℝ) := by nlinarith [norm_nonneg ξ]
  exact (ENNReal.ofReal_le_ofReal hh).trans_eq (by simp)
lemma fiber_product_le {ξ η : FiberHilbert} (hξ : ‖ξ‖ ≤ 1) (hη : ‖η‖ ≤ 1) :
    (∑' i,‖ξ i‖ₑ*‖η i‖ₑ) ≤ 1 := by
  have hc : (2:ℝ≥0∞).toReal.HolderConjugate (2:ℝ≥0∞).toReal := by norm_num [Real.holderConjugate_iff]
  have hh := lp.tsum_mul_le_mul_norm hc ξ η
  have ht : ∑' i,‖ξ i‖*‖η i‖ ≤ 1 := hh.2.trans (by nlinarith [norm_nonneg ξ,norm_nonneg η])
  have he : (∑' i,‖ξ i‖ₑ*‖η i‖ₑ)=ENNReal.ofReal (∑' i,‖ξ i‖*‖η i‖) := by
    rw [ENNReal.ofReal_tsum_of_nonneg (fun i => mul_nonneg (norm_nonneg _) (norm_nonneg _)) hh.1]
    simp only [ENNReal.ofReal_mul (norm_nonneg _),ofReal_norm]
  rw [he]
  exact (ENNReal.ofReal_le_ofReal ht).trans_eq (by simp)
lemma projection_vector_norm (q : FiberOperator) (hq : IsStarProjection q) (k : ℤ) :
    ‖q (lp.single 2 k 1)‖ ≤ 1 := by
  have hh := q.le_opNorm (lp.single 2 k 1)
  have he : ‖(lp.single 2 k (1:ℂ):FiberHilbert)‖=1 := by simp
  rw [he,mul_one] at hh
  exact hh.trans (hq.norm_le q)
end

open scoped BigOperators

end ContinuousCircleWeight

namespace CircleSampling

section

section
open MeasureTheory Set Filter ContinuousCircleWeight
open scoped Topology ENNReal ComplexInnerProductSpace BigOperators
attribute [local instance] OAI.CircleSampling.instMeasurableSpaceSubtypePreLpIntComplexMemAddSubgroupFiberHilbert_2
local instance instBorelSpaceSubtypePreLpIntComplexMemAddSubgroupFiberHilbert_2 : BorelSpace FiberHilbert := ⟨rfl⟩

lemma modelColumn_norm (P : ModelProjectionField) (x : CircleX) : ‖modelColumn P x‖ ≤ 1 := projection_vector_norm _ (P.projection x) 0
lemma modelComplement_norm (P : ModelProjectionField) (x : CircleX) : ‖modelComplement P x‖ ≤ 1 := projection_vector_norm _ (P.projection x).one_sub 0
lemma modelColumn_measurable (P : ModelProjectionField) : Measurable (modelColumn P) := P.measurable 0
lemma modelComplement_measurable (P : ModelProjectionField) : Measurable (modelComplement P) :=
  (measurable_const.sub (modelColumn_measurable P) : Measurable (fun x => (lp.single 2 0 1: FiberHilbert)-modelColumn P x))
lemma modelColumn_coordinate (P : ModelProjectionField) (k : ℤ) : Measurable (fun x => modelColumn P x k) :=
  (lp.evalCLM ℂ (fun _ : ℤ => ℂ) (2:ℝ≥0∞) k).continuous.measurable.comp (modelColumn_measurable P)
lemma modelComplement_coordinate (P : ModelProjectionField) (k : ℤ) : Measurable (fun x => modelComplement P x k) :=
  (lp.evalCLM ℂ (fun _ : ℤ => ℂ) (2:ℝ≥0∞) k).continuous.measurable.comp (modelComplement_measurable P)

lemma regular_model_order {ω : ActualSamples} (hω : ω∈regularSamples) (k : ℤ) :
    modelF k (lastEndpoint ω) ≤ modelF k (firstEndpoint ω) :=
  (div_le_one (modelF_pos _ _)).mp (modelF_ratio_ordered hω.2.1 hω.2.2.1 (regular_order hω) k)
lemma model_pair_convolution (P : ModelProjectionField) {ω : ActualSamples} (hω : ω∈regularSamples)
    (hpair : (1-P.p (lastEndpoint ω))*cappedDiagonal modelF 1 (firstEndpoint ω) (lastEndpoint ω)*P.p (firstEndpoint ω)=0)
    (hinv : (1-P.p (lastEndpoint ω))*fiberCocycleShift (fun k => modelF k (lastEndpoint ω))
      (fun k => modelF_pos k (lastEndpoint ω)) (modelF_antitone (lastEndpoint ω))*P.p (lastEndpoint ω)=0) (n : ℕ) :
    Summable (fun v => modelTerm P n v ω) ∧ (∑' v,modelTerm P n v ω)=0 := by
  let x := firstEndpoint ω
  let y := lastEndpoint ω
  have ho : ∀ k,modelF k y ≤ modelF k x := regular_model_order hω
  have hd : cappedDiagonal modelF 1 x y=cocycleRatioDiagonal (fun k => modelF k x) (fun k => modelF k y)
      (fun k => modelF_pos k x) (fun k => modelF_pos k y) ho := by
    ext u k
    rw [cappedDiagonal_apply_of_bound modelF modelF_pos 1 x y (fun k => (div_le_one (modelF_pos _ _)).mpr (ho k)),cocycleRatioDiagonal_apply]
  have hf : P.p y (cocycleRatioDiagonal (fun k => modelF k x) (fun k => modelF k y)
      (fun k => modelF_pos k x) (fun k => modelF_pos k y) ho (modelColumn P x))=
      cocycleRatioDiagonal (fun k => modelF k x) (fun k => modelF k y)
      (fun k => modelF_pos k x) (fun k => modelF_pos k y) ho (modelColumn P x) := by
    have hh := congrArg (fun A : FiberOperator => A (lp.single 2 0 1)) hpair
    change cappedDiagonal modelF 1 x y (modelColumn P x)-P.p y (cappedDiagonal modelF 1 x y (modelColumn P x))=0 at hh
    rw [hd] at hh
    exact (sub_eq_zero.mp hh).symm
  exact fiber_full_convolution (fun k => modelF k x) (fun k => modelF k y) (fun k => modelF_pos k x)
    (fun k => modelF_pos k y) (modelF_antitone y) ho (P.p y) (P.projection y) hinv (modelColumn P x) (lp.single 2 0 1) hf n
lemma model_convolution_ae (P : ModelProjectionField) (j : ℕ) :
    ∀ᵐ ω ∂actualSystem.probability (stageTagged j),ω∈regularSamples ∧ ∀ n : ℕ,
      Summable (fun v => modelTerm P n v ω) ∧ (∑' v,modelTerm P n v ω)=0 := by
  have hi : ∀ᵐ ω ∂actualSystem.probability (stageTagged j),
      (1-P.p (lastEndpoint ω))*fiberCocycleShift (fun k => modelF k (lastEndpoint ω)) (fun k => modelF_pos k (lastEndpoint ω)) (modelF_antitone (lastEndpoint ω))*P.p (lastEndpoint ω)=0 :=
    ae_of_ae_map lastEndpoint_measurable.aemeasurable ((actualSystem.hybrid_ac (stageTagged j) (fun _ => true) (summable_actual_error j)).ae_le P.invariant)
  filter_upwards [ae_regularSamples j,actual_pair_identity P j,hi] with ω hω hp hi
  exact ⟨hω,fun n => model_pair_convolution P hω hp hi n⟩

end

open MeasureTheory Set Filter ContinuousCircleWeight
open scoped ENNReal ComplexInnerProductSpace BigOperators

end

open MeasureTheory Set Filter CircleCoupling CircleDigits
open scoped ENNReal

end CircleSampling

end

end OAI
end

section
-- module Solutions.OAIQ2_Rot.RotationWeights_MaskedEstimates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ContinuousCircleWeight

universe uΩ uX uι uY

open MeasureTheory
open scoped ENNReal NNReal ComplexInnerProductSpace BigOperators
open MeasureTheory Filter Set Submodule
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ComplexInnerProductSpace
open MeasureTheory Filter Set
open Set
open scoped ComplexInnerProductSpace
open Set
open scoped ComplexInnerProductSpace
open MeasureTheory Set Filter Topology
open scoped BigOperators ComplexConjugate
open MeasureTheory Set Filter
open scoped BigOperators ENNReal
open Filter Set
open scoped Topology
open Filter Set
open scoped Topology
open Set MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter Set
open scoped Topology
open Set MeasureTheory
open scoped ENNReal Classical
open Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Topology
open scoped BigOperators
open scoped BigOperators
open Set
open Set
open Set
open Set MeasureTheory Filter
open scoped BigOperators ENNReal Topology Classical
open MeasureTheory Set Filter
open scoped ENNReal Topology
open MeasureTheory Set
open MeasureTheory Filter Set
open scoped Topology BoundedContinuousFunction
open MeasureTheory Set Filter Topology TopologicalSpace
open MeasureTheory Set
open scoped ENNReal BigOperators Classical
open MeasureTheory Set
open scoped BigOperators ENNReal Classical
open MeasureTheory Set
open scoped ENNReal
open MeasureTheory Set
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped BigOperators ENNReal Topology
open Set MeasureTheory Topology
open scoped symmDiff
open MeasureTheory Set
open scoped ENNReal BigOperators
open MeasureTheory Set
open scoped ENNReal
open MeasureTheory Set
open scoped BigOperators ENNReal

open MeasureTheory Set
open scoped ENNReal NNReal BigOperators

theorem endpoint_mask_integral_le {Ω : Type uΩ} {X : Type uX} [MeasurableSpace Ω]
    [MeasurableSpace X] (μ : Measure Ω) (x : Ω → X) (hx : Measurable x)
    (H : Set Ω) (hH : MeasurableSet H) (δ : ℝ≥0∞)
    (hdom : Measure.map x (μ.restrict H) ≤ δ • Measure.map x μ)
    (a : X → ℝ≥0∞) (ha : Measurable a) :
    (∫⁻ ω, H.indicator (fun ω => a (x ω)) ω ∂μ) ≤
      δ * ∫⁻ ω, a (x ω) ∂μ := by
  rw [lintegral_indicator hH, ← lintegral_map ha hx]
  calc
    _ ≤ ∫⁻ z, a z ∂δ • Measure.map x μ := lintegral_mono' hdom le_rfl
    _ = _ := by rw [lintegral_smul_measure, lintegral_map ha hx]; rfl

theorem endpoint_masked_squares {Ω : Type uΩ} {X : Type uX} {ι : Type uι} [MeasurableSpace Ω]
    [MeasurableSpace X] [Countable ι] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (x : Ω → X) (hx : Measurable x)
    (H : ι → Set Ω) (hH : ∀ i, MeasurableSet (H i)) (δ : ℝ≥0∞)
    (hdom : ∀ i, Measure.map x (μ.restrict (H i)) ≤ δ • Measure.map x μ)
    (a : ι → X → ℝ≥0∞) (ha : ∀ i, Measurable (a i))
    (hsq : ∀ᵐ ω ∂μ, (∑' i, a i (x ω) ^ 2) ≤ 1) :
    (∫⁻ ω, ∑' i, (H i).indicator (fun ω => a i (x ω) ^ 2) ω ∂μ) ≤ δ := by
  have hm (i : ι) : Measurable (fun ω => (H i).indicator
      (fun ω => a i (x ω) ^ 2) ω) :=
    (((ha i).comp hx).pow_const 2).indicator (hH i)
  rw [lintegral_tsum (fun i => (hm i).aemeasurable)]
  calc
    _ ≤ ∑' i, δ * ∫⁻ ω, a i (x ω) ^ 2 ∂μ :=
      ENNReal.tsum_le_tsum (fun i => endpoint_mask_integral_le μ x hx (H i) (hH i)
        δ (hdom i) (fun z => a i z ^ 2) ((ha i).pow_const 2))
    _ = δ * ∫⁻ ω, ∑' i, a i (x ω) ^ 2 ∂μ := by
      rw [ENNReal.tsum_mul_left]
      congr 1
      exact (lintegral_tsum (fun i => show AEMeasurable
        (fun ω => a i (x ω) ^ 2) μ from
          (((ha i).comp hx).pow_const 2).aemeasurable)).symm
    _ ≤ δ * 1 := mul_le_mul' le_rfl (by simpa using lintegral_mono_ae hsq)
    _ = δ := mul_one δ

theorem masked_product_integral_le {Ω : Type uΩ} {ι : Type uι} [MeasurableSpace Ω]
    [MeasurableSpace ι] [MeasurableSingletonClass ι] [Countable ι]
    (μ : Measure Ω) [SFinite μ]
    (a b : ι → Ω → ℝ≥0∞) (ha : ∀ i, Measurable (a i))
    (hb : ∀ i, Measurable (b i)) (H : ι → Set Ω)
    (hH : ∀ i, MeasurableSet (H i)) (δ : ℝ≥0∞)
    (hfirst : (∫⁻ ω, ∑' i, (H i).indicator (fun ω => a i ω ^ 2) ω ∂μ) ≤ δ)
    (hsecond : (∫⁻ ω, ∑' i, b i ω ^ 2 ∂μ) ≤ 1) :
    (∫⁻ ω, ∑' i, (H i).indicator (fun ω => a i ω * b i ω) ω ∂μ) ≤
      δ ^ (1 / 2 : ℝ) := by
  let A : ι × Ω → ℝ≥0∞ := fun z => (H z.1).indicator (a z.1) z.2
  let B : ι × Ω → ℝ≥0∞ := fun z => b z.1 z.2
  have hA : Measurable A := measurable_from_prod_countable_right
    (fun i => (ha i).indicator (hH i))
  have hB : Measurable B := measurable_from_prod_countable_right hb
  have hApow (z : ι × Ω) : A z ^ (2 : ℝ) =
      (H z.1).indicator (fun ω => a z.1 ω ^ 2) z.2 := by
    rw [ENNReal.rpow_two]
    by_cases hz : z.2 ∈ H z.1 <;> simp [A, hz]
  have hAB (z : ι × Ω) : (A * B) z =
      (H z.1).indicator (fun ω => a z.1 ω * b z.1 ω) z.2 := by
    by_cases hz : z.2 ∈ H z.1 <;> simp [A, B, hz]
  have hcs := ENNReal.lintegral_mul_le_Lp_mul_Lq (Measure.count.prod μ)
    (show Real.HolderConjugate 2 2 from by norm_num [Real.holderConjugate_iff])
    hA.aemeasurable hB.aemeasurable
  have hiA : (∫⁻ z, A z ^ (2 : ℝ) ∂Measure.count.prod μ) ≤ δ := by
    rw [lintegral_prod _ (hA.pow_const (2 : ℝ)).aemeasurable, lintegral_count]
    simp_rw [hApow]
    rwa [← lintegral_tsum (fun i => ((ha i).pow_const 2).indicator (hH i) |>.aemeasurable)]
  have hiB : (∫⁻ z, B z ^ (2 : ℝ) ∂Measure.count.prod μ) ≤ 1 := by
    rw [lintegral_prod _ (hB.pow_const (2 : ℝ)).aemeasurable, lintegral_count]
    simpa only [B, ENNReal.rpow_two,
      ← lintegral_tsum (fun i => ((hb i).pow_const 2).aemeasurable)] using hsecond
  have hiAB : (∫⁻ z, (A * B) z ∂Measure.count.prod μ) =
      (∫⁻ ω, ∑' i, (H i).indicator (fun ω => a i ω * b i ω) ω ∂μ) := by
    rw [lintegral_prod _ (hA.mul hB).aemeasurable, lintegral_count]
    simp_rw [hAB]
    exact (lintegral_tsum (fun i => show AEMeasurable
      (fun ω => (H i).indicator (fun ω => a i ω * b i ω) ω) μ from
        (((ha i).mul (hb i)).indicator (hH i)).aemeasurable)).symm
  rw [hiAB] at hcs
  exact hcs.trans (by
    calc
      _ ≤ δ ^ (1 / 2 : ℝ) * (1 : ℝ≥0∞) ^ (1 / 2 : ℝ) :=
        mul_le_mul' (ENNReal.rpow_le_rpow hiA (by norm_num))
          (ENNReal.rpow_le_rpow hiB (by norm_num))
      _ = _ := by simp)

theorem retained_sum_enorm_le {ι : Type uι} (z : ι → ℂ) (s : Finset ι)
    (hz : Summable z) (hzero : ∑' i, z i = 0) (a : ι → ℝ≥0∞)
    (ha : ∀ i ∉ s, ‖z i‖ₑ ≤ a i) :
    ‖∑ i ∈ s, z i‖ₑ ≤ ∑' i, a i := by
  classical
  have heq := hz.sum_add_tsum_compl (s := s)
  rw [hzero] at heq
  have hret : (∑ i ∈ s, z i) = -(∑' i : {i // i ∉ s}, z i) :=
    eq_neg_of_add_eq_zero_left heq
  rw [hret, enorm_neg]
  exact enorm_tsum_le_tsum_enorm.trans
    ((ENNReal.tsum_le_tsum (fun i : {i // i ∉ s} => ha i i.property)).trans
      (ENNReal.tsum_comp_le_tsum_of_injective Subtype.val_injective a))

theorem convolution_cut_bound {ι : Type uι} (z : ι → ℂ) (s : Finset ι)
    (hz : Summable z) (hzero : ∑' i, z i = 0)
    (a b h₁ h₂ : ι → ℝ≥0∞) (r : ℝ≥0∞)
    (hprod : ∑' i, a i * b i ≤ 1)
    (hbound : ∀ i ∉ s, ‖z i‖ₑ ≤ a i * b i * (r + h₁ i + h₂ i)) :
    ‖∑ i ∈ s, z i‖ₑ ≤ r + (∑' i, a i * b i * h₁ i) +
      (∑' i, a i * b i * h₂ i) := by
  apply (retained_sum_enorm_le z s hz hzero _ hbound).trans
  simp_rw [mul_add]
  rw [ENNReal.tsum_add, ENNReal.tsum_add, ENNReal.tsum_mul_right]
  exact add_le_add (add_le_add (by simpa only [one_mul] using
      (mul_le_mul' hprod (le_rfl : r ≤ r))) le_rfl) le_rfl

theorem two_endpoint_error_bound {Ω : Type uΩ} {X : Type uX} {Y : Type uY} {ι : Type uι} [MeasurableSpace Ω]
    [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace ι]
    [MeasurableSingletonClass ι] [Countable ι]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (x : Ω → X) (y : Ω → Y) (hx : Measurable x) (hy : Measurable y)
    (a : ι → X → ℝ≥0∞) (b : ι → Y → ℝ≥0∞)
    (ha : ∀ i, Measurable (a i)) (hb : ∀ i, Measurable (b i))
    (H₁ H₂ : ι → Set Ω) (hH₁ : ∀ i, MeasurableSet (H₁ i))
    (hH₂ : ∀ i, MeasurableSet (H₂ i)) (δ r : ℝ≥0∞)
    (hdom₁ : ∀ i, Measure.map x (μ.restrict (H₁ i)) ≤ δ • Measure.map x μ)
    (hdom₂ : ∀ i, Measure.map y (μ.restrict (H₂ i)) ≤ δ • Measure.map y μ)
    (hsq₁ : ∀ᵐ ω ∂μ, ∑' i, a i (x ω) ^ 2 ≤ 1)
    (hsq₂ : ∀ᵐ ω ∂μ, ∑' i, b i (y ω) ^ 2 ≤ 1)
    (c : Ω → ℝ≥0∞)
    (hc : ∀ᵐ ω ∂μ, c ω ≤ r +
      (∑' i, (H₁ i).indicator (fun ω => a i (x ω) * b i (y ω)) ω) +
      (∑' i, (H₂ i).indicator (fun ω => a i (x ω) * b i (y ω)) ω)) :
    (∫⁻ ω, c ω ∂μ) ≤ r + δ ^ (1 / 2 : ℝ) + δ ^ (1 / 2 : ℝ) := by
  have hi₁ := endpoint_masked_squares μ x hx H₁ hH₁ δ hdom₁ a ha hsq₁
  have hi₂ := endpoint_masked_squares μ y hy H₂ hH₂ δ hdom₂ b hb hsq₂
  have hbint : (∫⁻ ω, ∑' i, b i (y ω) ^ 2 ∂μ) ≤ 1 := by
    simpa using lintegral_mono_ae hsq₂
  have haint : (∫⁻ ω, ∑' i, a i (x ω) ^ 2 ∂μ) ≤ 1 := by
    simpa using lintegral_mono_ae hsq₁
  have hfirst := masked_product_integral_le μ (fun i ω => a i (x ω))
    (fun i ω => b i (y ω)) (fun i => (ha i).comp hx) (fun i => (hb i).comp hy)
    H₁ hH₁ δ hi₁ hbint
  have hsecond := masked_product_integral_le μ (fun i ω => b i (y ω))
    (fun i ω => a i (x ω)) (fun i => (hb i).comp hy) (fun i => (ha i).comp hx)
    H₂ hH₂ δ hi₂ haint
  simp_rw [mul_comm (b _ _) (a _ _)] at hsecond
  have hm₁ : Measurable (fun ω => ∑' i,
      (H₁ i).indicator (fun ω => a i (x ω) * b i (y ω)) ω) :=
    Measurable.tsum (fun i => (((ha i).comp hx).mul ((hb i).comp hy)).indicator (hH₁ i))
  apply (lintegral_mono_ae hc).trans
  have hm : Measurable (fun ω => r + ∑' i,
      (H₁ i).indicator (fun ω => a i (x ω) * b i (y ω)) ω) := measurable_const.add hm₁
  rw [lintegral_add_left hm, lintegral_add_left
    (measurable_const : Measurable (fun _ : Ω => r))]
  simpa using add_le_add (add_le_add le_rfl hfirst) hsecond



end ContinuousCircleWeight

end

end OAI
end

section
-- module Solutions.OAIQ2_Rot.RotationWeights_Convolution
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CircleSampling

open MeasureTheory
open scoped ENNReal NNReal ComplexInnerProductSpace BigOperators
open MeasureTheory Filter Set Submodule
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ComplexInnerProductSpace
open MeasureTheory Filter Set
open Set
open scoped ComplexInnerProductSpace
open Set
open scoped ComplexInnerProductSpace
open MeasureTheory Set Filter Topology
open scoped BigOperators ComplexConjugate
open MeasureTheory Set Filter
open scoped BigOperators ENNReal
open Filter Set
open scoped Topology
open Filter Set
open scoped Topology
open Set MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter Set
open scoped Topology
open Set MeasureTheory
open scoped ENNReal Classical
open Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Topology
open scoped BigOperators
open scoped BigOperators
open Set
open Set
open Set
open Set MeasureTheory Filter
open scoped BigOperators ENNReal Topology Classical
open MeasureTheory Set Filter
open scoped ENNReal Topology
open MeasureTheory Set
open MeasureTheory Filter Set
open scoped Topology BoundedContinuousFunction
open MeasureTheory Set Filter Topology TopologicalSpace
open MeasureTheory Set
open scoped ENNReal BigOperators Classical
open MeasureTheory Set
open scoped BigOperators ENNReal Classical
open MeasureTheory Set
open scoped ENNReal
open MeasureTheory Set
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped BigOperators ENNReal Topology
open Set MeasureTheory Topology
open scoped symmDiff
open MeasureTheory Set
open scoped ENNReal BigOperators
open MeasureTheory Set
open scoped ENNReal
open MeasureTheory Set
open scoped BigOperators ENNReal
open MeasureTheory Set
open scoped ENNReal NNReal BigOperators

section
open MeasureTheory Set Filter ContinuousCircleWeight
open scoped ENNReal BigOperators

lemma model_ratio_bounds {ω : ActualSamples} (hω : ω∈regularSamples) (j n : ℕ) (v : ℤ) :
    0 < modelF ((n:ℤ)+v) (lastEndpoint ω)/modelF v (firstEndpoint ω) ∧
    modelF ((n:ℤ)+v) (lastEndpoint ω)/modelF v (firstEndpoint ω) ≤ 1 ∧
    modelF ((n:ℤ)+v) (lastEndpoint ω)/modelF v (firstEndpoint ω) ≤
      modelF (longIndex j n v) (lastEndpoint ω)/modelF (longIndex j n v) (firstEndpoint ω) := by
  have hh := cocycle_two_ratio_bounds (fun k => modelF k (firstEndpoint ω)) (fun k => modelF k (lastEndpoint ω))
    (fun k => modelF_pos k _) (fun k => modelF_pos k _) (modelF_antitone _) (modelF_antitone _) (regular_model_order hω) n v
  refine ⟨hh.1,hh.2.1.trans hh.2.2.2.1,?_⟩
  unfold longIndex
  split_ifs
  · exact hh.2.1
  · exact hh.2.2.1

lemma model_ratio_masked {ω : ActualSamples} (hω : ω∈regularSamples) (j n : ℕ) (v : ℤ)
    (hv : v∉retainedIndices (polynomialWindow j) n) (ht : ω∈stageTagEvent j) :
    ENNReal.ofReal (modelF ((n:ℤ)+v) (lastEndpoint ω)/modelF v (firstEndpoint ω)) ≤
      ENNReal.ofReal (Real.exp (-crossingBudget j))+
        ((convolutionMasks j n).left v).indicator (fun _ => (1:ℝ≥0∞)) ω+
        ((convolutionMasks j n).right v).indicator (fun _ => (1:ℝ≥0∞)) ω := by
  classical
  have hh := model_ratio_bounds hω j n v
  have hone : ENNReal.ofReal (modelF ((n:ℤ)+v) (lastEndpoint ω)/modelF v (firstEndpoint ω)) ≤ 1 := by
    simpa using ENNReal.ofReal_le_ofReal hh.2.1
  by_cases hl : ω∈(convolutionMasks j n).left v
  · simp only [Set.indicator_of_mem hl]
    exact hone.trans ((le_add_self).trans le_self_add)
  · by_cases hr : ω∈(convolutionMasks j n).right v
    · simp only [Set.indicator_of_notMem hl,Set.indicator_of_mem hr,add_zero]
      exact hone.trans le_add_self
    · simp only [Set.indicator_of_notMem hl,Set.indicator_of_notMem hr,add_zero]
      exact ENNReal.ofReal_le_ofReal (hh.2.2.trans ((convolutionMasks j n).decay v hv ω hω ht hl hr))

lemma shifted_complement_squares (P : ModelProjectionField) (y : CircleX) (n : ℕ) :
    (∑' v : ℤ,‖modelComplement P y ((n:ℤ)+v)‖ₑ^2) ≤ 1 := by
  have hh := fiber_squares_le (modelComplement_norm P y)
  rwa [←(Equiv.addLeft (n:ℤ)).tsum_eq] at hh
lemma shifted_product_bound (P : ModelProjectionField) (x y : CircleX) (n : ℕ) :
    (∑' v : ℤ,‖modelColumn P x v‖ₑ*‖modelComplement P y ((n:ℤ)+v)‖ₑ) ≤ 1 := by
  have hh := fiber_product_le (modelColumn_norm P x) (show ‖fiberShift (-(n:ℤ)) (modelComplement P y)‖ ≤ 1 by simpa using modelComplement_norm P y)
  simpa only [fiberShift_apply,sub_neg_eq_add,add_comm] using hh

lemma modelTerm_enorm (P : ModelProjectionField) (n : ℕ) (v : ℤ) (ω : ActualSamples) :
    ‖modelTerm P n v ω‖ₑ=‖modelColumn P (firstEndpoint ω) v‖ₑ*‖modelComplement P (lastEndpoint ω) ((n:ℤ)+v)‖ₑ*
      ENNReal.ofReal (modelF ((n:ℤ)+v) (lastEndpoint ω)/modelF v (firstEndpoint ω)) := by
  rw [←ofReal_norm,modelTerm,norm_mul,norm_mul,Complex.norm_conj,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos (div_pos (modelF_pos _ _) (modelF_pos _ _)),
    ENNReal.ofReal_mul (mul_nonneg (div_pos (modelF_pos _ _) (modelF_pos _ _)).le (norm_nonneg _)),
    ENNReal.ofReal_mul (div_pos (modelF_pos _ _) (modelF_pos _ _)).le,ofReal_norm,ofReal_norm]
  ring

lemma modelRetained_cut (P : ModelProjectionField) (j n : ℕ) {ω : ActualSamples}
    (hω : ω∈regularSamples) (ht : ω∈stageTagEvent j)
    (hc : Summable (fun v => modelTerm P n v ω) ∧ (∑' v,modelTerm P n v ω)=0) :
    ‖modelRetained P j n ω‖ₑ ≤ ENNReal.ofReal (Real.exp (-crossingBudget j))+
      (∑' v, ((convolutionMasks j n).left v).indicator (fun ω => ‖modelColumn P (firstEndpoint ω) v‖ₑ*‖modelComplement P (lastEndpoint ω) ((n:ℤ)+v)‖ₑ) ω)+
      (∑' v, ((convolutionMasks j n).right v).indicator (fun ω => ‖modelColumn P (firstEndpoint ω) v‖ₑ*‖modelComplement P (lastEndpoint ω) ((n:ℤ)+v)‖ₑ) ω) := by
  classical
  have hh := convolution_cut_bound (fun v => modelTerm P n v ω) (retainedIndices (polynomialWindow j) n)
    hc.1 hc.2 (fun v => ‖modelColumn P (firstEndpoint ω) v‖ₑ) (fun v => ‖modelComplement P (lastEndpoint ω) ((n:ℤ)+v)‖ₑ)
    (fun v => ((convolutionMasks j n).left v).indicator (fun _ => (1:ℝ≥0∞)) ω)
    (fun v => ((convolutionMasks j n).right v).indicator (fun _ => (1:ℝ≥0∞)) ω)
    (ENNReal.ofReal (Real.exp (-crossingBudget j))) (shifted_product_bound P _ _ n) (fun v hv => by
      rw [modelTerm_enorm P n v ω]
      exact mul_le_mul' le_rfl (model_ratio_masked hω j n v hv ht))
  have hleft (v : ℤ) : ‖modelColumn P (firstEndpoint ω) v‖ₑ*‖modelComplement P (lastEndpoint ω) ((n:ℤ)+v)‖ₑ*
      ((convolutionMasks j n).left v).indicator (fun _ => (1:ℝ≥0∞)) ω =
      ((convolutionMasks j n).left v).indicator (fun ω => ‖modelColumn P (firstEndpoint ω) v‖ₑ*‖modelComplement P (lastEndpoint ω) ((n:ℤ)+v)‖ₑ) ω := by
    by_cases h : ω∈(convolutionMasks j n).left v <;> simp [h]
  have hright (v : ℤ) : ‖modelColumn P (firstEndpoint ω) v‖ₑ*‖modelComplement P (lastEndpoint ω) ((n:ℤ)+v)‖ₑ*
      ((convolutionMasks j n).right v).indicator (fun _ => (1:ℝ≥0∞)) ω =
      ((convolutionMasks j n).right v).indicator (fun ω => ‖modelColumn P (firstEndpoint ω) v‖ₑ*‖modelComplement P (lastEndpoint ω) ((n:ℤ)+v)‖ₑ) ω := by
    by_cases h : ω∈(convolutionMasks j n).right v <;> simp [h]
  simpa only [hleft,hright,modelRetained] using hh
end

open MeasureTheory Set Filter ContinuousCircleWeight
open scoped ENNReal BigOperators Topology

lemma convolutionError_eq (j : ℕ) :
    ENNReal.ofReal (Real.exp (-crossingBudget j))+
      ENNReal.ofReal (Real.exp (-crossingBudget j/400))^(1/2:ℝ)+
      ENNReal.ofReal (Real.exp (-crossingBudget j/400))^(1/2:ℝ)=ENNReal.ofReal (convolutionError j) := by
  rw [ENNReal.ofReal_rpow_of_pos (Real.exp_pos _),←Real.exp_mul]
  have he : -crossingBudget j/400*(1/2:ℝ)=-crossingBudget j/800 := by ring
  rw [he,←ENNReal.ofReal_add (Real.exp_pos _).le (Real.exp_pos _).le,←ENNReal.ofReal_add (by positivity) (Real.exp_pos _).le]
  congr 1
  unfold convolutionError
  ring

lemma integrated_retained_bound_oai (P : ModelProjectionField) (j n : ℕ) :
    (∫⁻ ω, (projectionEvent (modelDiagonal P) j).indicator (fun ω => ‖modelRetained P j n ω‖ₑ) ω ∂actualSystem.probability (stageTagged j)) ≤
      ENNReal.ofReal (convolutionError j) := by
  have hc : ∀ᵐ ω ∂actualSystem.probability (stageTagged j),
      (projectionEvent (modelDiagonal P) j).indicator (fun ω => ‖modelRetained P j n ω‖ₑ) ω ≤
      ENNReal.ofReal (Real.exp (-crossingBudget j))+
        (∑' v, ((convolutionMasks j n).left v).indicator (fun ω => ‖modelColumn P (firstEndpoint ω) v‖ₑ*‖modelComplement P (lastEndpoint ω) ((n:ℤ)+v)‖ₑ) ω)+
        (∑' v, ((convolutionMasks j n).right v).indicator (fun ω => ‖modelColumn P (firstEndpoint ω) v‖ₑ*‖modelComplement P (lastEndpoint ω) ((n:ℤ)+v)‖ₑ) ω) := by
    filter_upwards [model_convolution_ae P j] with ω hω
    by_cases he : ω∈projectionEvent (modelDiagonal P) j
    · rw [Set.indicator_of_mem he]
      exact modelRetained_cut P j n hω.1 he.1 (hω.2 n)
    · rw [Set.indicator_of_notMem he]
      exact zero_le
  have hh := two_endpoint_error_bound (actualSystem.probability (stageTagged j)) firstEndpoint lastEndpoint
    firstEndpoint_measurable lastEndpoint_measurable
    (fun v x => ‖modelColumn P x v‖ₑ) (fun v y => ‖modelComplement P y ((n:ℤ)+v)‖ₑ)
    (fun v => (modelColumn_coordinate P v).enorm) (fun v => (modelComplement_coordinate P _).enorm)
    (convolutionMasks j n).left (convolutionMasks j n).right
    (convolutionMasks j n).left_measurable (convolutionMasks j n).right_measurable
    (ENNReal.ofReal (Real.exp (-crossingBudget j/400))) (ENNReal.ofReal (Real.exp (-crossingBudget j)))
    (convolutionMasks j n).left_dom (convolutionMasks j n).right_dom
    (Eventually.of_forall (fun ω => fiber_squares_le (modelColumn_norm P (firstEndpoint ω))))
    (Eventually.of_forall (fun ω => shifted_complement_squares P (lastEndpoint ω) n)) _ hc
  rwa [convolutionError_eq] at hh


end CircleSampling

end

end OAI
end

theorem solution : type_of% @OAI.CircleSampling.integrated_retained_bound_oai := @OAI.CircleSampling.integrated_retained_bound_oai
