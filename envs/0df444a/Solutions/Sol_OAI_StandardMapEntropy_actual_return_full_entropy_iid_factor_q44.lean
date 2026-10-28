-- Prove2me | solution 1 for OAI.StandardMapEntropy.actual_return_full_entropy_iid_factor_q44
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T12:19:47.589883+00:00
-- url     : https://prove2.me/submissions/96ad74e7-2b10-4c16-8e42-f8ef3c203977

import Mathlib
import Definitions.Def_StandardMapComponents
import Definitions.Def_OAIQ44C002
import Theorems.Thm_OAI_HyperbolicCoding_goodIIDStage_initial_q44
import Theorems.Thm_OAI_HyperbolicCoding_goodIIDStage_next_q44

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
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_GridPartition
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace _root_.OAI.StandardMapEntropy.circleVolumeNullSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open Set Filter MeasureTheory
open scoped Topology ENNReal Classical BigOperators
namespace StandardMapEntropy
lemma measurable_circleRep : Measurable circleRep := by
  exact measurable_subtype_coe.comp (AddCircle.measurableEquivIco 1 0).measurable
lemma measurable_gridIndex (Q:ℕ) (hQ:0<Q) : Measurable (gridIndex Q hQ) := by
  apply measurable_to_countable
  intro y
  have h:Measurable (fun x:Circle=>⌊(Q:ℝ)*circleRep x⌋₊) :=
    Nat.measurable_floor.comp (measurable_const.mul measurable_circleRep)
  convert h (measurableSet_singleton (gridIndex Q hQ y).val) using 1
  all_goals try with_reducible_and_instances rfl
  ext x
  simp only [mem_preimage,mem_singleton_iff,Fin.ext_iff,gridIndex]
lemma measurable_gridLabel (Q:ℕ) (hQ:0<Q) : Measurable (gridLabel Q hQ) := by
  exact (measurable_of_finite (fun i:Fin Q×Fin Q=>(finProdFinEquiv i).castSucc)).comp
    (((measurable_gridIndex Q hQ).comp measurable_fst).prodMk ((measurable_gridIndex Q hQ).comp measurable_snd))
lemma gridLabel_eq_iff (Q:ℕ) (hQ:0<Q) (z w:Torus) :
    gridLabel Q hQ z=gridLabel Q hQ w ↔
      gridIndex Q hQ z.1=gridIndex Q hQ w.1 ∧ gridIndex Q hQ z.2=gridIndex Q hQ w.2 := by
  constructor
  · intro h
    have hv := congrArg (fun i:Fin (Q*Q+1)=>i.val) h
    have he:finProdFinEquiv (gridIndex Q hQ z.1,gridIndex Q hQ z.2)=
        finProdFinEquiv (gridIndex Q hQ w.1,gridIndex Q hQ w.2) := Fin.ext hv
    exact Prod.mk.inj (finProdFinEquiv.injective he)
  · rintro ⟨h1,h2⟩; simp only [gridLabel,h1,h2]
lemma gridIndex_bounds (Q:ℕ) (hQ:0<Q) (x:Circle) :
    (gridIndex Q hQ x:ℝ)/(Q:ℝ) ≤ circleRep x ∧ circleRep x<((gridIndex Q hQ x:ℝ)+1)/(Q:ℝ) := by
  have hq:(0:ℝ)<Q := Nat.cast_pos.mpr hQ
  constructor
  · apply (div_le_iff₀ hq).mpr
    simpa only [mul_comm,gridIndex] using Nat.floor_le (mul_nonneg hq.le (circleRep_mem x).1)
  · apply (lt_div_iff₀ hq).mpr
    simpa only [mul_comm,gridIndex] using Nat.lt_floor_add_one ((Q:ℝ)*circleRep x)
lemma gridIndex_close (Q:ℕ) (hQ:0<Q) {x y:Circle} (h:gridIndex Q hQ x=gridIndex Q hQ y) :
    |circleRep x-circleRep y|≤1/(Q:ℝ) := by
  have hx:=gridIndex_bounds Q hQ x
  have hy:=gridIndex_bounds Q hQ y
  rw [h] at hx
  rw [add_div] at hx hy
  exact abs_le.mpr ⟨by linarith,by linarith⟩
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

lemma continuous_standardDerivative (k : ℝ) : Continuous (standardDerivative k) :=
  continuous_const.clm_comp
    ((continuous_transferStep.comp ((continuous_torusPotential k).comp continuous_fst)).clm_comp
      continuous_const)

lemma conjugate_norm_le (A : ℂ →L[ℝ] ℂ) :
    ‖tangentCoordinates.comp (A.comp tangentCoordinates)‖ ≤ 9*‖A‖ := by
  calc
    _ ≤ ‖tangentCoordinates‖ * (‖A‖ * ‖tangentCoordinates‖) :=
      (ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))
    _ ≤ 3 * (‖A‖ * 3) := by gcongr <;> exact tangentCoordinates_norm_le
    _ = _ := by ring

end StandardMapEntropy

namespace StandardMapEntropy
open MeasureTheory Set Filter
open scoped Topology ENNReal ContDiff

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

lemma normalizedArea_absolutelyContinuous (E : Set Torus) : normalizedArea E ≪ area :=
  Measure.absolutelyContinuous_restrict.smul_left _

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

lemma continuous_standardDerivativeProduct (k : ℝ) (n : ℕ) :
    Continuous (fun z => standardDerivativeProduct k z n) := by
  induction n with
  | zero => exact continuous_const
  | succ n ih =>
    exact ((continuous_standardDerivative k).comp ((continuous_standardMap k).iterate n)).clm_comp ih

end StandardMapEntropy

end
end

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_Entropy_LiftGrid
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
open scoped BigOperators ENNReal Topology

lemma gridIndex_coe_int (Q : ℕ) (hQ : 0<Q) (y : ℝ) :
    gridIndex Q hQ (y : Circle)=gridIntIndex Q hQ ⌊(Q : ℝ)*y⌋ := by
  have hb : ((gridIndex Q hQ (y : Circle)).val : ℤ)=⌊(Q : ℝ)*y⌋-⌊y⌋*(Q : ℤ) := by
    change (⌊(Q : ℝ)*circleRep (y : Circle)⌋₊ : ℤ)=_
    rw [Int.natCast_floor_eq_floor (mul_nonneg (Nat.cast_nonneg Q) (circleRep_mem (y : Circle)).1),circleRep_coe]
    have he : (Q : ℝ)*Int.fract y=(Q : ℝ)*y-((⌊y⌋*(Q : ℤ) : ℤ) : ℝ) := by
      simp only [Int.fract,Int.cast_mul,Int.cast_natCast]
      ring
    rw [he,Int.floor_sub_intCast]
  have hm : ⌊(Q : ℝ)*y⌋%(Q : ℤ)=((gridIndex Q hQ (y : Circle)).val : ℤ) := by
    rw [←Int.sub_mul_emod_self_right ⌊(Q : ℝ)*y⌋ ⌊y⌋ (Q : ℤ),←hb]
    exact Int.emod_eq_of_lt (by omega) (by exact_mod_cast (gridIndex Q hQ (y : Circle)).isLt)
  apply Fin.ext
  simp only [gridIntIndex]
  rw [hm,Int.toNat_natCast]

lemma gridLabel_complex_lift (Q : ℕ) (hQ : 0<Q) (w : ℂ) :
    gridLabel Q hQ (complexProjection w)=gridIntLabel Q hQ (⌊(Q : ℝ)*w.re⌋,⌊(Q : ℝ)*w.im⌋) := by
  simp only [gridLabel,complexProjection,gridIndex_coe_int,gridIntLabel]
lemma floor_close_int {x y : ℝ} {M : ℕ} (h : |x-y|≤M) :
    ⌊x⌋∈Finset.Icc (⌊y⌋-(M : ℤ)-1) (⌊y⌋+(M : ℤ)+1) := by
  have hx0 := Int.floor_le x
  have hx1 := Int.lt_floor_add_one x
  have hy0 := Int.floor_le y
  have hy1 := Int.lt_floor_add_one y
  have hl := (abs_le.mp h).1
  have hu := (abs_le.mp h).2
  apply Finset.mem_Icc.mpr
  constructor
  · have hh : ((⌊y⌋-(M : ℤ)-1 : ℤ) : ℝ)≤(⌊x⌋ : ℝ) := by push_cast; linarith
    exact_mod_cast hh
  · have hh : (⌊x⌋ : ℝ)≤((⌊y⌋+(M : ℤ)+1 : ℤ) : ℝ) := by push_cast; linarith
    exact_mod_cast hh
lemma liftGridCover_card (Q : ℕ) (hQ : 0<Q) (c : ℂ) (M : ℕ) :
    (liftGridCover Q hQ c M).card≤(2*M+3)^2 := by
  apply (Finset.card_image_le).trans
  simp only [Finset.card,Finset.product,Multiset.card_product]
  change (Finset.Icc (⌊(Q : ℝ)*c.re⌋-(M : ℤ)-1) (⌊(Q : ℝ)*c.re⌋+(M : ℤ)+1)).card *
    (Finset.Icc (⌊(Q : ℝ)*c.im⌋-(M : ℤ)-1) (⌊(Q : ℝ)*c.im⌋+(M : ℤ)+1)).card ≤ _
  rw [Int.card_Icc,Int.card_Icc]
  have h1 : (⌊(Q : ℝ)*c.re⌋+(M : ℤ)+1+1-(⌊(Q : ℝ)*c.re⌋-(M : ℤ)-1)).toNat=2*M+3 := by omega
  have h2 : (⌊(Q : ℝ)*c.im⌋+(M : ℤ)+1+1-(⌊(Q : ℝ)*c.im⌋-(M : ℤ)-1)).toNat=2*M+3 := by omega
  rw [h1,h2,pow_two]
lemma liftGridCover_mem (Q : ℕ) (hQ : 0<Q) (c w : ℂ) (M : ℕ)
    (hw : ‖w-c‖≤(M : ℝ)/(Q : ℝ)) : gridLabel Q hQ (complexProjection w)∈liftGridCover Q hQ c M := by
  have hQpos : (0 : ℝ)<Q := Nat.cast_pos.mpr hQ
  have hr : |(Q : ℝ)*w.re-(Q : ℝ)*c.re|≤M := by
    rw [←mul_sub,abs_mul,abs_of_pos hQpos]
    have h := (Complex.abs_re_le_norm (w-c)).trans hw
    exact (mul_le_mul_of_nonneg_left h hQpos.le).trans_eq (mul_div_cancel₀ _ hQpos.ne')
  have hi : |(Q : ℝ)*w.im-(Q : ℝ)*c.im|≤M := by
    rw [←mul_sub,abs_mul,abs_of_pos hQpos]
    have h := (Complex.abs_im_le_norm (w-c)).trans hw
    exact (mul_le_mul_of_nonneg_left h hQpos.le).trans_eq (mul_div_cancel₀ _ hQpos.ne')
  rw [gridLabel_complex_lift]
  apply Finset.mem_image.mpr
  refine ⟨(⌊(Q : ℝ)*w.re⌋,⌊(Q : ℝ)*w.im⌋),?_,rfl⟩
  exact Finset.mem_product.mpr ⟨floor_close_int hr,floor_close_int hi⟩

end StandardMapEntropy

end
section
namespace StandardMapEntropy
open MeasureTheory Set Filter
open scoped BigOperators ENNReal Topology

lemma PlaneAreaPreserving.thin_cover {A : ℂ →L[ℝ] ℂ} (hA : PlaneAreaPreserving A) :
    ∃ (a : ℂ) (J : Finset ℤ),‖a‖=1 ∧ (J.card : ℝ)≤7*‖A‖ ∧
      ∀ v y : ℂ,‖v‖≤2 → ‖y-A v‖≤1 →
      ∃ j∈J,‖y-((j : ℝ)/‖A‖) • A a‖≤4 := by
  obtain ⟨a,ha,hAa,_,hAb,hL⟩ := hA.singular_pair
  have hLp : 0<‖A‖ := lt_of_lt_of_le zero_lt_one hL
  let N := ⌈2*‖A‖⌉₊
  have hN : 2*‖A‖≤(N : ℝ) := Nat.le_ceil _
  have hNb : (N : ℝ)<2*‖A‖+1 := Nat.ceil_lt_add_one (by positivity)
  let J := Finset.Icc (-(N : ℤ)) (N : ℤ)
  have hc : (J.card : ℝ)≤7*‖A‖ := by
    have hj : J.card=2*N+1 := by dsimp [J]; rw [Int.card_Icc]; omega
    rw [hj]
    push_cast
    nlinarith
  refine ⟨a,J,ha,hc,?_⟩
  intro v y hv hy
  have hd : |dot a v|≤2 := by simpa only [ha,one_mul] using (abs_dot_le_norm_mul a v).trans (by simpa [ha] using hv)
  have hw : |wedge a v|≤2 := by simpa only [ha,one_mul] using (abs_wedge_le_norm_mul a v).trans (by simpa [ha] using hv)
  let t := dot a v*‖A‖
  have ht : |t|≤(N : ℝ) := by
    dsimp [t]
    rw [abs_mul,abs_of_pos hLp]
    exact (mul_le_mul_of_nonneg_right hd hLp.le).trans hN
  have hj : ⌊t⌋∈J := by
    apply Finset.mem_Icc.mpr
    constructor
    · apply Int.le_floor.mpr
      simpa only [Int.cast_neg,Int.cast_natCast] using (abs_le.mp ht).1
    · apply Int.floor_le_iff.mpr
      simpa only [Int.cast_natCast] using lt_of_le_of_lt (abs_le.mp ht).2 (lt_add_one _)
  have hmajor : ‖(dot a v-(⌊t⌋ : ℝ)/‖A‖) • A a‖≤1 := by
    rw [norm_smul,Real.norm_eq_abs,hAa]
    have he : |dot a v-(⌊t⌋ : ℝ)/‖A‖| *‖A‖=|t-(⌊t⌋ : ℝ)| := by
      rw [←abs_of_pos hLp,←abs_mul]
      congr 1
      dsimp only [t]
      rw [abs_of_pos hLp]
      field_simp
    rw [he]
    exact abs_le.mpr ⟨by linarith [Int.floor_le t],by linarith [Int.lt_floor_add_one t]⟩
  have hminor : ‖(wedge a v) • A (quarterTurn a)‖≤2 := by
    rw [norm_smul,Real.norm_eq_abs,hAb]
    exact (mul_le_mul hw ((inv_le_one₀ hLp).mpr hL) (inv_nonneg.mpr hLp.le) (by norm_num)).trans_eq (mul_one _)
  have he : A v-((⌊t⌋ : ℝ)/‖A‖) • A a=
      (dot a v-(⌊t⌋ : ℝ)/‖A‖) • A a+(wedge a v) • A (quarterTurn a) := by
    conv_lhs => rw [unit_expansion a v ha]
    rw [map_add,map_smul,map_smul,sub_smul]
    abel
  refine ⟨⌊t⌋,hj,?_⟩
  have hn : ‖y-(((⌊t⌋ : ℝ)/‖A‖) • A a)‖≤‖y-A v‖+‖A v-(((⌊t⌋ : ℝ)/‖A‖) • A a)‖ := by
    simpa only [sub_add_sub_cancel] using norm_add_le (y-A v) (A v-(((⌊t⌋ : ℝ)/‖A‖) • A a))
  rw [he] at hn
  have hab := norm_add_le ((dot a v-(⌊t⌋ : ℝ)/‖A‖) • A a) ((wedge a v) • A (quarterTurn a))
  linarith

lemma PlaneAreaPreserving.grid_cover {A : ℂ →L[ℝ] ℂ} (hA : PlaneAreaPreserving A)
    (Q : ℕ) (hQ : 0<Q) (c : ℂ) :
    ∃ S : Finset (Fin (Q*Q+1)),(S.card : ℝ)≤1000*‖A‖ ∧
      ∀ v w : ℂ,‖v‖≤2/(Q : ℝ) → ‖w-c-A v‖≤1/(Q : ℝ) →
        gridLabel Q hQ (complexProjection w)∈S := by
  obtain ⟨a,J,ha,hJ,hcover⟩ := hA.thin_cover
  have hQp : (0 : ℝ)<Q := Nat.cast_pos.mpr hQ
  have hAp : 0<‖A‖ := lt_of_lt_of_le zero_lt_one hA.singular_pair.choose_spec.2.2.2.2
  let center : ℤ → ℂ := fun j => c+((j : ℝ)/((Q : ℝ)*‖A‖)) • A a
  let S : Finset (Fin (Q*Q+1)) := J.biUnion (fun j => liftGridCover Q hQ (center j) 4)
  have hcard : (S.card : ℝ)≤1000*‖A‖ := by
    have hn : S.card≤J.card*121 := calc
      _ ≤ ∑ j∈J,(liftGridCover Q hQ (center j) 4).card := Finset.card_biUnion_le
      _ ≤ ∑ _j∈J,121 := Finset.sum_le_sum (fun j _ => by simpa using liftGridCover_card Q hQ (center j) 4)
      _ = _ := by simp
    have hr : (S.card : ℝ)≤(J.card : ℝ)*121 := by exact_mod_cast hn
    nlinarith [norm_nonneg A]
  refine ⟨S,hcard,?_⟩
  intro v w hv hw
  have hv' : ‖(Q : ℝ) • v‖≤2 := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos hQp]
    exact (mul_le_mul_of_nonneg_left hv hQp.le).trans_eq (mul_div_cancel₀ _ hQp.ne')
  have hw' : ‖(Q : ℝ) • (w-c)-A ((Q : ℝ) • v)‖≤1 := by
    rw [map_smul,←smul_sub,norm_smul,Real.norm_eq_abs,abs_of_pos hQp]
    exact (mul_le_mul_of_nonneg_left hw hQp.le).trans_eq (mul_div_cancel₀ _ hQp.ne')
  obtain ⟨j,hj,hij⟩ := hcover ((Q : ℝ) • v) ((Q : ℝ) • (w-c)) hv' hw'
  have he : (Q : ℝ) • (w-center j)=(Q : ℝ) • (w-c)-((j : ℝ)/‖A‖) • A a := by
    simp only [center]
    rw [show w-(c+((j : ℝ)/((Q : ℝ)*‖A‖)) • A a)=
      (w-c)-((j : ℝ)/((Q : ℝ)*‖A‖)) • A a by abel,
      smul_sub,smul_smul]
    congr 2
    field_simp
  rw [←he,norm_smul,Real.norm_eq_abs,abs_of_pos hQp] at hij
  have hclose : ‖w-center j‖≤(4 : ℝ)/(Q : ℝ) := by
    apply (le_div_iff₀ hQp).mpr
    simpa only [mul_comm] using hij
  exact Finset.mem_biUnion.mpr ⟨j,hj,liftGridCover_mem Q hQ (center j) w 4 hclose⟩

end StandardMapEntropy

end
section
namespace StandardMapEntropy
open MeasureTheory Set Filter
open scoped Topology ENNReal

lemma norm_sub_le_of_derivative_bound {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E → F) (D : E → E →L[ℝ] F) (hD : ∀ x,HasFDerivAt f (D x) x)
    {B : ℝ} (hB : ∀ x,‖D x‖≤B) (x y : E) : ‖f x-f y‖≤B*‖x-y‖ := by
  exact (convex_univ : Convex ℝ (Set.univ : Set E)).norm_image_sub_le_of_norm_hasFDerivWithin_le
    (fun z _ => (hD z).hasFDerivWithinAt) (fun z _ => hB z) (Set.mem_univ y) (Set.mem_univ x)

lemma standardLift_iterate_control (k : ℝ) (hk : 0≤k) (n : ℕ) :
    ∃ B C : ℝ,0<B ∧ 0≤C ∧
      (∀ z : ℂ,‖standardDerivativeProduct k (complexProjection z) n‖≤B) ∧
      (∀ z w : ℂ,‖standardDerivativeProduct k (complexProjection z) n-
         standardDerivativeProduct k (complexProjection w) n‖≤C*‖z-w‖) := by
  induction n with
  | zero =>
    refine ⟨1,0,zero_lt_one,le_rfl,?_,?_⟩
    · intro z
      simp only [standardDerivativeProduct_zero,ContinuousLinearMap.norm_id,le_refl]
    · intro z w
      simp only [standardDerivativeProduct_zero,sub_self,norm_zero,zero_mul,le_refl]
  | succ n ih =>
    obtain ⟨B,C,hB,hC,hbound,hLip⟩ := ih
    let D := 9*growthBase k
    have hD : 0<D := by
      have hg := growthBase_ge_four k hk
      dsimp [D]
      linarith
    have hf : ∀ z w : ℂ,‖(standardLift k)^[n] z-(standardLift k)^[n] w‖≤B*‖z-w‖ :=
      norm_sub_le_of_derivative_bound _ _ (hasFDerivAt_standardLift_iterate k n) hbound
    refine ⟨D*B,derivativeVariationBound k*B^2+D*C,mul_pos hD hB,
      add_nonneg (mul_nonneg (derivativeVariationBound_nonneg k) (sq_nonneg B)) (mul_nonneg hD.le hC),?_,?_⟩
    · intro z
      exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul (standardDerivative_norm_bound k hk _) (hbound z) (norm_nonneg _) hD.le)
    · intro z w
      let Az := standardDerivative k ((standardMap k)^[n] (complexProjection z))
      let Aw := standardDerivative k ((standardMap k)^[n] (complexProjection w))
      let Pz := standardDerivativeProduct k (complexProjection z) n
      let Pw := standardDerivativeProduct k (complexProjection w) n
      have he : Az.comp Pz-Aw.comp Pw=(Az-Aw).comp Pz+Aw.comp (Pz-Pw) := by
        ext v
        simp only [sub_apply,add_apply,ContinuousLinearMap.comp_apply,map_sub]
        abel
      have hdiff : ‖Az-Aw‖≤derivativeVariationBound k*(B*‖z-w‖) := by
        have hh := standardDerivative_lift_sub_bound k ((standardLift k)^[n] z) ((standardLift k)^[n] w)
        rw [complexProjection_iterate,complexProjection_iterate] at hh
        exact hh.trans (mul_le_mul_of_nonneg_left (hf z w) (derivativeVariationBound_nonneg k))
      change ‖Az.comp Pz-Aw.comp Pw‖≤_
      rw [he]
      calc
        _ ≤ ‖(Az-Aw).comp Pz‖+‖Aw.comp (Pz-Pw)‖ := norm_add_le _ _
        _ ≤ ‖Az-Aw‖*‖Pz‖+‖Aw‖*‖Pz-Pw‖ :=
          add_le_add (ContinuousLinearMap.opNorm_comp_le _ _) (ContinuousLinearMap.opNorm_comp_le _ _)
        _ ≤ (derivativeVariationBound k*(B*‖z-w‖))*B+D*(C*‖z-w‖) := by
          apply add_le_add
          · exact mul_le_mul hdiff (hbound z) (norm_nonneg _) (mul_nonneg (derivativeVariationBound_nonneg k) (mul_nonneg hB.le (norm_nonneg _)))
          · exact mul_le_mul (standardDerivative_norm_bound k hk _) (hLip z w) (norm_nonneg _) hD.le
        _ = _ := by ring

lemma log_norm_sub_le_of_one_le {E : Type*} [SeminormedAddCommGroup E] {a b : E}
    (ha : 1≤‖a‖) (hb : 1≤‖b‖) : |Real.log ‖a‖-Real.log ‖b‖|≤‖a-b‖ := by
  have ha0 : 0<‖a‖ := lt_of_lt_of_le zero_lt_one ha
  have hb0 : 0<‖b‖ := lt_of_lt_of_le zero_lt_one hb
  have hab := Real.log_le_sub_one_of_pos (div_pos ha0 hb0)
  have hba := Real.log_le_sub_one_of_pos (div_pos hb0 ha0)
  rw [Real.log_div ha0.ne' hb0.ne'] at hab
  rw [Real.log_div hb0.ne' ha0.ne'] at hba
  have hd := norm_sub_norm_le a b
  have hd' := norm_sub_norm_le b a
  rw [norm_sub_rev b a] at hd'
  apply abs_le.mpr
  constructor
  · have hh : ‖b‖/‖a‖-1≤‖a-b‖ := by
      apply (sub_le_iff_le_add).mpr
      apply (div_le_iff₀ ha0).mpr
      nlinarith [norm_nonneg (a-b)]
    linarith
  · have hh : ‖a‖/‖b‖-1≤‖a-b‖ := by
      apply (sub_le_iff_le_add).mpr
      apply (div_le_iff₀ hb0).mpr
      nlinarith [norm_nonneg (a-b)]
    exact hab.trans hh

end StandardMapEntropy

end
section
namespace StandardMapEntropy.Entropy
open Set Finset
open scoped BigOperators

lemma shannon_nonneg {α : Type*} [Fintype α] (p : α → ℝ)
    (hp : ∀ a, 0≤p a) (hm : ∑ a,p a≤1) : 0 ≤ shannon p := by
  apply Finset.sum_nonneg
  intro a _
  exact Real.negMulLog_nonneg (hp a) ((Finset.single_le_sum (fun b _ => hp b) (Finset.mem_univ a)).trans hm)

lemma shannon_scale {α : Type*} [Fintype α] (p : α → ℝ) (c : ℝ) :
    shannon (fun a => c*p a)=c*shannon p+(∑ a,p a)*Real.negMulLog c := by
  simp only [shannon,Real.negMulLog_mul,Finset.sum_add_distrib,←Finset.mul_sum,←Finset.sum_mul]
  ring

lemma shannon_bound {α : Type*} [Fintype α] [Nonempty α] (p : α → ℝ)
    (hp : ∀ a, 0≤p a) (hm : ∑ a,p a=1) : shannon p≤Real.log (Fintype.card α) := by
  have hc : 0<(Fintype.card α : ℝ) := by exact_mod_cast Fintype.card_pos
  have hh := shannon_le_cross p (fun _ => (Fintype.card α : ℝ)⁻¹) hp
    (fun _ => (inv_pos.mpr hc).le) (fun _ _ => inv_ne_zero hc.ne') (by simp [hm,hc.ne'])
  rw [←Finset.sum_mul,hm,one_mul,Real.log_inv,neg_neg] at hh
  exact hh

lemma shannon_total_bound {α : Type*} [Fintype α] (p : α → ℝ)
    (hp : ∀ a, 0≤p a) : shannon p≤Real.negMulLog (∑ a,p a)+(∑ a,p a)*Real.log (Fintype.card α) := by
  let T : ℝ := ∑ a,p a
  have hT : 0≤T := Finset.sum_nonneg (fun a _ => hp a)
  by_cases he : T=0
  · have hz (a : α) : p a=0 := le_antisymm
      ((Finset.single_le_sum (fun b _ => hp b) (Finset.mem_univ a) : p a≤T).trans_eq he) (hp a)
    simp only [shannon,hz,Finset.sum_const_zero,Real.negMulLog_zero,zero_mul,add_zero,le_refl]
  have hT' : 0<T := lt_of_le_of_ne hT (Ne.symm he)
  have : Nonempty α := by
    by_contra h
    have : IsEmpty α := not_nonempty_iff.mp h
    exact he (by dsimp [T]; simp)
  let q : α → ℝ := fun a => p a/T
  have hq (a : α) : 0≤q a := div_nonneg (hp a) hT
  have hmass : ∑ a,q a=1 := by dsimp [q]; rw [←Finset.sum_div]; exact div_self he
  have hb := mul_le_mul_of_nonneg_left (shannon_bound q hq hmass) hT
  have hs := shannon_scale q T
  have heq : (fun a => T*q a)=p := by funext a; dsimp [q]; field_simp
  rw [heq,hmass,one_mul] at hs
  change shannon p≤Real.negMulLog T+T*Real.log (Fintype.card α)
  linarith

lemma matrix_super_row {α β : Type*} [Fintype α] [Fintype β]
    (p : α → β → ℝ) (hp : ∀ a b, 0≤p a b) :
    shannon (fun a => ∑ b,p a b)≤ shannon (fun ab : α×β => p ab.1 ab.2) := by
  have hh (a : α) (b : β) : -p a b*Real.log (∑ j,p a j)≤Real.negMulLog (p a b) := by
    by_cases he : p a b=0
    · simp [he]
    have hpos : 0<p a b := lt_of_le_of_ne (hp a b) (Ne.symm he)
    have hlog := Real.log_le_log hpos (matrix_le_row p hp a b)
    exact mul_le_mul_of_nonpos_left hlog (neg_nonpos.mpr (hp a b))
  have hs := Finset.sum_le_sum (s:=Finset.univ) (fun a _ => Finset.sum_le_sum (s:=Finset.univ) (fun b _ => hh a b))
  simp only [neg_mul,←Finset.sum_mul,Finset.sum_neg_distrib] at hs
  simpa only [shannon,Fintype.sum_prod_type,Real.negMulLog,neg_mul,Finset.sum_neg_distrib] using hs

end StandardMapEntropy.Entropy

end
end

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_Entropy_ObservableEntropy
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace StandardMapEntropy.Entropy
open MeasureTheory Set Filter
open scoped BigOperators ENNReal
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
variable [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
variable [MeasurableSingletonClass α] [MeasurableSingletonClass β] [MeasurableSingletonClass γ]

omit [IsFiniteMeasure μ] [MeasurableSpace α] [MeasurableSpace β]
  [MeasurableSingletonClass α] [MeasurableSingletonClass β] in
lemma obs_pair_swap (p : Ω → α) (q : Ω → β) :
    obs μ (fun x => (p x,q x))=obs μ (fun x => (q x,p x)) := by
  simp only [obs,shannon,Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun a _ => congrArg Real.negMulLog (mass_joint_swap μ p q a b)))

lemma obs_pair_ge_left (p : Ω → α) (q : Ω → β) (hp : Measurable p) (hq : Measurable q) :
    obs μ p ≤ obs μ (fun x => (p x,q x)) := by
  have h := matrix_super_row (fun a b => mass μ (fun x => (p x,q x)) (a,b))
    (fun a b => mass_nonneg μ _ _)
  simpa only [obs,Prod.mk.eta,←mass_joint_row μ p q hp hq] using h
lemma obs_pair_ge_right (p : Ω → α) (q : Ω → β) (hp : Measurable p) (hq : Measurable q) :
    obs μ q ≤ obs μ (fun x => (p x,q x)) := by
  rw [obs_pair_swap]
  exact obs_pair_ge_left μ q p hq hp

omit [IsFiniteMeasure μ] [Fintype α] [Fintype β] [MeasurableSpace α] [MeasurableSpace β]
  [MeasurableSingletonClass α] [MeasurableSingletonClass β] in
lemma mass_pair_function [DecidableEq β] (p : Ω → α) (g : α → β) (a : α) (b : β) :
    mass μ (fun x => (p x,g (p x))) (a,b)=if g a=b then mass μ p a else 0 := by
  classical
  by_cases h : g a=b
  · rw [ite_eq_left h]
    unfold mass
    congr 2
    ext x
    simp only [mem_preimage,mem_singleton_iff,Prod.mk.injEq]
    exact ⟨And.left,fun hp => ⟨hp,hp ▸ h⟩⟩
  · rw [ite_eq_right h]
    have he : ((fun x => (p x,g (p x))) ⁻¹' {(a,b)})=∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro x hx
      exact h ((congrArg g (Prod.mk.inj hx).1).symm.trans (Prod.mk.inj hx).2)
    simp only [mass,he,measure_empty,ENNReal.toReal_zero]
omit [IsFiniteMeasure μ] [MeasurableSpace α] [MeasurableSpace β]
  [MeasurableSingletonClass α] [MeasurableSingletonClass β] in
lemma obs_pair_function (p : Ω → α) (g : α → β) :
    obs μ (fun x => (p x,g (p x)))=obs μ p := by
  classical
  simp only [obs,shannon,Fintype.sum_prod_type,mass_pair_function]
  apply Finset.sum_congr rfl
  intro a _
  simp only [apply_ite Real.negMulLog,Real.negMulLog_zero,Finset.sum_ite_eq,Finset.mem_univ,ite_true]
lemma obs_factor (p : Ω → α) (g : α → β) (hp : Measurable p) (hg : Measurable (g ∘ p)) :
    obs μ (g ∘ p) ≤ obs μ p := by
  have h := obs_pair_ge_right μ p (g ∘ p) hp hg
  simpa only [Function.comp_def,obs_pair_function] using h

lemma sum_mass_mul_integral (p : Ω → α) (hp : Measurable p) (g : α → ℝ) :
    ∑ a,mass μ p a*g a=∫ x,g (p x) ∂μ := by
  classical
  have he (x : Ω) : (∑ a : α,(p ⁻¹' {a}).indicator (fun _ => g a) x)=g (p x) := by
    simp only [indicator_apply,mem_preimage,mem_singleton_iff,Finset.sum_ite_eq,Finset.mem_univ,ite_true]
  rw [←show (fun x => ∑ a : α,(p ⁻¹' {a}).indicator (fun _ => g a) x)=(fun x => g (p x)) from funext he]
  rw [integral_finsetSum _ (fun a _ => (integrable_const _).indicator (hp (measurableSet_singleton a)))]
  apply Finset.sum_congr rfl
  intro a _
  rw [integral_indicator (hp (measurableSet_singleton a)),integral_const,Measure.real,Measure.restrict_apply_univ]
  rfl

end StandardMapEntropy.Entropy

end
section
namespace StandardMapEntropy.Entropy
open MeasureTheory Set Filter
open scoped BigOperators ENNReal
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
variable {α β γ ζ : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype ζ]
variable [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ] [MeasurableSpace ζ]
variable [MeasurableSingletonClass α] [MeasurableSingletonClass β] [MeasurableSingletonClass γ] [MeasurableSingletonClass ζ]

omit [IsFiniteMeasure μ] [Fintype α] [Fintype β] [Fintype γ]
  [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
  [MeasurableSingletonClass α] [MeasurableSingletonClass β] [MeasurableSingletonClass γ] in
lemma mass_triple_assoc (p : Ω → α) (q : Ω → β) (r : Ω → γ) (a : α) (b : β) (c : γ) :
    mass μ (fun x => (p x,(q x,r x))) (a,(b,c))=
      mass μ (fun x => ((p x,q x),r x)) ((a,b),c) := by
  unfold mass
  congr 2
  ext x
  simp only [mem_preimage,mem_singleton_iff,Prod.mk.injEq,and_assoc]
omit [IsFiniteMeasure μ] [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
  [MeasurableSingletonClass α] [MeasurableSingletonClass β] [MeasurableSingletonClass γ] in
lemma obs_triple_assoc (p : Ω → α) (q : Ω → β) (r : Ω → γ) :
    obs μ (fun x => (p x,(q x,r x)))=obs μ (fun x => ((p x,q x),r x)) := by
  simpa only [Function.comp_def,Equiv.prodAssoc_apply] using obs_equiv μ (fun x => ((p x,q x),r x)) (Equiv.prodAssoc α β γ)

lemma obs_strong_subadd (p : Ω → α) (q : Ω → β) (r : Ω → γ)
    (hp : Measurable p) (hq : Measurable q) (hr : Measurable r) :
    obs μ (fun x => (p x,(q x,r x)))+obs μ q ≤
      obs μ (fun x => (p x,q x))+obs μ (fun x => (q x,r x)) := by
  let P : α → β → γ → ℝ := fun a b c => mass μ (fun x => (p x,(q x,r x))) (a,(b,c))
  have hrow (a : α) (b : β) : ∑ c,P a b c=mass μ (fun x => (p x,q x)) (a,b) := by
    simp only [P,mass_triple_assoc]
    exact (mass_joint_row μ _ r (hp.prodMk hq) hr (a,b)).symm
  have hcol (b : β) (c : γ) : ∑ a,P a b c=mass μ (fun x => (q x,r x)) (b,c) :=
    (mass_joint_col μ p _ hp (hq.prodMk hr) (b,c)).symm
  have htotal (b : β) : ∑ a,∑ c,P a b c=mass μ q b := by
    simp only [hrow]
    exact (mass_joint_col μ p q hp hq b).symm
  have hb (b : β) := matrix_subadd (fun a c => P a b c) (fun a c => mass_nonneg μ _ _)
  have hh := Finset.sum_le_sum (s:=Finset.univ) (fun b _ => hb b)
  simp only [shannon,Fintype.sum_prod_type,hrow,hcol,Finset.sum_sub_distrib,Finset.sum_add_distrib] at hh
  simp only [←mass_joint_col μ p q hp hq] at hh
  rw [Finset.sum_comm (f:=fun b a => ∑ c,Real.negMulLog (P a b c)),
    Finset.sum_comm (f:=fun b a => Real.negMulLog (mass μ (fun x => (p x,q x)) (a,b)))] at hh
  have h : obs μ (fun x => (p x,(q x,r x))) ≤
      obs μ (fun x => (p x,q x))+obs μ (fun x => (q x,r x))-obs μ q := by
    simpa only [obs,shannon,Fintype.sum_prod_type] using hh
  linarith

lemma cond_nonneg (p : Ω → α) (q : Ω → β) (hp : Measurable p) (hq : Measurable q) : 0 ≤ cond μ p q :=
  sub_nonneg.mpr (obs_pair_ge_right μ p q hp hq)
lemma cond_le_obs [IsProbabilityMeasure μ] (p : Ω → α) (q : Ω → β) (hp : Measurable p) (hq : Measurable q) :
    cond μ p q ≤ obs μ p := sub_le_iff_le_add.mpr (obs_pair_subadd_prob μ p q hp hq)
lemma cond_pair_right (p : Ω → α) (q : Ω → β) (r : Ω → γ)
    (hp : Measurable p) (hq : Measurable q) (hr : Measurable r) :
    cond μ p (fun x => (q x,r x)) ≤ cond μ p q := by
  have h := obs_strong_subadd μ p q r hp hq hr
  dsimp [cond]
  linarith
omit [IsFiniteMeasure μ] [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
  [MeasurableSingletonClass α] [MeasurableSingletonClass β] [MeasurableSingletonClass γ] in
lemma cond_pair_swap_right (p : Ω → α) (q : Ω → β) (r : Ω → γ) :
    cond μ p (fun x => (q x,r x))=cond μ p (fun x => (r x,q x)) := by
  have he : obs μ (fun x => (p x,(r x,q x)))=obs μ (fun x => (p x,(q x,r x))) := by
    simpa only [Function.comp_def,Equiv.prodCongr_apply,Prod.map_apply,Equiv.refl_apply,Equiv.prodComm_apply,Prod.swap_prod_mk] using
      obs_equiv μ (fun x => (p x,(q x,r x))) (Equiv.prodCongr (Equiv.refl α) (Equiv.prodComm β γ))
  unfold cond
  rw [he,obs_pair_swap μ q r]

omit [IsFiniteMeasure μ] [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
  [MeasurableSingletonClass α] [MeasurableSingletonClass β] [MeasurableSingletonClass γ] in
lemma cond_chain (p : Ω → α) (q : Ω → β) (r : Ω → γ) :
    cond μ (fun x => (p x,r x)) q=cond μ p q+cond μ r (fun x => (p x,q x)) := by
  have h1 := obs_pair_swap μ (fun x => (p x,r x)) q
  have h2 := obs_triple_assoc μ q p r
  have h3 := obs_pair_swap μ (fun x => (q x,p x)) r
  have h4 := cond_pair_swap_right μ r q p
  unfold cond at *
  have h5 := obs_pair_swap μ p q
  linarith
lemma cond_factor_right (p : Ω → α) (q : Ω → β) (g : β → γ)
    (hp : Measurable p) (hq : Measurable q) :
    cond μ p q ≤ cond μ p (g ∘ q) := by
  have hg : Measurable (g ∘ q) := (measurable_of_countable g).comp hq
  have h := cond_pair_right μ p (g ∘ q) q hp hg hq
  have he0 : cond μ p (fun x => (q x,g (q x)))=cond μ p q := by
    unfold cond
    dsimp only
    rw [obs_triple_assoc]
    rw [show obs μ (fun x => ((p x,q x),g (q x)))=obs μ (fun x => (p x,q x)) from
      obs_pair_function μ (fun x => (p x,q x)) (fun v : α×β => g v.2)]
    rw [obs_pair_function μ q g]
  have he : cond μ p (fun x => (g (q x),q x))=cond μ p q :=
    (cond_pair_swap_right μ p (g ∘ q) q).trans he0
  calc
    cond μ p q = cond μ p (fun x => (g (q x),q x)) := he.symm
    _ ≤ cond μ p (g ∘ q) := h

lemma cond_pair_subadd (p : Ω → α) (q : Ω → β) (r : Ω → γ) (s : Ω → ζ)
    (hp : Measurable p) (hq : Measurable q) (hr : Measurable r) (hs : Measurable s) :
    cond μ (fun x => (p x,r x)) (fun x => (q x,s x)) ≤ cond μ p q+cond μ r s := by
  rw [cond_chain]
  apply add_le_add (cond_pair_right μ p q s hp hq hs)
  exact cond_factor_right μ r (fun x => (p x,(q x,s x))) (fun v : α×(β×ζ) => v.2.2) hr (hp.prodMk (hq.prodMk hs))

end StandardMapEntropy.Entropy

end
section
namespace StandardMapEntropy.Entropy
open MeasureTheory Set Filter
open scoped BigOperators ENNReal Topology
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
variable {α β : Type*} [Fintype α] [Fintype β]
variable [MeasurableSpace α] [MeasurableSpace β]
variable [MeasurableSingletonClass α] [MeasurableSingletonClass β]

lemma obs_nonneg (p : Ω → α) (hp : Measurable p) : 0 ≤ obs μ p := by
  apply shannon_nonneg _ (mass_nonneg μ p)
  rw [mass_sum μ p hp,measure_univ,ENNReal.toReal_one]
omit [MeasurableSpace α] [MeasurableSingletonClass α] in
lemma obs_const [Nonempty α] (a : α) : obs μ (fun _ : Ω => a)=0 := by
  classical
  have he (b : α) : mass μ (fun _ : Ω => a) b=if a=b then 1 else 0 := by
    unfold mass
    by_cases h : a=b
    · subst b; simp
    · have hs : (fun _ : Ω => a) ⁻¹' {b}=∅ := by ext x; simp [h]
      simp [hs,h]
  simp only [obs,shannon,he,apply_ite Real.negMulLog,Real.negMulLog_one,Real.negMulLog_zero,ite_self,Finset.sum_const_zero]

omit [IsProbabilityMeasure μ] in
lemma cond_comp_preserving (f : Ω → Ω) (hf : MeasurePreserving f μ μ) (p : Ω → α) (q : Ω → β)
    (hp : Measurable p) (hq : Measurable q) : cond μ (p ∘ f) (q ∘ f)=cond μ p q := by
  unfold cond
  rw [show (fun x => ((p ∘ f) x,(q ∘ f) x))=(fun x => (p x,q x)) ∘ f from rfl,
    obs_comp_preserving μ f hf _ (hp.prodMk hq),obs_comp_preserving μ f hf q hq]

lemma obs_word_one (f : Ω → Ω) (p : Ω → α) (hp : Measurable p) : obs μ (word f p 1)=obs μ p := by
  have he (x : Ω) : word f p 1 x=(fun _ : Fin 1 => p x) := by
    funext i
    have hi : i.val=0 := by omega
    simp only [word,hi,Function.iterate_zero,Function.id_def]
  have hef : word f p 1=(fun x (_ : Fin 1) => p x) := funext he
  have h1 := obs_factor μ p (fun (a : α) (_ : Fin 1) => a) hp ((measurable_of_countable _).comp hp)
  have h2 := obs_factor μ (word f p 1) (fun v : Fin 1→α => v 0)
    (by simpa only [hef,Function.comp_def] using (measurable_of_countable (fun a (_ : Fin 1) => a)).comp hp)
    (by simpa only [Function.comp_def,word,Fin.val_zero,Function.iterate_zero,Function.id_def] using hp)
  apply le_antisymm
  · simpa only [Function.comp_def,hef] using h1
  · simpa only [Function.comp_def,word,Fin.val_zero,Function.iterate_zero,Function.id_def] using h2
omit [MeasurableSpace α] [MeasurableSingletonClass α] in
lemma obs_word_zero (f : Ω → Ω) (p : Ω → α) : obs μ (word f p 0)=0 := by
  have he : word f p 0=(fun _ : Ω => (fun i : Fin 0 => Fin.elim0 i)) := by funext x i; exact i.elim0
  rw [he,obs_const]

omit [IsProbabilityMeasure μ] [MeasurableSpace α] [MeasurableSpace β]
  [MeasurableSingletonClass α] [MeasurableSingletonClass β] in
lemma cond_equiv_left (p : Ω → α) (q : Ω → β)
    {γ : Type*} [Fintype γ] [MeasurableSpace γ] [MeasurableSingletonClass γ] (e : α ≃ γ) :
    cond μ (e ∘ p) q=cond μ p q := by
  have h := obs_equiv μ (fun x => (p x,q x)) (Equiv.prodCongr e (Equiv.refl β))
  unfold cond
  rw [show obs μ (fun x => ((e ∘ p) x,q x))=obs μ (fun x => (p x,q x)) from
    by simpa only [Function.comp_def,Equiv.prodCongr_apply,Prod.map_apply,Equiv.refl_apply] using h]
omit [IsProbabilityMeasure μ] [MeasurableSpace α] [MeasurableSpace β]
  [MeasurableSingletonClass α] [MeasurableSingletonClass β] in
lemma cond_equiv_right (p : Ω → α) (q : Ω → β)
    {γ : Type*} [Fintype γ] [MeasurableSpace γ] [MeasurableSingletonClass γ] (e : β ≃ γ) :
    cond μ p (e ∘ q)=cond μ p q := by
  have h := obs_equiv μ (fun x => (p x,q x)) (Equiv.prodCongr (Equiv.refl α) e)
  unfold cond
  rw [show obs μ (fun x => (p x,(e ∘ q) x))=obs μ (fun x => (p x,q x)) from
    by simpa only [Function.comp_def,Equiv.prodCongr_apply,Prod.map_apply,Equiv.refl_apply] using h,
    obs_equiv μ q e]
omit [IsProbabilityMeasure μ] in
lemma cond_word_split (f : Ω → Ω) (p : Ω → α) (q : Ω → β) (n m : ℕ) :
    cond μ (word f p (n+m)) (word f q (n+m))=
      cond μ (fun x => (word f p n x,word f p m (f^[n] x)))
        (fun x => (word f q n x,word f q m (f^[n] x))) := by
  rw [←cond_equiv_left μ (word f p (n+m)) (word f q (n+m)) (wordSplit n m),
    ←cond_equiv_right μ ((wordSplit n m) ∘ word f p (n+m)) (word f q (n+m)) (wordSplit n m)]
  simp only [Function.comp_def,word_split]
lemma cond_word_subadd (f : Ω → Ω) (hf : MeasurePreserving f μ μ) (p : Ω → α) (q : Ω → β)
    (hp : Measurable p) (hq : Measurable q) :
    Subadditive (fun n => cond μ (word f p n) (word f q n)) := by
  intro n m
  dsimp only
  rw [cond_word_split]
  have h := cond_pair_subadd μ (word f p n) (word f q n) ((word f p m) ∘ f^[n]) ((word f q m) ∘ f^[n])
    (word_measurable f hf.measurable p hp n) (word_measurable f hf.measurable q hq n)
    ((word_measurable f hf.measurable p hp m).comp (hf.measurable.iterate n))
    ((word_measurable f hf.measurable q hq m).comp (hf.measurable.iterate n))
  rw [cond_comp_preserving μ (f^[n]) (hf.iterate n) _ _
    (word_measurable f hf.measurable p hp m) (word_measurable f hf.measurable q hq m)] at h
  exact h
omit [IsProbabilityMeasure μ] in
lemma cond_word_one (f : Ω → Ω) (p : Ω → α) (q : Ω → β)
    (_hp : Measurable p) (_hq : Measurable q) :
    cond μ (word f p 1) (word f q 1)=cond μ p q := by
  have hp0 : (Equiv.funUnique (Fin 1) α) ∘ word f p 1=p := by
    funext x
    simp [word,Equiv.funUnique,Fin.default_eq_zero]
  have hq0 : (Equiv.funUnique (Fin 1) β) ∘ word f q 1=q := by
    funext x
    simp [word,Equiv.funUnique,Fin.default_eq_zero]
  rw [←cond_equiv_left μ (word f p 1) (word f q 1) (Equiv.funUnique (Fin 1) α),hp0,
    ←cond_equiv_right μ p (word f q 1) (Equiv.funUnique (Fin 1) β),hq0]
omit [MeasurableSpace α] [MeasurableSpace β]
  [MeasurableSingletonClass α] [MeasurableSingletonClass β] in
lemma cond_word_zero (f : Ω → Ω) (p : Ω → α) (q : Ω → β) :
    cond μ (word f p 0) (word f q 0)=0 := by
  have hp : word f p 0=(fun _ : Ω => (fun i : Fin 0 => Fin.elim0 i)) := by funext x i; exact i.elim0
  have hq : word f q 0=(fun _ : Ω => (fun i : Fin 0 => Fin.elim0 i)) := by funext x i; exact i.elim0
  simp only [cond,hp,hq,obs_const,sub_self]
lemma cond_word_bound (f : Ω → Ω) (hf : MeasurePreserving f μ μ) (p : Ω → α) (q : Ω → β)
    (hp : Measurable p) (hq : Measurable q) (n : ℕ) :
    cond μ (word f p n) (word f q n) ≤ n*cond μ p q := by
  induction n with
  | zero => simp only [cond_word_zero,Nat.cast_zero,zero_mul,le_refl]
  | succ n ih =>
    have h := cond_word_subadd μ f hf p q hp hq n 1
    change cond μ (word f p (n+1)) (word f q (n+1))≤
      cond μ (word f p n) (word f q n)+cond μ (word f p 1) (word f q 1) at h
    rw [cond_word_one μ f p q hp hq] at h
    calc
      _ ≤ cond μ (word f p n) (word f q n)+cond μ p q := h
      _ ≤ n*cond μ p q+cond μ p q := add_le_add ih le_rfl
      _ = _ := by push_cast; ring
lemma obs_word_comparison (f : Ω → Ω) (hf : MeasurePreserving f μ μ) (p : Ω → α) (q : Ω → β)
    (hp : Measurable p) (hq : Measurable q) (n : ℕ) :
    obs μ (word f p n) ≤ obs μ (word f q n)+n*cond μ p q := by
  have h := obs_pair_ge_left μ (word f p n) (word f q n)
    (word_measurable f hf.measurable p hp n) (word_measurable f hf.measurable q hq n)
  have hc := cond_word_bound μ f hf p q hp hq n
  unfold cond at hc ⊢
  linarith

lemma obs_word_bddBelow (f : Ω → Ω) (hf : Measurable f) (p : Ω → α) (hp : Measurable p) :
    BddBelow (Set.range (fun n : ℕ => obs μ (word f p n)/(n : ℝ))) := by
  refine ⟨0,?_⟩
  rintro _ ⟨n,rfl⟩
  exact div_nonneg (obs_nonneg μ _ (word_measurable f hf p hp n)) (Nat.cast_nonneg n)

end StandardMapEntropy.Entropy

end
section
namespace StandardMapEntropy.Entropy
open MeasureTheory Set Filter
open scoped BigOperators ENNReal Topology
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
variable {α β : Type*} [Fintype α] [Fintype β]
variable [MeasurableSpace α] [MeasurableSpace β]
variable [MeasurableSingletonClass α] [MeasurableSingletonClass β]

lemma rate_eq_lim (f : Ω → Ω) (hf : MeasurePreserving f μ μ) (p : Ω → α) (hp : Measurable p) :
    rate μ f p=(obs_word_subadd μ f hf p hp).lim := by
  rw [Subadditive.lim]; rfl
lemma rate_tendsto (f : Ω → Ω) (hf : MeasurePreserving f μ μ) (p : Ω → α) (hp : Measurable p) :
    Tendsto (fun n : ℕ => obs μ (word f p n)/(n : ℝ)) atTop (𝓝 (rate μ f p)) := by
  rw [rate_eq_lim μ f hf p hp]
  exact (obs_word_subadd μ f hf p hp).tendsto_lim (obs_word_bddBelow μ f hf.measurable p hp)
lemma rate_le_div (f : Ω → Ω) (hf : MeasurePreserving f μ μ) (p : Ω → α) (hp : Measurable p)
    {n : ℕ} (hn : n≠0) : rate μ f p≤obs μ (word f p n)/(n : ℝ) := by
  rw [rate_eq_lim μ f hf p hp]
  exact (obs_word_subadd μ f hf p hp).lim_le_div (obs_word_bddBelow μ f hf.measurable p hp) hn
lemma rate_nonneg (f : Ω → Ω) (hf : MeasurePreserving f μ μ) (p : Ω → α) (hp : Measurable p) :
    0 ≤ rate μ f p :=
  ge_of_tendsto' (rate_tendsto μ f hf p hp) (fun n => div_nonneg
    (obs_nonneg μ _ (word_measurable f hf.measurable p hp n)) (Nat.cast_nonneg n))
lemma rate_comparison (f : Ω → Ω) (hf : MeasurePreserving f μ μ) (p : Ω → α) (q : Ω → β)
    (hp : Measurable p) (hq : Measurable q) : rate μ f p ≤ rate μ f q+cond μ p q := by
  apply le_of_tendsto_of_tendsto (rate_tendsto μ f hf p hp) ((rate_tendsto μ f hf q hq).add_const _)
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn0 : (0 : ℝ)<n := by exact_mod_cast hn
  have h := div_le_div_of_nonneg_right (obs_word_comparison μ f hf p q hp hq n) hn0.le
  simpa only [add_div,mul_div_cancel_left₀ _ hn0.ne'] using h
lemma ofReal_rate_eq_iInf (f : Ω → Ω) (hf : MeasurePreserving f μ μ) (p : Ω → α) (hp : Measurable p) :
    ENNReal.ofReal (rate μ f p)=⨅ n : ℕ,ENNReal.ofReal (obs μ (word f p (n+1))/((n : ℝ)+1)) := by
  apply le_antisymm
  · apply le_iInf
    intro n
    apply ENNReal.ofReal_le_ofReal
    simpa only [Nat.cast_add,Nat.cast_one] using (rate_le_div μ f hf p hp (n:=n+1) (by omega))
  · have ht := (ENNReal.tendsto_ofReal (rate_tendsto μ f hf p hp)).comp (tendsto_add_atTop_nat 1)
    apply ge_of_tendsto' ht
    intro n
    simpa only [Function.comp_def,Nat.cast_add,Nat.cast_one] using
      (iInf_le (fun n : ℕ => ENNReal.ofReal (obs μ (word f p (n+1))/((n : ℝ)+1))) n)

end StandardMapEntropy.Entropy

end
section
namespace StandardMapEntropy
open MeasureTheory Set Filter
open scoped BigOperators ENNReal Topology
variable (μ : Measure Torus) [IsProbabilityMeasure μ]
lemma blockAtom_eq_fiber {r : ℕ} (f : Torus → Torus) (p : FinitePartition r)
    (n : ℕ) (w : Fin n → Fin (r+1)) : blockAtom f p n w=(Entropy.word f p.val n) ⁻¹' {w} := by
  ext x
  simp only [blockAtom,mem_ofPred_eq,mem_preimage,mem_singleton_iff,Entropy.word,funext_iff]
omit [IsProbabilityMeasure μ] in
lemma blockEntropy_eq_obs {r : ℕ} (f : Torus → Torus) (p : FinitePartition r) (n : ℕ) :
    blockEntropy μ f p n=Entropy.obs μ (Entropy.word f p.val n) := by
  simp only [blockEntropy,Entropy.obs,Entropy.shannon,Entropy.mass,Real.negMulLog,
    blockAtom_eq_fiber,Finset.sum_neg_distrib,neg_mul]
lemma partitionEntropy_eq_ofReal_rate {r : ℕ} (f : Torus → Torus)
    (hf : MeasurePreserving f μ μ) (p : FinitePartition r) :
    partitionEntropy μ f p=ENNReal.ofReal (Entropy.rate μ f p.val) := by
  rw [Entropy.ofReal_rate_eq_iInf μ f hf p.val p.property]
  simp only [partitionEntropy,blockEntropy_eq_obs]

end StandardMapEntropy

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

end StandardMapEntropy

end
end

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_Entropy_SupportEntropy
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace StandardMapEntropy.Entropy
open MeasureTheory Set Filter
open scoped BigOperators ENNReal
variable {α β : Type*} [Fintype α] [Fintype β]

lemma shannon_support_bound (p : α → ℝ) (hp : ∀ a,0≤p a) (s : Finset α)
    (hs : ∀ a,a∉s → p a=0) :
    shannon p≤Real.negMulLog (∑ a,p a)+(∑ a,p a)*Real.log (s.card : ℝ) := by
  classical
  have hsum : ∑ a : s,p a=∑ a,p a := by
    rw [Finset.sum_coe_sort]
    exact Finset.sum_subset (Finset.subset_univ s) (fun a _ ha => hs a ha)
  have hent : shannon (fun a : s => p a)=shannon p := by
    unfold shannon
    dsimp only
    rw [←Finset.sum_subtype s (fun a => Iff.rfl) (fun a => Real.negMulLog (p a))]
    exact Finset.sum_subset (Finset.subset_univ s) (fun a _ ha => by rw [hs a ha,Real.negMulLog_zero])
  have h := shannon_total_bound (fun a : s => p a) (fun a => hp a)
  simpa only [hent,hsum,Fintype.card_coe] using h

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
variable [MeasurableSpace α] [MeasurableSpace β]
variable [MeasurableSingletonClass α] [MeasurableSingletonClass β]
lemma cond_support_bound (p : Ω → α) (q : Ω → β) (hp : Measurable p) (hq : Measurable q)
    (S : β → Finset α) (hS : ∀ x,p x∈S (q x)) :
    cond μ p q≤∑ b,mass μ q b*Real.log ((S b).card : ℝ) := by
  classical
  have rz (b : β) (a : α) (ha : a∉S b) : mass μ (fun x => (p x,q x)) (a,b)=0 := by
    have he : (fun x => (p x,q x)) ⁻¹' {(a,b)}=∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro x hx
      obtain ⟨hx1,hx2⟩ := Prod.mk.inj hx
      exact ha (hx1 ▸ hx2 ▸ hS x)
    simp only [mass,he,measure_empty,ENNReal.toReal_zero]
  have hh := Finset.sum_le_sum (s:=Finset.univ) (fun b _ =>
    shannon_support_bound (fun a => mass μ (fun x => (p x,q x)) (a,b))
      (fun a => mass_nonneg μ _ _) (S b) (rz b))
  simp only [←mass_joint_col μ p q hp hq,shannon,Finset.sum_add_distrib] at hh
  unfold cond obs shannon
  rw [Fintype.sum_prod_type,Finset.sum_comm]
  linarith

end StandardMapEntropy.Entropy
end
section
namespace StandardMapEntropy.Entropy
open MeasureTheory Set Filter
open scoped BigOperators ENNReal Topology
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
variable {α : Type*} [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]

lemma errorObs_measurable (p q : Ω → α) (hp : Measurable p) (hq : Measurable q) :
    Measurable (errorObs p q) := by
  classical
  exact (measurable_of_countable (fun v : α×α => decide (v.1≠v.2))).comp (hp.prodMk hq)
omit [MeasurableSpace Ω] [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α] in
lemma errorObs_false (p q : Ω → α) (x : Ω) : errorObs p q x=false ↔ p x=q x := by
  classical
  simp [errorObs]
lemma obs_bool (e : Ω → Bool) (he : Measurable e) :
    obs μ e=Real.negMulLog (mass μ e true)+Real.negMulLog (1-mass μ e true) := by
  have hm := mass_sum μ e he
  simp only [Fintype.sum_bool,measure_univ,ENNReal.toReal_one] at hm
  have hf : mass μ e false=1-mass μ e true := by linarith
  simp only [obs,shannon,Fintype.sum_bool,hf]

lemma cond_fano (p q : Ω → α) (hp : Measurable p) (hq : Measurable q) :
    cond μ p q≤obs μ (errorObs p q)+mass μ (errorObs p q) true*Real.log (Fintype.card α) := by
  classical
  let e := errorObs p q
  have he := errorObs_measurable p q hp hq
  let S : Bool×α → Finset α := fun v => if v.1 then Finset.univ else {v.2}
  have hs (x : Ω) : p x∈S (e x,q x) := by
    by_cases h : p x=q x <;> simp [S,e,errorObs,h]
  have hb := cond_support_bound μ p (fun x => (e x,q x)) hp (he.prodMk hq) S hs
  have hv : (∑ v : Bool×α,mass μ (fun x => (e x,q x)) v*Real.log ((S v).card : ℝ))=
      mass μ e true*Real.log (Fintype.card α) := by
    simp only [Fintype.sum_prod_type,Fintype.sum_bool,S,Bool.false_eq_true,↓reduceIte,
      Finset.card_univ,Finset.card_singleton,Nat.cast_one,Real.log_one,mul_zero,Finset.sum_const_zero,add_zero]
    rw [←Finset.sum_mul,←mass_joint_row μ e q he hq true]
  rw [hv] at hb
  have hm := obs_pair_ge_right μ e (fun x => (p x,q x)) he (hp.prodMk hq)
  rw [obs_triple_assoc] at hm
  have hc := cond_chain μ e q p
  have ho := cond_le_obs μ e q he hq
  unfold cond at hb hc ho ⊢
  linarith
lemma cond_fano_bound (p q : Ω → α) (hp : Measurable p) (hq : Measurable q) :
    cond μ p q≤Real.negMulLog (mass μ (errorObs p q) true)+
      Real.negMulLog (1-mass μ (errorObs p q) true)+
      mass μ (errorObs p q) true*Real.log (Fintype.card α) := by
  rw [←obs_bool μ _ (errorObs_measurable p q hp hq)]
  exact cond_fano μ p q hp hq

lemma cond_small_of_error (ε : ℝ) (hε : 0<ε) :
    ∃ η : ℝ,0<η ∧ ∀ (p q : Ω → α), Measurable p → Measurable q →
      mass μ (errorObs p q) true<η → cond μ p q<ε := by
  let B : ℝ → ℝ := fun d => Real.negMulLog d+Real.negMulLog (1-d)+d*Real.log (Fintype.card α)
  have hB : Continuous B := Real.continuous_negMulLog.add
    (Real.continuous_negMulLog.comp (continuous_const.sub continuous_id)) |>.add
      (continuous_id.mul continuous_const)
  have hB0 : B 0=0 := by simp [B]
  have hev : ∀ᶠ d in 𝓝 (0 : ℝ),B d<ε :=
    (hB.continuousAt : ContinuousAt B 0).eventually (gt_mem_nhds (show B 0<ε by rw [hB0]; exact hε))
  obtain ⟨η,hη,hball⟩ := Metric.mem_nhds_iff.mp hev
  refine ⟨η,hη,?_⟩
  intro p q hp hq he
  have hm := mass_nonneg μ (errorObs p q) true
  have hb := hball (show mass μ (errorObs p q) true∈Metric.ball 0 η from by
    simpa only [Metric.mem_ball,Real.dist_eq,sub_zero,abs_of_nonneg hm] using he)
  exact lt_of_le_of_lt (cond_fano_bound μ p q hp hq) hb

end StandardMapEntropy.Entropy

end
section
namespace StandardMapEntropy.Entropy
open MeasureTheory Set Filter
open scoped BigOperators ENNReal Topology
variable {Ω : Type*} [MetricSpace Ω] [MeasurableSpace Ω] [BorelSpace Ω]
variable (μ : Measure Ω) [IsProbabilityMeasure μ] [μ.InnerRegularCompactLTTop]
variable {α : Type*} [Fintype α] [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α]

lemma compact_partition_core (p : Ω → α) (hp : Measurable p) (ε : ℝ) (hε : 0<ε) :
    ∃ K : Set Ω, IsCompact K ∧ μ Kᶜ≤ENNReal.ofReal ε ∧
      ∃ δ : ℝ,0<δ ∧ ∀ x∈K,∀ y∈K,dist x y<δ → p x=p y := by
  classical
  have hc : (0 : ℝ)<Fintype.card α := by exact_mod_cast Fintype.card_pos
  have hr : 0<ε/(Fintype.card α : ℝ) := div_pos hε hc
  have ha (a : α) := (hp (measurableSet_singleton a)).exists_isCompact_sdiff_lt
    (measure_ne_top μ _) (ENNReal.ofReal_pos.mpr hr).ne'
  choose K hKsub hKcompact hKerr using ha
  have herr : μ (⋃ a,K a)ᶜ≤ENNReal.ofReal ε := by
    have hs : (⋃ a,K a)ᶜ=⋃ a,(p ⁻¹' {a})\K a := by
      ext x
      simp only [mem_compl_iff,mem_iUnion,not_exists,Set.mem_sdiff,mem_preimage,mem_singleton_iff]
      constructor
      · intro h; exact ⟨p x,rfl,h (p x)⟩
      · rintro ⟨a,ha,haK⟩ b hb
        have hpb := hKsub b hb
        exact haK ((ha.symm.trans hpb) ▸ hb)
    rw [hs]
    calc
      _ ≤ ∑ a,μ ((p ⁻¹' {a})\K a) := by simpa only [tsum_fintype] using measure_iUnion_le (fun a => (p ⁻¹' {a})\K a)
      _ ≤ ∑ _a : α,ENNReal.ofReal (ε/(Fintype.card α : ℝ)) := Finset.sum_le_sum (fun a _ => (hKerr a).le)
      _ = (Fintype.card α : ℝ≥0∞)*ENNReal.ofReal (ε/(Fintype.card α : ℝ)) := by simp
      _ = ENNReal.ofReal ((Fintype.card α : ℝ)*(ε/(Fintype.card α : ℝ))) := by
        rw [ENNReal.ofReal_mul hc.le,ENNReal.ofReal_natCast]
      _ = ENNReal.ofReal ε := by congr 1; field_simp
  have hsep (ab : α×α) : ∃ δ : ℝ,0<δ ∧ ∀ x∈K ab.1,∀ y∈K ab.2,ab.1≠ab.2 → δ<dist x y := by
    by_cases he : ab.1=ab.2
    · exact ⟨1,by norm_num,fun _ _ _ _ h => False.elim (h he)⟩
    have hd : Disjoint (K ab.1) (K ab.2) := by
      apply disjoint_left.mpr
      intro x hx hy
      exact he ((hKsub ab.1 hx).symm.trans (hKsub ab.2 hy))
    obtain ⟨δ,hδ,hxy⟩ := Metric.exists_pos_forall_lt_edist (hKcompact ab.1) (hKcompact ab.2).isClosed hd
    refine ⟨δ,hδ,?_⟩
    intro x hx y hy _
    have h := (ENNReal.toReal_lt_toReal ENNReal.coe_ne_top (edist_ne_top x y)).mpr (hxy x hx y hy)
    simpa only [edist_dist,ENNReal.coe_toReal,ENNReal.toReal_ofReal dist_nonneg] using h
  choose d hd hdsep using hsep
  let δ := Finset.univ.inf' (Finset.univ_nonempty : (Finset.univ : Finset (α×α)).Nonempty) d
  have hδ : 0<δ := (Finset.lt_inf'_iff _).mpr (fun ab _ => hd ab)
  refine ⟨⋃ a,K a,isCompact_iUnion hKcompact,herr,δ,hδ,?_⟩
  intro x hx y hy hxy
  obtain ⟨a,ha⟩ := mem_iUnion.mp hx
  obtain ⟨b,hb⟩ := mem_iUnion.mp hy
  have he : a=b := by
    by_contra h
    have hs := hdsep (a,b) x ha y hb h
    exact (not_lt_of_ge ((Finset.inf'_le d (Finset.mem_univ (a,b))).trans hs.le)) hxy
  exact (hKsub a ha).trans (he.trans (hKsub b hb).symm)

lemma cond_small_of_diameter (p : Ω → α) (hp : Measurable p) (ε : ℝ) (hε : 0<ε) :
    ∃ δ : ℝ,0<δ ∧ ∀ {β : Type} [Fintype β] [MeasurableSpace β] [MeasurableSingletonClass β]
      (q : Ω → β),Measurable q →
      (∀ x y,q x=q y → dist x y<δ) → cond μ p q<ε := by
  classical
  obtain ⟨η,hη,hsmall⟩ := cond_small_of_error (α:=α) μ ε hε
  obtain ⟨K,hK,hKerr,δ,hδ,hsep⟩ := compact_partition_core μ p hp (η/2) (by positivity)
  refine ⟨δ,hδ,?_⟩
  intro β _ _ _ q hq hdiam
  let g : β → α := fun b => if h : ∃ x∈K,q x=b then p h.choose else Classical.choice inferInstance
  have he (x : Ω) (hx : x∈K) : g (q x)=p x := by
    have h : ∃ y∈K,q y=q x := ⟨x,hx,rfl⟩
    dsimp only [g]
    rw [dite_eq_left h]
    exact hsep h.choose h.choose_spec.1 x hx (hdiam _ _ h.choose_spec.2)
  have hm : mass μ (errorObs p (g ∘ q)) true<η := by
    have hs : (errorObs p (g ∘ q)) ⁻¹' {true}⊆Kᶜ := by
      intro x hx hxK
      have heq := (errorObs_false p (g ∘ q) x).mpr (he x hxK).symm
      have htrue : errorObs p (g ∘ q) x=true := hx
      rw [htrue] at heq
      cases heq
    have hu := ENNReal.toReal_mono ENNReal.ofReal_ne_top ((measure_mono hs).trans hKerr)
    rw [ENNReal.toReal_ofReal (by positivity)] at hu
    exact lt_of_le_of_lt hu (by linarith)
  have hh := hsmall p (g ∘ q) hp ((measurable_of_countable g).comp hq) hm
  exact lt_of_le_of_lt (cond_factor_right μ p q g hp hq) hh

end StandardMapEntropy.Entropy

end
section
namespace StandardMapEntropy
open MeasureTheory Set Filter
open scoped BigOperators ENNReal Topology

lemma circleRep_dist_le (x y : Circle) : dist x y≤|circleRep x-circleRep y| := by
  have h : ‖((circleRep x-circleRep y : ℝ) : Circle)‖≤‖circleRep x-circleRep y‖ :=
    QuotientAddGroup.norm_mk_le_norm
  simpa only [QuotientAddGroup.mk_sub,coe_circleRep,←dist_eq_norm,Real.dist_eq] using h
lemma gridLabel_dist_le (Q : ℕ) (hQ : 0<Q) {z w : Torus}
    (h : gridLabel Q hQ z=gridLabel Q hQ w) : dist z w≤1/(Q : ℝ) := by
  obtain ⟨h1,h2⟩ := (gridLabel_eq_iff Q hQ z w).mp h
  exact max_le ((circleRep_dist_le z.1 w.1).trans (gridIndex_close Q hQ h1))
    ((circleRep_dist_le z.2 w.2).trans (gridIndex_close Q hQ h2))

lemma metricEntropy_le_of_grid_rates (f : Torus → Torus) (hf : MeasurePreserving f area area) (b : ℝ)
    (hb : ∀ ε : ℝ,0<ε → ∃ Q₀ : ℕ,∀ Q : ℕ,Q₀≤Q → ∀ hQ : 0<Q,
      Entropy.rate area f (gridLabel Q hQ)≤b+ε) :
    metricEntropy area f≤ENNReal.ofReal b := by
  apply iSup_le
  intro r
  apply iSup_le
  intro p
  rw [partitionEntropy_eq_ofReal_rate area f hf p]
  apply ENNReal.ofReal_le_ofReal
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨δ,hδ,hsmall⟩ := Entropy.cond_small_of_diameter area p.val p.property (ε/2) (by positivity)
  obtain ⟨Q₀,hupper⟩ := hb (ε/2) (by positivity)
  obtain ⟨Q,hQbig⟩ := exists_nat_gt (max (Q₀ : ℝ) (max 1 δ⁻¹))
  have hQpos : (0 : ℝ)<Q := lt_trans zero_lt_one ((le_max_left _ _).trans_lt ((le_max_right _ _).trans_lt hQbig))
  have hQ : 0<Q := by exact_mod_cast hQpos
  have hQQ : Q₀≤Q := by exact_mod_cast ((le_max_left _ _).trans hQbig.le)
  have hm : 1/(Q : ℝ)<δ := (div_lt_iff₀ hQpos).mpr (by
    have hDQ : δ⁻¹<(Q : ℝ) := (le_max_right _ _).trans_lt ((le_max_right _ _).trans_lt hQbig)
    have hv := mul_lt_mul_of_pos_left hDQ hδ
    rw [mul_inv_cancel₀ hδ.ne'] at hv
    simpa only [mul_comm] using hv)
  have hs := hsmall (gridLabel Q hQ) (measurable_gridLabel Q hQ)
    (fun x y h => (gridLabel_dist_le Q hQ h).trans_lt hm)
  have hu := hupper Q hQQ hQ
  have hc := Entropy.rate_comparison area f hf p.val (gridLabel Q hQ) p.property (measurable_gridLabel Q hQ)
  linarith

end StandardMapEntropy

end
section
namespace StandardMapEntropy
open MeasureTheory Set Filter
open scoped Topology ENNReal BigOperators

lemma gridLabel_complexRep_close (Q : ℕ) (hQ : 0<Q) {z w : Torus}
    (h : gridLabel Q hQ z=gridLabel Q hQ w) : ‖complexRep z-complexRep w‖≤2/(Q : ℝ) := by
  obtain ⟨h1,h2⟩ := (gridLabel_eq_iff Q hQ z w).mp h
  have hh := add_le_add (gridIndex_close Q hQ h1) (gridIndex_close Q hQ h2)
  calc
    _ ≤ |circleRep z.1-circleRep w.1|+|circleRep z.2-circleRep w.2| := Complex.norm_le_abs_re_add_abs_im _
    _ ≤ 1/(Q : ℝ)+1/(Q : ℝ) := hh
    _ = _ := by ring

lemma integrable_log_standardDerivativeProduct (k : ℝ) (n : ℕ) :
    Integrable (fun z => Real.log ‖standardDerivativeProduct k z n‖) area :=
  ((continuous_standardDerivativeProduct k n).norm.log (fun z =>
    ne_of_gt (lt_of_lt_of_le zero_lt_one (standardDerivativeProduct_norm_ge_one k z n)))).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)

lemma standard_iterate_grid_cover (k : ℝ) (n : ℕ) {C : ℝ} (hC : 0≤C)
    (hLip : ∀ z w : ℂ,‖standardDerivativeProduct k (complexProjection z) n-
       standardDerivativeProduct k (complexProjection w) n‖≤C*‖z-w‖)
    (Q : ℕ) (hQ : 0<Q) (hQC : 4*C≤(Q : ℝ)) (z : Torus) :
    ∃ S : Finset (Fin (Q*Q+1)),(S.card : ℝ)≤1000*‖standardDerivativeProduct k z n‖ ∧
      ∀ w : Torus,gridLabel Q hQ w=gridLabel Q hQ z → gridLabel Q hQ ((standardMap k)^[n] w)∈S := by
  have hQp : (0 : ℝ)<Q := Nat.cast_pos.mpr hQ
  obtain ⟨S,hcard,hcover⟩ := (standardDerivativeProduct_area k z n).grid_cover Q hQ ((standardLift k)^[n] (complexRep z))
  refine ⟨S,hcard,?_⟩
  intro w hw
  have hdist := gridLabel_complexRep_close Q hQ hw
  have ht := quadratic_taylor_of_derivative_lipschitz ((standardLift k)^[n])
    (fun u => standardDerivativeProduct k (complexProjection u) n)
    (hasFDerivAt_standardLift_iterate k n) hC hLip (complexRep z) (complexRep w)
  rw [complexProjection_complexRep] at ht
  have herror : ‖(standardLift k)^[n] (complexRep w)-(standardLift k)^[n] (complexRep z)-
      standardDerivativeProduct k z n (complexRep w-complexRep z)‖≤1/(Q : ℝ) := by
    apply ht.trans
    calc
      _ ≤ C*(2/(Q : ℝ))^2 := mul_le_mul_of_nonneg_left (sq_le_sq₀ (norm_nonneg _) (by positivity) |>.mpr hdist) hC
      _ ≤ 1/(Q : ℝ) := by
        calc
          C*(2/(Q : ℝ))^2 = (4*C)/(Q : ℝ)^2 := by ring
          _ ≤ 1/(Q : ℝ) := by
            apply (div_le_div_iff₀ (sq_pos_of_pos hQp) hQp).mpr
            nlinarith
  have hh := hcover (complexRep w-complexRep z) ((standardLift k)^[n] (complexRep w)) hdist herror
  simpa only [complexProjection_iterate,complexProjection_complexRep] using hh

lemma standard_iterate_grid_log_variation (k : ℝ) (n : ℕ) {C : ℝ} (hC : 0≤C)
    (hLip : ∀ z w : ℂ,‖standardDerivativeProduct k (complexProjection z) n-
       standardDerivativeProduct k (complexProjection w) n‖≤C*‖z-w‖)
    (Q : ℕ) (hQ : 0<Q) {z w : Torus} (hw : gridLabel Q hQ w=gridLabel Q hQ z) :
    Real.log ‖standardDerivativeProduct k z n‖≤Real.log ‖standardDerivativeProduct k w n‖+2*C/(Q : ℝ) := by
  have hdist := gridLabel_complexRep_close Q hQ hw.symm
  have hd := hLip (complexRep z) (complexRep w)
  simp only [complexProjection_complexRep] at hd
  have hl := (le_abs_self (Real.log ‖standardDerivativeProduct k z n‖-Real.log ‖standardDerivativeProduct k w n‖)).trans
    (log_norm_sub_le_of_one_le (standardDerivativeProduct_norm_ge_one k z n) (standardDerivativeProduct_norm_ge_one k w n))
  have hh := hl.trans (hd.trans (mul_le_mul_of_nonneg_left hdist hC))
  rw [show C*(2/(Q : ℝ))=2*C/(Q : ℝ) by ring] at hh
  linarith

end StandardMapEntropy

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
-- module Solutions.OAIQ44_CM.StandardMap_Bernoulli_TailNameSaturation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace StandardMapEntropy.Entropy
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped BigOperators ENNReal symmDiff
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
variable {α β : Type*} [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]
    [Fintype β] [MeasurableSpace β] [MeasurableSingletonClass β] [Nonempty β]

omit [Fintype α] [MeasurableSingletonClass α] in
lemma exists_prefix_approx {Z : Ω → (ℕ → α)} (hZ : Measurable Z)
    {G : (ℕ → α) → β} (hG : Measurable G) (ε : ℝ) (hε : 0<ε) :
    ∃ (N : ℕ) (g : (Fin N → α) → β),
      μ {x | g (fun i => Z x i.val)≠G (Z x)}<ENNReal.ofReal ε := by
  classical
  let η := ε/((Fintype.card β : ℝ)+1)
  have hη : 0<η := div_pos hε (by positivity)
  let ν := μ.map Z
  have : IsProbabilityMeasure ν := by first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | (apply Measurable.aemeasurable; measurability) | measurability)
  have happ (b : β) : ∃ C ∈ measurableCylinders (fun _ : ℕ => α),
      ν (C ∆ (G ⁻¹' {b}))<ENNReal.ofReal η := by
    apply exists_measure_symmDiff_lt_of_generateFrom_isSetRing isSetRing_measurableCylinders
      (μ := ν) ?_ generateFrom_measurableCylinders.symm (hG (measurableSet_singleton b))
      (ENNReal.ofReal_pos.mpr hη)
    refine ⟨{univ},countable_singleton _,?_,by simp⟩
    simpa only [singleton_subset_iff] using (univ_mem_measurableCylinders (fun _ : ℕ => α))
  choose C hC hsmall using happ
  have hcyl (b : β) : ∃ (s : Finset ℕ) (S : Set (∀ i : s,α)),MeasurableSet S ∧ C b=cylinder s S := by
    simpa only [mem_measurableCylinders] using hC b
  choose s S hS hSC using hcyl
  let N : ℕ := 1+∑ b : β,(s b).sup id
  have hindex (b : β) (i : s b) : i.val<N := by
    have hl := Finset.le_sup (f := id) i.property
    have hs := Finset.single_le_sum (f := fun b : β => (s b).sup id)
      (fun b _ => Nat.zero_le _) (Finset.mem_univ b)
    dsimp only [id_eq] at hl
    dsimp [N]
    omega
  let P (b : β) (v : Fin N → α) : Prop := (fun i : s b => v ⟨i.val,hindex b i⟩)∈S b
  let g (v : Fin N → α) : β := if h : ∃ b,P b v then h.choose else Classical.choice inferInstance
  have hPred (b : β) (v : ℕ → α) : P b (fun i : Fin N => v i.val) ↔ v∈C b := by
    rw [hSC b]
    rfl
  have herr : {x | g (fun i => Z x i.val)≠G (Z x)}⊆
      Z ⁻¹' ⋃ b : β,C b ∆ (G ⁻¹' {b}) := by
    intro x hx
    by_contra hn
    have hall (b : β) : (Z x∈C b) ↔ G (Z x)=b := by
      have hb : Z x∉C b ∆ (G ⁻¹' {b}) := fun hb => hn (mem_iUnion_of_mem b hb)
      simp only [mem_symmDiff,mem_preimage,mem_singleton_iff] at hb
      tauto
    have hex : ∃ b,P b (fun i => Z x i.val) :=
      ⟨G (Z x),(hPred _ _).mpr ((hall _).mpr rfl)⟩
    have hg : g (fun i => Z x i.val)=hex.choose := dite_eq_left hex
    exact hx (hg.trans ((hall _).mp ((hPred _ _).mp hex.choose_spec)).symm)
  refine ⟨N,g,?_⟩
  have hCm (b : β) : MeasurableSet (C b) := by rw [hSC b]; exact (hS b).cylinder
  have hU : MeasurableSet (⋃ b : β,C b ∆ (G ⁻¹' {b})) :=
    MeasurableSet.iUnion (fun b => (hCm b).symmDiff (hG (measurableSet_singleton b)))
  calc
    μ {x | g (fun i => Z x i.val)≠G (Z x)}≤μ (Z ⁻¹' ⋃ b : β,C b ∆ (G ⁻¹' {b})) := measure_mono herr
    _=ν (⋃ b : β,C b ∆ (G ⁻¹' {b})) := (Measure.map_apply hZ hU).symm
    _≤∑ b : β,ν (C b ∆ (G ⁻¹' {b})) := measure_iUnion_fintype_le _ _
    _≤∑ _b : β,ENNReal.ofReal η := Finset.sum_le_sum (fun b _ => (hsmall b).le)
    _=ENNReal.ofReal ((Fintype.card β : ℝ)*η) := by
      simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
      rw [ENNReal.ofReal_mul (Nat.cast_nonneg _),ENNReal.ofReal_natCast]
    _<ENNReal.ofReal ε := ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by positivity) |>.mpr (by
      have hc : (0 : ℝ)≤Fintype.card β := Nat.cast_nonneg _
      dsimp [η]
      rw [←mul_div_assoc]
      apply (div_lt_iff₀ (by positivity)).mpr
      nlinarith)

lemma exists_cond_prefix_lt {Z : Ω → (ℕ → α)} (hZ : Measurable Z)
    {q : Ω → β} (hq : Measurable q)
    (hfactor : ∃ G : (ℕ → α) → β,Measurable G ∧ q=ᵐ[μ]G ∘ Z)
    (ε : ℝ) (hε : 0<ε) :
    ∃ N : ℕ,cond μ q (fun x => fun i : Fin N => Z x i.val)<ε := by
  classical
  obtain ⟨η,hη,hs⟩ := cond_small_of_error (α := β) μ ε hε
  obtain ⟨G,hG,hqG⟩ := hfactor
  obtain ⟨N,g,hg⟩ := exists_prefix_approx μ hZ hG η hη
  let p : Ω → (Fin N → α) := fun x i => Z x i.val
  have hp : Measurable p := Measurable.of_eval (fun i => (measurable_pi_apply i.val).comp hZ)
  have hm : mass μ (errorObs q (g ∘ p)) true<η := by
    have he : (errorObs q (g ∘ p)) ⁻¹' {true}=ᵐ[μ]{x | g (p x)≠G (Z x)} := by
      filter_upwards [hqG] with x hx
      change (errorObs q (g ∘ p) x=true)=(g (p x)≠G (Z x))
      apply propext
      simp only [errorObs,Function.comp_def,decide_eq_true_eq,hx,ne_comm]
    rw [mass,measure_congr he]
    exact (ENNReal.toReal_lt_of_lt_ofReal hg)
  exact ⟨N,lt_of_le_of_lt (cond_factor_right μ q p g hq hp)
    (hs q (g ∘ p) hq ((measurable_of_countable g).comp hp) hm)⟩

end StandardMapEntropy.Entropy

end
section
namespace HyperbolicCoding
open MeasureTheory Set Filter

lemma TailObservable.word {X A B : Type*} [MeasurableSpace X] [MeasurableSpace A] [MeasurableSpace B]
    {μ : Measure X} {T : X → X} (hT : MeasurePreserving T μ μ)
    {α : X → A} {q : X → B} (hq : TailObservable μ T α q) (n : ℕ) :
    TailObservable μ T α (StandardMapEntropy.Entropy.word T q n) := by
  intro m
  obtain ⟨G,hG,he⟩ := hq m
  let H (v : ℕ → A) (i : Fin n) := G (fun j => v (j+i.val))
  have hH : Measurable H := Measurable.of_eval (fun i => hG.comp
    (Measurable.of_eval (fun j => measurable_pi_apply (j+i.val))))
  refine ⟨H,hH,?_⟩
  have hall := ae_all_iff.mpr (fun i : Fin n => (hT.iterate i.val).quasiMeasurePreserving.ae he)
  filter_upwards [hall] with x hx
  funext i
  have hi := hx i
  change q (T^[i.val] x)=G (fun j => α (T^[j+i.val+m] x))
  rw [hi]
  change G (tailName T α m (T^[i.val] x))=G (fun j => α (T^[j+i.val+m] x))
  congr 1
  funext j
  simp only [tailName,←Function.iterate_add_apply]
  congr 2
  omega

end HyperbolicCoding
end
section
namespace StandardMapEntropy.Entropy
open MeasureTheory Set Filter
open scoped BigOperators ENNReal Topology
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
variable {α : Type*} [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]

omit [IsProbabilityMeasure μ] in
lemma cond_word_future_eq (f : Ω → Ω) (hf : MeasurePreserving f μ μ)
    (p : Ω → α) (hp : Measurable p) (n m : ℕ) :
    cond μ (word f p n) (fun x => word f p m (f^[n] x))=
      obs μ (word f p (n+m))-obs μ (word f p m) := by
  unfold cond
  rw [←obs_word_split μ f p n m]
  exact congrArg (fun t => obs μ (word f p (n+m))-t)
    (obs_comp_preserving μ (f^[n]) (hf.iterate n) (word f p m) (word_measurable f hf.measurable p hp m))

omit [IsProbabilityMeasure μ] in
lemma entropy_increment_eq (f : Ω → Ω) (hf : MeasurePreserving f μ μ)
    (p : Ω → α) (hp : Measurable p) (m : ℕ) :
    obs μ (word f p (m+1))-obs μ (word f p m)=
      cond μ p (fun x => word f p m (f x)) := by
  have h := cond_word_future_eq μ f hf p hp 1 m
  rw [Nat.add_comm 1 m] at h
  have he : (Equiv.funUnique (Fin 1) α) ∘ word f p 1=p := by
    funext x; rfl
  rw [←cond_equiv_left μ (word f p 1) (fun x => word f p m (f^[1] x))
    (Equiv.funUnique (Fin 1) α),he] at h
  simpa only [Function.iterate_one] using h.symm

lemma entropy_increment_antitone (f : Ω → Ω) (hf : MeasurePreserving f μ μ)
    (p : Ω → α) (hp : Measurable p) :
    Antitone (fun m : ℕ => obs μ (word f p (m+1))-obs μ (word f p m)) := by
  apply antitone_nat_of_succ_le
  intro m
  rw [entropy_increment_eq μ f hf p hp,entropy_increment_eq μ f hf p hp]
  exact cond_factor_right μ p (fun x => word f p (m+1) (f x))
    (fun v : Fin (m+1) → α => fun i : Fin m => v i.castSucc) hp
    ((word_measurable f hf.measurable p hp (m+1)).comp hf.measurable)

lemma entropy_increment_nonneg (f : Ω → Ω) (hf : MeasurePreserving f μ μ)
    (p : Ω → α) (hp : Measurable p) (m : ℕ) :
    0≤obs μ (word f p (m+1))-obs μ (word f p m) := by
  rw [entropy_increment_eq μ f hf p hp]
  exact cond_nonneg μ p _ hp ((word_measurable f hf.measurable p hp m).comp hf.measurable)

lemma entropy_increment_tendsto (f : Ω → Ω) (hf : MeasurePreserving f μ μ)
    (p : Ω → α) (hp : Measurable p) :
    Tendsto (fun m : ℕ => obs μ (word f p (m+1))-obs μ (word f p m)) atTop (𝓝 (rate μ f p)) := by
  let d := fun m : ℕ => obs μ (word f p (m+1))-obs μ (word f p m)
  have hbd : BddBelow (Set.range d) := ⟨0,by rintro _ ⟨m,rfl⟩; exact entropy_increment_nonneg μ f hf p hp m⟩
  have hd := tendsto_atTop_ciInf (entropy_increment_antitone μ f hf p hp) hbd
  have hs (n : ℕ) : ∑ j ∈ Finset.range n,d j=obs μ (word f p n) := by
    induction n with
    | zero => simp only [Finset.range_zero,Finset.sum_empty,obs_word_zero]
    | succ n ih => rw [Finset.sum_range_succ,ih]; dsimp [d]; ring
  change Tendsto d atTop (𝓝 (⨅ i,d i)) at hd
  have hh := hd.cesaro
  simp only [hs,←div_eq_inv_mul] at hh
  have he := tendsto_nhds_unique hh (rate_tendsto μ f hf p hp)
  rwa [he] at hd

lemma rate_le_entropy_increment (f : Ω → Ω) (hf : MeasurePreserving f μ μ)
    (p : Ω → α) (hp : Measurable p) (m : ℕ) :
    rate μ f p≤obs μ (word f p (m+1))-obs μ (word f p m) := by
  apply le_of_tendsto (entropy_increment_tendsto μ f hf p hp)
  filter_upwards [eventually_ge_atTop m] with n hn
  exact entropy_increment_antitone μ f hf p hp hn

lemma rate_mul_le_cond_future (f : Ω → Ω) (hf : MeasurePreserving f μ μ)
    (p : Ω → α) (hp : Measurable p) (n m : ℕ) :
    (n : ℝ)*rate μ f p ≤ cond μ (word f p n) (fun x => word f p m (f^[n] x)) := by
  rw [cond_word_future_eq μ f hf p hp]
  induction n with
  | zero =>
    simp only [Nat.cast_zero,zero_mul]
    have he (a b : ℕ) (h : a=b) : obs μ (word f p a)=obs μ (word f p b) := by subst b; rfl
    exact sub_nonneg.mpr (le_of_eq (he (0+m) m (Nat.zero_add m)).symm)
  | succ n ih =>
    have hh := rate_le_entropy_increment μ f hf p hp (n+m)
    rw [Nat.cast_add,Nat.cast_one]
    rw [show n+1+m=n+m+1 from by omega]
    nlinarith

end StandardMapEntropy.Entropy

end
section
namespace StandardMapEntropy.Entropy
open HyperbolicCoding MeasureTheory Set Filter
open scoped Topology
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
variable [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
variable [MeasurableSingletonClass α] [MeasurableSingletonClass β] [MeasurableSingletonClass γ]

lemma cond_triangle (p : Ω → α) (q : Ω → β) (r : Ω → γ)
    (hp : Measurable p) (hq : Measurable q) (hr : Measurable r) :
    cond μ p r ≤ cond μ p q+cond μ q r := by
  have h1 := cond_chain μ p r q
  have h2 := cond_chain μ q r p
  have hz := cond_nonneg μ q (fun x => (p x,r x)) hq (hp.prodMk hr)
  have hb := cond_pair_right μ p q r hp hq hr
  have he : cond μ (fun x => (p x,q x)) r=cond μ (fun x => (q x,p x)) r := by
    exact (cond_equiv_left μ (fun x => (p x,q x)) r (Equiv.prodComm α β)).symm
  linarith

lemma cond_word_window_bound (f : Ω → Ω) (hf : MeasurePreserving f μ μ)
    (p : Ω → α) (hp : Measurable p) (q : Ω → β) (hq : Measurable q) (n M : ℕ) :
    cond μ (word f q n) (word f p (n+M))≤(n : ℝ)*cond μ q (word f p M) := by
  let g (v : Fin (n+M) → α) (i : Fin n) (j : Fin M) := v ⟨j.val+i.val,by omega⟩
  have he : g ∘ word f p (n+M)=word f (word f p M) n := by
    funext x i j
    simp only [Function.comp_def,g,word,←Function.iterate_add_apply]
  have hb := cond_factor_right μ (word f q n) (word f p (n+M)) g
    (word_measurable f hf.measurable q hq n) (word_measurable f hf.measurable p hp _)
  rw [he] at hb
  exact hb.trans (cond_word_bound μ f hf q (word f p M) hq
    (word_measurable f hf.measurable p hp M) n)

lemma rate_mul_le_cond_tail [Nonempty β] (f : Ω → Ω) (hf : MeasurePreserving f μ μ)
    (p : Ω → α) (hp : Measurable p) (q : Ω → β) (hq : Measurable q)
    (ht : TailObservable μ f p q) (n : ℕ) :
    (n : ℝ)*rate μ f p ≤ cond μ (word f p n) q := by
  by_contra hn
  have hε : 0<(n : ℝ)*rate μ f p-cond μ (word f p n) q := sub_pos.mpr (lt_of_not_ge hn)
  obtain ⟨M,hM⟩ := exists_cond_prefix_lt μ (measurable_tailName hf.measurable hp n) hq
    (ht n) _ hε
  have he : (fun x => fun i : Fin M => tailName f p n x i.val)=
      (fun x => word f p M (f^[n] x)) := by
    funext x i
    simp only [tailName,word,←Function.iterate_add_apply]
  rw [he] at hM
  have hb := rate_mul_le_cond_future μ f hf p hp n M
  have hc := cond_triangle μ (word f p n) q (fun x => word f p M (f^[n] x))
    (word_measurable f hf.measurable p hp n) hq
    ((word_measurable f hf.measurable p hp M).comp (hf.measurable.iterate n))
  linarith

theorem tailObservable_rate_zero [Nonempty β] (f : Ω → Ω) (hf : MeasurePreserving f μ μ)
    (p : Ω → α) (hp : Measurable p) (q : Ω → β) (hq : Measurable q)
    (ht : TailObservable μ f p q) : rate μ f q=0 := by
  apply le_antisymm ?_ (rate_nonneg μ f hf q hq)
  by_contra hn
  have hε : 0 < rate μ f q/2 := half_pos (lt_of_not_ge hn)
  obtain ⟨M,hM⟩ := exists_cond_prefix_lt μ (measurable_tailName hf.measurable hp 0) hq
    (ht 0) _ hε
  change cond μ q (word f p M) < rate μ f q/2 at hM
  have hb (n : ℕ) : obs μ (word f q n)≤obs μ (word f p n)-(n : ℝ)*rate μ f p+
      obs μ (word f p M)+(n : ℝ)*(rate μ f q/2) := by
    have hl := rate_mul_le_cond_tail μ f hf p hp (word f q n)
      (word_measurable f hf.measurable q hq n) (ht.word hf n) (n+M)
    have hu := cond_word_window_bound μ f hf p hp q hq n M
    have hs := obs_word_subadd μ f hf p hp n M
    have he := obs_pair_swap μ (word f q n) (word f p (n+M))
    have hz := mul_nonneg (Nat.cast_nonneg M) (rate_nonneg μ f hf p hp)
    have hc := mul_le_mul_of_nonneg_left hM.le (Nat.cast_nonneg n)
    unfold cond at hl hu hc
    rw [Nat.cast_add] at hl
    nlinarith
  have hlim : Tendsto (fun n : ℕ => (obs μ (word f p n)/(n : ℝ)-rate μ f p)+
      obs μ (word f p M)/(n : ℝ)+rate μ f q/2) atTop (𝓝 (rate μ f q/2)) := by
    have hh := ((rate_tendsto μ f hf p hp).sub_const (rate μ f p)).add
      (tendsto_const_div_atTop_nhds_zero_nat (obs μ (word f p M)))
    simpa only [sub_self,zero_add] using hh.add_const (rate μ f q/2)
  have hh := le_of_tendsto_of_tendsto (rate_tendsto μ f hf q hq) hlim (show
      ∀ᶠ n : ℕ in atTop,obs μ (word f q n)/(n : ℝ)≤
        (obs μ (word f p n)/(n : ℝ)-rate μ f p)+
          obs μ (word f p M)/(n : ℝ)+rate μ f q/2 from by
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn0 : (0 : ℝ)<n := by exact_mod_cast hn
    apply (div_le_iff₀ hn0).mpr
    have h1 := div_mul_cancel₀ (obs μ (word f p n)) hn0.ne'
    have h2 := div_mul_cancel₀ (obs μ (word f p M)) hn0.ne'
    nlinarith [hb n])
  linarith

end StandardMapEntropy.Entropy

end
end

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_Bernoulli_ReverseFano
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace StandardMapEntropy.Entropy
open MeasureTheory Set Filter
open scoped BigOperators ENNReal
variable {α β : Type*} [Fintype α] [Fintype β]

lemma shannon_ge_one_sub_max (p : α → ℝ) (hp : ∀ a,0≤p a)
    (hs : ∑ a,p a=1) (m : ℝ) (hm : ∀ a,p a ≤ m) : 1-m≤ shannon p := by
  have hh (a : α) : p a*(1-m)≤Real.negMulLog (p a) := by
    by_cases hz : p a=0
    · simp only [hz,zero_mul,Real.negMulLog_zero,le_refl]
    have hpos : 0<p a := lt_of_le_of_ne (hp a) (Ne.symm hz)
    have hl := mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos hpos) (hp a)
    have hu := mul_le_mul_of_nonneg_left (sub_le_sub_left (hm a) 1) (hp a)
    unfold Real.negMulLog
    nlinarith
  have hh := Finset.sum_le_sum (s := Finset.univ) (fun a _ => hh a)
  simpa only [←Finset.sum_mul,hs,one_mul,shannon] using hh

lemma shannon_ge_total_sub_max (p : α → ℝ) (hp : ∀ a,0≤p a)
    (a₀ : α) (hm : ∀ a,p a≤p a₀) :
    (∑ a,p a)-p a₀≤ shannon p-Real.negMulLog (∑ a,p a) := by
  let S := ∑ a,p a
  have hS : 0≤S := Finset.sum_nonneg (fun a _ => hp a)
  by_cases hz : S=0
  · have he (a : α) : p a=0 := le_antisymm ((Finset.single_le_sum
        (fun b _ => hp b) (Finset.mem_univ a)).trans_eq hz) (hp a)
    simp only [he,Finset.sum_const_zero,sub_self,shannon,Real.negMulLog_zero,le_refl]
  have hS0 : 0<S := lt_of_le_of_ne hS (Ne.symm hz)
  have ht := shannon_ge_one_sub_max (fun a => p a/S)
    (fun a => div_nonneg (hp a) hS) (by rw [←Finset.sum_div]; exact div_self hz)
    (p a₀/S) (fun a => div_le_div_of_nonneg_right (hm a) hS)
  have hs := shannon_scale (fun a => p a/S) S
  have he : (fun a => S*(p a/S))=p := by funext a; exact mul_div_cancel₀ _ hz
  rw [he,←Finset.sum_div,div_self hz,one_mul] at hs
  have hh := mul_le_mul_of_nonneg_left ht hS
  have hc : S*(1-p a₀/S)=S-p a₀ := by field_simp
  rw [hc] at hh
  dsimp only [S] at hs hh
  linarith

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
variable [MeasurableSpace α] [MeasurableSpace β]
variable [MeasurableSingletonClass α] [MeasurableSingletonClass β]

theorem exists_decoder_error_le_cond [Nonempty α] (p : Ω → α) (q : Ω → β)
    (hp : Measurable p) (hq : Measurable q) :
    ∃ g : β → α,(μ {x | p x≠g (q x)}).toReal ≤ cond μ p q := by
  classical
  let J (a : α) (b : β) := mass μ (fun x => (p x,q x)) (a,b)
  have hm (b : β) : ∃ a₀ : α,∀ a,J a b≤J a₀ b := by
    obtain ⟨a,ha,hm⟩ := Finset.exists_max_image Finset.univ (fun a => J a b) Finset.univ_nonempty
    exact ⟨a,fun a' => hm a' (Finset.mem_univ a')⟩
  choose g hg using hm
  refine ⟨g,?_⟩
  have hcol (b : β) : ∑ a,J a b=mass μ q b := (mass_joint_col μ p q hp hq b).symm
  have hbound (b : β) : mass μ q b-J (g b) b≤
      shannon (fun a => J a b)-Real.negMulLog (mass μ q b) := by
    have hs := shannon_ge_total_sub_max (fun a => J a b) (fun a => mass_nonneg μ _ _)
      (g b) (hg b)
    rwa [hcol b] at hs
  have hall := Finset.sum_le_sum (s := Finset.univ) (fun b _ => hbound b)
  have herr : (μ {x | p x≠g (q x)}).toReal=∑ b,(mass μ q b-J (g b) b) := by
    let e : α×β → Bool := fun ab => decide (ab.1≠g ab.2)
    have he : (fun x => (e ((p x,q x)))) ⁻¹' {true}={x | p x≠g (q x)} := by
      ext x
      simp [e]
    have hh := mass_joint_col μ (fun x => (p x,q x)) (e ∘ (fun x => (p x,q x)))
      (hp.prodMk hq) ((measurable_of_countable e).comp (hp.prodMk hq)) true
    change mass μ (fun x => e (p x,q x)) true=_ at hh
    rw [mass,he] at hh
    simp only [Function.comp_def,mass_pair_function,Fintype.sum_prod_type] at hh
    rw [hh,Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro b _
    rw [←hcol b]
    have hsum : (∑ a : α,if a=g b then 0 else J a b)+J (g b) b=∑ a,J a b := by
      have hsingle : (∑ a : α,if a=g b then J a b else 0)=J (g b) b := by simp
      rw [←hsingle,←Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun a _ => by split_ifs <;> simp)
    have hid (a : α) : (if e (a,b)=true then J a b else 0)=if a=g b then 0 else J a b := by
      by_cases ha : a=g b <;> simp [e,ha]
    change (∑ a : α,if e (a,b)=true then J a b else 0)=(∑ a,J a b)-J (g b) b
    simp only [hid]
    exact (eq_sub_iff_add_eq.mpr hsum)
  rw [herr]
  unfold cond obs shannon
  simp only [Finset.sum_sub_distrib,shannon] at hall
  rw [Fintype.sum_prod_type,Finset.sum_comm]
  simpa only [Finset.sum_sub_distrib,J] using hall

end StandardMapEntropy.Entropy

end
section
open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace HyperbolicCoding

lemma exists_eventual_decoder {Y B : Type*} [MeasurableSpace Y] [MeasurableSpace B]
    [Fintype B] [MeasurableSingletonClass B] [Nonempty B]
    (G : ℕ → Y → B) (hG : ∀ n,Measurable (G n)) :
    ∃ H : Y → B,Measurable H ∧ ∀ v b,(∀ᶠ n : ℕ in atTop,G n v=b) → H v=b := by
  classical
  let b₀ : B := Classical.choice inferInstance
  let E (b : B) : Set Y := {v | ∀ᶠ n : ℕ in atTop,G n v=b}
  have hEm (b : B) : MeasurableSet (E b) := by
    have he : E b=⋃ N : ℕ,⋂ n : ℕ,⋂ (_h : N≤n),(G n) ⁻¹' {b} := by
      ext v
      simp only [E,mem_ofPred_eq,eventually_atTop,mem_iUnion,mem_iInter,mem_preimage,mem_singleton_iff]
    rw [he]
    exact MeasurableSet.iUnion (fun N => MeasurableSet.iInter (fun n =>
      MeasurableSet.iInter (fun _ : N≤n => hG n (measurableSet_singleton b))))
  have huniq (v : Y) (b c : B) (hb : v∈E b) (hc : v∈E c) : b=c := by
    obtain ⟨n,hn⟩ := (hb.and hc).exists
    exact hn.1.symm.trans hn.2
  let H (v : Y) : B := if h : ∃ b,v∈E b then h.choose else b₀
  have hHb (v : Y) (b : B) (hb : v∈E b) : H v=b := by
    have he : ∃ b,v∈E b := ⟨b,hb⟩
    dsimp only [H]
    rw [dite_eq_left he]
    exact huniq v _ b he.choose_spec hb
  refine ⟨H,?_,hHb⟩
  apply measurable_to_countable'
  intro b
  have he : H ⁻¹' {b}=E b ∪ (if b=b₀ then (⋃ c,E c)ᶜ else ∅) := by
    ext v
    simp only [mem_preimage,mem_singleton_iff,mem_union]
    by_cases hv : ∃ c,v∈E c
    · have hn : v∉(⋃ c,E c)ᶜ := by simpa using hv
      have hh : H v=b ↔ v∈E b :=
        ⟨fun h => h ▸ (show v∈E (H v) from by simpa only [H,dite_eq_left hv] using hv.choose_spec),hHb v b⟩
      by_cases hb : b=b₀
      · rw [ite_eq_left hb]
        simpa only [hn,or_false] using hh
      · rw [ite_eq_right hb]
        simpa only [mem_empty_iff_false,or_false] using hh
    · have hh : H v=b₀ := dite_eq_right hv
      have hn : v∈(⋃ c,E c)ᶜ := by simpa using hv
      have hb : v∉E b := fun hb => hv ⟨b,hb⟩
      by_cases he : b=b₀
      · rw [ite_eq_left he]
        simp only [hn,or_true,iff_true]
        exact hh.trans he.symm
      · rw [ite_eq_right he]
        simp only [hb,mem_empty_iff_false,or_self,iff_false]
        exact fun hc => he (hc.symm.trans hh)
  rw [he]
  apply (hEm b).union
  split_ifs
  · exact (MeasurableSet.iUnion hEm).compl
  · exact MeasurableSet.empty

theorem exists_factor_of_approx {X Y B : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSpace B] [Fintype B] [MeasurableSingletonClass B] [Nonempty B]
    (μ : Measure X) [IsFiniteMeasure μ] (Z : X → Y) (q : X → B)
    (happrox : ∀ ε : ℝ,0<ε → ∃ G : Y → B,Measurable G ∧
      μ {x | G (Z x)≠q x}<ENNReal.ofReal ε) :
    ∃ G : Y → B,Measurable G ∧ q=ᵐ[μ]G ∘ Z := by
  have happ (n : ℕ) := happrox ((1/2 : ℝ)^n) (pow_pos (by norm_num) n)
  choose G hG hsmall using happ
  obtain ⟨H,hH,hHb⟩ := exists_eventual_decoder G hG
  have hs : (∑' n : ℕ,μ {x | G n (Z x)≠q x})≠⊤ := by
    apply ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum (fun n => (hsmall n).le))
    simp only [ENNReal.ofReal_pow (by norm_num : (0 : ℝ)≤1/2),ENNReal.tsum_geometric]
    exact ENNReal.inv_ne_top.mpr (ne_of_gt (tsub_pos_iff_lt.mpr
      (ENNReal.ofReal_lt_one.mpr (by norm_num))))
  have ha := ae_eventually_notMem hs
  refine ⟨H,hH,?_⟩
  filter_upwards [ha] with x hx
  exact (hHb (Z x) (q x) (hx.mono (fun n hn => not_ne_iff.mp hn))).symm

end HyperbolicCoding

end
section
namespace StandardMapEntropy.Entropy
open HyperbolicCoding MeasureTheory Set Filter
open scoped Topology ENNReal
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
variable [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
variable [MeasurableSingletonClass α] [MeasurableSingletonClass β] [MeasurableSingletonClass γ]

lemma cond_factor_left (p : Ω → α) (q : Ω → β) (g : α → γ)
    (hp : Measurable p) (hq : Measurable q) : cond μ (g ∘ p) q ≤ cond μ p q := by
  unfold cond
  apply sub_le_sub_right
  exact obs_factor μ (fun x => (p x,q x)) (fun v : α×β => (g v.1,v.2))
    (hp.prodMk hq) (((measurable_of_countable g).comp hp).prodMk hq)

lemma cond_future_tendsto (f : Ω → Ω) (hf : MeasurePreserving f μ μ)
    (p : Ω → α) (hp : Measurable p) (n : ℕ) :
    Tendsto (fun m : ℕ => cond μ (word f p n) (fun x => word f p m (f^[n] x))) atTop
      (𝓝 ((n : ℝ)*rate μ f p)) := by
  simp_rw [cond_word_future_eq μ f hf p hp]
  induction n with
  | zero =>
    have he (m : ℕ) : obs μ (word f p (0+m))=obs μ (word f p m) := by
      have hi (a b : ℕ) (h : a=b) : obs μ (word f p a)=obs μ (word f p b) := by subst b; rfl
      exact hi _ _ (Nat.zero_add m)
    simpa only [he,sub_self,Nat.cast_zero,zero_mul] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
  | succ n ih =>
    have ht : Tendsto (fun m : ℕ => n+m) atTop atTop :=
      tendsto_atTop_mono (fun m => Nat.le_add_left m n) tendsto_id
    have hd := (entropy_increment_tendsto μ f hf p hp).comp ht
    have hh := hd.add ih
    have he (m : ℕ) :
        (obs μ (word f p ((n+m)+1))-obs μ (word f p (n+m)))+
          (obs μ (word f p (n+m))-obs μ (word f p m))=
            obs μ (word f p (n+1+m))-obs μ (word f p m) := by
      rw [show n+1+m=n+m+1 from by omega]
      ring
    simp only [Function.comp_def,he] at hh
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    simp only [Nat.cast_add,Nat.cast_one]
    ring_nf

theorem tailObservable_self_of_rate_zero [Nonempty α] (f : Ω → Ω)
    (hf : MeasurePreserving f μ μ) (p : Ω → α) (hp : Measurable p)
    (hz : rate μ f p=0) : TailObservable μ f p p := by
  intro n
  by_cases hn : n=0
  · subst n
    exact ⟨fun v => v 0,measurable_pi_apply 0,ae_of_all _ (fun x => rfl)⟩
  have hn0 : 0<n := Nat.pos_of_ne_zero hn
  apply exists_factor_of_approx μ (tailName f p n) p
  intro ε hε
  have ht := cond_future_tendsto μ f hf p hp n
  rw [hz,mul_zero] at ht
  have he := ht.eventually (gt_mem_nhds hε)
  obtain ⟨M,hM⟩ := he.exists
  let r : Ω → (Fin M → α) := fun x => word f p M (f^[n] x)
  have hr : Measurable r := (word_measurable f hf.measurable p hp M).comp (hf.measurable.iterate n)
  have hl : cond μ p r ≤ cond μ (word f p n) r :=
    cond_factor_left μ (word f p n) r (fun v => v ⟨0,hn0⟩)
      (word_measurable f hf.measurable p hp n) hr
  obtain ⟨g,hg⟩ := exists_decoder_error_le_cond μ p r hp hr
  let G (v : ℕ → α) := g (fun i : Fin M => v i.val)
  have hG : Measurable G := (measurable_of_countable g).comp
    (Measurable.of_eval (fun i : Fin M => measurable_pi_apply i.val))
  have hEq : {x | G (tailName f p n x)≠p x}={x | p x≠g (r x)} := by
    ext x
    change (g (fun i : Fin M => p (f^[i.val+n] x))≠p x) ↔
      p x≠g (fun i : Fin M => p (f^[i.val] (f^[n] x)))
    simp only [←Function.iterate_add_apply,ne_comm]
  refine ⟨G,hG,?_⟩
  rw [hEq,←ENNReal.toReal_lt_toReal (measure_ne_top _ _) ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal hε.le]
  exact hg.trans_lt (hl.trans_lt hM)

end StandardMapEntropy.Entropy

end
section
namespace StandardMapEntropy.Entropy
open MeasureTheory Set Filter
open scoped Topology
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
variable {α β : Type*} [Fintype α] [Fintype β]
variable [MeasurableSpace α] [MeasurableSpace β]
variable [MeasurableSingletonClass α] [MeasurableSingletonClass β]

omit [IsProbabilityMeasure μ] [MeasurableSpace α] [MeasurableSpace β]
  [MeasurableSingletonClass α] [MeasurableSingletonClass β] in
lemma obs_word_pair (f : Ω → Ω) (p : Ω → α) (q : Ω → β) (n : ℕ) :
    obs μ (word f (fun x => (p x,q x)) n)=obs μ (fun x => (word f p n x,word f q n x)) :=
  (obs_equiv μ (word f (fun x => (p x,q x)) n) (wordPairEquiv n)).symm

lemma rate_pair_ge_left (f : Ω → Ω) (hf : MeasurePreserving f μ μ)
    (p : Ω → α) (q : Ω → β) (hp : Measurable p) (hq : Measurable q) :
    rate μ f p ≤ rate μ f (fun x => (p x,q x)) := by
  apply le_of_tendsto_of_tendsto (rate_tendsto μ f hf p hp)
    (rate_tendsto μ f hf (fun x => (p x,q x)) (hp.prodMk hq))
  apply Eventually.of_forall
  intro n
  dsimp only
  rw [obs_word_pair]
  exact div_le_div_of_nonneg_right (obs_pair_ge_left μ (word f p n) (word f q n)
    (word_measurable f hf.measurable p hp n) (word_measurable f hf.measurable q hq n)) (Nat.cast_nonneg n)

lemma rate_pair_subadd (f : Ω → Ω) (hf : MeasurePreserving f μ μ)
    (p : Ω → α) (q : Ω → β) (hp : Measurable p) (hq : Measurable q) :
    rate μ f (fun x => (p x,q x)) ≤ rate μ f p+rate μ f q := by
  apply le_of_tendsto_of_tendsto (rate_tendsto μ f hf (fun x => (p x,q x)) (hp.prodMk hq))
    ((rate_tendsto μ f hf p hp).add (rate_tendsto μ f hf q hq))
  apply Eventually.of_forall
  intro n
  dsimp only
  rw [obs_word_pair,←add_div]
  exact div_le_div_of_nonneg_right (obs_pair_subadd_prob μ (word f p n) (word f q n)
    (word_measurable f hf.measurable p hp n) (word_measurable f hf.measurable q hq n)) (Nat.cast_nonneg n)

lemma rate_pair_eq_of_zero (f : Ω → Ω) (hf : MeasurePreserving f μ μ)
    (p : Ω → α) (q : Ω → β) (hp : Measurable p) (hq : Measurable q) (hz : rate μ f q=0) :
    rate μ f (fun x => (p x,q x))=rate μ f p := by
  have hl := rate_pair_ge_left μ f hf p q hp hq
  have hu := rate_pair_subadd μ f hf p q hp hq
  rw [hz,add_zero] at hu
  exact le_antisymm hu hl

omit [IsProbabilityMeasure μ] in
lemma rate_comp_iterate (f : Ω → Ω) (hf : MeasurePreserving f μ μ)
    (p : Ω → α) (hp : Measurable p) (s : ℕ) : rate μ f (p ∘ f^[s])=rate μ f p := by
  have he (n : ℕ) : word f (p ∘ f^[s]) n=(word f p n) ∘ f^[s] := by
    funext x i
    simp only [word,Function.comp_def,←Function.iterate_add_apply,Nat.add_comm]
  have hs (n : ℕ) : obs μ (word f (p ∘ f^[s]) n)=obs μ (word f p n) := by
    rw [he]
    exact obs_comp_preserving μ (f^[s]) (hf.iterate s) (word f p n) (word_measurable f hf.measurable p hp n)
  unfold rate
  simp only [hs]

end StandardMapEntropy.Entropy

end
section
namespace StandardMapEntropy.Entropy
open HyperbolicCoding MeasureTheory Set Filter
open scoped Topology
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
variable {α β : Type*} [Fintype α] [Fintype β]
variable [MeasurableSpace α] [MeasurableSpace β]
variable [MeasurableSingletonClass α] [MeasurableSingletonClass β]

lemma rate_mul_le_cond_future_zero (f : Ω → Ω) (hf : MeasurePreserving f μ μ)
    (p : Ω → α) (q : Ω → β) (hp : Measurable p) (hq : Measurable q)
    (hz : rate μ f q=0) (n M : ℕ) :
    (n : ℝ)*rate μ f p ≤ cond μ (word f p n) (fun x => (word f p M (f^[n] x),q x)) := by
  by_cases hn : n=0
  · subst n
    simp only [Nat.cast_zero,zero_mul]
    exact cond_nonneg μ (word f p 0) _ (word_measurable f hf.measurable p hp 0)
      (((word_measurable f hf.measurable p hp M).comp (hf.measurable.iterate 0)).prodMk hq)
  by_contra h
  have hε : 0<(n : ℝ)*rate μ f p-cond μ (word f p n) (fun x => (word f p M (f^[n] x),q x)) :=
    sub_pos.mpr (lt_of_not_ge h)
  have ht := cond_future_tendsto μ f hf q hq n
  rw [hz,mul_zero] at ht
  obtain ⟨L,hL,hLM⟩ := ((ht.eventually (gt_mem_nhds hε)).and (eventually_ge_atTop M)).exists
  let r : Ω → α×β := fun x => (p x,q x)
  let R : Ω → (Fin L → α×β) := fun x => word f r L (f^[n] x)
  have hR : Measurable R := (word_measurable f hf.measurable r (hp.prodMk hq) L).comp (hf.measurable.iterate n)
  have hpN := word_measurable f hf.measurable p hp n
  have hqN := word_measurable f hf.measurable q hq n
  have hlo := rate_mul_le_cond_future μ f hf r (hp.prodMk hq) n L
  rw [rate_pair_eq_of_zero μ f hf p q hp hq hz] at hlo
  have he : cond μ (word f r n) R=cond μ (word f q n) R+
      cond μ (word f p n) (fun x => (word f q n x,R x)) := by
    rw [←cond_equiv_left μ (word f r n) R
      ((wordPairEquiv n).trans (Equiv.prodComm (Fin n → α) (Fin n → β)))]
    exact cond_chain μ (word f q n) R (word f p n)
  change _ ≤ cond μ (word f r n) R at hlo
  rw [he] at hlo
  have hQ : cond μ (word f q n) R ≤ cond μ (word f q n) (fun x => word f q L (f^[n] x)) :=
    cond_factor_right μ (word f q n) R (fun v : Fin L → α×β => fun i => (v i).2) hqN hR
  let g (v : (Fin n → β)×(Fin L → α×β)) : (Fin M → α)×β :=
    (fun i => (v.2 ⟨i.val,lt_of_lt_of_le i.isLt hLM⟩).1,v.1 ⟨0,Nat.pos_of_ne_zero hn⟩)
  have hge : g ∘ (fun x => (word f q n x,R x))=
      (fun x => (word f p M (f^[n] x),q x)) := rfl
  have hP := cond_factor_right μ (word f p n) (fun x => (word f q n x,R x)) g hpN (hqN.prodMk hR)
  rw [hge] at hP
  linarith

lemma cond_future_zero_bound (f : Ω → Ω) (hf : MeasurePreserving f μ μ)
    (p : Ω → α) (q : Ω → β) (hp : Measurable p) (hq : Measurable q)
    (hz : rate μ f q=0) (n M : ℕ) :
    cond μ q (fun x => word f p M (f^[n] x)) ≤ cond μ q (word f p n)+
      cond μ (word f p n) (fun x => word f p M (f^[n] x))-(n : ℝ)*rate μ f p := by
  let P := word f p n
  let R : Ω → (Fin M → α) := fun x => word f p M (f^[n] x)
  have hPm : Measurable P := word_measurable f hf.measurable p hp n
  have hRm : Measurable R := (word_measurable f hf.measurable p hp M).comp (hf.measurable.iterate n)
  have hl := rate_mul_le_cond_future_zero μ f hf p q hp hq hz n M
  have hs := cond_pair_swap_right μ P q R
  have h1 := cond_chain μ P R q
  have h2 := cond_chain μ q R P
  have he : cond μ (fun x => (P x,q x)) R=cond μ (fun x => (q x,P x)) R :=
    (cond_equiv_left μ (fun x => (P x,q x)) R (Equiv.prodComm _ _)).symm
  have hu := cond_pair_right μ q P R hq hPm hRm
  change (n : ℝ)*rate μ f p ≤ cond μ P (fun x => (R x,q x)) at hl
  rw [←hs] at hl
  change cond μ q R ≤ cond μ q P+cond μ P R-(n : ℝ)*rate μ f p
  linarith

end StandardMapEntropy.Entropy

end
section
namespace StandardMapEntropy.Entropy
open MeasureTheory Set Filter
open scoped Topology
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
variable {α : Type*} [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]

lemma inverse_iterate_forward_sub (e : Ω ≃ᵐ Ω) {M i : ℕ} (hi : i≤M) (x : Ω) :
    e.symm^[i] (e^[M] x)=e^[M-i] x := by
  have hx : e^[M] x=e^[i] (e^[M-i] x) := by
    rw [←Function.iterate_add_apply,show i+(M-i)=M from by omega]
  rw [hx]
  exact (show Function.LeftInverse (e.symm : Ω → Ω) e from e.symm_apply_apply).iterate i _

lemma forward_iterate_inverse_sub (e : Ω ≃ᵐ Ω) {M i : ℕ} (hi : i≤M) (x : Ω) :
    e^[M] (e.symm^[i] x)=e^[M-i] x := by
  have hx : e^[M] (e.symm^[i] x)=e^[M-i] (e^[i] (e.symm^[i] x)) := by
    rw [←Function.iterate_add_apply,show M-i+i=M from by omega]
  rw [hx,(show Function.LeftInverse (e : Ω → Ω) e.symm from e.apply_symm_apply).iterate i x]

omit [IsProbabilityMeasure μ] in
lemma obs_word_inverse (e : Ω ≃ᵐ Ω) (he : MeasurePreserving e μ μ)
    (p : Ω → α) (hp : Measurable p) (n : ℕ) :
    obs μ (word e.symm p n)=obs μ (word e p n) := by
  have hw : (word e.symm p n) ∘ e^[n-1]=(wordReverseEquiv n) ∘ word e p n := by
    funext x i
    change p (e.symm^[i.val] (e^[n-1] x))=p (e^[i.rev.val] x)
    rw [inverse_iterate_forward_sub e (by omega)]
    congr 2
    have h := Fin.val_rev i
    omega
  have h := obs_comp_preserving μ (e^[n-1]) (he.iterate (n-1)) (word e.symm p n)
    (word_measurable e.symm e.symm.measurable p hp n)
  rw [hw,obs_equiv] at h
  exact h.symm

omit [IsProbabilityMeasure μ] in
lemma rate_inverse (e : Ω ≃ᵐ Ω) (he : MeasurePreserving e μ μ)
    (p : Ω → α) (hp : Measurable p) : rate μ e.symm p=rate μ e p := by
  unfold rate
  simp only [obs_word_inverse μ e he p hp]

end StandardMapEntropy.Entropy

end
end

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_Bernoulli_RohlinSinaiFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace HyperbolicCoding
open StandardMapEntropy.Entropy MeasureTheory Set Filter
open scoped Topology ENNReal
variable {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ]
variable {A B : Type*} [Fintype A] [Fintype B]
variable [MeasurableSpace A] [MeasurableSpace B]
variable [MeasurableSingletonClass A] [MeasurableSingletonClass B] [Nonempty B]

theorem zero_entropy_opposite_factor (e : X ≃ᵐ X) (he : MeasurePreserving e μ μ)
    (p : X → A) (q : X → B) (hp : Measurable p) (hq : Measurable q)
    (hz : rate μ e q=0)
    (hfactor : ∃ F : (ℕ → A) → B,Measurable F ∧ q=ᵐ[μ]F ∘ tailName e.symm p 0) :
    TailObservable μ e p q := by
  intro m
  apply exists_factor_of_approx μ (tailName e p m) q
  intro ε hε
  obtain ⟨M,hM⟩ := exists_cond_prefix_lt μ (measurable_tailName e.symm.measurable hp 0) hq
    hfactor (ε/2) (half_pos hε)
  change cond μ q (word e.symm p M)<ε/2 at hM
  let n := M+m+1
  let qS := q ∘ e^[M]
  have hqS : Measurable qS := hq.comp (e.measurable.iterate M)
  have hqz : rate μ e qS=0 := (rate_comp_iterate μ e he q hq M).trans hz
  let g₀ (v : Fin n → A) (i : Fin M) := v ⟨M-i.val,by dsimp [n]; omega⟩
  have hg₀ : g₀ ∘ word e p n=(word e.symm p M) ∘ e^[M] := by
    funext x i
    change p (e^[M-i.val] x)=p (e.symm^[i.val] (e^[M] x))
    rw [inverse_iterate_forward_sub e (by omega)]
  have hP : cond μ qS (word e p n) ≤ cond μ q (word e.symm p M) := by
    have hh := cond_factor_right μ qS (word e p n) g₀ hqS (word_measurable e e.measurable p hp n)
    rw [hg₀] at hh
    exact hh.trans_eq (cond_comp_preserving μ (e^[M]) (he.iterate M) q (word e.symm p M)
      hq (word_measurable e.symm e.symm.measurable p hp M))
  have hsmall : cond μ qS (word e p n)<ε := lt_trans (hP.trans_lt hM) (by linarith)
  have ht : Tendsto (fun L : ℕ => cond μ qS (word e p n)+
      cond μ (word e p n) (fun x => word e p L (e^[n] x))-(n : ℝ)*rate μ e p)
      atTop (𝓝 (cond μ qS (word e p n))) := by
    simpa only [add_sub_cancel_right] using
      ((cond_future_tendsto μ e he p hp n).const_add (cond μ qS (word e p n))).sub_const ((n : ℝ)*rate μ e p)
  obtain ⟨L,hL⟩ := (ht.eventually (gt_mem_nhds hsmall)).exists
  let r : X → (Fin L → A) := fun x => word e p L (e^[n] x)
  have hr : Measurable r := (word_measurable e e.measurable p hp L).comp (e.measurable.iterate n)
  have hc : cond μ qS r<ε := (cond_future_zero_bound μ e he p qS hp hqS hqz n L).trans_lt hL
  obtain ⟨g,hg⟩ := exists_decoder_error_le_cond μ qS r hqS hr
  let G (v : ℕ → A) := g (fun i : Fin L => v (i.val+1))
  have hG : Measurable G := (measurable_of_countable g).comp
    (Measurable.of_eval (fun i : Fin L => measurable_pi_apply (i.val+1)))
  have hcancel (x : X) : e^[M] (e.symm^[M] x)=x :=
    (show Function.LeftInverse (e : X → X) e.symm from e.apply_symm_apply).iterate M x
  have hnM : M≤n := by dsimp [n]; omega
  have hrx (x : X) : r (e.symm^[M] x)=(fun i : Fin L => tailName e p m x (i.val+1)) := by
    funext i
    change p (e^[i.val] (e^[n] (e.symm^[M] x)))=p (e^[i.val+1+m] x)
    rw [forward_iterate_inverse_sub e hnM,←Function.iterate_add_apply]
    congr 2
    dsimp [n]
    omega
  have hset : {x | G (tailName e p m x)≠q x}=
      (e.symm^[M]) ⁻¹' {x | qS x≠g (r x)} := by
    ext x
    change g (fun i : Fin L => tailName e p m x (i.val+1))≠q x ↔
      q (e^[M] (e.symm^[M] x))≠g (r (e.symm^[M] x))
    rw [hcancel,hrx]
    exact ne_comm
  have hEm : MeasurableSet {x | qS x≠g (r x)} :=
    (measurableSet_eq_fun hqS ((measurable_of_countable g).comp hr)).compl
  refine ⟨G,hG,?_⟩
  rw [hset,((he.symm e).iterate M).measure_preimage hEm.nullMeasurableSet,
    ←ENNReal.toReal_lt_toReal (measure_ne_top _ _) ENNReal.ofReal_ne_top,ENNReal.toReal_ofReal hε.le]
  exact hg.trans_lt hc

theorem TailObservable.reverse (e : X ≃ᵐ X) (he : MeasurePreserving e μ μ)
    (p : X → A) (q : X → B) (hp : Measurable p) (hq : Measurable q)
    (ht : TailObservable μ e p q) : TailObservable μ e.symm p q := by
  have hz := tailObservable_rate_zero μ e he p hp q hq ht
  apply zero_entropy_opposite_factor μ e.symm (he.symm e) p q hp hq
  · simpa only [rate_inverse μ e he q hq] using hz
  · simpa only [MeasurableEquiv.symm_symm] using ht 0

end HyperbolicCoding

end
section
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped Topology ENNReal symmDiff

namespace HyperbolicCoding

lemma law_distance_le_disagreement {Ω Y : Type*} [MeasurableSpace Ω] [MeasurableSpace Y]
    (κ : Measure Ω) [IsFiniteMeasure κ] {p q : Ω → Y}
    (hp : Measurable p) (hq : Measurable q) {D : Set Y} (hD : MeasurableSet D) :
    |(κ.map p).real D-(κ.map q).real D|≤κ.real {w | p w≠q w} := by
  simp only [Measure.real,Measure.map_apply hp hD,Measure.map_apply hq hD]
  apply (abs_measureReal_sub_le_measureReal_symmDiff
    (hD.preimage hp).nullMeasurableSet (hD.preimage hq).nullMeasurableSet).trans
  apply ENNReal.toReal_mono (measure_ne_top _ _)
  apply measure_mono
  intro w hw he
  have hh : (w∈p ⁻¹' D)=(w∈q ⁻¹' D) := by simp only [mem_preimage,he]
  simp only [Set.mem_symmDiff,hh,and_not_self,or_self] at hw

end HyperbolicCoding

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
variable {X : Type*} [MeasurableSpace X]

lemma integerIterate_add (e : X ≃ᵐ X) (m n : ℤ) (x : X) :
    integerIterate e (m+n) x=integerIterate e m (integerIterate e n x) := by
  simp only [integerIterate,zpow_add,Equiv.Perm.coe_mul,Function.comp_apply]
lemma integerIterate_nat (e : X ≃ᵐ X) (n : ℕ) (x : X) : integerIterate e n x=e^[n] x := by
  simp only [integerIterate,zpow_natCast,Equiv.Perm.coe_pow,MeasurableEquiv.coe_toEquiv]
lemma integerIterate_neg_nat (e : X ≃ᵐ X) (n : ℕ) (x : X) : integerIterate e (-(n : ℤ)) x=e.symm^[n] x := by
  simp only [integerIterate,zpow_neg,zpow_natCast,←inv_pow,Equiv.Perm.inv_def,Equiv.Perm.coe_pow]
  rfl
lemma integerIterate_nat_fun (e : X ≃ᵐ X) (n : ℕ) : integerIterate e (n : ℤ)=e^[n] :=
  funext (integerIterate_nat e n)
lemma integerIterate_neg_nat_fun (e : X ≃ᵐ X) (n : ℕ) : integerIterate e (-(n : ℤ))=e.symm^[n] :=
  funext (integerIterate_neg_nat e n)
lemma integerIterate_measurable (e : X ≃ᵐ X) (n : ℤ) : Measurable (integerIterate e n) := by
  cases n with
  | ofNat m => simpa only [Int.ofNat_eq_natCast,integerIterate_nat_fun] using e.measurable.iterate m
  | negSucc m =>
    have hn : Int.negSucc m= -((m+1 : ℕ) : ℤ) := by omega
    simpa only [hn,integerIterate_neg_nat_fun] using e.symm.measurable.iterate (m+1)
lemma integerIterate_measurePreserving (e : X ≃ᵐ X) {μ : Measure X}
    (he : MeasurePreserving e μ μ) (n : ℤ) : MeasurePreserving (integerIterate e n) μ μ := by
  cases n with
  | ofNat m => simpa only [Int.ofNat_eq_natCast,integerIterate_nat_fun] using he.iterate m
  | negSucc m =>
    have hn : Int.negSucc m= -((m+1 : ℕ) : ℤ) := by omega
    simpa only [hn,integerIterate_neg_nat_fun] using (he.symm e).iterate (m+1)

lemma measurable_orbitName {A : Type*} [MeasurableSpace A] (e : X ≃ᵐ X) {α : X → A}
    (hα : Measurable α) : Measurable (orbitName e α) :=
  Measurable.of_eval (fun n => hα.comp (integerIterate_measurable e n))
lemma orbitName_shift {A : Type*} (e : X ≃ᵐ X) (α : X → A) (x : X) :
    orbitName e α (e x)=fun i => orbitName e α x (i+1) := by
  funext i
  simp only [orbitName,integerIterate_add,integerIterate_one]

end HyperbolicCoding

end
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
open scoped ENNReal Topology
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

lemma LawClose.symm {μ ν : Measure X} {ε : ℝ} (h : LawClose μ ν ε) : LawClose ν μ ε := by
  intro D hD
  rw [abs_sub_comm]
  exact h D hD

lemma LawClose.triangle {μ ν κ : Measure X} {ε δ : ℝ}
    (h : LawClose μ ν ε) (h' : LawClose ν κ δ) : LawClose μ κ (ε+δ) := by
  intro D hD
  exact (abs_sub_le (μ.real D) (ν.real D) (κ.real D)).trans (add_le_add (h D hD) (h' D hD))

lemma LawClose.map {μ ν : Measure X} {ε : ℝ} (h : LawClose μ ν ε)
    {f : X → Y} (hf : Measurable f) : LawClose (μ.map f) (ν.map f) ε := by
  intro D hD
  simp only [Measure.real,Measure.map_apply hf hD]
  exact h _ (hD.preimage hf)

lemma real_prod_apply (μ : Measure X) (ν : Measure Y) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {D : Set (X×Y)} (hD : MeasurableSet D) :
    (μ.prod ν).real D=∫ x,ν.real ((Prod.mk x) ⁻¹' D) ∂μ := by
  rw [Measure.real,Measure.prod_apply hD]
  exact (integral_toReal (measurable_measure_prodMk_left hD).aemeasurable
    (Filter.Eventually.of_forall (fun _ => measure_lt_top ν _))).symm

lemma integrable_real_section (μ : Measure X) (ν : Measure Y) [IsFiniteMeasure μ] [IsProbabilityMeasure ν]
    {D : Set (X×Y)} (hD : MeasurableSet D) :
    Integrable (fun x => ν.real ((Prod.mk x) ⁻¹' D)) μ := by
  apply (integrable_const (1 : ℝ)).mono'
    (measurable_measure_prodMk_left hD).ennreal_toReal.aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun x => by
    rw [Real.norm_eq_abs,abs_of_nonneg ENNReal.toReal_nonneg]
    exact measureReal_le_one)

lemma LawClose.prod_same_left (μ : Measure X) [IsProbabilityMeasure μ]
    {ν η : Measure Y} [IsProbabilityMeasure ν] [IsProbabilityMeasure η]
    {ε : ℝ} (h : LawClose ν η ε) : LawClose (μ.prod ν) (μ.prod η) ε := by
  intro D hD
  rw [real_prod_apply μ ν hD,real_prod_apply μ η hD,
    ←integral_sub (integrable_real_section μ ν hD) (integrable_real_section μ η hD)]
  calc
    _≤∫ x,|ν.real ((Prod.mk x) ⁻¹' D)-η.real ((Prod.mk x) ⁻¹' D)| ∂μ := by
      simpa only [Real.norm_eq_abs] using (norm_integral_le_integral_norm
        (fun x => ν.real ((Prod.mk x) ⁻¹' D)-η.real ((Prod.mk x) ⁻¹' D)))
    _≤∫ _x : X,ε ∂μ := integral_mono_ae
      ((integrable_real_section μ ν hD).sub (integrable_real_section μ η hD)).abs
      (integrable_const ε) (Filter.Eventually.of_forall (fun x => h _ (hD.preimage measurable_prodMk_left)))
    _=ε := by simp

lemma LawClose.prod_same_right {μ ν : Measure X} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {ε : ℝ} (h : LawClose μ ν ε) (η : Measure Y) [IsProbabilityMeasure η] :
    LawClose (μ.prod η) (ν.prod η) ε := by
  simpa only [Measure.prod_swap] using (h.prod_same_left η).map measurable_swap

lemma LawClose.prod {μ ν : Measure X} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {η κ : Measure Y} [IsProbabilityMeasure η] [IsProbabilityMeasure κ]
    {ε δ : ℝ} (h : LawClose μ ν ε) (h' : LawClose η κ δ) :
    LawClose (μ.prod η) (ν.prod κ) (ε+δ) :=
  (h.prod_same_right η).triangle (h'.prod_same_left ν)

end HyperbolicCoding

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

lemma LawClose.mono {μ ν : Measure X} {ε δ : ℝ} (h : LawClose μ ν ε) (hεδ : ε≤δ) :
    LawClose μ ν δ := fun D hD => (h D hD).trans hεδ

lemma measurable_remotePair {T S : X → X} {α : X → A}
    (hT : Measurable T) (hS : Measurable S) (hα : Measurable α) (n : ℕ) :
    Measurable (remotePair T S α n) :=
  (measurable_tailName hS hα n).prodMk (measurable_tailName hT hα n)

lemma stationary_tail_law (μ : Measure X) {T : X → X} (hT : MeasurePreserving T μ μ)
    {α : X → A} (hα : Measurable α) (n : ℕ) :
    μ.map (tailName T α n)=μ.map (tailName T α 0) := by
  have heq : tailName T α n=(tailName T α 0) ∘ T^[n] := by
    funext x i
    simp only [tailName,Function.comp_apply,Nat.add_zero,←Function.iterate_add_apply]
  rw [heq,←Measure.map_map (measurable_tailName hT.measurable hα 0) (hT.measurable.iterate n),
    (hT.iterate n).map_eq]

end HyperbolicCoding

end
end

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_Coding_PartitionLimit
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
variable {X A : Type*} [MeasurableSpace X]

theorem exists_partition_limit [MeasurableSpace A] [Fintype A] [MeasurableSingletonClass A] [Nonempty A]
    (μ : Measure X) (q : ℕ → X → A) (hq : ∀ n,Measurable (q n))
    (hs : (∑' n : ℕ,μ {x | q (n+1) x≠q n x})≠⊤) :
    ∃ p : X → A,Measurable p ∧ ∀ᵐ x ∂μ,∀ᶠ n : ℕ in atTop,q n x=p x := by
  obtain ⟨p,hp,hlim⟩ := exists_eventual_decoder q hq
  have hh := ae_eventually_notMem hs
  refine ⟨p,hp,?_⟩
  filter_upwards [hh] with x hx
  obtain ⟨N,hN⟩ := eventually_atTop.mp hx
  have hconst : ∀ n,N≤n → q n x=q N x := by
    intro n hn
    induction n,hn using Nat.le_induction with
    | base => rfl
    | succ n hn ih => exact (not_ne_iff.mp (hN n hn)).trans ih
  have hc : ∀ᶠ n : ℕ in atTop,q n x=q N x := eventually_atTop.mpr ⟨N,hconst⟩
  rwa [hlim x (q N x) hc]

lemma measureReal_tendsto_zero_of_ae_eventually_notMem (μ : Measure X) [IsFiniteMeasure μ]
    (D : ℕ → Set X) (hD : ∀ n,MeasurableSet (D n))
    (ha : ∀ᵐ x ∂μ,∀ᶠ n : ℕ in atTop,x∉D n) :
    Tendsto (fun n => μ.real (D n)) atTop (𝓝 0) := by
  let U (n : ℕ) : Set X := ⋃ j : ℕ,⋃ (_ : n≤j),D j
  have hU (n : ℕ) : MeasurableSet (U n) :=
    MeasurableSet.iUnion (fun j => MeasurableSet.iUnion (fun _ => hD j))
  have hanti : Antitone U := by
    intro n m hnm x hx
    obtain ⟨j,hx⟩ := mem_iUnion.mp hx
    obtain ⟨hj,hx⟩ := mem_iUnion.mp hx
    exact mem_iUnion.mpr ⟨j,mem_iUnion.mpr ⟨hnm.trans hj,hx⟩⟩
  have hi : μ (⋂ n,U n)=0 := by
    apply measure_eq_zero_iff_ae_notMem.mpr
    filter_upwards [ha] with x hx hmem
    obtain ⟨N,hN⟩ := eventually_atTop.mp hx
    obtain ⟨j,hmem⟩ := mem_iUnion.mp (mem_iInter.mp hmem N)
    obtain ⟨hj,hmem⟩ := mem_iUnion.mp hmem
    exact hN j hj hmem
  have ht := tendsto_measure_iInter_atTop (μ := μ) (fun n => (hU n).nullMeasurableSet)
    hanti ⟨0,measure_ne_top μ _⟩
  rw [hi] at ht
  have htr := (ENNReal.tendsto_toReal (by simp : (0 : ℝ≥0∞)≠⊤)).comp ht
  simp only [Function.comp_def,ENNReal.toReal_zero] at htr
  apply squeeze_zero (fun _ => measureReal_nonneg) (fun n => ?_) htr
  exact measureReal_mono (μ := μ) (fun x hx => mem_iUnion.mpr ⟨n,mem_iUnion.mpr ⟨le_rfl,hx⟩⟩) (measure_ne_top μ _)

lemma partition_limit_integer_names [MeasurableSpace A] {μ : Measure X} (e : X ≃ᵐ X) (he : MeasurePreserving e μ μ)
    {q : ℕ → X → A} {p : X → A}
    (hlim : ∀ᵐ x ∂μ,∀ᶠ n : ℕ in atTop,q n x=p x) :
    ∀ᵐ x ∂μ,∀ s : Finset ℤ,∀ᶠ n : ℕ in atTop,∀ i∈s,
      orbitName e (q n) x i=orbitName e p x i := by
  have hh : ∀ i : ℤ,∀ᵐ x ∂μ,∀ᶠ n : ℕ in atTop,
      q n (integerIterate e i x)=p (integerIterate e i x) :=
    fun i => (integerIterate_measurePreserving e he i).quasiMeasurePreserving.ae hlim
  filter_upwards [ae_all_iff.mpr hh] with x hx s
  have hall : ∀ᶠ n : ℕ in atTop,∀ i : s,
      q n (integerIterate e i x)=p (integerIterate e i x) :=
    Filter.eventually_all.2 (fun i => hx i)
  exact hall.mono (fun n hn i hi => hn ⟨i,hi⟩)

end HyperbolicCoding

end
section
namespace HyperbolicCoding
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal Topology
variable {X A : Type*} [MeasurableSpace X] [MeasurableSpace A] [Fintype A]

lemma finite_code_error_tendsto_zero {μ : Measure X} [IsFiniteMeasure μ]
    (e : X ≃ᵐ X) (he : MeasurePreserving e μ μ)
    [MeasurableEq A] {q : ℕ → X → A} {p : X → A}
    (hq : ∀ n,Measurable (q n)) (hp : Measurable p)
    (hlim : ∀ᵐ x ∂μ,∀ᶠ n : ℕ in atTop,q n x=p x) (s : Finset ℤ) :
    Tendsto (fun n => μ.real {x | s.restrict (orbitName e (q n) x)≠s.restrict (orbitName e p x)})
      atTop (𝓝 0) := by
  apply measureReal_tendsto_zero_of_ae_eventually_notMem μ
  · intro n
    exact (measurableSet_eq_fun ((measurable_restrict (s : Set ℤ)).comp (measurable_orbitName e (hq n)))
      ((measurable_restrict (s : Set ℤ)).comp (measurable_orbitName e hp))).compl
  · filter_upwards [partition_limit_integer_names e he hlim] with x hx
    filter_upwards [hx s] with n hn
    simp only [not_ne_iff]
    funext i
    exact hn i i.property

lemma finite_box_law_tendsto {μ : Measure X} [IsFiniteMeasure μ]
    (e : X ≃ᵐ X) (he : MeasurePreserving e μ μ)
    [MeasurableEq A] {q : ℕ → X → A} {p : X → A}
    (hq : ∀ n,Measurable (q n)) (hp : Measurable p)
    (hlim : ∀ᵐ x ∂μ,∀ᶠ n : ℕ in atTop,q n x=p x)
    (s : Finset ℤ) (t : ℤ → Set A) (ht : ∀ i,MeasurableSet (t i)) :
    Tendsto (fun n => (μ.map (orbitName e (q n))).real (Set.pi s t)) atTop
      (𝓝 ((μ.map (orbitName e p)).real (Set.pi s t))) := by
  let D : Set (s → A) := Set.pi Set.univ (fun i => t i)
  have hD : MeasurableSet D := MeasurableSet.univ_pi (fun i => ht i)
  have hpre : (s.restrict : (ℤ → A) → (s → A)) ⁻¹' D=Set.pi s t := by
    ext w
    simp only [D,mem_preimage,Set.mem_pi,mem_univ,true_implies,Finset.mem_coe,Finset.restrict]
    exact ⟨fun h i hi => h ⟨i,hi⟩,fun h i => h i i.property⟩
  have hdist (n : ℕ) :
      |(μ.map (orbitName e (q n))).real (Set.pi s t)-
       (μ.map (orbitName e p)).real (Set.pi s t)|≤
        μ.real {x | s.restrict (orbitName e (q n) x)≠s.restrict (orbitName e p x)} := by
    have hd := law_distance_le_disagreement μ
      ((measurable_restrict (s : Set ℤ)).comp (measurable_orbitName e (hq n)))
      ((measurable_restrict (s : Set ℤ)).comp (measurable_orbitName e hp)) hD
    have hr : Measurable (s.restrict : (ℤ → A) → (s → A)) := measurable_restrict (s : Set ℤ)
    have hmap (u : X → A) (hu : Measurable u) :
        (μ.map (s.restrict ∘ orbitName e u)).real D=
          (μ.map (orbitName e u)).real (Set.pi s t) := by
      simp only [Measure.real]
      rw [←Measure.map_map hr (measurable_orbitName e hu),Measure.map_apply hr hD,hpre]
    change |(μ.map (s.restrict ∘ orbitName e (q n))).real D-
      (μ.map (s.restrict ∘ orbitName e p)).real D|≤_ at hd
    rw [hmap (q n) (hq n),hmap p hp] at hd
    exact hd
  have hz := squeeze_zero (fun n => abs_nonneg _ ) hdist
    (finite_code_error_tendsto_zero e he hq hp hlim s)
  exact tendsto_iff_dist_tendsto_zero.mpr (by simpa only [Real.dist_eq] using hz)

theorem iid_law_of_partition_limit {μ : Measure X} [IsProbabilityMeasure μ]
    (e : X ≃ᵐ X) (he : MeasurePreserving e μ μ)
    [MeasurableEq A] {q : ℕ → X → A} {p : X → A}
    (hq : ∀ n,Measurable (q n)) (hp : Measurable p)
    (hlim : ∀ᵐ x ∂μ,∀ᶠ n : ℕ in atTop,q n x=p x)
    (β : Measure A) [IsProbabilityMeasure β]
    (hblock : ∀ (s : Finset ℤ) (t : ℤ → Set A),(∀ i,MeasurableSet (t i)) →
      Tendsto (fun n => (μ.map (orbitName e (q n))).real (Set.pi s t)) atTop
        (𝓝 ((∏ i∈s,β (t i)).toReal))) :
    MeasurePreserving (orbitName e p) μ (Measure.infinitePi (fun _ : ℤ => β)) := by
  refine ⟨measurable_orbitName e hp,Measure.eq_infinitePi _ ?_⟩
  intro s t ht
  have h := tendsto_nhds_unique (finite_box_law_tendsto e he hq hp hlim s t ht) (hblock s t ht)
  have hf : (∏ i∈s,β (t i))≠⊤ := by
    rw [←Measure.infinitePi_pi (fun _ : ℤ => β) (fun i _ => ht i)]
    exact measure_ne_top _ _
  exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) hf).mp h

end HyperbolicCoding

end
end

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_Coupling_FiniteMaximalCoupling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace HyperbolicCoding
open MeasureTheory Set
open scoped BigOperators ENNReal

theorem finite_maximal_coupling_equal_mass {A : Type*} [Fintype A] [DecidableEq A]
    (p q : A → ℝ) (hp : ∀ a,0≤p a) (hq : ∀ a,0≤q a)
    (heq : ∑ a,p a=∑ a,q a) :
    ∃ r : A → A → ℝ,(∀ a b,0 ≤ r a b) ∧
      (∀ a,∑ b,r a b=p a) ∧ (∀ b,∑ a,r a b=q b) ∧
      (∑ a,∑ b,r a b*(if a=b then 0 else 1))=∑ a,max (p a-q a) 0 := by
  classical
  let d : A → ℝ := fun a => min (p a) (q a)
  let u : A → ℝ := fun a => p a-d a
  let v : A → ℝ := fun a => q a-d a
  let t : ℝ := ∑ a,u a
  have hd (a) : 0≤d a := le_min (hp a) (hq a)
  have hu (a) : 0≤u a := sub_nonneg.mpr (min_le_left _ _)
  have hv (a) : 0≤v a := sub_nonneg.mpr (min_le_right _ _)
  have ht : 0≤t := Finset.sum_nonneg (fun a _ => hu a)
  have htv : ∑ a,v a=t := by
    dsimp only [t,u,v]
    rw [Finset.sum_sub_distrib,Finset.sum_sub_distrib,heq]
  have huv (a) : u a*v a=0 := by
    rcases le_total (p a) (q a) with ha | ha
    · simp only [u,v,d,min_eq_left ha,sub_self,zero_mul]
    · simp only [u,v,d,min_eq_right ha,sub_self,mul_zero]
  have hmax (a) : u a=max (p a-q a) 0 := by
    rcases le_total (p a) (q a) with ha | ha
    · simp only [u,d,min_eq_left ha,sub_self,max_eq_right (sub_nonpos.mpr ha)]
    · simp only [u,d,min_eq_right ha,max_eq_left (sub_nonneg.mpr ha)]
  by_cases ht0 : t=0
  · have hu0 (a) : u a=0 := by
      have hh := Finset.single_le_sum (fun b _ => hu b) (Finset.mem_univ a)
      change u a≤t at hh
      rw [ht0] at hh
      exact le_antisymm hh (hu a)
    have hv0 (a) : v a=0 := by
      have hh := Finset.single_le_sum (fun b _ => hv b) (Finset.mem_univ a)
      rw [htv,ht0] at hh
      exact le_antisymm hh (hv a)
    refine ⟨fun a b => if a=b then p a else 0,?_,?_,?_,?_⟩
    · intro a b
      dsimp only
      split_ifs
      · exact hp a
      · exact le_rfl
    · intro a; simp
    · intro b
      simp only [Finset.sum_ite_eq',Finset.mem_univ,ite_true]
      have h1 := hu0 b
      have h2 := hv0 b
      dsimp [u,v] at h1 h2
      linarith
    · have he (a b : A) : (if a=b then p a else 0)*(if a=b then (0 : ℝ) else 1)=0 := by
        by_cases h : a=b <;> simp [h]
      simp_rw [he]
      simp only [Finset.sum_const_zero]
      rw [←show (∑ a,u a)=(∑ a,max (p a-q a) 0) from Finset.sum_congr rfl (fun a _ => hmax a)]
      exact ht0.symm
  · have htpos : 0<t := lt_of_le_of_ne ht (Ne.symm ht0)
    let r : A → A → ℝ := fun a b => (if a=b then d a else 0)+u a*v b/t
    have hr (a b) : 0 ≤ r a b := by
      dsimp only [r]
      exact add_nonneg (by split_ifs; exact hd a; exact le_rfl) (div_nonneg (mul_nonneg (hu a) (hv b)) ht)
    have hrow (a) : ∑ b,r a b=p a := by
      simp only [r,Finset.sum_add_distrib,Finset.sum_ite_eq,Finset.mem_univ,ite_true,
        ←Finset.sum_div,←Finset.mul_sum,htv,mul_div_cancel_right₀ _ ht0]
      dsimp only [u]
      ring
    have hcol (b) : ∑ a,r a b=q b := by
      simp only [r,Finset.sum_add_distrib,Finset.sum_ite_eq',Finset.mem_univ,ite_true,
        ←Finset.sum_div,←Finset.sum_mul]
      change d b+t*v b/t=q b
      rw [mul_div_cancel_left₀ _ ht0]
      dsimp only [v]
      ring
    refine ⟨r,hr,hrow,hcol,?_⟩
    have hoff (a b) : r a b*(if a=b then 0 else 1)=u a*v b/t := by
      by_cases hab : a=b
      · subst b; simp [huv]
      · simp only [r,ite_eq_right hab,zero_add,mul_one]
    simp_rw [hoff]
    simp only [←Finset.sum_div,←Finset.mul_sum,htv,mul_div_cancel_right₀ _ ht0]
    exact Finset.sum_congr rfl (fun a _ => hmax a)

theorem finite_maximal_coupling {A : Type*} [Fintype A] [DecidableEq A]
    (p q : A → ℝ) (hp : ∀ a,0≤p a) (hq : ∀ a,0≤q a)
    (hp1 : ∑ a,p a=1) (hq1 : ∑ a,q a=1) :
    ∃ r : A → A → ℝ,(∀ a b,0 ≤ r a b) ∧
      (∀ a,∑ b,r a b=p a) ∧ (∀ b,∑ a,r a b=q b) ∧
      (∑ a,∑ b,r a b*(if a=b then 0 else 1))=∑ a,max (p a-q a) 0 :=
  finite_maximal_coupling_equal_mass p q hp hq (hp1.trans hq1.symm)

end HyperbolicCoding

end
section
namespace HyperbolicCoding
open MeasureTheory Set
open scoped BigOperators ENNReal

lemma positive_mass_difference_le {A : Type*} [Fintype A] [MeasurableSpace A]
    [MeasurableSingletonClass A] (μ ν : Measure A) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {ε : ℝ} (h : LawClose μ ν ε) :
    (∑ a,max (μ.real {a}-ν.real {a}) 0)≤ε := by
  classical
  let D := Finset.univ.filter (fun a : A => ν.real {a}≤μ.real {a})
  have hm (a : A) : max (μ.real {a}-ν.real {a}) 0=
      if ν.real {a}≤μ.real {a} then μ.real {a}-ν.real {a} else 0 := by
    split_ifs with ha
    · exact max_eq_left (sub_nonneg.mpr ha)
    · exact max_eq_right (sub_nonpos.mpr (le_of_not_ge ha))
  have he : (∑ a,max (μ.real {a}-ν.real {a}) 0)=μ.real D-ν.real D := by
    simp_rw [hm]
    rw [←Finset.sum_filter]
    change (∑ a∈D,(μ.real {a}-ν.real {a}))=_
    rw [Finset.sum_sub_distrib,sum_measureReal_singleton,sum_measureReal_singleton]
  rw [he]
  exact (le_abs_self _).trans (h D D.measurableSet)

theorem finite_coupling_of_lawClose {A : Type*} [Fintype A] [DecidableEq A]
    [MeasurableSpace A] [MeasurableSingletonClass A]
    (μ ν : Measure A) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {ε : ℝ} (h : LawClose μ ν ε) :
    ∃ r : A → A → ℝ,(∀ a b,0 ≤ r a b) ∧
      (∀ a,∑ b,r a b=μ.real {a}) ∧ (∀ b,∑ a,r a b=ν.real {b}) ∧
      (∑ a,∑ b,r a b*(if a=b then 0 else 1))≤ε := by
  obtain ⟨r,hr,hrow,hcol,herr⟩ := finite_maximal_coupling (fun a => μ.real {a}) (fun a => ν.real {a})
    (fun _ => measureReal_nonneg) (fun _ => measureReal_nonneg)
    (by simp)
    (by simp)
  exact ⟨r,hr,hrow,hcol,herr.le.trans (positive_mass_difference_le μ ν h)⟩

end HyperbolicCoding

end
section
namespace HyperbolicCoding
open scoped BigOperators
variable {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]

namespace MatrixCoupling
variable {p : A → ℝ} {q : B → ℝ} {s : C → ℝ}

lemma comp_cost_le (r : MatrixCoupling p q) (t : MatrixCoupling q s)
    (d : A → B → ℝ) (e : B → C → ℝ) (f : A → C → ℝ)
    (htri : ∀ a b c,f a c≤d a b+e b c) :
    (r.comp t).cost f ≤ r.cost d+t.cost e := by
  unfold cost comp
  simp only [Finset.sum_mul]
  calc
    _≤∑ a,∑ c,∑ b,glueWeight r t a b c*(d a b+e b c) :=
      Finset.sum_le_sum (fun a _ => Finset.sum_le_sum (fun c _ =>
        Finset.sum_le_sum (fun b _ => mul_le_mul_of_nonneg_left (htri a b c) (glueWeight_nonneg r t a b c))))
    _=(∑ a,∑ c,∑ b,glueWeight r t a b c*d a b)+
        (∑ a,∑ c,∑ b,glueWeight r t a b c*e b c) := by
      simp only [mul_add,Finset.sum_add_distrib]
    _=(∑ a,∑ b,r.weight a b*d a b)+(∑ b,∑ c,t.weight b c*e b c) := by
      congr 1
      · apply Finset.sum_congr rfl
        intro a _
        rw [Finset.sum_comm]
        simp only [←Finset.sum_mul,glueWeight_row]
      · rw [Finset.sum_comm]
        calc
          _ = ∑ c,∑ b,∑ a,glueWeight r t a b c*e b c := by
            apply Finset.sum_congr rfl
            intro c _
            exact Finset.sum_comm
          _ = ∑ c,∑ b,t.weight b c*e b c := by simp only [←Finset.sum_mul,glueWeight_col]
          _ = _ := Finset.sum_comm

end MatrixCoupling
end HyperbolicCoding

end
section
namespace StandardMapEntropy.Entropy
open MeasureTheory Set Filter
open scoped ENNReal Topology BigOperators
variable {X A : Type*} [MeasurableSpace X] [MeasurableSpace A]
    [Fintype A] [MeasurableSingletonClass A]

lemma integrable_finite_observation (μ : Measure X) [IsFiniteMeasure μ]
    (p : X → A) (hp : Measurable p) (g : A → ℝ) : Integrable (fun x => g (p x)) μ := by
  classical
  apply Integrable.of_bound ((measurable_of_countable g).comp hp).aestronglyMeasurable (∑ a,|g a|)
  exact ae_of_all _ (fun x => by
    rw [Real.norm_eq_abs]
    exact Finset.single_le_sum (fun a _ => abs_nonneg (g a)) (Finset.mem_univ _))

lemma information_integrable (μ : Measure X) [IsFiniteMeasure μ]
    (p : X → A) (hp : Measurable p) : Integrable (information μ p) μ :=
  integrable_finite_observation μ p hp (fun a : A => -Real.log (mass μ p a))

lemma integral_information (μ : Measure X) [IsFiniteMeasure μ]
    (p : X → A) (hp : Measurable p) : (∫ x,information μ p x ∂μ)=obs μ p := by
  simp only [information]
  rw [←sum_mass_mul_integral μ p hp (fun a => -Real.log (mass μ p a))]
  simp only [obs,shannon,Real.negMulLog,mul_neg,neg_mul]

omit [MeasurableSpace A] [MeasurableSingletonClass A] in
lemma ae_mass_positive (μ : Measure X) [IsFiniteMeasure μ] (p : X → A) :
    ∀ᵐ x ∂μ,0 < mass μ p (p x) := by
  have hzero (a : A) : ∀ᵐ x ∂μ,mass μ p a=0 → p x≠a := by
    by_cases ha : mass μ p a=0
    · have hm : μ (p ⁻¹' {a})=0 := by
        apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top μ _) ENNReal.zero_ne_top).mp
        exact ha
      filter_upwards [measure_eq_zero_iff_ae_notMem.mp hm] with x hx _h
      exact hx
    · exact ae_of_all _ (fun _ h => (ha h).elim)
  filter_upwards [ae_all_iff.mpr hzero] with x hx
  exact lt_of_le_of_ne (mass_nonneg μ p _) (Ne.symm (fun h => hx (p x) h rfl))

end StandardMapEntropy.Entropy

end
section
namespace HyperbolicCoding
open MeasureTheory Set StandardMapEntropy.Entropy
open scoped ENNReal BigOperators
variable {X A B C D : Type*} [MeasurableSpace X]
    [Fintype A] [Fintype B] [Fintype C] [Fintype D]

namespace MatrixCoupling
variable {p : A → ℝ} {q : B → ℝ} {s : C → ℝ} {t : D → ℝ}

lemma diagonal_cost (p : A → ℝ) (hp : ∀ a,0≤p a) (d : A → A → ℝ)
    (hd : ∀ a,d a a=0) : (diagonal p hp).cost d=0 := by
  classical
  unfold cost diagonal
  simp only [ite_mul,zero_mul,Finset.sum_ite_eq,Finset.mem_univ,ite_true,hd,mul_zero,Finset.sum_const_zero]

lemma product_cost (r : MatrixCoupling p q) (u : MatrixCoupling s t)
    (hp : ∑ a,p a=1) (hs : ∑ c,s c=1) (d : A → B → ℝ) (e : C → D → ℝ) :
    (r.product u).cost (fun ac bd => d ac.1 bd.1+e ac.2 bd.2)=r.cost d+u.cost e := by
  unfold cost product
  simp only [Fintype.sum_prod_type,mul_add,Finset.sum_add_distrib]
  congr 1
  · calc
      _ = ∑ a,∑ c,∑ b,r.weight a b*d a b*(∑ v,u.weight c v) := by
        apply Finset.sum_congr rfl
        intro a _
        apply Finset.sum_congr rfl
        intro c _
        apply Finset.sum_congr rfl
        intro b _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro v _
        ring
      _ = ∑ a,∑ c,∑ b,r.weight a b*d a b*s c := by simp only [u.row]
      _ = ∑ a,∑ b,r.weight a b*d a b := by
        apply Finset.sum_congr rfl
        intro a _
        rw [Finset.sum_comm]
        simp only [←Finset.mul_sum,hs,mul_one]
  · calc
      _ = ∑ a,∑ c,(∑ b,r.weight a b)*(∑ v,u.weight c v*e c v) := by
        apply Finset.sum_congr rfl
        intro a _
        apply Finset.sum_congr rfl
        intro c _
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro b _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro v _
        ring
      _ = ∑ a,∑ c,p a*(∑ v,u.weight c v*e c v) := by simp only [r.row]
      _ = ∑ c,∑ v,u.weight c v*e c v := by
        rw [Finset.sum_comm]
        simp only [←Finset.sum_mul,hp,one_mul]

section Observations
variable [MeasurableSpace A] [MeasurableSingletonClass A]
    [MeasurableSpace B] [MeasurableSingletonClass B]
variable (μ : Measure X) [IsFiniteMeasure μ]

lemma observations_cost (p : X → A) (q : X → B) (hp : Measurable p) (hq : Measurable q)
    (d : A → B → ℝ) : (observations μ p q hp hq).cost d=∫ x,d (p x) (q x) ∂μ := by
  change (∑ a,∑ b,mass μ (fun x => (p x,q x)) (a,b)*d a b)=_
  simpa only [Fintype.sum_prod_type] using
    sum_mass_mul_integral μ (fun x => (p x,q x)) (hp.prodMk hq) (fun ab => d ab.1 ab.2)

end Observations
end MatrixCoupling
end HyperbolicCoding

end
section
namespace HyperbolicCoding
open MeasureTheory MeasureTheory.Measure ProbabilityTheory Set Filter
open scoped ENNReal Topology

lemma continuous_cdf_atomless (ν : Measure ℝ) [IsProbabilityMeasure ν]
    [NullSingletonClass ν] : Continuous (cdf ν) := by
  have hc : Continuous (fun a : ℝ => ∫ _x in Iic a,(1 : ℝ) ∂ν) := by
    rw [continuous_iff_continuousAt]
    intro a
    have h := ((integrable_const (1 : ℝ)).integrableOn : IntegrableOn (fun _x : ℝ => (1 : ℝ)) (Iic (a+1)) ν)
    exact (h.continuousOn_Iic_primitive_Iic a (by simp)).continuousAt (Iic_mem_nhds (by linarith))
  simpa only [integral_const,smul_eq_mul,mul_one,measureReal_restrict_apply_univ,←cdf_eq_real] using hc

theorem exists_event_real_mass {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] [NullSingletonClass μ]
    {t : ℝ} (ht : 0≤t) (ht1 : t≤1) :
    ∃ E : Set X,MeasurableSet E ∧ μ.real E=t := by
  by_cases ht0 : t=0
  · exact ⟨∅,MeasurableSet.empty,by simp [ht0]⟩
  by_cases hte : t=1
  · exact ⟨univ,MeasurableSet.univ,by simp [hte]⟩
  let b : X → ℝ := embeddingReal X
  have hb : MeasurableEmbedding b := measurableEmbedding_embeddingReal X
  let ν := μ.map b
  have : IsProbabilityMeasure ν := by first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | (apply Measurable.aemeasurable; measurability) | measurability)
  have : NullSingletonClass ν := by
    constructor
    intro y
    rw [show ν=μ.map b from rfl,Measure.map_apply hb.measurable (measurableSet_singleton y)]
    by_cases hy : ∃ x,b x=y
    · obtain ⟨x,rfl⟩ := hy
      have hs : b ⁻¹' {b x}={x} := by
        ext z
        exact hb.injective.eq_iff
      simp only [hs,measure_singleton]
    · have hs : b ⁻¹' {y}=∅ := eq_empty_iff_forall_notMem.mpr (fun x hx => hy ⟨x,hx⟩)
      simp only [hs,measure_empty]
  have hs := isPreconnected_univ.intermediate_value_Ioo (s:=Set.univ)
    (show (atBot : Filter ℝ)≤𝓟 Set.univ by simp) (show (atTop : Filter ℝ)≤𝓟 Set.univ by simp)
    (continuous_cdf_atomless ν).continuousOn (tendsto_cdf_atBot ν) (tendsto_cdf_atTop ν)
    (show t∈Ioo (0 : ℝ) 1 from ⟨lt_of_le_of_ne ht (Ne.symm ht0),lt_of_le_of_ne ht1 hte⟩)
  obtain ⟨r,_hr,hrt⟩ := hs
  refine ⟨b ⁻¹' Iic r,measurableSet_Iic.preimage hb.measurable,?_⟩
  rw [←map_measureReal_apply hb.measurable measurableSet_Iic]
  exact (cdf_eq_real ν r).symm.trans hrt

theorem exists_subset_real_mass {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] [NullSingletonClass μ]
    {S : Set X} (hS : MeasurableSet S) {t : ℝ} (ht : 0≤t) (htS : t≤μ.real S) :
    ∃ E : Set X,MeasurableSet E ∧ E⊆S ∧ μ.real E=t := by
  by_cases ht0 : t=0
  · exact ⟨∅,MeasurableSet.empty,empty_subset _,by simp [ht0]⟩
  have htpos : 0<t := lt_of_le_of_ne ht (Ne.symm ht0)
  have hSr : 0<μ.real S := htpos.trans_le htS
  have hS0 : μ S≠0 := by
    intro h
    simp only [Measure.real,h,ENNReal.toReal_zero] at hSr
    exact lt_irrefl _ hSr
  let ν : Measure X := (μ S)⁻¹ • μ.restrict S
  have : IsProbabilityMeasure ν := by
    constructor
    simp only [ν,Measure.smul_apply,smul_eq_mul,Measure.restrict_apply MeasurableSet.univ,univ_inter]
    exact ENNReal.inv_mul_cancel hS0 (measure_ne_top μ S)
  have : NullSingletonClass ν := by
    constructor
    intro x
    have hz : μ ({x}∩S)=0 := measure_mono_null inter_subset_left (measure_singleton x)
    simp only [ν,Measure.smul_apply,smul_eq_mul,Measure.restrict_apply (measurableSet_singleton x),hz,mul_zero]
  obtain ⟨T,hT,hTm⟩ := exists_event_real_mass ν (div_nonneg ht hSr.le) ((div_le_one hSr).mpr htS)
  refine ⟨S∩T,hS.inter hT,inter_subset_left,?_⟩
  have he : ν.real T=μ.real (S∩T)/μ.real S := by
    simp only [ν,Measure.real,Measure.smul_apply,smul_eq_mul,Measure.restrict_apply hT,
      ENNReal.toReal_mul,ENNReal.toReal_inv,inter_comm T S,div_eq_mul_inv]
    ring
  rw [he] at hTm
  exact (div_left_inj' hSr.ne').mp hTm

end HyperbolicCoding

end
end

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_Coupling_AtomlessFinitePartition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace HyperbolicCoding
open MeasureTheory Set
open scoped ENNReal BigOperators
variable {X A : Type*} [MeasurableSpace X] [StandardBorelSpace X]
variable (μ : Measure X) [IsFiniteMeasure μ] [NullSingletonClass μ]

theorem exists_disjoint_cuts (s : Finset A) (w : A → ℝ) (hw : ∀ a,0≤w a)
    {S : Set X} (hS : MeasurableSet S) (hsum : (∑ a∈s,w a)≤μ.real S) :
    ∃ E : A → Set X,(∀ a∈s,MeasurableSet (E a) ∧ E a⊆S ∧ μ.real (E a)=w a) ∧
      (∀ a∈s,∀ b∈s,a≠b → Disjoint (E a) (E b)) := by
  classical
  induction s using Finset.induction_on generalizing S with
  | empty => exact ⟨fun _ => ∅,by simp,by simp⟩
  | @insert a s ha ih =>
    have hsumnonneg : 0≤∑ b∈s,w b := Finset.sum_nonneg (fun b _ => hw b)
    rw [Finset.sum_insert ha] at hsum
    obtain ⟨D,hD,hDS,hDm⟩ := exists_subset_real_mass μ hS (hw a) (by linarith)
    have hrem : (∑ b∈s,w b)≤μ.real (S\D) := by
      rw [measureReal_sdiff hDS hD,hDm]
      linarith
    obtain ⟨F,hF,hFd⟩ := ih (hS.diff hD) hrem
    refine ⟨fun b => if b=a then D else F b,?_,?_⟩
    · intro b hb
      by_cases hba : b=a
      · subst b
        simpa using And.intro hD (And.intro hDS hDm)
      · have hbs : b∈s := (Finset.mem_insert.mp hb).resolve_left hba
        simpa only [ite_eq_right hba] using And.intro (hF b hbs).1
          (And.intro ((hF b hbs).2.1.trans sdiff_subset) (hF b hbs).2.2)
    · intro b hb c hc hbc
      by_cases hba : b=a
      · subst b
        have hca : c≠a := Ne.symm hbc
        have hcs := (Finset.mem_insert.mp hc).resolve_left hca
        simp only [ite_eq_right hca]
        exact disjoint_left.mpr (fun x hxD hxF => ((hF c hcs).2.1 hxF).2 hxD)
      · by_cases hca : c=a
        · subst c
          have hbs := (Finset.mem_insert.mp hb).resolve_left hba
          simp only [ite_eq_right hba]
          exact disjoint_left.mpr (fun x hxF hxD => ((hF b hbs).2.1 hxF).2 hxD)
        · simp only [ite_eq_right hba,ite_eq_right hca]
          exact hFd b ((Finset.mem_insert.mp hb).resolve_left hba) c
            ((Finset.mem_insert.mp hc).resolve_left hca) hbc

end HyperbolicCoding

end
section
namespace HyperbolicCoding
open MeasureTheory Set

lemma exists_measurable_coloring {X A : Type*} [MeasurableSpace X]
    [MeasurableSpace A] [Nonempty A] (s : Finset A) (E : A → Set X)
    (hm : ∀ a∈s,MeasurableSet (E a))
    (hd : ∀ a∈s,∀ b∈s,a≠b → Disjoint (E a) (E b)) :
    ∃ q : X → A,Measurable q ∧ ∀ a∈s,∀ x∈E a,q x=a := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨fun _ => Classical.arbitrary A,measurable_const,by simp⟩
  | @insert a s ha ih =>
    obtain ⟨q,hq,hqa⟩ := ih (fun b hb => hm b (Finset.mem_insert_of_mem hb))
      (fun b hb c hc => hd b (Finset.mem_insert_of_mem hb) c (Finset.mem_insert_of_mem hc))
    let q' : X → A := (E a).piecewise (fun _ => a) q
    refine ⟨q',measurable_const.piecewise (hm a (Finset.mem_insert_self _ _)) hq,?_⟩
    intro b hb x hx
    by_cases hba : b=a
    · subst b
      exact Set.piecewise_eq_of_mem _ _ _ hx
    · have hbs := (Finset.mem_insert.mp hb).resolve_left hba
      have hxa : x∉E a := fun hxa => (hd b hb a (Finset.mem_insert_self _ _) hba).le_bot ⟨hx,hxa⟩
      exact (Set.piecewise_eq_of_notMem _ _ _ hxa).trans (hqa b hbs x hx)

end HyperbolicCoding

end
section
namespace HyperbolicCoding
open MeasureTheory Set
open scoped ENNReal BigOperators

theorem exists_finite_random_variable {X A : Type*} [MeasurableSpace X] [StandardBorelSpace X]
    [MeasurableSpace A] [Fintype A] [Nonempty A]
    (μ : Measure X) [IsFiniteMeasure μ] [NullSingletonClass μ]
    {S : Set X} (hS : MeasurableSet S) (w : A → ℝ) (hw : ∀ a,0≤w a)
    (hwS : ∑ a,w a=μ.real S) :
    ∃ q : X → A,Measurable q ∧ ∀ a,μ.real (S∩q ⁻¹' {a})=w a := by
  classical
  obtain ⟨E,hE,hEd⟩ := exists_disjoint_cuts μ Finset.univ w hw hS hwS.le
  have hm (a : A) := (hE a (Finset.mem_univ a)).1
  have hsub (a : A) := (hE a (Finset.mem_univ a)).2.1
  have he (a : A) := (hE a (Finset.mem_univ a)).2.2
  have hd : Pairwise (Function.onFun Disjoint E) := fun a b hab =>
    hEd a (Finset.mem_univ a) b (Finset.mem_univ b) hab
  obtain ⟨q,hq,hqa⟩ := exists_measurable_coloring Finset.univ E
    (fun a _ => hm a) (fun a _ b _ => hd (i:=a) (j:=b))
  have hUm : MeasurableSet (⋃ a,E a) := MeasurableSet.iUnion hm
  have hUS : (⋃ a,E a)⊆S := iUnion_subset hsub
  have hUr : μ.real (⋃ a,E a)=μ.real S := by
    rw [measureReal_iUnion_fintype hd hm]
    simp_rw [he]
    exact hwS
  have hz : μ (S\⋃ a,E a)=0 := (measureReal_eq_zero_iff).mp (by
    rw [measureReal_sdiff hUS hUm,hUr,sub_self])
  have hAE : ∀ᵐ x ∂μ,x∈S → ∃ a,x∈E a := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp hz] with x hx hxS
    by_contra hh
    apply hx
    exact ⟨hxS,by simpa only [mem_iUnion,not_exists] using hh⟩
  refine ⟨q,hq,fun a => ?_⟩
  have hEq : (S∩q ⁻¹' {a} : Set X) =ᵐ[μ] E a := by
    filter_upwards [hAE] with x hx
    apply propext
    constructor
    · rintro ⟨hxS,hxq⟩
      obtain ⟨b,hxb⟩ := hx hxS
      have hba : b=a := (hqa b (Finset.mem_univ b) x hxb).symm.trans hxq
      change x∈E a
      exact hba ▸ hxb
    · intro hxa
      exact ⟨hsub a hxa,hqa a (Finset.mem_univ a) x hxa⟩
  exact (measureReal_congr hEq).trans (he a)

end HyperbolicCoding

end
section
namespace HyperbolicCoding
open MeasureTheory Set StandardMapEntropy.Entropy
open scoped ENNReal BigOperators
variable {X A B : Type*} [MeasurableSpace X] [StandardBorelSpace X]
    [MeasurableSpace A] [Fintype A] [MeasurableSingletonClass A]
    [MeasurableSpace B] [Fintype B] [MeasurableSingletonClass B] [Nonempty B]
variable (μ : Measure X) [IsProbabilityMeasure μ] [NullSingletonClass μ]

omit [MeasurableSingletonClass B] in
theorem realize_finite_coupling (p : X → A) (hp : Measurable p)
    (r : A → B → ℝ) (hr : ∀ a b,0 ≤ r a b) (hrow : ∀ a,∑ b,r a b=mass μ p a) :
    ∃ q : X → B,Measurable q ∧ ∀ a b,mass μ (fun x => (p x,q x)) (a,b)=r a b := by
  have hh (a : A) : ∃ q : X → B,Measurable q ∧
      ∀ b,μ.real ((p ⁻¹' {a})∩q ⁻¹' {b})=r a b :=
    exists_finite_random_variable μ (hp (measurableSet_singleton a)) (r a) (hr a) (hrow a)
  choose q hq hqr using hh
  let q' : X → B := fun x => q (p x) x
  have hq' : Measurable q' := (measurable_from_prod_countable_right
    (f:=fun ax : A×X => q ax.1 ax.2) hq).comp (hp.prodMk measurable_id)
  refine ⟨q',hq',fun a b => ?_⟩
  have hset : (fun x => (p x,q' x)) ⁻¹' {(a,b)}=(p ⁻¹' {a})∩q a ⁻¹' {b} := by
    ext x
    simp only [mem_preimage,mem_singleton_iff,Prod.mk.injEq,mem_inter_iff,q']
    constructor
    · rintro ⟨ha,hb⟩
      exact ⟨ha,by simpa only [ha] using hb⟩
    · rintro ⟨ha,hb⟩
      exact ⟨ha,by simpa only [ha] using hb⟩
  simpa only [mass,hset,Measure.real] using hqr a b

omit [StandardBorelSpace X] [NullSingletonClass μ] in
lemma repaint_error_eq_sum [DecidableEq A] (p q : X → A) (hp : Measurable p) (hq : Measurable q) :
    μ.real {x | p x≠q x}=(∑ a,∑ b,mass μ (fun x => (p x,q x)) (a,b)*(if a=b then 0 else 1)) := by
  classical
  let g : A×A → ℝ := fun ab => if ab.1=ab.2 then 0 else 1
  have hs := sum_mass_mul_integral μ (fun x => (p x,q x)) (hp.prodMk hq) g
  rw [Fintype.sum_prod_type] at hs
  have hi : (∫ x,g (p x,q x) ∂μ)=μ.real {x | p x≠q x} := by
    have he : (fun x => g (p x,q x))={x | p x≠q x}.indicator (fun _x : X => (1 : ℝ)) := by
      funext x
      by_cases hx : p x=q x <;> simp [g,hx]
    have hD : MeasurableSet {x | p x≠q x} := (measurableSet_eq_fun hp hq).compl
    rw [he]
    change (∫ x,{x | p x≠q x}.indicator (fun _x : X => (1 : ℝ)) x ∂μ)=_
    rw [integral_indicator hD]
    simp
  exact hi.symm.trans hs.symm

end HyperbolicCoding

end
section
namespace StandardMapEntropy.Entropy
open MeasureTheory Set
open scoped BigOperators
variable {X A B C : Type*} [MeasurableSpace X]
    [MeasurableSpace A] [Fintype A] [MeasurableSingletonClass A]
    [MeasurableSpace B] [Fintype B] [MeasurableSingletonClass B]
    [MeasurableSpace C] [Fintype C] [MeasurableSingletonClass C]
variable (μ : Measure X) [IsFiniteMeasure μ]

omit [Fintype A] [Fintype C] in
lemma mass_triple_first_third (p : X → A) (q : X → B) (r : X → C)
    (hp : Measurable p) (hq : Measurable q) (hr : Measurable r) (a : A) (c : C) :
    mass μ (fun x => (p x,r x)) (a,c)=
      ∑ b,mass μ (fun x => ((p x,q x),r x)) ((a,b),c) := by
  rw [mass_joint_row μ (fun x => (p x,r x)) q (hp.prodMk hr) hq (a,c)]
  apply Finset.sum_congr rfl
  intro b _hb
  unfold mass
  congr 2
  ext x
  simp only [mem_preimage,mem_singleton_iff,Prod.mk.injEq]
  tauto

omit [Fintype B] [Fintype C] in
lemma mass_triple_second_third (p : X → A) (q : X → B) (r : X → C)
    (hp : Measurable p) (hq : Measurable q) (hr : Measurable r) (b : B) (c : C) :
    mass μ (fun x => (q x,r x)) (b,c)=
      ∑ a,mass μ (fun x => ((p x,q x),r x)) ((a,b),c) := by
  rw [mass_joint_row μ (fun x => (q x,r x)) p (hq.prodMk hr) hp (b,c)]
  apply Finset.sum_congr rfl
  intro a _ha
  unfold mass
  congr 2
  ext x
  simp only [mem_preimage,mem_singleton_iff,Prod.mk.injEq]
  tauto

end StandardMapEntropy.Entropy
end
section
namespace HyperbolicCoding
open MeasureTheory Set StandardMapEntropy.Entropy
open scoped ENNReal BigOperators
variable {X A B : Type*} [MeasurableSpace X] [StandardBorelSpace X]
    [MeasurableSpace A] [Fintype A] [MeasurableSingletonClass A]
    [MeasurableSpace B] [Fintype B] [MeasurableSingletonClass B] [Nonempty B]
variable (μ : Measure X) [IsProbabilityMeasure μ] [NullSingletonClass μ]

theorem copy_independent_of_finite_past (p : X → A) (q : X → B)
    (hp : Measurable p) (hq : Measurable q) {ε : ℝ}
    (hclose : LawClose (μ.map (fun x => (p x,q x))) ((μ.map p).prod (μ.map q)) ε) :
    ∃ q' : X → B,Measurable q' ∧ μ.map q'=μ.map q ∧
      μ.map (fun x => (p x,q' x))=(μ.map p).prod (μ.map q) ∧
      μ.real {x | q x≠q' x}≤ε := by
  classical
  have : IsProbabilityMeasure (μ.map p) := by first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | (apply Measurable.aemeasurable; measurability) | measurability)
  have : IsProbabilityMeasure (μ.map q) := by first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | (apply Measurable.aemeasurable; measurability) | measurability)
  have : IsProbabilityMeasure (μ.map (fun x => (p x,q x))) := by first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | (apply Measurable.aemeasurable; measurability) | measurability)
  let u : A → B → ℝ := fun a b => mass μ (fun x => (p x,q x)) (a,b)
  let v : A → B → ℝ := fun a b => mass μ p a*mass μ q b
  have hu (a b) : 0≤u a b := mass_nonneg _ _ _
  have hv (a b) : 0≤v a b := mul_nonneg (mass_nonneg _ _ _) (mass_nonneg _ _ _)
  have hrow (a) : ∑ b,u a b=∑ b,v a b := by
    rw [←mass_joint_row μ p q hp hq]
    dsimp only [v]
    rw [←Finset.mul_sum,mass_sum μ q hq]
    simp
  have hc (a) := finite_maximal_coupling_equal_mass (u a) (v a) (hu a) (hv a) (hrow a)
  choose r hr hrrow hrcol hrerr using hc
  obtain ⟨q',hq',hqq'⟩ := realize_finite_coupling μ (fun x => (p x,q x))
    (hp.prodMk hq) (fun ab c => r ab.1 ab.2 c) (fun ab c => hr ab.1 ab.2 c)
    (fun ab => hrrow ab.1 ab.2)
  have hpair (a b) : mass μ (fun x => (p x,q' x)) (a,b)=v a b := by
    rw [mass_triple_first_third μ p q q' hp hq hq']
    simpa only [hqq'] using hrcol a b
  have hprod (a b) : ((μ.map p).prod (μ.map q)).real {(a,b)}=v a b := by
    rw [←singleton_prod_singleton,Measure.real,Measure.prod_prod,ENNReal.toReal_mul]
    rw [←Measure.real,←Measure.real,map_measureReal_apply hp (measurableSet_singleton a),
      map_measureReal_apply hq (measurableSet_singleton b)]
    rfl
  have hmap : μ.map (fun x => (p x,q' x))=(μ.map p).prod (μ.map q) := by
    apply Measure.ext_of_singleton
    rintro ⟨a,b⟩
    apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp
    rw [←Measure.real,map_measureReal_apply (hp.prodMk hq') (measurableSet_singleton (a,b))]
    exact (hpair a b).trans (hprod a b).symm
  have hmarg : μ.map q'=μ.map q := by
    apply Measure.ext_of_singleton
    intro b
    apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp
    rw [←Measure.real,←Measure.real,map_measureReal_apply hq' (measurableSet_singleton b),
      map_measureReal_apply hq (measurableSet_singleton b)]
    change mass μ q' b=mass μ q b
    rw [mass_joint_col μ p q' hp hq']
    simp_rw [hpair]
    dsimp only [v]
    rw [←Finset.sum_mul,mass_sum μ p hp]
    simp
  refine ⟨q',hq',hmarg,hmap,?_⟩
  rw [repaint_error_eq_sum μ q q' hq hq']
  simp_rw [mass_triple_second_third μ p q q' hp hq hq',hqq',Finset.sum_mul]
  have herr : (∑ a,∑ b,∑ c,r a b c*(if b=c then (0 : ℝ) else 1))≤ε := by
    simp_rw [hrerr]
    have hh := positive_mass_difference_le (μ.map (fun x => (p x,q x)))
      ((μ.map p).prod (μ.map q)) hclose
    rw [Fintype.sum_prod_type] at hh
    have hu' (a b) : (μ.map (fun x => (p x,q x))).real {(a,b)}=u a b :=
      map_measureReal_apply (hp.prodMk hq) (measurableSet_singleton (a,b))
    simpa only [hu',hprod] using hh
  calc
    _=(∑ b,∑ a,∑ c,r a b c*(if b=c then (0 : ℝ) else 1)) := by
      apply Finset.sum_congr rfl
      intro b _
      rw [Finset.sum_comm]
    _=(∑ a,∑ b,∑ c,r a b c*(if b=c then (0 : ℝ) else 1)) := Finset.sum_comm
    _≤ε := herr

end HyperbolicCoding

end
section
namespace HyperbolicCoding
open MeasureTheory Set StandardMapEntropy.Entropy
open scoped ENNReal BigOperators
variable {X A B C D : Type*} [MeasurableSpace X]
    [Fintype A] [Fintype B] [Fintype C] [Fintype D]

lemma symbolCost_self {E : Type*} (a : E) : symbolCost a a=0 := by simp [symbolCost]
lemma symbolCost_triangle {E : Type*} (a b c : E) : symbolCost a c≤ symbolCost a b+symbolCost b c := by
  classical
  by_cases h1 : a=b <;> by_cases h2 : b=c <;> by_cases h3 : a=c <;> simp_all [symbolCost]

namespace MatrixCoupling
variable {p : A → ℝ} {q : B → ℝ}

lemma reindex_cost (r : MatrixCoupling p q) (e : C ≃ A) (f : D ≃ B) (d : A → B → ℝ) :
    (r.reindex e f).cost (fun a b => d (e a) (f b))=r.cost d := by
  change (∑ a,∑ b,r.weight (e a) (f b)*d (e a) (f b))=∑ a,∑ b,r.weight a b*d a b
  have hf (a : C) := f.sum_comp (fun b => r.weight (e a) b*d (e a) b)
  simp_rw [hf]
  exact e.sum_comp (fun a => ∑ b,r.weight a b*d a b)

end MatrixCoupling

lemma nameCost_self {E : Type*} {n : ℕ} (a : Fin n → E) : nameCost a a=0 := by
  simp [nameCost,symbolCost_self]
lemma nameCost_triangle {E : Type*} {n : ℕ} (a b c : Fin n → E) :
    nameCost a c≤nameCost a b+nameCost b c := by
  simp only [nameCost,←Finset.sum_add_distrib]
  exact Finset.sum_le_sum (fun i _ => symbolCost_triangle _ _ _)

section Copy
variable [StandardBorelSpace X] [MeasurableSpace A] [MeasurableSingletonClass A]
    [MeasurableSpace B] [MeasurableSingletonClass B] [Nonempty B]
variable (μ : Measure X) [IsProbabilityMeasure μ] [NullSingletonClass μ]

theorem coupling_step (p : X → A) (q : X → B) (hp : Measurable p) (hq : Measurable q)
    (t : A → ℝ) (r : MatrixCoupling (mass μ p) t)
    (d : A → A → ℝ) (hdiag : ∀ a,d a a=0) (htri : ∀ a b c,d a c≤d a b+d b c)
    {ε : ℝ}
    (hclose : LawClose (μ.map (fun x => (p x,q x))) ((μ.map p).prod (μ.map q)) ε) :
    ∃ s : MatrixCoupling (mass μ (fun x => (q x,p x)))
      (fun ba : B×A => mass μ q ba.1*t ba.2),
      s.cost (fun ba bb => symbolCost ba.1 bb.1+d ba.2 bb.2)≤ε+r.cost d := by
  classical
  obtain ⟨q',hq',_hm,hjoint,herr⟩ := copy_independent_of_finite_past μ p q hp hq hclose
  have hmass (b : B) (a : A) : mass μ (fun x => (q' x,p x)) (b,a)=mass μ q b*mass μ p a := by
    have hh := congrArg (fun M : Measure (A×B) => M.real {(a,b)}) hjoint
    rw [map_measureReal_apply (hp.prodMk hq') (measurableSet_singleton (a,b))] at hh
    have hprod : ((μ.map p).prod (μ.map q)).real {(a,b)}=mass μ p a*mass μ q b := by
      rw [←singleton_prod_singleton,Measure.real,Measure.prod_prod,ENNReal.toReal_mul]
      rw [←Measure.real,←Measure.real,map_measureReal_apply hp (measurableSet_singleton a),
        map_measureReal_apply hq (measurableSet_singleton b)]
      rfl
    rw [hprod] at hh
    have he : mass μ (fun x => (q' x,p x)) (b,a)=mass μ (fun x => (p x,q' x)) (a,b) := by
      unfold mass
      congr 2
      ext x
      simp only [mem_preimage,mem_singleton_iff,Prod.mk.injEq,and_comm]
    exact he.trans (hh.trans (mul_comm _ _))
  let R := MatrixCoupling.observations μ (fun x => (q x,p x)) (fun x => (q' x,p x))
    (hq.prodMk hp) (hq'.prodMk hp)
  let R' : MatrixCoupling (mass μ (fun x => (q x,p x)))
      (fun ba : B×A => mass μ q ba.1*mass μ p ba.2) := {
    weight := R.weight
    nonneg := R.nonneg
    row := R.row
    col := fun ba => (R.col ba).trans (hmass ba.1 ba.2) }
  let S := (MatrixCoupling.diagonal (mass μ q) (mass_nonneg μ q)).product r
  let cost : (B×A) → (B×A) → ℝ := fun ba bb => symbolCost ba.1 bb.1+d ba.2 bb.2
  have hR : R'.cost cost≤ε := by
    change R.cost cost≤ε
    rw [MatrixCoupling.observations_cost]
    change (∫ x,symbolCost (q x) (q' x)+d (p x) (p x) ∂μ)≤ε
    simp only [hdiag,add_zero]
    have he : (∫ x,symbolCost (q x) (q' x) ∂μ)=μ.real {x | q x≠q' x} := by
      rw [←sum_mass_mul_integral μ (fun x => (q x,q' x)) (hq.prodMk hq')
        (fun ab => symbolCost ab.1 ab.2),Fintype.sum_prod_type]
      exact (repaint_error_eq_sum μ q q' hq hq').symm
    rwa [he]
  have hS : S.cost cost=r.cost d := by
    rw [MatrixCoupling.product_cost]
    · rw [MatrixCoupling.diagonal_cost _ _ symbolCost symbolCost_self,zero_add]
    · simp only [mass_sum μ q hq,measure_univ,ENNReal.toReal_one]
    · simp only [mass_sum μ p hp,measure_univ,ENNReal.toReal_one]
  refine ⟨R'.comp S,?_⟩
  have h := MatrixCoupling.comp_cost_le R' S cost cost cost (fun a b c => by
    dsimp [cost]
    have h1 := symbolCost_triangle a.1 b.1 c.1
    have h2 := htri a.2 b.2 c.2
    linarith)
  exact h.trans (by rw [hS]; linarith)

end Copy
end HyperbolicCoding

end
end

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_Coupling_SequentialChunkCoupling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace HyperbolicCoding
open MeasureTheory Set StandardMapEntropy.Entropy
open scoped ENNReal BigOperators
variable {X A : Type*} [MeasurableSpace X] [StandardBorelSpace X]
    [MeasurableSpace A] [Fintype A] [MeasurableSingletonClass A] [Nonempty A]
variable (μ : Measure X) [IsProbabilityMeasure μ] [NullSingletonClass μ]

omit [StandardBorelSpace X] [Fintype A] [MeasurableSingletonClass A] [Nonempty A] in
lemma finiteName_measurable (q : ℕ → X → A) (hq : ∀ i,Measurable (q i)) (i n : ℕ) :
    Measurable (finiteName q i n) := Measurable.of_eval (fun index => hq (i+index))

omit [MeasurableSpace X] [StandardBorelSpace X] [MeasurableSpace A] [Fintype A]
  [MeasurableSingletonClass A] [Nonempty A] in
lemma finiteName_cons (q : ℕ → X → A) (i n : ℕ) (x : X) :
    finiteName q i (n+1) x=Fin.cons (q i x) (finiteName q (i+1) n x) := by
  funext j
  refine Fin.cases ?_ (fun j => ?_) j
  · simp [finiteName]
  · simp [finiteName,Nat.add_comm,Nat.add_left_comm]

omit [StandardBorelSpace X] [MeasurableSpace A] [Fintype A] [MeasurableSingletonClass A]
  [Nonempty A] [IsProbabilityMeasure μ] [NullSingletonClass μ] in
lemma independentNameWeights_cons (q : ℕ → X → A) (i n : ℕ) (w : Fin (n+1) → A) :
    independentNameWeights μ q i (n+1) w=
      mass μ (q i) (w 0)*independentNameWeights μ q (i+1) n (Fin.tail w) := by
  rw [independentNameWeights,Fin.prod_univ_succ]
  simp only [Fin.val_zero,Nat.add_zero,Fin.val_succ,Fin.tail,independentNameWeights]
  congr 2
  funext j
  congr 2
  omega

omit [StandardBorelSpace X] [IsProbabilityMeasure μ] [NullSingletonClass μ] in
lemma mass_equiv_inverse {B C : Type*} [MeasurableSpace B] [Fintype B] [MeasurableSingletonClass B]
    [MeasurableSpace C] [Fintype C] [MeasurableSingletonClass C]
    (p : X → B) (e : B ≃ C) (c : C) : mass μ (e ∘ p) c=mass μ p (e.symm c) := by
  unfold mass
  congr 2
  ext x
  simp only [mem_preimage,mem_singleton_iff,Function.comp_apply,←Equiv.eq_symm_apply]

omit [MeasurableSpace A] [Fintype A] [MeasurableSingletonClass A] [Nonempty A] in
lemma nameCost_split {n : ℕ} (v w : Fin (n+1) → A) :
    nameCost v w=symbolCost (v 0) (w 0)+nameCost (Fin.tail v) (Fin.tail w) := by
  rw [nameCost,Fin.sum_univ_succ]
  rfl

theorem sequential_chunk_coupling (q : ℕ → X → A) (hq : ∀ i,Measurable (q i))
    {ε : ℝ}
    (hremote : ∀ i n : ℕ,LawClose
      (μ.map (fun x => (finiteName q (i+1) n x,q i x)))
      ((μ.map (finiteName q (i+1) n)).prod (μ.map (q i))) ε) :
    ∀ i n : ℕ,∃ r : MatrixCoupling (mass μ (finiteName q i n)) (independentNameWeights μ q i n),
      r.cost nameCost≤(n : ℝ)*ε := by
  intro i n
  induction n generalizing i with
  | zero =>
    have hm (w : Fin 0 → A) : mass μ (finiteName q i 0) w=1 := by
      have he : (finiteName q i 0) ⁻¹' {w}=univ := by
        ext x
        simp only [mem_preimage,mem_singleton_iff,mem_univ,iff_true]
        funext j
        exact j.elim0
      simp [mass,he]
    let r : MatrixCoupling (mass μ (finiteName q i 0)) (independentNameWeights μ q i 0) := {
      weight := fun _ _ => 1
      nonneg := fun _ _ => zero_le_one
      row := fun w => by simp [hm]
      col := fun w => by simp [independentNameWeights] }
    refine ⟨r,?_⟩
    simp [MatrixCoupling.cost,nameCost]
  | succ n ih =>
    obtain ⟨r,hr⟩ := ih (i+1)
    obtain ⟨s,hs⟩ := coupling_step μ (finiteName q (i+1) n) (q i)
      (finiteName_measurable q hq (i+1) n) (hq i)
      (independentNameWeights μ q (i+1) n) r nameCost nameCost_self nameCost_triangle (hremote i n)
    let e : (A×(Fin n → A)) ≃ (Fin (n+1) → A) := Fin.consEquiv (fun _ => A)
    let t := s.reindex e.symm e.symm
    have hm (w : Fin (n+1) → A) :
        mass μ (fun x => (q i x,finiteName q (i+1) n x)) (e.symm w)=mass μ (finiteName q i (n+1)) w := by
      rw [←mass_equiv_inverse μ _ e w]
      congr 1
      funext x
      exact (finiteName_cons q i n x).symm
    have hw (w : Fin (n+1) → A) :
        mass μ (q i) (e.symm w).1*independentNameWeights μ q (i+1) n (e.symm w).2=
          independentNameWeights μ q i (n+1) w := (independentNameWeights_cons μ q i n w).symm
    let R : MatrixCoupling (mass μ (finiteName q i (n+1))) (independentNameWeights μ q i (n+1)) := {
      weight := t.weight
      nonneg := t.nonneg
      row := fun w => (t.row w).trans (hm w)
      col := fun w => (t.col w).trans (hw w) }
    have hcost : R.cost nameCost=s.cost (fun a b => symbolCost a.1 b.1+nameCost a.2 b.2) := by
      change t.cost nameCost=_
      have he : (nameCost : (Fin (n+1) → A) → (Fin (n+1) → A) → ℝ)=
          (fun v w => symbolCost (e.symm v).1 (e.symm w).1+nameCost (e.symm v).2 (e.symm w).2) := by
        funext v w
        exact nameCost_split v w
      rw [he]
      exact MatrixCoupling.reindex_cost s e.symm e.symm
        (fun a b : A×(Fin n → A) => symbolCost a.1 b.1+nameCost a.2 b.2)
    refine ⟨R,?_⟩
    rw [hcost]
    calc
      _≤ε+r.cost nameCost := hs
      _≤ε+(n : ℝ)*ε := by linarith
      _=((n+1 : ℕ) : ℝ)*ε := by push_cast; ring

end HyperbolicCoding

end
section
namespace HyperbolicCoding
open MeasureTheory Set
open scoped ENNReal
variable {X A B C : Type*} [MeasurableSpace X] [MeasurableSpace A]
    [MeasurableSpace B] [MeasurableSpace C]
variable (μ : Measure X) [IsProbabilityMeasure μ]

lemma LawClose.nonneg {ν η : Measure X} {ε : ℝ} (h : LawClose ν η ε) : 0≤ε := by
  simpa using h ∅ MeasurableSet.empty

lemma lawClose_pair_factor_left (p : X → A) (q : X → B) (c : A → C)
    (hp : Measurable p) (hq : Measurable q) (hc : Measurable c) {ε : ℝ}
    (h : LawClose (μ.map (fun x => (p x,q x))) ((μ.map p).prod (μ.map q)) ε) :
    LawClose (μ.map (fun x => (c (p x),q x))) ((μ.map (c ∘ p)).prod (μ.map q)) ε := by
  have : IsProbabilityMeasure (μ.map p) := by first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | (apply Measurable.aemeasurable; measurability) | measurability)
  have : IsProbabilityMeasure (μ.map q) := by first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | (apply Measurable.aemeasurable; measurability) | measurability)
  have hh := h.map (hc.prodMap measurable_id)
  rw [Measure.map_map (hc.prodMap measurable_id) (hp.prodMk hq)] at hh
  rw [←Measure.map_prod_map _ _ hc measurable_id,Measure.map_map hc hp,Measure.map_id] at hh
  exact hh

lemma lawClose_pair_swap (p : X → A) (q : X → B)
    (hp : Measurable p) (hq : Measurable q) {ε : ℝ}
    (h : LawClose (μ.map (fun x => (p x,q x))) ((μ.map p).prod (μ.map q)) ε) :
    LawClose (μ.map (fun x => (q x,p x))) ((μ.map q).prod (μ.map p)) ε := by
  have hh := h.map measurable_swap
  rw [Measure.map_map measurable_swap (hp.prodMk hq),Measure.prod_swap] at hh
  exact hh

omit [IsProbabilityMeasure μ] in
lemma map_observation_comp (T : X → X) (hT : MeasurePreserving T μ μ)
    (p : X → A) (hp : Measurable p) : μ.map (p ∘ T)=μ.map p := by
  rw [←Measure.map_map hp hT.measurable,hT.map_eq]

omit [IsProbabilityMeasure μ] in
lemma lawClose_pair_comp (T : X → X) (hT : MeasurePreserving T μ μ)
    (p : X → A) (q : X → B) (hp : Measurable p) (hq : Measurable q) {ε : ℝ}
    (h : LawClose (μ.map (fun x => (p x,q x))) ((μ.map p).prod (μ.map q)) ε) :
    LawClose (μ.map (fun x => (p (T x),q (T x))))
      ((μ.map (p ∘ T)).prod (μ.map (q ∘ T))) ε := by
  rw [map_observation_comp μ T hT p hp,map_observation_comp μ T hT q hq]
  have he : (fun x => (p (T x),q (T x)))=(fun x => (p x,q x)) ∘ T := rfl
  rw [he,map_observation_comp μ T hT _ (hp.prodMk hq)]
  exact h

end HyperbolicCoding

end
section
namespace HyperbolicCoding
open MeasureTheory Set StandardMapEntropy.Entropy
open scoped ENNReal BigOperators
variable {X A : Type*} [MeasurableSpace X] [StandardBorelSpace X]
    [MeasurableSpace A] [Fintype A] [MeasurableSingletonClass A] [Nonempty A]
variable (μ : Measure X) [IsProbabilityMeasure μ] [NullSingletonClass μ]

omit [StandardBorelSpace X] [Fintype A] [MeasurableSingletonClass A] [Nonempty A] in
lemma chunkObservation_measurable (f : X → X) (p : X → A)
    (hf : Measurable f) (hp : Measurable p) (k g i : ℕ) :
    Measurable (chunkObservation f p k g i) :=
  (word_measurable f hf p hp k).comp (hf.iterate _)

omit [MeasurableSpace X] [StandardBorelSpace X] [MeasurableSpace A] [Fintype A]
  [MeasurableSingletonClass A] [Nonempty A] in
lemma selectChunks_word (f : X → X) (p : X → A) (k g n : ℕ) (x : X) :
    selectChunks k g n (word f p (n*(k+g)) x)=
      finiteName (chunkObservation f p k g) 0 n x := by
  funext j r
  change p (f^[j.val*(k+g)+r.val] x)=p (f^[r.val] (f^[(0+j.val)*(k+g)] x))
  rw [←Function.iterate_add_apply]
  congr 2
  simp only [Nat.zero_add]
  omega

omit [MeasurableSpace X] [StandardBorelSpace X] [MeasurableSpace A] [Fintype A]
  [MeasurableSingletonClass A] [Nonempty A] in
lemma chunkName_translate (f : X → X) (p : X → A) (k g i n : ℕ) (x : X) :
    finiteName (chunkObservation f p k g) 0 n (f^[i*(k+g)] x)=
      finiteName (chunkObservation f p k g) i n x := by
  funext j r
  change p (f^[r.val] (f^[(0+j.val)*(k+g)] (f^[i*(k+g)] x)))=
    p (f^[r.val] (f^[(i+j.val)*(k+g)] x))
  simp only [←Function.iterate_add_apply]
  congr 2
  ring

theorem stationary_chunk_coupling (f : X → X) (hf : MeasurePreserving f μ μ)
    (p : X → A) (hp : Measurable p) (k g : ℕ) {ε : ℝ}
    (hremote : ∀ M : ℕ,LawClose
      (μ.map (fun x => (word f p M (f^[k+g] x),word f p k x)))
      ((μ.map (fun x => word f p M (f^[k+g] x))).prod (μ.map (word f p k))) ε) :
    ∀ n : ℕ,∃ r : MatrixCoupling (mass μ (finiteName (chunkObservation f p k g) 0 n))
      (fun w : Fin n → Fin k → A => ∏ j,mass μ (word f p k) (w j)),
      r.cost nameCost≤(n : ℝ)*ε := by
  have hq := chunkObservation_measurable f p hf.measurable hp k g
  have hc : ∀ i n : ℕ,LawClose
      (μ.map (fun x => (finiteName (chunkObservation f p k g) (i+1) n x,
        chunkObservation f p k g i x)))
      ((μ.map (finiteName (chunkObservation f p k g) (i+1) n)).prod
        (μ.map (chunkObservation f p k g i))) ε := by
    intro i n
    have hs : Measurable (selectChunks (A:=A) k g n) :=
      Measurable.of_eval (fun _ => Measurable.of_eval (fun _ => measurable_pi_apply _))
    have h := lawClose_pair_factor_left μ _ _ (selectChunks k g n)
      ((word_measurable f hf.measurable p hp _).comp (hf.measurable.iterate _))
      (word_measurable f hf.measurable p hp k) hs (hremote (n*(k+g)))
    have hh := lawClose_pair_comp μ (f^[i*(k+g)]) (hf.iterate _) _ _
      (hs.comp ((word_measurable f hf.measurable p hp _).comp (hf.measurable.iterate _)))
      (word_measurable f hf.measurable p hp k) h
    have he (x : X) : selectChunks k g n
        (word f p (n*(k+g)) (f^[k+g] (f^[i*(k+g)] x)))=
          finiteName (chunkObservation f p k g) (i+1) n x := by
      rw [selectChunks_word,←Function.iterate_add_apply]
      rw [show k+g+i*(k+g)=(i+1)*(k+g) by ring]
      exact chunkName_translate f p k g (i+1) n x
    simp only [Function.comp_def,he] at hh
    exact hh
  intro n
  obtain ⟨r,hr⟩ := sequential_chunk_coupling μ _ hq hc 0 n
  have hw (w : Fin n → Fin k → A) :
      independentNameWeights μ (chunkObservation f p k g) 0 n w=
        ∏ j,mass μ (word f p k) (w j) := by
    apply Finset.prod_congr rfl
    intro j _
    have hh := congrArg (fun ν : Measure (Fin k → A) => ν.real {w j})
      (map_observation_comp μ _ (hf.iterate ((0+j.val)*(k+g)))
        (word f p k) (word_measurable f hf.measurable p hp k))
    rw [map_measureReal_apply ((word_measurable f hf.measurable p hp k).comp
      (hf.measurable.iterate _)) (measurableSet_singleton _),
      map_measureReal_apply (word_measurable f hf.measurable p hp k) (measurableSet_singleton _)] at hh
    exact hh
  let R : MatrixCoupling (mass μ (finiteName (chunkObservation f p k g) 0 n))
      (fun w : Fin n → Fin k → A => ∏ j,mass μ (word f p k) (w j)) := {
    weight := r.weight
    nonneg := r.nonneg
    row := r.row
    col := fun w => (r.col w).trans (hw w) }
  exact ⟨R,hr⟩

end HyperbolicCoding

end
section
namespace HyperbolicCoding
open scoped BigOperators
variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq B]

lemma productWeights_sum (w : B → A → ℝ) (hw : ∀ b,∑ a,w b a=1) :
    ∑ D,productWeights w D=1 := by
  unfold productWeights
  rw [←Fintype.prod_sum]
  simp only [hw,Finset.prod_const_one]

end HyperbolicCoding

end
section
namespace HyperbolicCoding
open scoped BigOperators
variable {A : Type*} [Fintype A]
namespace MatrixCoupling
variable {p q : A → ℝ}

lemma symm_cost (r : MatrixCoupling p q) (d : A → A → ℝ) (hd : ∀ a b,d a b=d b a) :
    r.symm.cost d=r.cost d := by
  unfold cost symm
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  rw [hd]

theorem exists_power (r : MatrixCoupling p q) (hp : ∑ a,p a=1) :
    ∀ n : ℕ,∃ R : MatrixCoupling (fun w : Fin n → A => ∏ j,p (w j))
      (fun w : Fin n → A => ∏ j,q (w j)),R.cost nameCost=(n : ℝ)*r.cost symbolCost := by
  classical
  intro n
  induction n with
  | zero =>
    let R : MatrixCoupling (fun w : Fin 0 → A => ∏ j,p (w j)) (fun w : Fin 0 → A => ∏ j,q (w j)) := {
      weight := fun _ _ => 1
      nonneg := fun _ _ => zero_le_one
      row := fun _ => by simp
      col := fun _ => by simp }
    refine ⟨R,?_⟩
    simp [cost,nameCost]
  | succ n ih =>
    obtain ⟨R,hR⟩ := ih
    let S := r.product R
    let e : (A×(Fin n → A)) ≃ (Fin (n+1) → A) := Fin.consEquiv (fun _ => A)
    let t := S.reindex e.symm e.symm
    let T : MatrixCoupling (fun w : Fin (n+1) → A => ∏ j,p (w j))
        (fun w : Fin (n+1) → A => ∏ j,q (w j)) := {
      weight := t.weight
      nonneg := t.nonneg
      row := fun w => (t.row w).trans (by exact (Fin.prod_univ_succ (fun j => p (w j))).symm)
      col := fun w => (t.col w).trans (by exact (Fin.prod_univ_succ (fun j => q (w j))).symm) }
    have he : (nameCost : (Fin (n+1) → A) → (Fin (n+1) → A) → ℝ)=
        (fun v w => symbolCost (e.symm v).1 (e.symm w).1+nameCost (e.symm v).2 (e.symm w).2) := by
      funext v w
      rw [nameCost,Fin.sum_univ_succ]
      rfl
    have hmass : (∑ w : Fin n → A,∏ j,p (w j))=1 :=
      productWeights_sum (fun _ : Fin n => p) (fun _ => hp)
    refine ⟨T,?_⟩
    change t.cost nameCost=_
    rw [he,MatrixCoupling.reindex_cost S e.symm e.symm
      (fun a b : A×(Fin n → A) => symbolCost a.1 b.1+nameCost a.2 b.2)]
    rw [MatrixCoupling.product_cost r R hp hmass symbolCost nameCost,hR]
    push_cast
    ring

end MatrixCoupling
end HyperbolicCoding

end
section
namespace HyperbolicCoding
open MeasureTheory Set StandardMapEntropy.Entropy
open scoped ENNReal BigOperators

lemma symbolCost_comm {A : Type*} (a b : A) : symbolCost a b=symbolCost b a := by
  classical
  simp only [symbolCost,eq_comm]
lemma nameCost_comm {A : Type*} {n : ℕ} (a b : Fin n → A) : nameCost a b=nameCost b a := by
  simp only [nameCost,symbolCost_comm]

lemma coupling_of_observation_lawClose {X Y A : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSpace A] [Fintype A] [MeasurableSingletonClass A]
    (μ : Measure X) (ν : Measure Y) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (p : X → A) (q : Y → A) (hp : Measurable p) (hq : Measurable q) {ε : ℝ}
    (h : LawClose (μ.map p) (ν.map q) ε) :
    ∃ R : MatrixCoupling (mass μ p) (mass ν q),R.cost symbolCost≤ε := by
  classical
  have : IsProbabilityMeasure (μ.map p) := by first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | (apply Measurable.aemeasurable; measurability) | measurability)
  have : IsProbabilityMeasure (ν.map q) := by first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | (apply Measurable.aemeasurable; measurability) | measurability)
  obtain ⟨r,hr,hrow,hcol,hcost⟩ := finite_coupling_of_lawClose (μ.map p) (ν.map q) h
  let R : MatrixCoupling (mass μ p) (mass ν q) := {
    weight := r
    nonneg := hr
    row := fun a => (hrow a).trans (map_measureReal_apply hp (measurableSet_singleton a))
    col := fun a => (hcol a).trans (map_measureReal_apply hq (measurableSet_singleton a)) }
  exact ⟨R,hcost⟩

theorem chunk_process_transport {X Y A : Type*}
    [MeasurableSpace X] [StandardBorelSpace X] [MeasurableSpace Y] [StandardBorelSpace Y]
    [MeasurableSpace A] [Fintype A] [MeasurableSingletonClass A] [Nonempty A]
    (μ : Measure X) (ν : Measure Y) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    [NullSingletonClass μ] [NullSingletonClass ν]
    (f : X → X) (hf : MeasurePreserving f μ μ) (p : X → A) (hp : Measurable p)
    (T : Y → Y) (hT : MeasurePreserving T ν ν) (q : Y → A) (hq : Measurable q)
    (k g : ℕ) {εP εQ δ : ℝ}
    (hP : ∀ M : ℕ,LawClose
      (μ.map (fun x => (word f p M (f^[k+g] x),word f p k x)))
      ((μ.map (fun x => word f p M (f^[k+g] x))).prod (μ.map (word f p k))) εP)
    (hQ : ∀ M : ℕ,LawClose
      (ν.map (fun x => (word T q M (T^[k+g] x),word T q k x)))
      ((ν.map (fun x => word T q M (T^[k+g] x))).prod (ν.map (word T q k))) εQ)
    (hlaw : LawClose (μ.map (word f p k)) (ν.map (word T q k)) δ) :
    ∀ n : ℕ,∃ R : MatrixCoupling (mass μ (finiteName (chunkObservation f p k g) 0 n))
      (mass ν (finiteName (chunkObservation T q k g) 0 n)),
      R.cost nameCost≤(n : ℝ)*(εP+δ+εQ) := by
  intro n
  obtain ⟨RP,hRP⟩ := stationary_chunk_coupling μ f hf p hp k g hP n
  obtain ⟨RQ,hRQ⟩ := stationary_chunk_coupling ν T hT q hq k g hQ n
  obtain ⟨r,hr⟩ := coupling_of_observation_lawClose μ ν (word f p k) (word T q k)
    (word_measurable f hf.measurable p hp k) (word_measurable T hT.measurable q hq k) hlaw
  obtain ⟨S,hS⟩ := r.exists_power (by
    simp only [mass_sum μ (word f p k) (word_measurable f hf.measurable p hp k),
      measure_univ,ENNReal.toReal_one]) n
  refine ⟨(RP.comp S).comp RQ.symm,?_⟩
  have h1 := MatrixCoupling.comp_cost_le RP S nameCost nameCost nameCost nameCost_triangle
  have h2 := MatrixCoupling.comp_cost_le (RP.comp S) RQ.symm nameCost nameCost nameCost nameCost_triangle
  rw [MatrixCoupling.symm_cost RQ nameCost nameCost_comm] at h2
  rw [hS] at h1
  have h3 := mul_le_mul_of_nonneg_left hr (Nat.cast_nonneg n)
  nlinarith

end HyperbolicCoding

end
end

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_Coupling_ChunkNameCost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace HyperbolicCoding
open scoped BigOperators
lemma symbolCost_le_one {A : Type*} (a b : A) : symbolCost a b≤1 := by
  unfold symbolCost
  split <;> norm_num
lemma nameCost_le_card {A : Type*} {n : ℕ} (v w : Fin n → A) : nameCost v w≤(n : ℝ) := by
  calc
    _≤∑ _i : Fin n,(1 : ℝ) := Finset.sum_le_sum (fun i _ => symbolCost_le_one _ _)
    _=_ := by simp
lemma nameCost_le_chunkCost {A : Type*} {n : ℕ} (v w : Fin n → A) :
    nameCost v w≤(n : ℝ)*symbolCost v w := by
  classical
  by_cases h : v=w
  · subst w; simp only [nameCost_self,symbolCost_self,mul_zero,le_refl]
  · simpa only [symbolCost,ite_eq_right h,mul_one] using nameCost_le_card v w

theorem nameCost_le_retained_chunks {A : Type*} (k g n : ℕ)
    (v w : Fin (n*(k+g)) → A) :
    nameCost v w≤(k : ℝ)*nameCost (selectChunks k g n v) (selectChunks k g n w)+(n*g : ℕ) := by
  have he : nameCost v w=∑ j : Fin n,∑ r : Fin (k+g),
      symbolCost (v (finProdFinEquiv (j,r))) (w (finProdFinEquiv (j,r))) := by
    rw [nameCost,←Equiv.sum_comp finProdFinEquiv (fun i => symbolCost (v i) (w i)),Fintype.sum_prod_type]
  rw [he]
  have hb (j : Fin n) : (∑ r : Fin (k+g),
      symbolCost (v (finProdFinEquiv (j,r))) (w (finProdFinEquiv (j,r))))≤
      (k : ℝ)*symbolCost (selectChunks k g n v j) (selectChunks k g n w j)+(g : ℝ) := by
    rw [Fin.sum_univ_add]
    have hp : (∑ r : Fin k,symbolCost (v (finProdFinEquiv (j,Fin.castAdd g r)))
        (w (finProdFinEquiv (j,Fin.castAdd g r))))=
        nameCost (selectChunks k g n v j) (selectChunks k g n w j) := by
      apply Finset.sum_congr rfl
      intro r _
      unfold selectChunks
      congr 2 <;> apply Fin.ext <;> dsimp [finProdFinEquiv] <;> ring
    have hg : (∑ r : Fin g,symbolCost (v (finProdFinEquiv (j,Fin.natAdd k r)))
        (w (finProdFinEquiv (j,Fin.natAdd k r))))≤(g : ℝ) := by
      calc
        _≤∑ _r : Fin g,(1 : ℝ) := Finset.sum_le_sum (fun r _ => symbolCost_le_one _ _)
        _=_ := by simp
    rw [hp]
    have hc := nameCost_le_chunkCost (selectChunks k g n v j) (selectChunks k g n w j)
    linarith
  calc
    _≤∑ j : Fin n,((k : ℝ)*symbolCost (selectChunks k g n v j) (selectChunks k g n w j)+(g : ℝ)) :=
      Finset.sum_le_sum (fun j _ => hb j)
    _=_ := by
      simp only [Finset.sum_add_distrib,←Finset.mul_sum,Finset.sum_const,Finset.card_univ,
        Fintype.card_fin,nsmul_eq_mul,nameCost]
      norm_cast

end HyperbolicCoding

end
section
namespace HyperbolicCoding
open MeasureTheory Set StandardMapEntropy.Entropy
open scoped BigOperators ENNReal
namespace MatrixCoupling
variable {A B : Type*} [Fintype A] [Fintype B] {p : A → ℝ} {q : B → ℝ}
lemma cost_mono (r : MatrixCoupling p q) (d e : A → B → ℝ) (h : ∀ a b,d a b≤e a b) :
    r.cost d ≤ r.cost e :=
  Finset.sum_le_sum (fun a _ => Finset.sum_le_sum (fun b _ =>
    mul_le_mul_of_nonneg_left (h a b) (r.nonneg a b)))
lemma cost_affine (r : MatrixCoupling p q) (hp : ∑ a,p a=1) (K C : ℝ) (d : A → B → ℝ) :
    r.cost (fun a b => K*d a b+C)=K*r.cost d+C := by
  unfold cost
  simp only [mul_add,Finset.sum_add_distrib]
  congr 1
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b _
    ring
  · simp only [←Finset.sum_mul,r.row,hp,one_mul]
end MatrixCoupling

variable {X Y A B : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSpace A] [Fintype A] [MeasurableSingletonClass A]
    [MeasurableSpace B] [Fintype B] [MeasurableSingletonClass B]

theorem lift_observation_transport (μ : Measure X) (ν : Measure Y)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (p : X → A) (q : Y → A) (hp : Measurable p) (hq : Measurable q)
    (c : A → B) (S : MatrixCoupling (mass μ (c ∘ p)) (mass ν (c ∘ q)))
    (d : B → B → ℝ) (hdiag : ∀ b,d b b=0) (htri : ∀ a b c,d a c≤d a b+d b c) :
    ∃ R : MatrixCoupling (mass μ p) (mass ν q),R.cost (fun a b => d (c a) (c b))≤S.cost d := by
  have hc : Measurable c := measurable_of_countable c
  let P := MatrixCoupling.observations μ p (c ∘ p) hp (hc.comp hp)
  let Q := MatrixCoupling.observations ν (c ∘ q) q (hc.comp hq) hq
  have hP : P.cost (fun a b => d (c a) b)=0 := by
    rw [MatrixCoupling.observations_cost]
    simp only [Function.comp_apply,hdiag,integral_zero]
  have hQ : Q.cost (fun a b => d a (c b))=0 := by
    rw [MatrixCoupling.observations_cost]
    simp only [Function.comp_apply,hdiag,integral_zero]
  refine ⟨(P.comp S).comp Q,?_⟩
  have h1 := MatrixCoupling.comp_cost_le P S (fun a b => d (c a) b) d
    (fun a b => d (c a) b) (fun a b v => htri (c a) b v)
  have h2 := MatrixCoupling.comp_cost_le (P.comp S) Q (fun a b => d (c a) b)
    (fun a b => d a (c b)) (fun a b => d (c a) (c b)) (fun a b v => htri (c a) b (c v))
  rw [hP,zero_add] at h1
  rw [hQ,add_zero] at h2
  exact h2.trans h1

end HyperbolicCoding

end
section
namespace HyperbolicCoding
open MeasureTheory Set StandardMapEntropy.Entropy
open scoped ENNReal BigOperators

theorem full_word_transport {X Y A : Type*}
    [MeasurableSpace X] [StandardBorelSpace X] [MeasurableSpace Y] [StandardBorelSpace Y]
    [MeasurableSpace A] [Fintype A] [MeasurableSingletonClass A] [Nonempty A]
    (μ : Measure X) (ν : Measure Y) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    [NullSingletonClass μ] [NullSingletonClass ν]
    (f : X → X) (hf : MeasurePreserving f μ μ) (p : X → A) (hp : Measurable p)
    (T : Y → Y) (hT : MeasurePreserving T ν ν) (q : Y → A) (hq : Measurable q)
    (k g : ℕ) {εP εQ δ : ℝ}
    (hP : ∀ M : ℕ,LawClose
      (μ.map (fun x => (word f p M (f^[k+g] x),word f p k x)))
      ((μ.map (fun x => word f p M (f^[k+g] x))).prod (μ.map (word f p k))) εP)
    (hQ : ∀ M : ℕ,LawClose
      (ν.map (fun x => (word T q M (T^[k+g] x),word T q k x)))
      ((ν.map (fun x => word T q M (T^[k+g] x))).prod (ν.map (word T q k))) εQ)
    (hlaw : LawClose (μ.map (word f p k)) (ν.map (word T q k)) δ) :
    ∀ n : ℕ,∃ R : MatrixCoupling (mass μ (word f p (n*(k+g))))
      (mass ν (word T q (n*(k+g)))),
      R.cost nameCost≤(n : ℝ)*((k : ℝ)*(εP+δ+εQ)+(g : ℝ)) := by
  intro n
  obtain ⟨S,hS⟩ := chunk_process_transport μ ν f hf p hp T hT q hq k g hP hQ hlaw n
  have hPsel : selectChunks k g n ∘ word f p (n*(k+g))=
      finiteName (chunkObservation f p k g) 0 n := funext (selectChunks_word f p k g n)
  have hQsel : selectChunks k g n ∘ word T q (n*(k+g))=
      finiteName (chunkObservation T q k g) 0 n := funext (selectChunks_word T q k g n)
  let S' : MatrixCoupling (mass μ (selectChunks k g n ∘ word f p (n*(k+g))))
      (mass ν (selectChunks k g n ∘ word T q (n*(k+g)))) := {
    weight := S.weight
    nonneg := S.nonneg
    row := fun w => by rw [hPsel]; exact S.row w
    col := fun w => by rw [hQsel]; exact S.col w }
  obtain ⟨R,hR⟩ := lift_observation_transport μ ν (word f p (n*(k+g))) (word T q (n*(k+g)))
    (word_measurable f hf.measurable p hp _) (word_measurable T hT.measurable q hq _)
    (selectChunks k g n) S' nameCost nameCost_self nameCost_triangle
  refine ⟨R,?_⟩
  have hmass : (∑ v,mass μ (word f p (n*(k+g))) v)=1 := by
    simp only [mass_sum μ _ (word_measurable f hf.measurable p hp _),measure_univ,ENNReal.toReal_one]
  have hbd := R.cost_mono nameCost
    (fun v w => (k : ℝ)*nameCost (selectChunks k g n v) (selectChunks k g n w)+(n*g : ℕ))
    (nameCost_le_retained_chunks k g n)
  rw [R.cost_affine hmass] at hbd
  have hk0 : 0≤(k : ℝ) := Nat.cast_nonneg k
  have h1 := mul_le_mul_of_nonneg_left hR hk0
  have hS' : S'.cost nameCost≤(n : ℝ)*(εP+δ+εQ) := hS
  have h2 := mul_le_mul_of_nonneg_left hS' hk0
  push_cast at hbd
  nlinarith

end HyperbolicCoding

end
section
namespace HyperbolicCoding
open MeasureTheory Set Filter
open scoped ENNReal Topology
variable {X A B C : Type*} [MeasurableSpace X] [MeasurableSpace A]
    [MeasurableSpace B] [MeasurableSpace C]
variable (μ : Measure X) [IsProbabilityMeasure μ]
    (e : X ≃ᵐ X) (he : MeasurePreserving e μ μ) (α : X → A) (hα : Measurable α)

include he hα
lemma finite_remote_lawClose {n : ℕ} {ε : ℝ}
    (h : LawClose (μ.map (remotePair e e.symm α n)) (remoteProductLaw μ e e.symm α) ε)
    (f : (ℕ → A) → B) (g : (ℕ → A) → C) (hf : Measurable f) (hg : Measurable g) :
    LawClose (μ.map (fun x => (f (tailName e.symm α n x),g (tailName e α n x))))
      ((μ.map (fun x => f (tailName e.symm α n x))).prod
        (μ.map (fun x => g (tailName e α n x)))) ε := by
  have hh := h.map (hf.prodMap hg)
  rw [Measure.map_map (hf.prodMap hg) (measurable_remotePair e.measurable e.symm.measurable hα n)] at hh
  have hmf : (μ.map (tailName e.symm α 0)).map f=μ.map (fun x => f (tailName e.symm α n x)) := by
    rw [←stationary_tail_law μ (he.symm e) hα n,Measure.map_map hf
      (measurable_tailName e.symm.measurable hα n)]
    rfl
  have hmg : (μ.map (tailName e α 0)).map g=μ.map (fun x => g (tailName e α n x)) := by
    rw [←stationary_tail_law μ he hα n,Measure.map_map hg
      (measurable_tailName e.measurable hα n)]
    rfl
  unfold remoteProductLaw at hh
  rw [←Measure.map_prod_map _ _ hf hg,hmf,hmg] at hh
  exact hh

end HyperbolicCoding

end
section
namespace HyperbolicCoding
open MeasureTheory Set Filter StandardMapEntropy.Entropy
open scoped ENNReal Topology
variable {X A : Type*} [MeasurableSpace X] [MeasurableSpace A]
    [Fintype A] [MeasurableSingletonClass A]
variable (μ : Measure X) [IsProbabilityMeasure μ]

omit [Fintype A] [MeasurableSingletonClass A] in
theorem weakBernoulli_forward_blocks (e : X ≃ᵐ X) (he : MeasurePreserving e μ μ)
    (α : X → A) (hα : Measurable α) (hwb : WeakBernoulliProcess μ e α)
    {ε : ℝ} (hε : 0<ε) : ∃ g : ℕ,∀ k M : ℕ,LawClose
      (μ.map (fun x => (word e α M (e^[k+g] x),word e α k x)))
      ((μ.map (fun x => word e α M (e^[k+g] x))).prod (μ.map (word e α k))) ε := by
  obtain ⟨N,hN⟩ := (hwb ε hε).exists
  refine ⟨2*N,?_⟩
  intro k M
  let P : (ℕ → A) → (Fin k → A) := fun w i => w (k-i.val)
  let Q : (ℕ → A) → (Fin M → A) := fun w i => w i.val
  have hP : Measurable P := Measurable.of_eval (fun index => measurable_pi_apply (k-index.val))
  have hQ : Measurable Q := Measurable.of_eval (fun index => measurable_pi_apply index.val)
  have hfin := finite_remote_lawClose μ e he α hα hN P Q hP hQ
  have hp : Measurable (fun x => P (tailName e.symm α N x)) :=
    hP.comp (measurable_tailName e.symm.measurable hα N)
  have hq : Measurable (fun x => Q (tailName e α N x)) :=
    hQ.comp (measurable_tailName e.measurable hα N)
  have hcomp := lawClose_pair_comp μ (e^[k+N]) (he.iterate (k+N)) _ _ hp hq hfin
  have hswap := lawClose_pair_swap μ _ _ (hp.comp (he.measurable.iterate (k+N)))
    (hq.comp (he.measurable.iterate (k+N))) hcomp
  have hp' (x : X) : P (tailName e.symm α N (e^[k+N] x))=word e α k x := by
    funext i
    change α (e.symm^[(k-i.val)+N] (e^[k+N] x))=α (e^[i.val] x)
    rw [inverse_iterate_forward_sub e (by omega)]
    congr 2
    omega
  have hq' (x : X) : Q (tailName e α N (e^[k+N] x))=word e α M (e^[k+2*N] x) := by
    funext i
    change α (e^[i.val+N] (e^[k+N] x))=α (e^[i.val] (e^[k+2*N] x))
    rw [←Function.iterate_add_apply,←Function.iterate_add_apply]
    congr 2
    omega
  simpa only [Function.comp_def,hp',hq'] using hswap

end HyperbolicCoding

end
section
namespace StandardMapEntropy.Entropy
open MeasureTheory Set HyperbolicCoding
open scoped ENNReal Topology BigOperators
variable {A X Y : Type*} [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]
    [MeasurableSpace X] [MeasurableSpace Y]

omit [MeasurableSpace A] [MeasurableSingletonClass A] in
lemma continuous_shannon : Continuous (shannon (α:=A)) := by
  unfold shannon
  fun_prop

theorem finite_entropy_continuity (μ : Measure A) {ε : ℝ} (hε : 0<ε) :
    ∃ δ : ℝ,0<δ ∧ ∀ ν : Measure A,LawClose μ ν δ →
      |shannon (fun a => μ.real {a})-shannon (fun a => ν.real {a})|<ε := by
  obtain ⟨η,hη,hcont⟩ := Metric.continuousAt_iff.mp (continuous_shannon (A:=A)).continuousAt ε hε
  refine ⟨η/2,half_pos hη,?_⟩
  intro ν hν
  have hd : dist (fun a => ν.real {a}) (fun a => μ.real {a})<η := by
    apply (dist_pi_lt_iff hη).mpr
    intro a
    rw [Real.dist_eq,abs_sub_comm]
    exact (hν {a} (measurableSet_singleton a)).trans_lt (half_lt_self hη)
  simpa only [Real.dist_eq,abs_sub_comm] using hcont hd

lemma obs_eq_entropy_map (μ : Measure X) (p : X → A) (hp : Measurable p) :
    obs μ p=shannon (fun a => (μ.map p).real {a}) := by
  unfold obs
  congr 1
  funext a
  exact (map_measureReal_apply hp (measurableSet_singleton a)).symm

theorem obs_continuity_in_law (μ : Measure X) (p : X → A) (hp : Measurable p)
    {ε : ℝ} (hε : 0<ε) : ∃ δ : ℝ,0<δ ∧
    ∀ (ν : Measure Y) (q : Y → A),Measurable q → LawClose (μ.map p) (ν.map q) δ →
      |obs μ p-obs ν q|<ε := by
  obtain ⟨δ,hδ,hh⟩ := finite_entropy_continuity (μ.map p) hε
  refine ⟨δ,hδ,?_⟩
  intro ν q hq hclose
  rw [obs_eq_entropy_map μ p hp,obs_eq_entropy_map ν q hq]
  exact hh _ hclose

end StandardMapEntropy.Entropy

end
section
namespace StandardMapEntropy.Entropy
open MeasureTheory Set
open scoped BigOperators ENNReal
variable {X A B C D : Type*} [MeasurableSpace X]
    [MeasurableSpace A] [Fintype A] [MeasurableSingletonClass A]
    [MeasurableSpace B] [Fintype B] [MeasurableSingletonClass B]
    [MeasurableSpace C] [Fintype C] [MeasurableSingletonClass C]
    [MeasurableSpace D] [Fintype D] [MeasurableSingletonClass D]
variable (μ : Measure X) [IsProbabilityMeasure μ]

lemma cond_factor_chain (q : X → B) (r : X → A) (d : B → D)
    (hq : Measurable q) (hr : Measurable r) :
    cond μ q r=cond μ (d ∘ q) r+cond μ q (fun x => (d (q x),r x)) := by
  have hd : Measurable (d ∘ q) := (measurable_of_countable d).comp hq
  have he : cond μ (fun x => (d (q x),q x)) r=cond μ q r := by
    apply le_antisymm
    · exact cond_factor_left μ q r (fun b => (d b,b)) hq hr
    · exact cond_factor_left μ (fun x => (d (q x),q x)) r Prod.snd (hd.prodMk hq) hr
  rw [←he,cond_chain]
  rfl

theorem conditional_defect_data_processing (p : X → A) (q : X → B)
    (c : A → C) (d : B → D) (hp : Measurable p) (hq : Measurable q) :
    cond μ (d ∘ q) (c ∘ p)-cond μ (d ∘ q) p≤
      cond μ q (c ∘ p)-cond μ q p := by
  have hc : Measurable (c ∘ p) := (measurable_of_countable c).comp hp
  have hd : Measurable (d ∘ q) := (measurable_of_countable d).comp hq
  have h1 := cond_factor_chain μ q (c ∘ p) d hq hc
  have h2 := cond_factor_chain μ q p d hq hp
  have h3 := cond_factor_right μ q (fun x => (d (q x),p x))
    (fun v : D×A => (v.1,c v.2)) hq (hd.prodMk hp)
  change cond μ q (fun x => (d (q x),p x))≤
    cond μ q (fun x => (d (q x),c (p x))) at h3
  simp only [Function.comp_def] at h1 h2 ⊢
  linarith

end StandardMapEntropy.Entropy

end
section
namespace HyperbolicCoding
open scoped BigOperators

lemma log_ratio_hellinger_bound {p q : ℝ} (hp : 0≤p) (hq : 0≤q)
    (hs : p≠0 → q≠0) : 2*p-2*Real.sqrt p*Real.sqrt q≤p*(Real.log p-Real.log q) := by
  by_cases hp0 : p=0
  · simp [hp0]
  have hp' : 0<p := lt_of_le_of_ne hp (Ne.symm hp0)
  have hq' : 0<q := lt_of_le_of_ne hq (Ne.symm (hs hp0))
  have ha : 0<Real.sqrt p := Real.sqrt_pos.mpr hp'
  have hb : 0<Real.sqrt q := Real.sqrt_pos.mpr hq'
  have hh := mul_le_mul_of_nonneg_left
    (Real.log_le_sub_one_of_pos (div_pos hb ha)) (mul_nonneg (by norm_num : (0 : ℝ)≤2) hp)
  rw [Real.log_div hb.ne' ha.ne',Real.log_sqrt hq,Real.log_sqrt hp] at hh
  have hr : p*(Real.sqrt q/Real.sqrt p)=Real.sqrt p*Real.sqrt q := by
    calc
      _=(Real.sqrt p*Real.sqrt p)*(Real.sqrt q/Real.sqrt p) :=
        congrArg (fun t : ℝ => t*(Real.sqrt q/Real.sqrt p)) (Real.mul_self_sqrt hp).symm
      _=_ := by field_simp
  have he : 2*p*(Real.sqrt q/Real.sqrt p-1)=2*Real.sqrt p*Real.sqrt q-2*p := by
    calc
      _=2*(p*(Real.sqrt q/Real.sqrt p))-2*p := by ring
      _=_ := by rw [hr]; ring
  rw [he] at hh
  nlinarith

theorem finite_pinsker_sq {A : Type*} [Fintype A] (p q : A → ℝ)
    (hp : ∀ a,0≤p a) (hq : ∀ a,0≤q a)
    (hp1 : ∑ a,p a=1) (hq1 : ∑ a,q a=1) (hs : ∀ a,p a≠0 → q a≠0) :
    (∑ a,|p a-q a|)^2≤4*relativeInformation p q := by
  let u : A → ℝ := fun a => Real.sqrt (p a)-Real.sqrt (q a)
  let v : A → ℝ := fun a => Real.sqrt (p a)+Real.sqrt (q a)
  have hu (a) : (u a)^2=p a+q a-2*Real.sqrt (p a)*Real.sqrt (q a) := by
    dsimp [u]
    nlinarith [Real.sq_sqrt (hp a),Real.sq_sqrt (hq a)]
  have huv (a) : |p a-q a|=|u a| * v a := by
    have he : p a-q a=u a*v a := by
      dsimp [u,v]
      nlinarith [Real.sq_sqrt (hp a),Real.sq_sqrt (hq a)]
    rw [he,abs_mul,abs_of_nonneg (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))]
  have hH : (∑ a,(u a)^2) ≤ relativeInformation p q := by
    have hh := Finset.sum_le_sum (s:=Finset.univ) (fun a _ => log_ratio_hellinger_bound (hp a) (hq a) (hs a))
    have he : (∑ a,(u a)^2)=(∑ a,(2*p a-2*Real.sqrt (p a)*Real.sqrt (q a))) := by
      simp_rw [hu]
      rw [Finset.sum_sub_distrib,Finset.sum_add_distrib,hp1,hq1,Finset.sum_sub_distrib,←Finset.mul_sum,hp1]
      norm_num
    rw [he]
    exact hh
  have hV : (∑ a,(v a)^2)≤4 := by
    have hv (a) : (v a)^2≤2*p a+2*q a := by
      dsimp [v]
      nlinarith [sq_nonneg (u a),hu a,Real.sq_sqrt (hp a),Real.sq_sqrt (hq a)]
    calc
      _≤∑ a,(2*p a+2*q a) := Finset.sum_le_sum (fun a _ => hv a)
      _=4 := by rw [Finset.sum_add_distrib,←Finset.mul_sum,←Finset.mul_sum,hp1,hq1]; norm_num
  have hc := Finset.sum_mul_sq_le_sq_mul_sq (s:=Finset.univ) (fun a => |u a|) v
  simp only [sq_abs] at hc
  simp_rw [huv]
  calc
    _≤(∑ a,(u a)^2)*(∑ a,(v a)^2) := hc
    _≤(∑ a,(u a)^2)*4 := mul_le_mul_of_nonneg_left hV (Finset.sum_nonneg (fun a _ => sq_nonneg (u a)))
    _≤4*relativeInformation p q := by nlinarith [hH]

end HyperbolicCoding

end
end

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_Coupling_ConditionalRefinementInformation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace StandardMapEntropy.Entropy
open MeasureTheory Set HyperbolicCoding
open scoped BigOperators ENNReal
variable {X A B C : Type*} [MeasurableSpace X]
    [MeasurableSpace A] [Fintype A] [MeasurableSingletonClass A]
    [MeasurableSpace B] [Fintype B] [MeasurableSingletonClass B]
    [MeasurableSpace C] [Fintype C] [MeasurableSingletonClass C]
variable (μ : Measure X) [IsProbabilityMeasure μ]

omit [MeasurableSpace A] [Fintype A] [MeasurableSingletonClass A]
  [MeasurableSpace B] [Fintype B] [MeasurableSingletonClass B] in
lemma mass_factor_le (p : X → A) (g : A → B) (a : A) :
    mass μ p a≤ mass μ (g ∘ p) (g a) := by
  unfold mass
  apply ENNReal.toReal_mono (measure_ne_top μ _)
  apply measure_mono
  intro x hx
  exact congrArg g hx

omit [MeasurableSpace A] [Fintype A] [MeasurableSingletonClass A]
  [MeasurableSpace B] [Fintype B] [MeasurableSingletonClass B]
  [MeasurableSpace C] [Fintype C] [MeasurableSingletonClass C] [IsProbabilityMeasure μ] in
lemma refinementCopyWeights_nonneg (p : X → A) (q : X → B) (c : A → C) (a : A) (b : B) :
    0 ≤ refinementCopyWeights μ p q c a b :=
  div_nonneg (mul_nonneg (mass_nonneg _ _ _) (mass_nonneg _ _ _)) (mass_nonneg _ _ _)

omit [Fintype C] in
lemma refinementCopyWeights_row (p : X → A) (q : X → B) (c : A → C)
    (hp : Measurable p) (hq : Measurable q) (a : A) :
    (∑ b,refinementCopyWeights μ p q c a b)=mass μ p a := by
  have hc : Measurable (c ∘ p) := (measurable_of_countable c).comp hp
  by_cases hz : mass μ (c ∘ p) (c a)=0
  · have hp0 : mass μ p a=0 := le_antisymm ((mass_factor_le μ p c a).trans (le_of_eq hz)) (mass_nonneg _ _ _)
    simp only [refinementCopyWeights,hp0,zero_mul,zero_div,Finset.sum_const_zero]
  · have hrow : (∑ b,mass μ (fun x => (c (p x),q x)) (c a,b))=mass μ (c ∘ p) (c a) :=
      (mass_joint_row μ (c ∘ p) q hc hq (c a)).symm
    simp only [refinementCopyWeights,←Finset.sum_div,←Finset.mul_sum,hrow,mul_div_cancel_right₀ _ hz]

omit [MeasurableSpace A] [Fintype A] [MeasurableSingletonClass A]
  [MeasurableSpace B] [Fintype B] [MeasurableSingletonClass B]
  [MeasurableSpace C] [Fintype C] [MeasurableSingletonClass C] in
lemma refinementCopyWeights_support (p : X → A) (q : X → B) (c : A → C) (a : A) (b : B)
    (h : mass μ (fun x => (p x,q x)) (a,b)≠0) : refinementCopyWeights μ p q c a b≠0 := by
  have hu : 0 < mass μ (fun x => (p x,q x)) (a,b) := lt_of_le_of_ne (mass_nonneg _ _ _) (Ne.symm h)
  have hp : 0 < mass μ p a := hu.trans_le (mass_factor_le μ (fun x => (p x,q x)) Prod.fst (a,b))
  have hcb : 0 < mass μ (fun x => (c (p x),q x)) (c a,b) :=
    hu.trans_le (mass_factor_le μ (fun x => (p x,q x)) (fun ab => (c ab.1,ab.2)) (a,b))
  have hc : 0 < mass μ (c ∘ p) (c a) := hp.trans_le (mass_factor_le μ p c a)
  exact ne_of_gt (div_pos (mul_pos hp hcb) hc)

theorem refinement_relativeInformation (p : X → A) (q : X → B) (c : A → C)
    (hp : Measurable p) (hq : Measurable q) :
    relativeInformation (fun ab : A×B => mass μ (fun x => (p x,q x)) ab)
      (fun ab => refinementCopyWeights μ p q c ab.1 ab.2)=
        cond μ q (c ∘ p)-cond μ q p := by
  have hc : Measurable (c ∘ p) := (measurable_of_countable c).comp hp
  let pq : X → A×B := fun x => (p x,q x)
  let cq : X → C×B := fun x => (c (p x),q x)
  have hpq : Measurable pq := hp.prodMk hq
  have hcq : Measurable cq := hc.prodMk hq
  unfold relativeInformation
  rw [sum_mass_mul_integral μ pq hpq]
  have he : (fun x => Real.log (mass μ pq (pq x))-
      Real.log (refinementCopyWeights μ p q c (p x) (q x)))=ᵐ[μ]
      (fun x => -information μ pq x+information μ p x+information μ cq x-information μ (c ∘ p) x) := by
    filter_upwards [ae_mass_positive μ p,ae_mass_positive μ cq,ae_mass_positive μ (c ∘ p)] with x hx hcx hcpx
    dsimp only [refinementCopyWeights,information,pq,cq,Function.comp_apply] at *
    rw [Real.log_div (mul_pos hx hcx).ne' hcpx.ne',Real.log_mul hx.ne' hcx.ne']
    ring
  rw [integral_congr_ae he]
  rw [integral_sub (f:=fun x => -information μ pq x+information μ p x+information μ cq x)
    (g:=fun x => information μ (c ∘ p) x) (((information_integrable μ pq hpq).neg.add (information_integrable μ p hp)).add
    (information_integrable μ cq hcq)) (information_integrable μ (c ∘ p) hc)]
  rw [integral_add (f:=fun x => -information μ pq x+information μ p x) (g:=fun x => information μ cq x) ((information_integrable μ pq hpq).neg.add (information_integrable μ p hp))
      (information_integrable μ cq hcq),integral_add (f:=fun x => -information μ pq x) (g:=fun x => information μ p x) (information_integrable μ pq hpq).neg
      (information_integrable μ p hp),integral_neg]
  simp only [integral_information μ pq hpq,integral_information μ p hp,
    integral_information μ cq hcq,integral_information μ (c ∘ p) hc]
  unfold cond
  rw [obs_pair_swap μ q (c ∘ p),obs_pair_swap μ q p]
  dsimp only [pq,cq,Function.comp_apply]
  ring

end StandardMapEntropy.Entropy

end
section
namespace HyperbolicCoding
open MeasureTheory Set
open scoped BigOperators
variable {A : Type*} [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]
variable (μ ν : Measure A) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]

lemma finite_l1_le_two_of_lawClose {ε : ℝ} (h : LawClose μ ν ε) :
    (∑ a,|μ.real {a}-ν.real {a}|)≤2*ε := by
  have he (a : A) : |μ.real {a}-ν.real {a}|=
      max (μ.real {a}-ν.real {a}) 0+max (ν.real {a}-μ.real {a}) 0 := by
    rcases le_total (μ.real {a}) (ν.real {a}) with ha|ha
    · rw [abs_of_nonpos (sub_nonpos.mpr ha),max_eq_right (sub_nonpos.mpr ha),max_eq_left (sub_nonneg.mpr ha)]
      ring
    · rw [abs_of_nonneg (sub_nonneg.mpr ha),max_eq_left (sub_nonneg.mpr ha),max_eq_right (sub_nonpos.mpr ha)]
      ring
  simp_rw [he,Finset.sum_add_distrib]
  linarith [positive_mass_difference_le μ ν h,positive_mass_difference_le ν μ h.symm]

lemma lawClose_of_finite_l1 {ε : ℝ} (h : (∑ a,|μ.real {a}-ν.real {a}|)≤ε) : LawClose μ ν ε := by
  classical
  intro D _hD
  let S : Finset A := Finset.univ.filter (fun a => a∈D)
  have he : (S : Set A)=D := by ext a; simp [S]
  have hμ : μ.real D=∑ a∈S,μ.real {a} := by rw [←he]; exact (sum_measureReal_singleton S).symm
  have hν : ν.real D=∑ a∈S,ν.real {a} := by rw [←he]; exact (sum_measureReal_singleton S).symm
  rw [hμ,hν,←Finset.sum_sub_distrib]
  apply le_trans (Finset.abs_sum_le_sum_abs _ _) (le_trans ?_ h)
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S) (fun a _ _ => abs_nonneg _)

end HyperbolicCoding

end
section
namespace StandardMapEntropy.Entropy
open MeasureTheory Set HyperbolicCoding
open scoped BigOperators ENNReal
variable {X A B C : Type*} [MeasurableSpace X]
    [MeasurableSpace A] [Fintype A] [MeasurableSingletonClass A]
    [MeasurableSpace B] [Fintype B] [MeasurableSingletonClass B]
    [MeasurableSpace C] [Fintype C] [MeasurableSingletonClass C]
variable (μ : Measure X) [IsProbabilityMeasure μ]

lemma sum_mass_factor_mul (p : X → A) (hp : Measurable p) (c : A → C) (F : C → ℝ) :
    (∑ a,mass μ p a*F (c a))=∑ d,mass μ (c ∘ p) d*F d := by
  calc
    _ = ∫ x, (F ∘ c) (p x) ∂μ := sum_mass_mul_integral μ p hp (F ∘ c)
    _ = _ := (sum_mass_mul_integral μ (c ∘ p)
      ((measurable_of_countable c).comp hp) F).symm

omit [MeasurableSingletonClass B] in
lemma refinement_distance_eq (p : X → A) (q : X → B) (c : A → C)
    (hp : Measurable p) (_ : Measurable q) :
    (∑ a,∑ b,|refinementCopyWeights μ p q c a b-mass μ p a*mass μ q b|)=
      ∑ d,∑ b,|mass μ (fun x => (c (p x),q x)) (d,b)-mass μ (c ∘ p) d*mass μ q b| := by
  have he (a : A) (b : B) : |refinementCopyWeights μ p q c a b-mass μ p a*mass μ q b|=
      mass μ p a*|mass μ (fun x => (c (p x),q x)) (c a,b)/mass μ (c ∘ p) (c a)-mass μ q b| := by
    unfold refinementCopyWeights
    rw [mul_div_assoc,←mul_sub,abs_mul,abs_of_nonneg (mass_nonneg μ p a)]
  simp_rw [he]
  rw [Finset.sum_comm]
  have hec (b : B) := sum_mass_factor_mul μ p hp c
    (fun d => |mass μ (fun x => (c (p x),q x)) (d,b)/mass μ (c ∘ p) d-mass μ q b|)
  simp_rw [hec]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d _
  apply Finset.sum_congr rfl
  intro b _
  let u := mass μ (c ∘ p) d
  let v := mass μ (fun x => (c (p x),q x)) (d,b)
  have hu : 0≤u := mass_nonneg _ _ _
  have hv : 0≤v := mass_nonneg _ _ _
  have hvu : v≤u := mass_factor_le μ (fun x => (c (p x),q x)) Prod.fst (d,b)
  change u*|v/u-mass μ q b|=|v-u*mass μ q b|
  by_cases hu0 : u=0
  · have hv0 : v=0 := le_antisymm (hvu.trans (le_of_eq hu0)) hv
    simp [hu0,hv0]
  · calc
      _ = |u*(v/u-mass μ q b)| := by rw [abs_mul,abs_of_nonneg hu]
      _ = _ := by congr 1; rw [mul_sub,mul_div_cancel₀ _ hu0]

theorem lawClose_of_coarse_independence (p : X → A) (q : X → B) (c : A → C)
    (hp : Measurable p) (hq : Measurable q) {ε δ : ℝ} (hδ : 0≤δ)
    (hclose : LawClose (μ.map (fun x => (c (p x),q x)))
      ((μ.map (c ∘ p)).prod (μ.map q)) ε)
    (hdef : 4*(cond μ q (c ∘ p)-cond μ q p)≤δ^2) :
    LawClose (μ.map (fun x => (p x,q x))) ((μ.map p).prod (μ.map q)) (δ+2*ε) := by
  have hc : Measurable (c ∘ p) := (measurable_of_countable c).comp hp
  have : IsProbabilityMeasure (μ.map p) := by first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | (apply Measurable.aemeasurable; measurability) | measurability)
  have : IsProbabilityMeasure (μ.map q) := by first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | (apply Measurable.aemeasurable; measurability) | measurability)
  have : IsProbabilityMeasure (μ.map (c ∘ p)) := by first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | (apply Measurable.aemeasurable; measurability) | measurability)
  have : IsProbabilityMeasure (μ.map (fun x => (p x,q x))) := by first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | (apply Measurable.aemeasurable; measurability) | measurability)
  have : IsProbabilityMeasure (μ.map (fun x => (c (p x),q x))) := by first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | (apply Measurable.aemeasurable; measurability) | measurability)
  let u : A×B → ℝ := fun ab => mass μ (fun x => (p x,q x)) ab
  let v : A×B → ℝ := fun ab => refinementCopyWeights μ p q c ab.1 ab.2
  have hu1 : (∑ ab,u ab)=1 := by simp only [u,mass_sum μ _ (hp.prodMk hq),measure_univ,ENNReal.toReal_one]
  have hv1 : (∑ ab,v ab)=1 := by
    rw [Fintype.sum_prod_type]
    simp only [v,refinementCopyWeights_row μ p q c hp hq,mass_sum μ p hp,measure_univ,ENNReal.toReal_one]
  have hpen := finite_pinsker_sq u v (fun _ => mass_nonneg _ _ _)
    (fun ab => refinementCopyWeights_nonneg μ p q c ab.1 ab.2) hu1 hv1
    (fun ab => refinementCopyWeights_support μ p q c ab.1 ab.2)
  have hinfo : relativeInformation u v=cond μ q (c ∘ p)-cond μ q p :=
    refinement_relativeInformation μ p q c hp hq
  rw [hinfo] at hpen
  have hUV : (∑ ab,|u ab-v ab|)≤δ := by nlinarith [hpen.trans hdef]
  have hmap (a : A) (b : B) : (μ.map (fun x => (p x,q x))).real {(a,b)}=u (a,b) :=
    map_measureReal_apply (hp.prodMk hq) (measurableSet_singleton (a,b))
  have hmapC (d : C) (b : B) : (μ.map (fun x => (c (p x),q x))).real {(d,b)}=
      mass μ (fun x => (c (p x),q x)) (d,b) :=
    map_measureReal_apply (hc.prodMk hq) (measurableSet_singleton (d,b))
  have hprod (a : A) (b : B) : ((μ.map p).prod (μ.map q)).real {(a,b)}=mass μ p a*mass μ q b := by
    rw [←singleton_prod_singleton,Measure.real,Measure.prod_prod,ENNReal.toReal_mul]
    rw [←Measure.real,←Measure.real,map_measureReal_apply hp (measurableSet_singleton a),
      map_measureReal_apply hq (measurableSet_singleton b)]
    rfl
  have hprodC (d : C) (b : B) : ((μ.map (c ∘ p)).prod (μ.map q)).real {(d,b)}=
      mass μ (c ∘ p) d*mass μ q b := by
    rw [←singleton_prod_singleton,Measure.real,Measure.prod_prod,ENNReal.toReal_mul]
    rw [←Measure.real,←Measure.real,map_measureReal_apply hc (measurableSet_singleton d),
      map_measureReal_apply hq (measurableSet_singleton b)]
    rfl
  have hcoarse := finite_l1_le_two_of_lawClose _ _ hclose
  rw [Fintype.sum_prod_type] at hcoarse
  simp only [hmapC,hprodC] at hcoarse
  have hVP : (∑ ab : A×B,|v ab-mass μ p ab.1*mass μ q ab.2|)≤2*ε := by
    rw [Fintype.sum_prod_type]
    exact (refinement_distance_eq μ p q c hp hq).le.trans hcoarse
  apply lawClose_of_finite_l1
  rw [Fintype.sum_prod_type]
  simp only [hmap,hprod]
  rw [Fintype.sum_prod_type] at hUV hVP
  calc
    _≤∑ a,∑ b,(|u (a,b)-v (a,b)|+|v (a,b)-mass μ p a*mass μ q b|) :=
      Finset.sum_le_sum (fun a _ => Finset.sum_le_sum (fun b _ => abs_sub_le _ _ _))
    _=(∑ a,∑ b,|u (a,b)-v (a,b)|)+(∑ a,∑ b,|v (a,b)-mass μ p a*mass μ q b|) := by simp only [Finset.sum_add_distrib]
    _≤δ+2*ε := add_le_add hUV hVP

end StandardMapEntropy.Entropy

end
section
namespace StandardMapEntropy.Entropy
open MeasureTheory Set Filter HyperbolicCoding
open scoped Topology ENNReal BigOperators
variable {X A : Type*} [MeasurableSpace X] [MeasurableSpace A]
    [Fintype A] [MeasurableSingletonClass A]
variable (μ : Measure X) [IsProbabilityMeasure μ]

theorem uniform_remote_from_finite_entropy
    (f : X → X) (hf : MeasurePreserving f μ μ) (p : X → A) (hp : Measurable p)
    (k g L : ℕ) {ε δ : ℝ} (hδ : 0≤δ)
    (hclose : LawClose
      (μ.map (fun x => (word f p L (f^[k+g] x),word f p k x)))
      ((μ.map (fun x => word f p L (f^[k+g] x))).prod (μ.map (word f p k))) ε)
    (hdef : 4*(cond μ (word f p (k+g))
      (fun x => word f p L (f^[k+g] x))-(k+g : ℕ)*rate μ f p)≤δ^2) :
    ∀ M : ℕ,L≤M → LawClose
      (μ.map (fun x => (word f p M (f^[k+g] x),word f p k x)))
      ((μ.map (fun x => word f p M (f^[k+g] x))).prod (μ.map (word f p k))) (δ+2*ε) := by
  intro M hLM
  let rM : X → (Fin M → A) := fun x => word f p M (f^[k+g] x)
  let c : (Fin M → A) → (Fin L → A) := fun w i => w (Fin.castLE hLM i)
  let d : (Fin (k+g) → A) → (Fin k → A) := fun w i => w (Fin.castLE (Nat.le_add_right k g) i)
  have hrM : Measurable rM := (word_measurable f hf.measurable p hp M).comp (hf.measurable.iterate (k+g))
  have hc : c ∘ rM=(fun x => word f p L (f^[k+g] x)) := by funext x i; rfl
  have hd : d ∘ word f p (k+g)=word f p k := by funext x i; rfl
  have hdata := conditional_defect_data_processing μ rM (word f p (k+g)) c d
    hrM (word_measurable f hf.measurable p hp (k+g))
  rw [hd,hc] at hdata
  have hlower := rate_mul_le_cond_future μ f hf p hp (k+g) M
  have hdef' : 4*(cond μ (word f p k) (c ∘ rM)-cond μ (word f p k) rM)≤δ^2 := by
    rw [hc]
    change (k+g : ℕ)*rate μ f p ≤ cond μ (word f p (k+g)) rM at hlower
    linarith
  apply lawClose_of_coarse_independence μ rM (word f p k) c hrM
    (word_measurable f hf.measurable p hp k) hδ
  · exact hclose
  · exact hdef'

theorem eventually_finite_entropy_test
    (f : X → X) (hf : MeasurePreserving f μ μ) (p : X → A) (hp : Measurable p)
    (n : ℕ) {δ : ℝ} (hδ : 0<δ) :
    ∀ᶠ L : ℕ in atTop,4*(cond μ (word f p n)
      (fun x => word f p L (f^[n] x))-(n : ℝ)*rate μ f p)<δ^2 := by
  have ht := ((cond_future_tendsto μ f hf p hp n).sub_const ((n : ℝ)*rate μ f p)).const_mul 4
  have he : (4 : ℝ)*((n : ℝ)*rate μ f p-(n : ℝ)*rate μ f p)=0 := by ring
  rw [he] at ht
  exact ht.eventually (gt_mem_nhds (sq_pos_of_pos hδ))

end StandardMapEntropy.Entropy

end
section
namespace HyperbolicCoding
open MeasureTheory Set
open scoped ENNReal
variable {X Y A B : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSpace A] [MeasurableSpace B]

lemma independence_law_stable (μ : Measure X) (ν : Measure Y)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (p : X → A) (q : X → B) (p' : Y → A) (q' : Y → B)
    (hp : Measurable p) (hq : Measurable q) (hp' : Measurable p') (hq' : Measurable q')
    {ε δ : ℝ}
    (h : LawClose (μ.map (fun x => (p x,q x))) (ν.map (fun y => (p' y,q' y))) δ)
    (hi : LawClose (μ.map (fun x => (p x,q x))) ((μ.map p).prod (μ.map q)) ε) :
    LawClose (ν.map (fun y => (p' y,q' y))) ((ν.map p').prod (ν.map q')) (ε+3*δ) := by
  have hleft := h.map measurable_fst
  have hright := h.map measurable_snd
  rw [Measure.map_map measurable_fst (hp.prodMk hq),Measure.map_map measurable_fst (hp'.prodMk hq')] at hleft
  rw [Measure.map_map measurable_snd (hp.prodMk hq),Measure.map_map measurable_snd (hp'.prodMk hq')] at hright
  change LawClose (μ.map p) (ν.map p') δ at hleft
  change LawClose (μ.map q) (ν.map q') δ at hright
  have : IsProbabilityMeasure (μ.map p) := by first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | (apply Measurable.aemeasurable; measurability) | measurability)
  have : IsProbabilityMeasure (μ.map q) := by first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | (apply Measurable.aemeasurable; measurability) | measurability)
  have : IsProbabilityMeasure (ν.map p') := by first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | (apply Measurable.aemeasurable; measurability) | measurability)
  have : IsProbabilityMeasure (ν.map q') := by first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | (apply Measurable.aemeasurable; measurability) | measurability)
  convert h.symm.triangle (hi.triangle (hleft.prod hright)) using 1 <;> first | rfl | ring

end HyperbolicCoding

namespace StandardMapEntropy.Entropy
open MeasureTheory Set Filter HyperbolicCoding
open scoped ENNReal Topology
variable {X Y A : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSpace A] [Fintype A] [MeasurableSingletonClass A]
variable (μ : Measure X) [IsProbabilityMeasure μ]

omit [IsProbabilityMeasure μ] in
theorem finite_entropy_test_open (f : X → X) (hf : MeasurePreserving f μ μ)
    (p : X → A) (hp : Measurable p) (n L : ℕ) {r : ℝ}
    (hr : cond μ (word f p n) (fun x => word f p L (f^[n] x))-(n : ℝ)*rate μ f p < r) :
    ∃ δ : ℝ,0<δ ∧ ∀ (ν : Measure Y) (_ : IsProbabilityMeasure ν)
      (T : Y → Y) (_ : MeasurePreserving T ν ν) (q : Y → A),Measurable q →
      LawClose (μ.map (word f p (n+L))) (ν.map (word T q (n+L))) δ →
      rate μ f p-δ ≤ rate ν T q →
      cond ν (word T q n) (fun y => word T q L (T^[n] y))-(n : ℝ)*rate ν T q < r := by
  let D := cond μ (word f p n) (fun x => word f p L (f^[n] x))-(n : ℝ)*rate μ f p
  let γ := (r-D)/(2*((n : ℝ)+2))
  have hn : 0≤(n : ℝ) := Nat.cast_nonneg n
  have hγ : 0<γ := div_pos (sub_pos.mpr hr) (by positivity)
  obtain ⟨δW,hδW,hW⟩ := obs_continuity_in_law (Y:=Y) μ (word f p (n+L))
    (word_measurable f hf.measurable p hp (n+L)) hγ
  obtain ⟨δL,hδL,hL⟩ := obs_continuity_in_law (Y:=Y) μ (word f p L)
    (word_measurable f hf.measurable p hp L) hγ
  let δ := min γ (min δW δL)
  have hδ : 0<δ := lt_min hγ (lt_min hδW hδL)
  refine ⟨δ,hδ,?_⟩
  intro ν hν T hT q hq hclose hrate
  let : IsProbabilityMeasure ν := hν
  have hW' := hW ν (word T q (n+L)) (word_measurable T hT.measurable q hq (n+L))
    (hclose.mono ((min_le_right γ (min δW δL)).trans (min_le_left δW δL)))
  let c : (Fin (n+L) → A) → (Fin L → A) := fun w i => w (Fin.castLE (Nat.le_add_left L n) i)
  have hshort := hclose.map (measurable_of_countable c)
  rw [Measure.map_map (measurable_of_countable c) (word_measurable f hf.measurable p hp (n+L)),
    Measure.map_map (measurable_of_countable c) (word_measurable T hT.measurable q hq (n+L))] at hshort
  change LawClose (μ.map (word f p L)) (ν.map (word T q L)) δ at hshort
  have hL' := hL ν (word T q L) (word_measurable T hT.measurable q hq L)
    (hshort.mono ((min_le_right γ (min δW δL)).trans (min_le_right δW δL)))
  have hδγ : δ≤γ := min_le_left _ _
  have hmargin : ((n : ℝ)+2)*γ=(r-D)/2 := by dsimp [γ]; field_simp
  have hmul := mul_le_mul_of_nonneg_left (show rate μ f p-γ ≤ rate ν T q by linarith) hn
  obtain ⟨hWlo,hWhi⟩ := abs_lt.mp hW'
  obtain ⟨hLlo,hLhi⟩ := abs_lt.mp hL'
  rw [cond_word_future_eq ν T hT q hq]
  have hD : D=obs μ (word f p (n+L))-obs μ (word f p L)-(n : ℝ)*rate μ f p := by
    dsimp [D]
    rw [cond_word_future_eq μ f hf p hp]
  nlinarith

end StandardMapEntropy.Entropy

end
section
namespace StandardMapEntropy.Entropy
open MeasureTheory Set Filter HyperbolicCoding
open scoped ENNReal Topology
variable {X A : Type*} [MeasurableSpace X] [MeasurableSpace A]
    [Fintype A] [MeasurableSingletonClass A]
variable (μ : Measure X) [IsProbabilityMeasure μ]

theorem all_remote_from_finite_entropy
    (f : X → X) (hf : MeasurePreserving f μ μ) (p : X → A) (hp : Measurable p)
    (k g L : ℕ) {ε δ : ℝ} (hδ : 0≤δ)
    (hclose : LawClose
      (μ.map (fun x => (word f p L (f^[k+g] x),word f p k x)))
      ((μ.map (fun x => word f p L (f^[k+g] x))).prod (μ.map (word f p k))) ε)
    (hdef : 4*(cond μ (word f p (k+g))
      (fun x => word f p L (f^[k+g] x))-(k+g : ℕ)*rate μ f p)≤δ^2) :
    ∀ M : ℕ,LawClose
      (μ.map (fun x => (word f p M (f^[k+g] x),word f p k x)))
      ((μ.map (fun x => word f p M (f^[k+g] x))).prod (μ.map (word f p k))) (δ+2*ε) := by
  intro M
  by_cases hLM : L≤M
  · exact uniform_remote_from_finite_entropy μ f hf p hp k g L hδ hclose hdef M hLM
  · have hML : M≤L := by omega
    let c : (Fin L → A) → (Fin M → A) := fun w i => w (Fin.castLE hML i)
    have h := lawClose_pair_factor_left μ (fun x => word f p L (f^[k+g] x))
      (word f p k) c ((word_measurable f hf.measurable p hp L).comp (hf.measurable.iterate (k+g)))
      (word_measurable f hf.measurable p hp k) (measurable_of_countable c) hclose
    have hε : 0≤ε := hclose.nonneg
    exact h.mono (by linarith)

end StandardMapEntropy.Entropy

end
section
namespace HyperbolicCoding
open MeasureTheory Set Filter StandardMapEntropy.Entropy
open scoped ENNReal Topology BigOperators

lemma lawClose_prefix {X Y A : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSpace A] [Fintype A] [MeasurableSingletonClass A]
    (μ : Measure X) (ν : Measure Y) (f : X → X) (T : Y → Y)
    (hf : Measurable f) (hT : Measurable T) (p : X → A) (q : Y → A)
    (hp : Measurable p) (hq : Measurable q) {m n : ℕ} (hmn : m≤n) {δ : ℝ}
    (h : LawClose (μ.map (word f p n)) (ν.map (word T q n)) δ) :
    LawClose (μ.map (word f p m)) (ν.map (word T q m)) δ := by
  let c : (Fin n → A) → (Fin m → A) := fun w i => w (Fin.castLE hmn i)
  have hc : Measurable c := measurable_of_countable c
  have hh := h.map hc
  rw [Measure.map_map hc (word_measurable f hf p hp n),
    Measure.map_map hc (word_measurable T hT q hq n)] at hh
  exact hh

lemma lawClose_remote_of_word {X Y A : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSpace A] [Fintype A] [MeasurableSingletonClass A]
    (μ : Measure X) (ν : Measure Y) (f : X → X) (T : Y → Y)
    (hf : Measurable f) (hT : Measurable T) (p : X → A) (q : Y → A)
    (hp : Measurable p) (hq : Measurable q) (k g L : ℕ) {δ : ℝ}
    (h : LawClose (μ.map (word f p ((k+g)+L))) (ν.map (word T q ((k+g)+L))) δ) :
    LawClose (μ.map (fun x => (word f p L (f^[k+g] x),word f p k x)))
      (ν.map (fun x => (word T q L (T^[k+g] x),word T q k x))) δ := by
  let c : (Fin ((k+g)+L) → A) → ((Fin L → A)×(Fin k → A)) :=
    fun w => (fun i => w ⟨i.val+(k+g),by omega⟩,fun i => w ⟨i.val,by omega⟩)
  have hc : Measurable c := measurable_of_countable c
  have hh := h.map hc
  rw [Measure.map_map hc (word_measurable f hf p hp _),
    Measure.map_map hc (word_measurable T hT q hq _)] at hh
  have he (x : X) : c (word f p ((k+g)+L) x)=(word f p L (f^[k+g] x),word f p k x) := by
    apply Prod.ext
    · funext i
      exact congrArg p (Function.iterate_add_apply f i.val (k+g) x)
    · rfl
  have he' (y : Y) : c (word T q ((k+g)+L) y)=(word T q L (T^[k+g] y),word T q k y) := by
    apply Prod.ext
    · funext i
      exact congrArg q (Function.iterate_add_apply T i.val (k+g) y)
    · rfl
  simpa only [Function.comp_def,he,he'] using hh

theorem weakBernoulli_finite_determination {X Y A : Type*}
    [MeasurableSpace X] [StandardBorelSpace X] [MeasurableSpace Y] [StandardBorelSpace Y]
    [MeasurableSpace A] [Fintype A] [MeasurableSingletonClass A] [Nonempty A]
    (μ : Measure X) [IsProbabilityMeasure μ] [NullSingletonClass μ]
    (e : X ≃ᵐ X) (he : MeasurePreserving e μ μ) (p : X → A) (hp : Measurable p)
    (hwb : WeakBernoulliProcess μ e p) {η : ℝ} (hη : 0<η) :
    ∃ m s : ℕ,0 < s ∧ ∃ δ : ℝ,0<δ ∧
      ∀ (ν : Measure Y) (_ : IsProbabilityMeasure ν) (_ : NullSingletonClass ν)
        (T : Y → Y) (_ : MeasurePreserving T ν ν) (q : Y → A),Measurable q →
        LawClose (μ.map (word e p m)) (ν.map (word T q m)) δ →
        rate μ e p-δ ≤ rate ν T q →
        ∀ n : ℕ,∃ R : MatrixCoupling (mass μ (word e p (n*s))) (mass ν (word T q (n*s))),
          R.cost nameCost≤η*(n*s : ℕ) := by
  let ε : ℝ := η/100
  have hε : 0<ε := div_pos hη (by norm_num)
  obtain ⟨g,hg⟩ := weakBernoulli_forward_blocks μ e he p hp hwb hε
  obtain ⟨k,hk⟩ := exists_nat_gt ((g : ℝ)/ε+1)
  have hkpos : 0<k := by
    have hg0 : 0≤(g : ℝ)/ε := div_nonneg (Nat.cast_nonneg g) hε.le
    have hkR : 0<(k : ℝ) := by linarith
    exact_mod_cast hkR
  have hkg : (g : ℝ)≤ε*(k : ℝ) := by
    have hh := (div_lt_iff₀ hε).mp (show (g : ℝ)/ε<(k : ℝ) by linarith)
    nlinarith
  obtain ⟨L,hL⟩ := (eventually_finite_entropy_test μ e he p hp (k+g) hε).exists
  obtain ⟨δ₀,hδ₀,hopen⟩ := finite_entropy_test_open (Y:=Y) μ e he p hp (k+g) L
    (r:=ε^2/4) (by linarith)
  let δ := min ε δ₀
  have hδ : 0<δ := lt_min hε hδ₀
  refine ⟨(k+g)+L,k+g,by omega,δ,hδ,?_⟩
  intro ν hν hnonatomic T hT q hq hclose hrate n
  let : IsProbabilityMeasure ν := hν
  let : NullSingletonClass ν := hnonatomic
  have hdε : δ≤ε := min_le_left _ _
  have hd₀ : δ≤δ₀ := min_le_right _ _
  have hd := hopen ν hν T hT q hq (hclose.mono hd₀) (by linarith)
  have hj := lawClose_remote_of_word μ ν e T he.measurable hT.measurable p q hp hq k g L hclose
  have hfinite := independence_law_stable μ ν
    (fun x => word e p L (e^[k+g] x)) (word e p k)
    (fun y => word T q L (T^[k+g] y)) (word T q k)
    ((word_measurable e he.measurable p hp L).comp (he.measurable.iterate _))
    (word_measurable e he.measurable p hp k)
    ((word_measurable T hT.measurable q hq L).comp (hT.measurable.iterate _))
    (word_measurable T hT.measurable q hq k) hj (hg k L)
  have hremoteQ := all_remote_from_finite_entropy ν T hT q hq k g L hε.le hfinite
    (show 4*(cond ν (word T q (k+g)) (fun y => word T q L (T^[k+g] y))-
      (k+g : ℕ)*rate ν T q)≤ε^2 by linarith)
  have hshort := lawClose_prefix μ ν e T he.measurable hT.measurable p q hp hq
    (show k≤(k+g)+L by omega) hclose
  obtain ⟨R,hR⟩ := full_word_transport μ ν e he p hp T hT q hq k g (hg k) hremoteQ hshort n
  refine ⟨R,hR.trans ?_⟩
  have hb : (k : ℝ)*(ε+δ+(ε+2*(ε+3*δ)))+(g : ℝ)≤η*(k+g : ℕ) := by
    have hk0 : 0≤(k : ℝ) := Nat.cast_nonneg k
    have hg0 : 0≤(g : ℝ) := Nat.cast_nonneg g
    have hsmall : ε+δ+(ε+2*(ε+3*δ))≤11*ε := by linarith
    have hh := mul_le_mul_of_nonneg_left hsmall hk0
    have hηε : η=100*ε := by dsimp [ε]; ring
    push_cast
    rw [hηε]
    nlinarith [mul_nonneg hε.le hk0,mul_nonneg hε.le hg0]
  have hn := mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg n)
  push_cast at hn ⊢
  nlinarith

end HyperbolicCoding

end
end

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_Coding_TypicalWordCodebook
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace HyperbolicCoding
open MeasureTheory Set Filter StandardMapEntropy.Entropy
open scoped BigOperators ENNReal Topology
variable {A : Type*} [Fintype A] [DecidableEq A]

omit [DecidableEq A] in
lemma productWordWeight_sum (p : A → ℝ) (hp : ∑ a,p a=1) (n : ℕ) :
    (∑ w : Fin n → A,productWordWeight p n w)=1 :=
  productWeights_sum (fun _ : Fin n => p) (fun _ => hp)

end HyperbolicCoding

end
section
namespace HyperbolicCoding
open MeasureTheory Set StandardMapEntropy.Entropy
open scoped BigOperators ENNReal
variable {A : Type*} [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]

lemma finiteWeightLaw_singleton (p : A → ℝ) (a : A) :
    finiteWeightLaw p {a}=ENNReal.ofReal (p a) := by
  classical
  simp [finiteWeightLaw,Measure.finsetSum_apply,Measure.smul_apply,Pi.single_apply]

omit [MeasurableSingletonClass A] in
lemma finiteWeightLaw_probability (p : A → ℝ) (hp : ∀ a,0≤p a) (hs : ∑ a,p a=1) :
    IsProbabilityMeasure (finiteWeightLaw p) := by
  constructor
  simp only [finiteWeightLaw,Measure.finsetSum_apply,Measure.smul_apply,smul_eq_mul,
    Measure.dirac_apply_of_mem (mem_univ _),mul_one]
  rw [←ENNReal.ofReal_sum_of_nonneg (fun a _ => hp a),hs,ENNReal.ofReal_one]

omit [Fintype A] [MeasurableSingletonClass A] in
lemma iidShift_iterate (w : ℤ → A) (n : ℕ) (i : ℤ) :
    (iidShift^[n]) w i=w (i+n) := by
  induction n generalizing i with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    change (iidShift^[n]) w (i+1)=_
    rw [ih]
    congr 1
    push_cast
    ring

omit [Fintype A] [MeasurableSingletonClass A] in
lemma iidShift_preserving (β : Measure A) [IsProbabilityMeasure β] :
    MeasurePreserving (iidShift (A:=A)) (Measure.infinitePi (fun _ : ℤ => β))
      (Measure.infinitePi (fun _ : ℤ => β)) := by
  refine ⟨iidShift.measurable,?_⟩
  exact Measure.map_infinitePi_infinitePi_of_inj (fun i j : ℤ => by omega)

omit [Fintype A] [MeasurableSingletonClass A] in
lemma iid_word_eq (n : ℕ) (w : ℤ → A) :
    word iidShift (fun z : ℤ → A => z 0) n w=fun i : Fin n => w i.val := by
  funext i
  change (iidShift^[i.val]) w 0=_
  rw [iidShift_iterate,zero_add]

omit [Fintype A] [MeasurableSingletonClass A] in
lemma iid_word_law (β : Measure A) [IsProbabilityMeasure β] (n : ℕ) :
    (Measure.infinitePi (fun _ : ℤ => β)).map (word iidShift (fun z : ℤ → A => z 0) n)=
      Measure.pi (fun _ : Fin n => β) := by
  have hi : Function.Injective (fun i : Fin n => (i.val : ℤ)) := by
    intro i j h
    apply Fin.ext
    change (i.val : ℤ)=(j.val : ℤ) at h
    exact Int.ofNat_inj.mp h
  simpa only [funext (iid_word_eq (A:=A) n),Measure.infinitePi_eq_pi] using
    (Measure.map_infinitePi_infinitePi_of_inj (P:=fun _ : ℤ => β) hi)

lemma iid_word_mass (p : A → ℝ) (hp : ∀ a,0≤p a) (hs : ∑ a,p a=1)
    (n : ℕ) (w : Fin n → A) :
    mass (Measure.infinitePi (fun _ : ℤ => finiteWeightLaw p))
      (word iidShift (fun z : ℤ → A => z 0) n) w=productWordWeight p n w := by
  let : IsProbabilityMeasure (finiteWeightLaw p) := finiteWeightLaw_probability p hp hs
  change (Measure.infinitePi (fun _ : ℤ => finiteWeightLaw p)).real
    ((word iidShift (fun z : ℤ → A => z 0) n) ⁻¹' {w})=_
  rw [←map_measureReal_apply (word_measurable iidShift iidShift.measurable _
    (measurable_pi_apply 0) n) (measurableSet_singleton w)]
  rw [iid_word_law,Measure.real,Measure.pi_singleton]
  simp only [finiteWeightLaw_singleton,ENNReal.toReal_prod,ENNReal.toReal_ofReal (hp _),productWordWeight]

end HyperbolicCoding

end
section
namespace HyperbolicCoding
open MeasureTheory ProbabilityTheory Set Filter StandardMapEntropy.Entropy
open scoped BigOperators ENNReal Topology
variable {A : Type*} [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]

omit [Fintype A] [MeasurableSingletonClass A] in
lemma iid_disjoint_coordinate_independent {I J : Type*} (β : Measure A) [IsProbabilityMeasure β]
    (f : I → ℤ) (g : J → ℤ) (hfg : ∀ i j,f i≠g j) :
    IndepFun (fun w : ℤ → A => fun i => w (f i)) (fun w : ℤ → A => fun j => w (g j))
      (Measure.infinitePi (fun _ : ℤ => β)) := by
  classical
  apply IndepFun.process_indepFun_process (fun i => measurable_pi_apply (f i))
    (fun j => measurable_pi_apply (g j))
  intro S T
  have hST : Disjoint (S.image f) (T.image g) := by
    apply Finset.disjoint_left.mpr
    intro z hz hz'
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨j,hj,he⟩ := Finset.mem_image.mp hz'
    exact hfg i j he.symm
  have h := (iIndepFun_infinitePi (P:=fun _ : ℤ => β) (X:=fun _ a => a)
    (fun _ => measurable_id)).indepFun_finset (S.image f) (T.image g) hST
    (fun _ => measurable_pi_apply _)
  let F : ((S.image f) → A) → (S → A) := fun w i => w ⟨f i,Finset.mem_image.mpr ⟨i,i.2,rfl⟩⟩
  let G : ((T.image g) → A) → (T → A) := fun w j => w ⟨g j,Finset.mem_image.mpr ⟨j,j.2,rfl⟩⟩
  exact h.comp (Measurable.of_eval (fun _ => measurable_pi_apply _))
    (Measurable.of_eval (fun _ => measurable_pi_apply _)) (φ:=F) (ψ:=G)

omit [Fintype A] [MeasurableSingletonClass A] in
lemma iidShift_symm_iterate (w : ℤ → A) (n : ℕ) (i : ℤ) :
    (iidShift.symm^[n]) w i=w (i-n) := by
  induction n generalizing i with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    change (iidShift.symm^[n]) w (i-1)=_
    rw [ih]
    congr 1
    push_cast
    ring

omit [Fintype A] [MeasurableSingletonClass A] in
lemma iid_tail_eq (w : ℤ → A) (n : ℕ) :
    tailName iidShift (fun w : ℤ → A => w 0) n w=fun i : ℕ => w ((i+n : ℕ) : ℤ) := by
  funext i
  simp only [tailName,iidShift_iterate,zero_add]

omit [Fintype A] [MeasurableSingletonClass A] in
lemma iid_past_eq (w : ℤ → A) (n : ℕ) :
    tailName iidShift.symm (fun w : ℤ → A => w 0) n w=fun i : ℕ => w (-((i+n : ℕ) : ℤ)) := by
  funext i
  simp only [tailName,iidShift_symm_iterate,zero_sub]

omit [Fintype A] [MeasurableSingletonClass A] in
theorem iid_weakBernoulli (β : Measure A) [IsProbabilityMeasure β] :
    WeakBernoulliProcess (Measure.infinitePi (fun _ : ℤ => β)) iidShift (fun w : ℤ → A => w 0) := by
  intro ε hε
  filter_upwards [eventually_ge_atTop 1] with n hn
  let μ := Measure.infinitePi (fun _ : ℤ => β)
  have hi := iid_disjoint_coordinate_independent β (fun i : ℕ => -((i+n : ℕ) : ℤ))
    (fun i : ℕ => ((i+n : ℕ) : ℤ)) (by intro i j h; omega)
  have hp : IndepFun (tailName iidShift.symm (fun w : ℤ → A => w 0) n)
      (tailName iidShift (fun w : ℤ → A => w 0) n) μ := by
    have hP : tailName iidShift.symm (fun w : ℤ → A => w 0) n=
        fun w : ℤ → A => fun i : ℕ => w (-((i+n : ℕ) : ℤ)) := funext (fun w => iid_past_eq w n)
    have hF : tailName iidShift (fun w : ℤ → A => w 0) n=
        fun w : ℤ → A => fun i : ℕ => w ((i+n : ℕ) : ℤ) := funext (fun w => iid_tail_eq w n)
    rw [hP,hF]
    exact hi
  have hmap := hp.map_prod_eq_prod_map_map
    (measurable_tailName iidShift.symm.measurable (measurable_pi_apply 0) n).aemeasurable
    (measurable_tailName iidShift.measurable (measurable_pi_apply 0) n).aemeasurable
  have hpres := iidShift_preserving β
  rw [stationary_tail_law μ (hpres.symm iidShift) (measurable_pi_apply 0) n,
    stationary_tail_law μ hpres (measurable_pi_apply 0) n] at hmap
  have heq : μ.map (remotePair iidShift iidShift.symm (fun w : ℤ → A => w 0) n)=
      remoteProductLaw μ iidShift iidShift.symm (fun w : ℤ → A => w 0) := hmap
  change LawClose (μ.map (remotePair iidShift iidShift.symm (fun w : ℤ → A => w 0) n))
    (remoteProductLaw μ iidShift iidShift.symm (fun w : ℤ → A => w 0)) ε
  rw [heq]
  intro D _
  simpa only [sub_self,abs_zero] using hε.le

omit [MeasurableSpace A] [MeasurableSingletonClass A] in
lemma shannon_product_weights {B : Type*} [Fintype B] (p : A → ℝ) (q : B → ℝ)
    (hp : ∑ a,p a=1) (hq : ∑ b,q b=1) :
    shannon (fun ab : A×B => p ab.1*q ab.2)=shannon p+shannon q := by
  simp only [shannon,Fintype.sum_prod_type,Real.negMulLog_mul,Finset.sum_add_distrib]
  simp only [←Finset.sum_mul,←Finset.mul_sum,hp,hq,one_mul]

omit [MeasurableSpace A] [MeasurableSingletonClass A] in
lemma shannon_productWordWeight (p : A → ℝ) (hs : ∑ a,p a=1) (n : ℕ) :
    shannon (productWordWeight p n)=(n : ℝ)*weightEntropy p := by
  classical
  have hdef : shannon p=weightEntropy p := by
    unfold shannon weightEntropy
    apply Finset.sum_congr rfl
    intro a _
    simp [Real.negMulLog]
  induction n with
  | zero => simp [shannon,productWordWeight]
  | succ n ih =>
    let e : (A×(Fin n → A)) ≃ (Fin (n+1) → A) := Fin.consEquiv (fun _ => A)
    have he : (∑ w : Fin (n+1) → A,Real.negMulLog (productWordWeight p (n+1) w))=
        ∑ ab : A×(Fin n → A),Real.negMulLog (p ab.1*productWordWeight p n ab.2) := by
      rw [←Equiv.sum_comp e]
      apply Finset.sum_congr rfl
      intro ab _
      congr 1
      simp [productWordWeight,Fin.prod_univ_succ,e]
    rw [shannon,he]
    change shannon (fun ab : A×(Fin n → A) => p ab.1*productWordWeight p n ab.2)=_
    rw [shannon_product_weights p _ hs (productWordWeight_sum p hs n),hdef,ih]
    push_cast
    ring

theorem iid_rate [DecidableEq A] (p : A → ℝ) (hp : ∀ a,0≤p a) (hs : ∑ a,p a=1) :
    rate (Measure.infinitePi (fun _ : ℤ => finiteWeightLaw p)) iidShift
      (fun w : ℤ → A => w 0)=weightEntropy p := by
  let : IsProbabilityMeasure (finiteWeightLaw p) := finiteWeightLaw_probability p hp hs
  have hword (n : ℕ) : obs (Measure.infinitePi (fun _ : ℤ => finiteWeightLaw p))
      (word iidShift (fun w : ℤ → A => w 0) n)=(n : ℝ)*weightEntropy p := by
    rw [obs,funext (iid_word_mass p hp hs n)]
    exact shannon_productWordWeight p hs n
  have ht := rate_tendsto (Measure.infinitePi (fun _ : ℤ => finiteWeightLaw p)) iidShift
    (iidShift_preserving _) (fun w : ℤ → A => w 0) (measurable_pi_apply 0)
  apply tendsto_nhds_unique ht
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_gt_atTop 0] with n hn
  rw [hword,mul_div_cancel_left₀ _ (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn))]

end HyperbolicCoding

end
section
namespace HyperbolicCoding
open MeasureTheory ProbabilityTheory Set Filter StandardMapEntropy.Entropy
open scoped BigOperators ENNReal Topology
variable {A : Type*} [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]

omit [MeasurableSpace A] [MeasurableSingletonClass A] in
lemma weight_le_one (p : A → ℝ) (hp : ∀ a,0≤p a) (hs : ∑ a,p a=1) (a : A) : p a≤1 := by
  rw [←hs]
  exact Finset.single_le_sum (fun b _ => hp b) (Finset.mem_univ a)

omit [MeasurableSpace A] [MeasurableSingletonClass A] in
lemma weightEntropy_zero_of_one (p : A → ℝ) (hp : ∀ a,0≤p a) (hs : ∑ a,p a=1)
    {a : A} (ha : p a=1) : weightEntropy p=0 := by
  classical
  have hzer : ∑ b∈Finset.univ.erase a,p b=0 := by
    have hh := Finset.sum_erase_add (s:=Finset.univ) p (Finset.mem_univ a)
    rw [hs,ha] at hh
    linarith
  have hb (b : A) (hba : b≠a) : p b=0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hp i)).mp hzer b (by simp [hba])
  unfold weightEntropy
  apply Finset.sum_eq_zero
  intro b _
  by_cases hba : b=a
  · simp [hba,ha]
  · simp [hb b hba]

omit [MeasurableSpace A] [MeasurableSingletonClass A] in
lemma positive_weightEntropy_max_bound (p : A → ℝ) (hp : ∀ a,0≤p a)
    (hs : ∑ a,p a=1) (hh : 0 < weightEntropy p) :
    ∃ c : ℝ,0 ≤ c ∧ c < 1 ∧ ∀ a,p a ≤ c := by
  classical
  have : Nonempty A := by
    by_contra h
    have : IsEmpty A := not_nonempty_iff.mp h
    simp at hs
  obtain ⟨a,ha,hamax⟩ := Finset.exists_max_image Finset.univ p Finset.univ_nonempty
  refine ⟨p a,hp a,?_,fun b => hamax b (Finset.mem_univ b)⟩
  apply lt_of_le_of_ne (weight_le_one p hp hs a)
  intro he
  have hz := weightEntropy_zero_of_one p hp hs he
  linarith

theorem iid_nullSingleton [DecidableEq A] (p : A → ℝ) (hp : ∀ a,0≤p a)
    (hs : ∑ a,p a=1) (hh : 0 < weightEntropy p) :
    NullSingletonClass (Measure.infinitePi (fun _ : ℤ => finiteWeightLaw p)) := by
  let : IsProbabilityMeasure (finiteWeightLaw p) := finiteWeightLaw_probability p hp hs
  let μ := Measure.infinitePi (fun _ : ℤ => finiteWeightLaw p)
  obtain ⟨c,hc,hc1,hbound⟩ := positive_weightEntropy_max_bound p hp hs hh
  constructor
  intro w
  have hb (n : ℕ) : μ.real {w} ≤ c^n := by
    have hsub : ({w} : Set (ℤ → A))⊆
        (word iidShift (fun y : ℤ → A => y 0) n) ⁻¹' {word iidShift (fun y : ℤ → A => y 0) n w} := by
      rintro y rfl
      rfl
    have h := measureReal_mono (μ:=μ) hsub
    change μ.real {w}≤ mass μ (word iidShift (fun y : ℤ → A => y 0) n)
      (word iidShift (fun y : ℤ → A => y 0) n w) at h
    have himass := iid_word_mass p hp hs n (word iidShift (fun y : ℤ → A => y 0) n w)
    change mass μ _ _=_ at himass
    rw [himass] at h
    apply h.trans
    calc
      productWordWeight p n _ ≤ ∏ _i : Fin n,c := Finset.prod_le_prod
        (fun _ _ => hp _) (fun _ _ => hbound _)
      _=c^n := by simp
  have hz : μ.real {w}=0 := le_antisymm
    (ge_of_tendsto' (tendsto_pow_atTop_nhds_zero_of_lt_one hc hc1) hb) ENNReal.toReal_nonneg
  exact (ENNReal.toReal_eq_zero_iff _).mp hz |>.resolve_right (measure_ne_top μ _)

theorem iid_finite_determination {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]
    [Nonempty A] [DecidableEq A]
    (β : A → ℝ) (hβ : ∀ a,0≤β a) (hβsum : ∑ a,β a=1)
    (hβentropy : 0 < weightEntropy β) {η : ℝ} (hη : 0 < η) :
    ∃ m s : ℕ,0 < s ∧ ∃ δ : ℝ,0 < δ ∧
      ∀ (μ : Measure X) (_ : IsProbabilityMeasure μ) (_ : NullSingletonClass μ)
        (f : X → X) (_ : MeasurePreserving f μ μ) (q : X → A),Measurable q →
        LawClose (μ.map (word f q m)) (Measure.pi (fun _ : Fin m => finiteWeightLaw β)) δ →
        weightEntropy β-δ ≤ rate μ f q →
        ∀ n : ℕ,∃ R : MatrixCoupling (mass μ (word f q (n*s))) (productWordWeight β (n*s)),
          R.cost nameCost≤η*(n*s : ℕ) := by
  let : IsProbabilityMeasure (finiteWeightLaw β) := finiteWeightLaw_probability β hβ hβsum
  let ν := Measure.infinitePi (fun _ : ℤ => finiteWeightLaw β)
  let : NullSingletonClass ν := iid_nullSingleton β hβ hβsum hβentropy
  obtain ⟨m,s,hs,δ,hδ,hfd⟩ := weakBernoulli_finite_determination (Y:=X) ν iidShift
    (iidShift_preserving _) (fun w : ℤ → A => w 0) (measurable_pi_apply 0)
    (iid_weakBernoulli _) hη
  refine ⟨m,s,hs,δ,hδ,?_⟩
  intro μ hμ hnull f hf q hq hlaw hrate n
  let : IsProbabilityMeasure μ := hμ
  let : NullSingletonClass μ := hnull
  have hclose : LawClose (ν.map (word iidShift (fun w : ℤ → A => w 0) m))
      (μ.map (word f q m)) δ := by
    rw [iid_word_law]
    exact hlaw.symm
  have hrate' : rate ν iidShift (fun w : ℤ → A => w 0)-δ ≤ rate μ f q := by
    simpa only [ν,iid_rate β hβ hβsum] using hrate
  obtain ⟨R,hR⟩ := hfd μ hμ hnull f hf q hq hclose hrate' n
  have hR' : R.symm.cost nameCost≤η*(n*s : ℕ) := by
    rw [MatrixCoupling.symm_cost R nameCost nameCost_comm]
    exact hR
  have heq : mass ν (word iidShift (fun w : ℤ → A => w 0) (n*s)) =
      productWordWeight β (n*s) := funext (iid_word_mass β hβ hβsum (n*s))
  rw [←heq]
  exact ⟨R.symm,hR'⟩

end HyperbolicCoding

end

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_Entropy_LocallyFiniteLower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace StandardMapEntropy.Entropy
open MeasureTheory Set Filter
open scoped Topology ENNReal BigOperators
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
variable {α β : Type*} [Fintype α] [Fintype β]
variable [MeasurableSpace α] [MeasurableSpace β] [MeasurableSingletonClass α] [MeasurableSingletonClass β]
omit [IsProbabilityMeasure μ] [MeasurableSpace α] [MeasurableSpace β]
  [MeasurableSingletonClass α] [MeasurableSingletonClass β] in
lemma rate_equiv (f : Ω → Ω) (p : Ω → α) (e : α ≃ β) : rate μ f (e ∘ p)=rate μ f p := by
  have he (n : ℕ) : obs μ (word f (e ∘ p) n)=obs μ (word f p n) := by
    have hword : word f (e ∘ p) n=(Equiv.piCongrRight (fun _ : Fin n => e)) ∘ word f p n := rfl
    rw [hword,obs_equiv]
  simp only [rate,he]
end StandardMapEntropy.Entropy

namespace StandardMapEntropy
open MeasureTheory Set Filter
open scoped Topology ENNReal
lemma finite_rate_le_metricEntropy {α : Type*} [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]
    (μ : Measure Torus) [IsProbabilityMeasure μ] (f : Torus → Torus) (hf : MeasurePreserving f μ μ)
    (p : Torus → α) (hp : Measurable p) : ENNReal.ofReal (Entropy.rate μ f p)≤ metricEntropy μ f := by
  let : Nonempty α := ⟨p (0,0)⟩
  have hcard : Fintype.card α-1+1=Fintype.card α := Nat.sub_add_cancel (Fintype.card_pos)
  let e : α ≃ Fin (Fintype.card α-1+1) := (Fintype.equivFin α).trans (finCongr hcard.symm)
  let q : FinitePartition (Fintype.card α-1) := ⟨e ∘ p,(measurable_of_countable e).comp hp⟩
  have hle : partitionEntropy μ f q≤ metricEntropy μ f := le_iSup_of_le _ (le_iSup_of_le q le_rfl)
  rw [partitionEntropy_eq_ofReal_rate μ f hf q] at hle
  exact (congrArg ENNReal.ofReal (Entropy.rate_equiv μ f p e)).symm.le.trans hle
end StandardMapEntropy

end
end

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_Entropy_FiniteBinCoding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace StandardMapEntropy.Entropy
open MeasureTheory Set Filter
open scoped BigOperators ENNReal Topology
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
variable {α : Type*} [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]

omit [MeasurableSpace Ω] [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α] in
lemma word_eval_zero (f : Ω → Ω) (p : Ω → α) (n : ℕ) :
    (fun v : Fin (n+1)→α => v 0) ∘ word f p (n+1)=p := by
  funext x
  simp only [Function.comp_def,word,Fin.val_zero,Function.iterate_zero,Function.id_def]
lemma obs_word_markov_step (f : Ω → Ω) (hf : MeasurePreserving f μ μ) (p : Ω → α)
    (hp : Measurable p) (n : ℕ) :
    obs μ (word f p (n+2))≤obs μ (word f p (n+1))+cond μ p (p ∘ f) := by
  have hs := obs_word_split μ f p 1 (n+1)
  have hp1 : word f p 1=(fun x (_ : Fin 1) => p x) := by
    funext x i
    simp only [word,Fin.val_eq_zero,Function.iterate_zero,Function.id_def]
  have hc := cond_factor_right μ p ((word f p (n+1)) ∘ f) (fun v : Fin (n+1)→α => v 0)
    hp ((word_measurable f hf.measurable p hp (n+1)).comp hf.measurable)
  have he : (fun v : Fin (n+1)→α => v 0) ∘ ((word f p (n+1)) ∘ f)=p ∘ f :=
    congrArg (fun g => g ∘ f) (word_eval_zero f p n)
  rw [he] at hc
  have hpair : obs μ (fun x => (word f p 1 x,word f p (n+1) (f x)))=
      obs μ (fun x => (p x,word f p (n+1) (f x))) := by
    have hh := obs_equiv μ (fun x => (word f p 1 x,word f p (n+1) (f x)))
      (Equiv.prodCongr (Equiv.funUnique (Fin 1) α) (Equiv.refl (Fin (n+1)→α)))
    simpa only [Function.comp_def,Equiv.prodCongr_apply,Prod.map_apply,Equiv.refl_apply,
      Equiv.funUnique_apply,word,Fin.default_eq_zero,Fin.val_zero,Function.iterate_zero,Function.id_def] using hh.symm
  have hobs := obs_comp_preserving μ f hf (word f p (n+1)) (word_measurable f hf.measurable p hp (n+1))
  have hn : 1+(n+1)=n+2 := by omega
  rw [hn] at hs
  simp only [Function.iterate_one] at hs
  rw [hs,hpair]
  unfold cond at hc
  change _≤_+((obs μ (fun x => (p x,(p ∘ f) x)))-obs μ (p ∘ f))
  dsimp only [Function.comp_def] at hc hobs ⊢
  linarith
lemma obs_word_markov_bound (f : Ω → Ω) (hf : MeasurePreserving f μ μ) (p : Ω → α)
    (hp : Measurable p) (n : ℕ) :
    obs μ (word f p (n+1))≤obs μ p+(n : ℝ)*cond μ p (p ∘ f) := by
  induction n with
  | zero => simp only [Nat.cast_zero,zero_mul,add_zero,obs_word_one μ f p hp,le_refl]
  | succ n ih =>
    have h := obs_word_markov_step μ f hf p hp n
    have he : (n+1 : ℕ)+1=n+2 := by omega
    rw [he]
    push_cast
    linarith
lemma rate_le_oneStep (f : Ω → Ω) (hf : MeasurePreserving f μ μ) (p : Ω → α)
    (hp : Measurable p) : rate μ f p ≤ cond μ p (p ∘ f) := by
  have hseq := (rate_tendsto μ f hf p hp).comp (tendsto_add_atTop_nat 1)
  have h0 : Tendsto (fun n : ℕ => (obs μ p-cond μ p (p ∘ f))/((n : ℝ)+1)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_atTop_mono (fun n : ℕ => le_add_of_nonneg_right (show (0 : ℝ)≤1 by norm_num)) tendsto_natCast_atTop_atTop)
  have hlim := h0.const_add (cond μ p (p ∘ f))
  apply le_of_tendsto_of_tendsto hseq (show Tendsto
    (fun n : ℕ => cond μ p (p ∘ f)+(obs μ p-cond μ p (p ∘ f))/((n : ℝ)+1))
    atTop (𝓝 (cond μ p (p ∘ f))) from by simpa only [add_zero] using hlim)
  apply Eventually.of_forall
  intro n
  dsimp only [Function.comp_def]
  rw [Nat.cast_add,Nat.cast_one]
  have h := div_le_div_of_nonneg_right (obs_word_markov_bound μ f hf p hp n)
    (show 0≤(n : ℝ)+1 by positivity)
  dsimp only [Function.comp_def] at h ⊢
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  field_simp
  ring

end StandardMapEntropy.Entropy

end
section
namespace StandardMapEntropy
open MeasureTheory Set Filter
open scoped Topology ENNReal BigOperators

lemma grid_rate_derivative_upper (k : ℝ) (n : ℕ) {C : ℝ} (hC : 0≤C)
    (hLip : ∀ z w : ℂ,‖standardDerivativeProduct k (complexProjection z) n-
       standardDerivativeProduct k (complexProjection w) n‖≤C*‖z-w‖)
    (Q : ℕ) (hQ : 0<Q) (hQC : 4*C≤(Q : ℝ)) :
    Entropy.rate area ((standardMap k)^[n]) (gridLabel Q hQ)≤
      Real.log 1000+(∫ z,Real.log ‖standardDerivativeProduct k z n‖ ∂area)+2*C/(Q : ℝ) := by
  classical
  let p := gridLabel Q hQ
  let f := (standardMap k)^[n]
  have hp : Measurable p := measurable_gridLabel Q hQ
  have hf : MeasurePreserving f area area := (measurePreserving_standardMap k).iterate n
  let anchor : Fin (Q*Q+1) → Torus := fun b => if h : ∃ z,p z=b then h.choose else (0,0)
  have hanchor (z : Torus) : p (anchor (p z))=p z := by
    simp only [anchor,dite_eq_left (show ∃ w,p w=p z from ⟨z,rfl⟩)]
    exact (show ∃ w,p w=p z from ⟨z,rfl⟩).choose_spec
  choose S hsize hcover using (fun b => standard_iterate_grid_cover k n hC hLip Q hQ hQC (anchor b))
  have hcardpos (b : Fin (Q*Q+1)) : 0<(S b).card :=
    Finset.card_pos.mpr ⟨p (f (anchor b)),hcover b (anchor b) rfl⟩
  have hlogcard (b : Fin (Q*Q+1)) :
      Real.log ((S b).card : ℝ)≤Real.log 1000+Real.log ‖standardDerivativeProduct k (anchor b) n‖ := by
    have hh := Real.log_le_log (Nat.cast_pos.mpr (hcardpos b)) (hsize b)
    rwa [Real.log_mul (by norm_num : (1000 : ℝ)≠0)
      (ne_of_gt (lt_of_lt_of_le zero_lt_one (standardDerivativeProduct_norm_ge_one k (anchor b) n)))] at hh
  have htransition : Entropy.cond area p (p ∘ f)=Entropy.cond area (p ∘ f) p := by
    unfold Entropy.cond
    rw [Entropy.obs_pair_swap area p (p ∘ f),Entropy.obs_comp_preserving area f hf p hp]
  have hu := Entropy.cond_support_bound area (p ∘ f) p (hp.comp hf.measurable) hp S
    (fun z => hcover (p z) z (hanchor z).symm)
  rw [Entropy.sum_mass_mul_integral area p hp (fun b => Real.log ((S b).card : ℝ))] at hu
  have hi : Integrable (fun z => Real.log 1000+Real.log ‖standardDerivativeProduct k z n‖+2*C/(Q : ℝ)) area :=
    ((integrable_const _).add (integrable_log_standardDerivativeProduct k n)).add (integrable_const _)
  have hpoint (z : Torus) : Real.log ((S (p z)).card : ℝ)≤
      Real.log 1000+Real.log ‖standardDerivativeProduct k z n‖+2*C/(Q : ℝ) := by
    have hh := standard_iterate_grid_log_variation k n hC hLip Q hQ (hanchor z).symm
    exact (hlogcard (p z)).trans (by linarith)
  have hint := integral_mono_of_nonneg (μ:=area) (f:=fun z => Real.log ((S (p z)).card : ℝ))
    (ae_of_all _ (fun z => Real.log_nonneg (by exact_mod_cast (hcardpos (p z))))) hi (ae_of_all _ hpoint)
  have he : (∫ z,Real.log 1000+Real.log ‖standardDerivativeProduct k z n‖+2*C/(Q : ℝ) ∂area)=
      Real.log 1000+(∫ z,Real.log ‖standardDerivativeProduct k z n‖ ∂area)+2*C/(Q : ℝ) := by
    rw [integral_add (f:=fun z : Torus => Real.log 1000+Real.log ‖standardDerivativeProduct k z n‖)
      (g:=fun _ : Torus => 2*C/(Q : ℝ)) ((integrable_const _).add (integrable_log_standardDerivativeProduct k n)) (integrable_const _),
      integral_add (f:=fun _ : Torus => Real.log (1000 : ℝ)) (g:=fun z => Real.log ‖standardDerivativeProduct k z n‖)
        (integrable_const _) (integrable_log_standardDerivativeProduct k n)]
    simp only [integral_const,Measure.real,measure_univ,ENNReal.toReal_one,one_smul]
  rw [he] at hint
  exact (Entropy.rate_le_oneStep area f hf p hp).trans (htransition ▸ hu.trans hint)

lemma eventually_grid_rate_derivative_upper (k : ℝ) (hk : 0≤k) (n : ℕ) :
    ∀ ε : ℝ,0<ε → ∃ Q₀ : ℕ,∀ Q : ℕ,Q₀≤Q → ∀ hQ : 0<Q,
      Entropy.rate area ((standardMap k)^[n]) (gridLabel Q hQ)≤
        Real.log 1000+(∫ z,Real.log ‖standardDerivativeProduct k z n‖ ∂area)+ε := by
  obtain ⟨B,C,hB,hC,hbound,hLip⟩ := standardLift_iterate_control k hk n
  intro ε hε
  obtain ⟨Q₀,hQ₀⟩ := exists_nat_gt (max (4*C) (2*C/ε))
  refine ⟨Q₀,?_⟩
  intro Q hQQ hQ
  have hQQ' : (Q₀ : ℝ)≤Q := by exact_mod_cast hQQ
  have hQC : 4*C≤(Q : ℝ) := (le_max_left _ _).trans (hQ₀.le.trans hQQ')
  have hQε : 2*C/ε≤(Q : ℝ) := (le_max_right _ _).trans (hQ₀.le.trans hQQ')
  have herr : 2*C/(Q : ℝ)≤ε := by
    apply (div_le_iff₀ (Nat.cast_pos.mpr hQ)).mpr
    have hh := (div_le_iff₀ hε).mp hQε
    simpa only [mul_comm] using hh
  exact (grid_rate_derivative_upper k n hC hLip Q hQ hQC).trans (add_le_add le_rfl herr)

lemma metricEntropy_iterate_derivative_upper (k : ℝ) (hk : 0≤k) (n : ℕ) :
    metricEntropy area ((standardMap k)^[n])≤
      ENNReal.ofReal (Real.log 1000+(∫ z,Real.log ‖standardDerivativeProduct k z n‖ ∂area)) :=
  metricEntropy_le_of_grid_rates _ ((measurePreserving_standardMap k).iterate n) _
    (eventually_grid_rate_derivative_upper k hk n)

end StandardMapEntropy

end
end

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_Coding_SanitizedTowerLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace HyperbolicCoding
open MeasureTheory Set Filter StandardMapEntropy.Entropy
open scoped BigOperators ENNReal Topology
variable {X A : Type*} [MeasurableSpace X] [StandardBorelSpace X]
  [MeasurableSpace A] [Fintype A] [DecidableEq A] [MeasurableSingletonClass A] [Nonempty A]

lemma exists_iidCopyTest (μ : Measure X) [IsProbabilityMeasure μ] [NullSingletonClass μ]
    (e : X ≃ᵐ X) (he : MeasurePreserving e μ μ)
    (β : A → ℝ) (hβ : ∀ a,0≤β a) (hβsum : ∑ a,β a=1)
    (hβentropy : 0 < weightEntropy β) {η : ℝ} (hη : 0 < η) :
    Nonempty (IIDCopyTest μ e β η) := by
  obtain ⟨m,t,ht,δ,hδ,hfd⟩ := iid_finite_determination (X:=X) β hβ hβsum hβentropy hη
  exact ⟨⟨m,t,ht,δ,hδ,fun q hq hl hr => hfd μ inferInstance inferInstance e he q hq hl hr⟩⟩

end HyperbolicCoding

end

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_Coding_FullEntropyCopySequence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace HyperbolicCoding
open MeasureTheory Set Filter StandardMapEntropy.Entropy
open scoped BigOperators ENNReal Topology
variable {X A : Type*} [MeasurableSpace X] [StandardBorelSpace X]
  [TopologicalSpace X] [SecondCountableTopology X] [OpensMeasurableSpace X]
  [MeasurableSpace A] [Fintype A] [DecidableEq A] [MeasurableSingletonClass A] [Nonempty A]

omit [StandardBorelSpace X] [TopologicalSpace X] [SecondCountableTopology X]
  [OpensMeasurableSpace X] in
lemma FiniteRateSupremum.upper {μ : Measure X} [IsProbabilityMeasure μ] {f : X → X} {h : ℝ}
    (H : FiniteRateSupremum μ f h)
    {C : Type*} [Fintype C] [Nonempty C] [MeasurableSpace C] [MeasurableSingletonClass C]
    (p : X → C) (hp : Measurable p) : rate μ f p≤h := by
  have hc : Fintype.card C-1+1=Fintype.card C := Nat.sub_add_cancel Fintype.card_pos
  let e : C ≃ Fin (Fintype.card C-1+1) := (Fintype.equivFin C).trans (finCongr hc.symm)
  have he := H.1 (Fintype.card C-1) (e ∘ p) ((measurable_of_finite e).comp hp)
  rwa [rate_equiv] at he

omit [StandardBorelSpace X] [TopologicalSpace X] [SecondCountableTopology X]
  [OpensMeasurableSpace X] [DecidableEq A] [Nonempty A] in
lemma iid_lawClose_prefix (μ : Measure X) (e : X ≃ᵐ X) (p : X → A) (hp : Measurable p)
    (β : A → ℝ) (hβ : ∀ a,0≤β a) (hβsum : ∑ a,β a=1)
    {m n : ℕ} (hmn : m≤n) {δ : ℝ}
    (h : LawClose (μ.map (word e p n))
      (Measure.pi (fun _ : Fin n => finiteWeightLaw β)) δ) :
    LawClose (μ.map (word e p m))
      (Measure.pi (fun _ : Fin m => finiteWeightLaw β)) δ := by
  let : IsProbabilityMeasure (finiteWeightLaw β) := finiteWeightLaw_probability β hβ hβsum
  let ν := Measure.infinitePi (fun _ : ℤ => finiteWeightLaw β)
  have h' : LawClose (μ.map (word e p n))
      (ν.map (word iidShift (fun w : ℤ → A => w 0) n)) δ := by
    simpa only [ν,iid_word_law] using h
  have hh := lawClose_prefix μ ν e iidShift e.measurable iidShift.measurable p
    (fun w : ℤ → A => w 0) hp (measurable_pi_apply 0) hmn h'
  simpa only [ν,iid_word_law] using hh

theorem full_entropy_copy_sequence (μ : Measure X) [IsProbabilityMeasure μ]
    [NullSingletonClass μ] [μ.OuterRegular] (e : X ≃ᵐ X) (he : Ergodic e μ)
    (htotal : ∀ m : ℕ,0 < m → Ergodic (e^[m]) μ)
    (β : A → ℝ) (hβ : ∀ a,0≤β a) (hβsum : ∑ a,β a=1)
    (hβentropy : 0 < weightEntropy β) (H : FiniteRateSupremum μ e (weightEntropy β))
    (zero one : A) (h01 : zero≠one) (η : ℕ → ℝ) (hη : ∀ n,0 < η n) :
    ∃ q : ℕ → X → A,(∀ n,Measurable (q n)) ∧
      (∀ n,μ.real {x | q (n+1) x≠q n x}<η n) ∧
      (∀ n,LawClose (μ.map (word e (q n) n))
        (Measure.pi (fun _ : Fin n => finiteWeightLaw β)) (1/(n+1 : ℝ))) := by
  have hT (n : ℕ) : Nonempty (IIDCopyTest μ e β (η n/2)) :=
    exists_iidCopyTest μ e he.toMeasurePreserving β hβ hβsum hβentropy (half_pos (hη n))
  let T (n : ℕ) : IIDCopyTest μ e β (η n/2) := Classical.choice (hT n)
  obtain ⟨q₀,hq₀⟩ := goodIIDStage_initial_q44 μ e he htotal β hβ hβsum hβentropy H zero one h01 (T 0) 0
  have hnext (n : ℕ) (q : {q : X → A // GoodIIDStage μ e β (T n) n q}) :
      ∃ q' : X → A,GoodIIDStage μ e β (T (n+1)) (n+1) q' ∧
        μ.real {x | q.val x≠q' x}<η n :=
    goodIIDStage_next_q44 μ e he htotal β hβ hβsum hβentropy H zero one h01 (hη n)
      (T n) (T (n+1)) q.property
  let next (n : ℕ) (q : {q : X → A // GoodIIDStage μ e β (T n) n q}) :
      {q' : X → A // GoodIIDStage μ e β (T (n+1)) (n+1) q'} :=
    ⟨Classical.choose (hnext n q),(Classical.choose_spec (hnext n q)).1⟩
  let z : (n : ℕ) → {q : X → A // GoodIIDStage μ e β (T n) n q} :=
    fun n => Nat.rec (motive:=fun j => {q : X → A // GoodIIDStage μ e β (T j) j q})
      ⟨q₀,hq₀⟩ next n
  refine ⟨fun n => (z n).val,fun n => (z n).property.1,?_,?_⟩
  · intro n
    have h := (Classical.choose_spec (hnext n (z n))).2
    have h' : μ.real {x | (z n).val x≠(z (n+1)).val x}<η n := h
    have hs : {x | (z (n+1)).val x≠(z n).val x}=
        {x | (z n).val x≠(z (n+1)).val x} := Set.ext (fun _ => ne_comm)
    rw [hs]
    exact h'
  · intro n
    exact (iid_lawClose_prefix μ e (z n).val (z n).property.1 β hβ hβsum
      (le_max_right _ _) (z n).property.2.1).mono (min_le_right _ _)

end HyperbolicCoding

end
section
namespace HyperbolicCoding
open MeasureTheory Set Filter StandardMapEntropy.Entropy
open scoped BigOperators ENNReal Topology
variable {X Y A : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  [MeasurableSpace A] [Fintype A] [MeasurableSingletonClass A]

omit [Fintype A] [MeasurableSingletonClass A] in
lemma iidShift_integerIterate (n : ℤ) (w : ℤ → A) (i : ℤ) :
    integerIterate iidShift n w i=w (i+n) := by
  cases n with
  | ofNat m => rw [Int.ofNat_eq_natCast,integerIterate_nat,iidShift_iterate]
  | negSucc m =>
    have hn : Int.negSucc m= -((m+1 : ℕ) : ℤ) := by omega
    rw [hn,integerIterate_neg_nat,iidShift_symm_iterate,sub_eq_add_neg]

omit [Fintype A] [MeasurableSingletonClass A] in
lemma iid_orbitName (w : ℤ → A) : orbitName iidShift (fun z : ℤ → A => z 0) w=w := by
  funext i
  exact (iidShift_integerIterate i w 0).trans (by rw [zero_add])

lemma finite_integer_window (s : Finset ℤ) :
    ∃ a : ℤ,∃ N : ℕ,∀ i∈s,0≤ i-a ∧ i-a < (N : ℤ) := by
  let b := s.sup Int.natAbs
  refine ⟨-(b : ℤ),2*b+1,?_⟩
  intro i hi
  have hb : i.natAbs≤b := Finset.le_sup (f:=Int.natAbs) hi
  have hb' : (i.natAbs : ℤ)≤b := by exact_mod_cast hb
  have h1 : -i≤(i.natAbs : ℤ) := by simpa only [Int.natAbs_neg] using (Int.le_natAbs (a:=-i))
  have h2 := (Int.le_natAbs (a:=i))
  constructor <;> omega

lemma orbit_restrict_map_eq_window (μ : Measure X) (e : X ≃ᵐ X)
    (he : MeasurePreserving e μ μ) (p : X → A) (hp : Measurable p)
    (s : Finset ℤ) (a : ℤ) (N : ℕ) (hb : ∀ i∈s,0≤ i-a ∧ i-a < (N : ℤ)) :
    μ.map (s.restrict ∘ orbitName e p)=
      (μ.map (word e p N)).map (fun w : Fin N → A => fun i : s =>
        w ⟨(i.val-a).toNat,by have h := hb i.val i.property; omega⟩) := by
  let W : (Fin N → A) → (s → A) := fun w i =>
    w ⟨(i.val-a).toNat,by have h := hb i.val i.property; omega⟩
  have hW : Measurable W := measurable_of_finite W
  have hpN := word_measurable e e.measurable p hp N
  have hfun : s.restrict ∘ orbitName e p=(W ∘ word e p N) ∘ integerIterate e a := by
    funext x i
    change p (integerIterate e i.val x) = p (e^[((i.val-a).toNat)] (integerIterate e a x))
    rw [←integerIterate_nat,←integerIterate_add]
    have h := hb i.val i.property
    congr 2
    omega
  change μ.map (s.restrict ∘ orbitName e p)=(μ.map (word e p N)).map W
  rw [hfun,←Measure.map_map (hW.comp hpN) (integerIterate_measurable e a),
    (integerIterate_measurePreserving e he a).map_eq,Measure.map_map hW hpN]

lemma lawClose_orbit_restrict_of_word
    (μ : Measure X) (ν : Measure Y) (e : X ≃ᵐ X) (d : Y ≃ᵐ Y)
    (he : MeasurePreserving e μ μ) (hd : MeasurePreserving d ν ν)
    (p : X → A) (q : Y → A) (hp : Measurable p) (hq : Measurable q)
    (s : Finset ℤ) (a : ℤ) (N : ℕ) (hb : ∀ i∈s,0≤ i-a ∧ i-a < (N : ℤ))
    {δ : ℝ} (hl : LawClose (μ.map (word e p N)) (ν.map (word d q N)) δ) :
    LawClose (μ.map (s.restrict ∘ orbitName e p))
      (ν.map (s.restrict ∘ orbitName d q)) δ := by
  rw [orbit_restrict_map_eq_window μ e he p hp s a N hb,
    orbit_restrict_map_eq_window ν d hd q hq s a N hb]
  exact hl.map (measurable_of_finite _)

omit [Fintype A] [MeasurableSingletonClass A] in
lemma restricted_box_lawClose (μ : Measure X) (ν : Measure Y)
    (e : X ≃ᵐ X) (d : Y ≃ᵐ Y) (p : X → A) (q : Y → A)
    (hp : Measurable p) (hq : Measurable q) (s : Finset ℤ)
    (t : ℤ → Set A) (ht : ∀ i,MeasurableSet (t i)) {δ : ℝ}
    (h : LawClose (μ.map (s.restrict ∘ orbitName e p))
      (ν.map (s.restrict ∘ orbitName d q)) δ) :
    |(μ.map (orbitName e p)).real (Set.pi s t)-
      (ν.map (orbitName d q)).real (Set.pi s t)|≤δ := by
  let D : Set (s → A) := Set.pi Set.univ (fun i => t i.val)
  have hD : MeasurableSet D := MeasurableSet.pi Set.countable_univ (fun i _ => ht i.val)
  have hpre : (s.restrict : (ℤ → A) → (s → A)) ⁻¹' D=Set.pi s t := by
    ext w
    simp only [D,mem_preimage,Set.mem_pi,mem_univ,true_implies,Finset.mem_coe,Finset.restrict]
    exact ⟨fun h i hi => h ⟨i,hi⟩,fun h i => h i i.property⟩
  have hr : Measurable (s.restrict : (ℤ → A) → (s → A)) := measurable_restrict (s : Set ℤ)
  have h1 : (μ.map (s.restrict ∘ orbitName e p)).real D=
      (μ.map (orbitName e p)).real (Set.pi s t) := by
    simp only [Measure.real]
    rw [←Measure.map_map hr (measurable_orbitName e hp),Measure.map_apply hr hD,hpre]
  have h2 : (ν.map (s.restrict ∘ orbitName d q)).real D=
      (ν.map (orbitName d q)).real (Set.pi s t) := by
    simp only [Measure.real]
    rw [←Measure.map_map hr (measurable_orbitName d hq),Measure.map_apply hr hD,hpre]
  simpa only [h1,h2] using h D hD

theorem iid_law_of_growing_forward_words [Nonempty A]
    (μ : Measure X) [IsProbabilityMeasure μ] (e : X ≃ᵐ X)
    (he : MeasurePreserving e μ μ) (q : ℕ → X → A) (hq : ∀ n,Measurable (q n))
    (p : X → A) (hp : Measurable p)
    (hlim : ∀ᵐ x ∂μ,∀ᶠ n : ℕ in atTop,q n x=p x)
    (β : Measure A) [IsProbabilityMeasure β] (ε : ℕ → ℝ)
    (hε : Tendsto ε atTop (𝓝 0))
    (hlaw : ∀ n,LawClose (μ.map (word e (q n) n))
      (Measure.pi (fun _ : Fin n => β)) (ε n)) :
    MeasurePreserving (orbitName e p) μ (Measure.infinitePi (fun _ : ℤ => β)) := by
  apply iid_law_of_partition_limit e he hq hp hlim β
  intro s t ht
  let ν := Measure.infinitePi (fun _ : ℤ => β)
  obtain ⟨a,N,hN⟩ := finite_integer_window s
  have htarget : (ν.map (orbitName iidShift (fun w : ℤ → A => w 0))).real (Set.pi s t)=
      (∏ i∈s,β (t i)).toReal := by
    rw [show orbitName iidShift (fun w : ℤ → A => w 0)=id from funext iid_orbitName,
      Measure.map_id]
    exact congrArg ENNReal.toReal (Measure.infinitePi_pi (fun _ : ℤ => β) (fun i _ => ht i))
  have hbound : ∀ᶠ n : ℕ in atTop,
      |(μ.map (orbitName e (q n))).real (Set.pi s t)-(∏ i∈s,β (t i)).toReal|≤ε n := by
    filter_upwards [eventually_ge_atTop N] with n hn
    have hb : ∀ i∈s,0≤ i-a ∧ i-a < (n : ℤ) := by
      intro i hi
      have h := hN i hi
      exact ⟨h.1,lt_of_lt_of_le h.2 (by exact_mod_cast hn)⟩
    have hl : LawClose (μ.map (word e (q n) n))
        (ν.map (word iidShift (fun w : ℤ → A => w 0) n)) (ε n) := by
      simpa only [ν,iid_word_law] using hlaw n
    have hr := lawClose_orbit_restrict_of_word μ ν e iidShift he (iidShift_preserving β)
      (q n) (fun w : ℤ → A => w 0) (hq n) (measurable_pi_apply 0) s a n hb hl
    have hh := restricted_box_lawClose μ ν e iidShift (q n) (fun w : ℤ → A => w 0)
      (hq n) (measurable_pi_apply 0) s t ht hr
    rwa [htarget] at hh
  apply tendsto_iff_dist_tendsto_zero.mpr
  simp only [Real.dist_eq]
  exact squeeze_zero' (Eventually.of_forall (fun _ => abs_nonneg _)) hbound hε

end HyperbolicCoding

end
section
namespace HyperbolicCoding
open MeasureTheory Set Filter StandardMapEntropy.Entropy
open scoped BigOperators ENNReal NNReal Topology
variable {X A : Type*} [MeasurableSpace X]
  [MeasurableSpace A] [Fintype A] [MeasurableSingletonClass A]

omit [Fintype A] [MeasurableSingletonClass A] in
lemma word_law_of_iid_factor (μ : Measure X) (e : X ≃ᵐ X) (p : X → A)
    (_hp : Measurable p) (β : Measure A) [IsProbabilityMeasure β]
    (hcode : MeasurePreserving (orbitName e p) μ (Measure.infinitePi (fun _ : ℤ => β)))
    (n : ℕ) : μ.map (word e p n)=Measure.pi (fun _ : Fin n => β) := by
  have heq : word iidShift (fun w : ℤ → A => w 0) n ∘ orbitName e p=word e p n := by
    funext x i
    rw [Function.comp_apply,iid_word_eq]
    exact congrArg p (integerIterate_nat e i.val x)
  have hm := congrArg (fun ν => ν.map (word iidShift (fun w : ℤ → A => w 0) n)) hcode.map_eq
  rw [Measure.map_map (word_measurable iidShift iidShift.measurable _ (measurable_pi_apply 0) n)
    hcode.measurable,heq,iid_word_law] at hm
  exact hm

lemma rate_of_iid_factor [DecidableEq A] (μ : Measure X) [IsProbabilityMeasure μ]
    (e : X ≃ᵐ X) (he : MeasurePreserving e μ μ) (p : X → A) (hp : Measurable p)
    (β : A → ℝ) (hβ : ∀ a,0≤β a) (hβsum : ∑ a,β a=1)
    (hcode : MeasurePreserving (orbitName e p) μ
      (Measure.infinitePi (fun _ : ℤ => finiteWeightLaw β))) :
    rate μ e p=weightEntropy β := by
  let : IsProbabilityMeasure (finiteWeightLaw β) := finiteWeightLaw_probability β hβ hβsum
  have hword (n : ℕ) : obs μ (word e p n)=(n : ℝ)*weightEntropy β := by
    have hmass : mass μ (word e p n)=productWordWeight β n := by
      funext w
      change μ.real ((word e p n) ⁻¹' {w})=_
      rw [←map_measureReal_apply (word_measurable e e.measurable p hp n) (measurableSet_singleton w),
        word_law_of_iid_factor μ e p hp (finiteWeightLaw β) hcode,
        Measure.real,Measure.pi_singleton]
      simp only [finiteWeightLaw_singleton,ENNReal.toReal_prod,ENNReal.toReal_ofReal (hβ _),
        productWordWeight]
    rw [obs,hmass]
    exact shannon_productWordWeight β hβsum n
  apply tendsto_nhds_unique (rate_tendsto μ e he p hp)
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_gt_atTop 0] with n hn
  rw [hword,mul_div_cancel_left₀ _ (Nat.cast_ne_zero.mpr hn.ne')]

omit [MeasurableSpace A] [Fintype A] [MeasurableSingletonClass A] in
lemma geometric_repainting_summable (μ : Measure X) [IsFiniteMeasure μ]
    (q : ℕ → X → A)
    (h : ∀ n,μ.real {x | q (n+1) x≠q n x}<((1/2 : ℝ≥0)^n : ℝ)) :
    (∑' n : ℕ,μ {x | q (n+1) x≠q n x})≠⊤ := by
  have hs : (∑' n : ℕ,(((1/2 : ℝ≥0)^n) : ℝ≥0∞))≠⊤ := by
    apply ENNReal.tsum_coe_ne_top_iff_summable_coe.mpr
    simpa only [NNReal.coe_pow,NNReal.coe_div,NNReal.coe_one,NNReal.coe_ofNat] using
      (summable_geometric_of_lt_one (show (0 : ℝ)≤1/2 by norm_num) (by norm_num : (1/2 : ℝ) < 1))
  apply ne_top_of_le_ne_top hs
  apply ENNReal.tsum_le_tsum
  intro n
  apply (ENNReal.toReal_le_toReal (measure_ne_top μ _) (by simp)).mp
  simpa only [Measure.real,ENNReal.toReal_pow,ENNReal.coe_toReal,NNReal.coe_pow] using (h n).le

variable [StandardBorelSpace X] [TopologicalSpace X] [SecondCountableTopology X]
  [OpensMeasurableSpace X] [DecidableEq A] [Nonempty A]

theorem full_entropy_iid_factor (μ : Measure X) [IsProbabilityMeasure μ]
    [NullSingletonClass μ] [μ.OuterRegular] (e : X ≃ᵐ X) (he : Ergodic e μ)
    (htotal : ∀ m : ℕ,0 < m → Ergodic (e^[m]) μ)
    (β : A → ℝ) (hβ : ∀ a,0≤β a) (hβsum : ∑ a,β a=1)
    (hβentropy : 0 < weightEntropy β) (H : FiniteRateSupremum μ e (weightEntropy β))
    (zero one : A) (h01 : zero≠one) :
    ∃ p : X → A,Measurable p ∧
      MeasurePreserving (orbitName e p) μ (Measure.infinitePi (fun _ : ℤ => finiteWeightLaw β)) ∧
      rate μ e p=weightEntropy β ∧
      (∀ x,orbitName e p (e x)=fun i => orbitName e p x (i+1)) ∧
      (∀ r : ℕ,∀ α : X → Fin (r+1),Measurable α →
        rate μ e (fun x => (p x,α x))=weightEntropy β) := by
  let : IsProbabilityMeasure (finiteWeightLaw β) := finiteWeightLaw_probability β hβ hβsum
  obtain ⟨q,hq,hpaint,hlaw⟩ := full_entropy_copy_sequence μ e he htotal β hβ hβsum hβentropy
    H zero one h01 (fun n => ((1/2 : ℝ≥0)^n : ℝ)) (fun _ => by positivity)
  obtain ⟨p,hp,hlim⟩ := exists_partition_limit μ q hq (geometric_repainting_summable μ q hpaint)
  have hcode := iid_law_of_growing_forward_words μ e he.toMeasurePreserving q hq p hp hlim
    (finiteWeightLaw β) (fun n => 1/(n+1 : ℝ)) tendsto_one_div_add_atTop_nhds_zero_nat hlaw
  have hrate := rate_of_iid_factor μ e he.toMeasurePreserving p hp β hβ hβsum hcode
  refine ⟨p,hp,hcode,hrate,fun x => orbitName_shift e p x,?_⟩
  intro r α hα
  apply le_antisymm (H.upper (fun x => (p x,α x)) (hp.prodMk hα))
  rw [←hrate]
  exact rate_pair_ge_left μ e he.toMeasurePreserving p α hp hα

end HyperbolicCoding

end
section
namespace StandardMapEntropy.Entropy
open MeasureTheory Set Filter
open scoped BigOperators ENNReal Topology

lemma shannon_weighted_le {A : Type*} [Fintype A]
    (p q : A → ℝ) (hp : ∀ a,0 ≤ p a) (hq : ∀ a,0 ≤ q a)
    (hps : ∑ a,p a=1) (hqs : ∑ a,q a=1)
    {c : ℝ} (hc : 0 < c) (hdom : ∀ a,c*p a ≤ q a) :
    c*shannon p ≤ shannon q := by
  have hs (a : A) (ha : p a≠0) : q a≠0 := by
    have hp' : 0 < p a := lt_of_le_of_ne (hp a) (Ne.symm ha)
    exact ne_of_gt ((mul_pos hc hp').trans_le (hdom a))
  have hh := mul_le_mul_of_nonneg_left
    (shannon_le_cross p q hp hq hs (by rw [hps,hqs])) hc.le
  apply hh.trans
  rw [shannon,←Finset.sum_neg_distrib,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro a _
  have hq1 : q a ≤ 1 := (Finset.single_le_sum (fun b _ => hq b) (Finset.mem_univ a)).trans_eq hqs
  have hl : Real.log (q a) ≤ 0 := Real.log_nonpos (hq a) hq1
  have hh := mul_le_mul_of_nonpos_right (hdom a) hl
  rw [Real.negMulLog]
  nlinarith

variable {X A : Type*} [MeasurableSpace X] [MeasurableSpace A]
  [Fintype A] [MeasurableSingletonClass A]
lemma obs_weighted_le (μ ν : Measure X) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {c : ℝ} (hc : 0 < c) (hdom : ∀ E : Set X,c*ν.real E ≤ μ.real E)
    (p : X → A) (hp : Measurable p) : c*obs ν p ≤ obs μ p :=
  shannon_weighted_le (mass ν p) (mass μ p) (mass_nonneg _ _) (mass_nonneg _ _)
    (by simpa only [measure_univ,ENNReal.toReal_one] using mass_sum ν p hp)
    (by simpa only [measure_univ,ENNReal.toReal_one] using mass_sum μ p hp) hc (fun a => hdom _)

lemma rate_weighted_le (μ ν : Measure X) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {c : ℝ} (hc : 0 < c) (hdom : ∀ E : Set X,c*ν.real E ≤ μ.real E)
    (f : X → X) (hμ : MeasurePreserving f μ μ) (hν : MeasurePreserving f ν ν)
    (p : X → A) (hp : Measurable p) : c*rate ν f p ≤ rate μ f p := by
  apply le_of_tendsto_of_tendsto
    ((rate_tendsto ν f hν p hp).const_mul c) (rate_tendsto μ f hμ p hp)
  apply Filter.Eventually.of_forall
  intro n
  have hh := div_le_div_of_nonneg_right
    (obs_weighted_le μ ν hc hdom (word f p n) (word_measurable f hμ.measurable p hp n))
    (Nat.cast_nonneg n)
  simpa only [mul_div_assoc] using hh
end StandardMapEntropy.Entropy

namespace StandardMapEntropy
open MeasureTheory Set Filter HyperbolicCoding
open scoped BigOperators ENNReal Topology
lemma area_weight_normalized (E : Set Torus) (hE : 0 < area E) (B : Set Torus) :
    area.real E*(normalizedArea E).real B ≤ area.real B := by
  have hc : area.real E≠0 := (ENNReal.toReal_pos hE.ne' (measure_ne_top area E)).ne'
  have he : area.real E*(normalizedArea E).real B=(area.restrict E).real B := by
    simp only [normalizedArea,Measure.real,Measure.smul_apply,smul_eq_mul,
      ENNReal.toReal_mul,ENNReal.toReal_inv]
    change area.real E*((area.real E)⁻¹*(area.restrict E).real B)=_
    rw [←mul_assoc,mul_inv_cancel₀ hc,one_mul]
    rfl
  rw [he]
  exact ENNReal.toReal_mono (measure_ne_top area B) (Measure.restrict_le_self B)

lemma restricted_finite_rate_upper {A : Type*} [MeasurableSpace A]
    [Fintype A] [MeasurableSingletonClass A]
    (k : ℝ) (hk : 0 ≤ k) (n : ℕ) (E : Set Torus) (hE : 0 < area E)
    (hinv : MeasurePreserving ((standardMap k)^[n]) (normalizedArea E) (normalizedArea E))
    (p : Torus → A) (hp : Measurable p) :
    Entropy.rate (normalizedArea E) ((standardMap k)^[n]) p ≤
      (Real.log 1000+(∫ z,Real.log ‖standardDerivativeProduct k z n‖ ∂area))/(area.real E) := by
  let := normalizedArea_probability hE
  have hc : 0 < area.real E := ENNReal.toReal_pos hE.ne' (measure_ne_top area E)
  have hweighted := Entropy.rate_weighted_le area (normalizedArea E) hc
    (area_weight_normalized E hE) _ ((measurePreserving_standardMap k).iterate n) hinv p hp
  have hu := (finite_rate_le_metricEntropy area _ ((measurePreserving_standardMap k).iterate n) p hp).trans
    (metricEntropy_iterate_derivative_upper k hk n)
  have hnonneg : 0 ≤ Real.log 1000+(∫ z,Real.log ‖standardDerivativeProduct k z n‖ ∂area) := by
    apply add_nonneg (Real.log_nonneg (by norm_num))
    apply integral_nonneg
    intro z
    exact Real.log_nonneg (standardDerivativeProduct_norm_ge_one k z n)
  have hh := (ENNReal.ofReal_le_ofReal_iff hnonneg).mp hu
  apply (le_div_iff₀ hc).mpr
  simpa only [mul_comm] using hweighted.trans hh
end StandardMapEntropy

end
section
namespace HyperbolicCoding
open MeasureTheory Set Filter StandardMapEntropy.Entropy
open scoped BigOperators ENNReal Topology
variable {X : Type*} [MeasurableSpace X]

theorem exists_finiteRateSupremum (μ : Measure X) (f : X → X)
    (b : ℝ) (hb : ∀ r : ℕ,∀ p : X → Fin (r+1),Measurable p → rate μ f p ≤ b) :
    ∃ h : ℝ,FiniteRateSupremum μ f h ∧ h ≤ b := by
  let S : Set ℝ := {v | ∃ r : ℕ,∃ p : X → Fin (r+1),Measurable p ∧ v=rate μ f p}
  have hne : S.Nonempty := ⟨rate μ f (fun _ => (0 : Fin 1)),0,fun _ => 0,measurable_const,rfl⟩
  have hbd : BddAbove S := ⟨b,by rintro v ⟨r,p,hp,rfl⟩; exact hb r p hp⟩
  refine ⟨sSup S,⟨?_,?_⟩,csSup_le hne (by rintro v ⟨r,p,hp,rfl⟩; exact hb r p hp)⟩
  · intro r p hp
    exact le_csSup hbd ⟨r,p,hp,rfl⟩
  · intro ε hε
    obtain ⟨v,hv,hlt⟩ := exists_lt_of_lt_csSup hne (show sSup S-ε < sSup S by linarith)
    obtain ⟨r,p,hp,rfl⟩ := hv
    exact ⟨r,p,hp,hlt⟩
end HyperbolicCoding
end

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_Coding_PositiveWeakBernoulliRate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace HyperbolicCoding
open MeasureTheory Set Filter StandardMapEntropy.Entropy
open scoped BigOperators ENNReal Topology
variable {X A : Type*} [MeasurableSpace X] [MeasurableSpace A]
  [Fintype A] [MeasurableSingletonClass A] [Nonempty A]

lemma weakBernoulli_zero_rate_diagonal (μ : Measure X) [IsProbabilityMeasure μ]
    (e : X ≃ᵐ X) (he : MeasurePreserving e μ μ) (p : X → A) (hp : Measurable p)
    (hwb : WeakBernoulliProcess μ e p) (hz : rate μ e p=0) :
    ∀ ε : ℝ,0 < ε → LawClose (μ.map (fun x => (p x,p x))) ((μ.map p).prod (μ.map p)) ε := by
  have hf := tailObservable_self_of_rate_zero μ e he p hp hz
  have hb := hf.reverse μ e he p p hp hp
  intro ε hε
  obtain ⟨n,hn⟩ := (hwb ε hε).exists
  obtain ⟨F,hF,hFeq⟩ := hf n
  obtain ⟨B,hB,hBeq⟩ := hb n
  have hh := hn.map (hB.prodMap hF)
  have hPast : (μ.map (tailName e.symm p 0)).map B=μ.map p := by
    rw [←stationary_tail_law μ (he.symm e) hp n,
      Measure.map_map hB (measurable_tailName e.symm.measurable hp n)]
    exact Measure.map_congr hBeq.symm
  have hFuture : (μ.map (tailName e p 0)).map F=μ.map p := by
    rw [←stationary_tail_law μ he hp n,
      Measure.map_map hF (measurable_tailName e.measurable hp n)]
    exact Measure.map_congr hFeq.symm
  have hJoint : (μ.map (remotePair e e.symm p n)).map (Prod.map B F)=μ.map (fun x => (p x,p x)) := by
    rw [Measure.map_map (hB.prodMap hF) (measurable_remotePair e.measurable e.symm.measurable hp n)]
    apply Measure.map_congr
    filter_upwards [hBeq,hFeq] with x hx hy
    exact Prod.ext hx.symm hy.symm
  rw [hJoint,remoteProductLaw,←Measure.map_prod_map _ _ hB hF,hPast,hFuture] at hh
  exact hh

lemma weakBernoulli_zero_rate_constant (μ : Measure X) [IsProbabilityMeasure μ]
    (e : X ≃ᵐ X) (he : MeasurePreserving e μ μ) (p : X → A) (hp : Measurable p)
    (hwb : WeakBernoulliProcess μ e p) (hz : rate μ e p=0) :
    ∃ a : A,∀ᵐ x ∂μ,p x=a := by
  classical
  have hmass (a : A) : mass μ p a=0 ∨ mass μ p a=1 := by
    have heq : mass μ p a-mass μ p a*mass μ p a=0 := by
      apply abs_eq_zero.mp
      apply le_antisymm ?_ (abs_nonneg _)
      apply le_of_forall_pos_le_add
      intro ε hε
      simp only [zero_add]
      have hh := weakBernoulli_zero_rate_diagonal μ e he p hp hwb hz (ε/2) (half_pos hε)
        ({a} ×ˢ {a}) ((measurableSet_singleton a).prod (measurableSet_singleton a))
      have hdiag : (fun x => (p x,p x)) ⁻¹' ({a} ×ˢ {a})=p ⁻¹' {a} := by
        ext x
        simp
      rw [Measure.real,Measure.map_apply (hp.prodMk hp)
        ((measurableSet_singleton a).prod (measurableSet_singleton a)),hdiag] at hh
      have hprod : ((μ.map p).prod (μ.map p)).real ({a} ×ˢ {a})=mass μ p a*mass μ p a := by
        simp only [Measure.real,Measure.prod_prod,ENNReal.toReal_mul,
          Measure.map_apply hp (measurableSet_singleton a),mass]
      rw [hprod] at hh
      exact hh.trans (by linarith)
    rcases mul_eq_zero.mp (show mass μ p a*(1-mass μ p a)=0 by nlinarith) with h | h
    · exact Or.inl h
    · exact Or.inr (by linarith)
  have hs : ∑ a,mass μ p a=1 := by
    simpa only [measure_univ,ENNReal.toReal_one] using mass_sum μ p hp
  have hex : ∃ a,mass μ p a=1 := by
    by_contra! h
    have hz : ∀ a,mass μ p a=0 := fun a => (hmass a).resolve_right (h a)
    simp only [hz,Finset.sum_const_zero] at hs
    norm_num at hs
  obtain ⟨a,ha⟩ := hex
  refine ⟨a,?_⟩
  have hm : μ (p ⁻¹' {a})=1 := by
    rw [←ENNReal.ofReal_toReal (measure_ne_top μ _)]
    change ENNReal.ofReal (mass μ p a)=1
    rw [ha,ENNReal.ofReal_one]
  exact (ae_iff_prob_eq_one (measurableSet_setOfPred.mp (measurableSet_eq_fun hp measurable_const))).mpr hm

theorem separating_weakBernoulli_positive_rate (μ : Measure X) [IsProbabilityMeasure μ]
    [NullSingletonClass μ] (e : X ≃ᵐ X) (he : MeasurePreserving e μ μ)
    (α : ℕ → ℕ → X → Bool) (hα : ∀ i j,Measurable (α i j))
    (hsep : Function.Injective (fun x => fun i j => α i j x))
    (hwb : ∀ M,WeakBernoulliProcess μ e (joinedBinary α M)) :
    ∃ M : ℕ,0 < rate μ e (joinedBinary α M) := by
  by_contra! h
  have hz (M : ℕ) : rate μ e (joinedBinary α M)=0 :=
    le_antisymm (h M) (rate_nonneg μ e he _ (measurable_joinedBinary hα M))
  choose a ha using fun M => weakBernoulli_zero_rate_constant μ e he
    (joinedBinary α M) (measurable_joinedBinary hα M) (hwb M) (hz M)
  have hall : ∀ᵐ x ∂μ,∀ M,joinedBinary α M x=a M := ae_all_iff.mpr ha
  obtain ⟨x,hx⟩ := hall.exists
  have hone : ∀ᵐ y ∂μ,y=x := by
    filter_upwards [hall] with y hy
    apply hsep
    funext i j
    let M := max i j+1
    have hij : (⟨i,by dsimp [M]; omega⟩,⟨j,by dsimp [M]; omega⟩) ∈
        (Set.univ : Set (Fin M × Fin M)) := mem_univ _
    have hh := congrFun ((hy M).trans (hx M).symm)
      (⟨i,by dsimp [M]; omega⟩,⟨j,by dsimp [M]; omega⟩)
    exact hh
  have hset : ({x} : Set X)=ᵐ[μ]univ := by
    filter_upwards [hone] with y hy
    change (y=x)=True
    simp only [hy,eq_self]
  have hm := measure_congr hset
  exact zero_ne_one (by simpa only [measure_singleton,measure_univ] using hm)
end HyperbolicCoding

end
section
namespace HyperbolicCoding
open MeasureTheory Set Filter StandardMapEntropy.Entropy
open scoped BigOperators ENNReal Topology

lemma weightEntropy_eq_shannon {A : Type*} [Fintype A] (p : A → ℝ) :
    weightEntropy p=shannon p := by
  unfold weightEntropy shannon
  apply Finset.sum_congr rfl
  intro a _
  rw [Real.negMulLog]
  ring

lemma entropyPath_nonneg (n : ℕ) {t : ℝ} (ht : t∈Icc (0 : ℝ) 1) (a : Fin (n+2)) :
    0 ≤ entropyPath n t a := by
  unfold entropyPath
  exact add_nonneg (mul_nonneg (sub_nonneg.mpr ht.2) (by split_ifs <;> norm_num))
    (div_nonneg ht.1 (by positivity))

lemma entropyPath_sum (n : ℕ) (t : ℝ) : ∑ a,entropyPath n t a=1 := by
  have hc : (n+2 : ℝ)≠0 := ne_of_gt (by positivity)
  simp only [entropyPath,Finset.sum_add_distrib,←Finset.mul_sum,
    Finset.sum_ite_eq',Finset.mem_univ,ite_true,mul_one,Finset.sum_const,
    Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_add,Nat.cast_ofNat]
  field_simp
  ring

lemma entropyPath_continuous (n : ℕ) : Continuous (fun t => weightEntropy (entropyPath n t)) := by
  simp_rw [weightEntropy_eq_shannon]
  apply continuous_shannon.comp
  apply continuous_pi
  intro a
  unfold entropyPath
  fun_prop

lemma entropyPath_zero (n : ℕ) : weightEntropy (entropyPath n 0)=0 := by
  unfold weightEntropy entropyPath
  simp only [sub_zero,mul_ite,mul_one,mul_zero,zero_div,add_zero]
  apply Finset.sum_eq_zero
  intro a _
  split_ifs <;> simp

lemma entropyPath_one (n : ℕ) : weightEntropy (entropyPath n 1)=Real.log (n+2 : ℝ) := by
  have hc : (n+2 : ℝ)≠0 := ne_of_gt (by positivity)
  unfold weightEntropy entropyPath
  simp only [sub_self,zero_mul,zero_add,one_div,Real.log_inv,neg_neg,Finset.sum_const,
    Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_add,Nat.cast_ofNat]
  rw [←mul_assoc,mul_inv_cancel₀ hc,one_mul]

theorem exists_finite_weight_entropy (h : ℝ) (hh : 0 ≤ h) :
    ∃ n : ℕ,∃ β : Fin (n+2) → ℝ,(∀ a,0 ≤ β a) ∧ (∑ a,β a=1) ∧ weightEntropy β=h := by
  obtain ⟨n,hn⟩ := exists_nat_gt (Real.exp h)
  have hn2 : Real.exp h < (n+2 : ℝ) := by linarith
  have hl : h < Real.log (n+2 : ℝ) := by
    simpa only [Real.log_exp] using Real.log_lt_log (Real.exp_pos h) hn2
  have him := intermediate_value_Icc (show (0 : ℝ) ≤ 1 by norm_num)
    (entropyPath_continuous n).continuousOn
  have hmem : h∈Icc (weightEntropy (entropyPath n 0)) (weightEntropy (entropyPath n 1)) := by
    rw [entropyPath_zero,entropyPath_one]
    exact ⟨hh,hl.le⟩
  obtain ⟨t,ht,heq⟩ := him hmem
  exact ⟨n,entropyPath n t,entropyPath_nonneg n ht,entropyPath_sum n t,heq⟩
end HyperbolicCoding

end
section
namespace StandardMapEntropy
open MeasureTheory Set Filter HyperbolicCoding Entropy
open scoped BigOperators ENNReal Topology

lemma normalizedArea_nullSingleton (E : Set Torus) : NullSingletonClass (normalizedArea E) := by
  have : NullSingletonClass area := by unfold area; infer_instance
  constructor
  intro z
  exact normalizedArea_absolutelyContinuous E (measure_singleton z)

theorem actual_return_full_entropy_iid_factor_q44_oai (k : ℝ) (hk : 0 ≤ k) (N : ℕ)
    (E : Set Torus) (hE : 0 < area E)
    (htotal : ∀ m : ℕ,0 < m → Ergodic (((standardMap k)^[N])^[m]) (normalizedArea E))
    (α : ℕ → ℕ → Torus → Bool) (hα : ∀ i j,Measurable (α i j))
    (hsep : Function.Injective (fun z => fun i j => α i j z))
    (hwb : ∀ M : ℕ,WeakBernoulliProcess (normalizedArea E)
      (iterateEquiv (standardMap_measurableEquiv k) N) (joinedBinary α M)) :
    ∃ n : ℕ,∃ β : Fin (n+2) → ℝ,∃ p : Torus → Fin (n+2),
      (∀ a,0 ≤ β a) ∧ (∑ a,β a=1) ∧ 0 < weightEntropy β ∧ Measurable p ∧
      FiniteRateSupremum (normalizedArea E) ((standardMap k)^[N]) (weightEntropy β) ∧
      MeasurePreserving (orbitName (iterateEquiv (standardMap_measurableEquiv k) N) p)
        (normalizedArea E) (Measure.infinitePi (fun _ : ℤ => finiteWeightLaw β)) ∧
      rate (normalizedArea E) ((standardMap k)^[N]) p=weightEntropy β ∧
      (∀ z,orbitName (iterateEquiv (standardMap_measurableEquiv k) N) p ((standardMap k)^[N] z)=
        fun i => orbitName (iterateEquiv (standardMap_measurableEquiv k) N) p z (i+1)) ∧
      (∀ r : ℕ,∀ γ : Torus → Fin (r+1),Measurable γ →
        rate (normalizedArea E) ((standardMap k)^[N]) (fun z => (p z,γ z))=weightEntropy β) := by
  let := normalizedArea_probability hE
  let := normalizedArea_nullSingleton E
  let e := iterateEquiv (standardMap_measurableEquiv k) N
  have heq : (e : Torus → Torus)=(standardMap k)^[N] := funext (iterateEquiv_apply _ N)
  have he : Ergodic e (normalizedArea E) := by
    rw [heq]
    simpa only [Function.iterate_one] using htotal 1 (by omega)
  have het : ∀ m : ℕ,0 < m → Ergodic (e^[m]) (normalizedArea E) := by
    simpa only [heq] using htotal
  obtain ⟨h,H,_hbound⟩ := exists_finiteRateSupremum (normalizedArea E) ((standardMap k)^[N])
    ((Real.log 1000+(∫ z,Real.log ‖standardDerivativeProduct k z N‖ ∂area))/area.real E)
    (fun r p hp => restricted_finite_rate_upper k hk N E hE
      (by simpa only [heq] using he.toMeasurePreserving) p hp)
  have H' : FiniteRateSupremum (normalizedArea E) e h := by simpa only [heq] using H
  obtain ⟨M,hM⟩ := separating_weakBernoulli_positive_rate (normalizedArea E) e
    he.toMeasurePreserving α hα hsep hwb
  have hh : 0 < h := hM.trans_le (H'.upper _ (measurable_joinedBinary hα M))
  obtain ⟨n,β,hβ,hβsum,hβentropy⟩ := exists_finite_weight_entropy h hh.le
  have hpos : 0 < weightEntropy β := hβentropy.symm ▸ hh
  have Hβ : FiniteRateSupremum (normalizedArea E) e (weightEntropy β) := hβentropy.symm ▸ H'
  obtain ⟨p,hp,hcode,hr,hshift,hjoint⟩ := full_entropy_iid_factor (normalizedArea E) e he het
    β hβ hβsum hpos Hβ (⟨0,by omega⟩ : Fin (n+2)) (⟨1,by omega⟩ : Fin (n+2))
    (by intro h; have hv := congrArg Fin.val h; simp only at hv; omega)
  refine ⟨n,β,p,hβ,hβsum,hpos,hp,?_,hcode,?_,?_,?_⟩
  · simpa only [heq] using Hβ
  · simpa only [heq] using hr
  · simpa only [heq] using hshift
  · simpa only [heq] using hjoint
end StandardMapEntropy

end

end OAI
end

theorem solution : type_of% @OAI.StandardMapEntropy.actual_return_full_entropy_iid_factor_q44_oai := @OAI.StandardMapEntropy.actual_return_full_entropy_iid_factor_q44_oai
