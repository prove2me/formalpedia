-- Prove2me | solution 1 for OAI.StandardMapEntropy.bandMoment_order_q44
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T12:39:31.862831+00:00
-- url     : https://prove2.me/submissions/eb9ab3de-0b8e-4cf8-ad7e-19bebe5b5784

import Mathlib
import Definitions.Def_OAIQ44C002

section
-- module Solutions.OAIQ44_CM.StandardMap_SmoothCap
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter
open scoped Interval Topology
namespace StandardMapEntropy
lemma capSlope_contDiff : ContDiff ℝ 2 capSlope := by unfold capSlope; fun_prop
lemma capSlope_continuous : Continuous capSlope := capSlope_contDiff.continuous
lemma capSlope_bounds (u : ℝ) : 0≤ capSlope u ∧ capSlope u≤1 := by
  unfold capSlope
  constructor <;> linarith [Real.smoothTransition.le_one (10000*u-1),Real.smoothTransition.nonneg (10000*u-1)]
lemma capSlope_one {u : ℝ} (hu : u≤1/10000) : capSlope u=1 := by
  unfold capSlope
  rw [Real.smoothTransition.zero_of_nonpos (by linarith)]; ring
lemma capSlope_zero {u : ℝ} (hu : 1/5000≤ u) : capSlope u=0 := by
  unfold capSlope
  rw [Real.smoothTransition.one_of_one_le (by linarith)]; ring
lemma capPrimitive_hasDerivAt (u : ℝ) : HasDerivAt capPrimitive (capSlope u) u := by
  exact intervalIntegral.integral_hasDerivAt_right (capSlope_continuous.intervalIntegrable 0 u)
    (capSlope_continuous.stronglyMeasurableAtFilter volume (𝓝 u)) capSlope_continuous.continuousAt
lemma capPrimitive_deriv : deriv capPrimitive=capSlope := funext (fun u => (capPrimitive_hasDerivAt u).deriv)
lemma capPrimitive_contDiff : ContDiff ℝ 2 capPrimitive := by
  suffices ContDiff ℝ ((1 : WithTop ℕ∞)+1) capPrimitive by (convert this using 1; norm_num)
  apply contDiff_succ_iff_deriv.mpr
  refine ⟨fun u => (capPrimitive_hasDerivAt u).differentiableAt,?_,?_⟩
  · norm_num
  · rw [capPrimitive_deriv]
    exact capSlope_contDiff.of_le (by norm_num)
lemma capPrimitive_monotone : Monotone capPrimitive := by
  intro x y hxy
  have he := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (capSlope_continuous.intervalIntegrable 0 x) (capSlope_continuous.intervalIntegrable x y)
  have h0 := intervalIntegral.integral_nonneg (μ := volume) hxy (fun t _ => (capSlope_bounds t).1)
  change (∫ t in (0:ℝ)..x,capSlope t)≤(∫ t in (0:ℝ)..y,capSlope t)
  linarith
lemma capPrimitive_linear {u : ℝ} (hu : u≤1/10000) : capPrimitive u=u := by
  unfold capPrimitive
  have he : (∫ t in (0:ℝ)..u,capSlope t)=(∫ _t in (0:ℝ)..u,(1:ℝ)) := by
    apply intervalIntegral.integral_congr
    intro t ht
    apply capSlope_one
    rw [mem_uIcc] at ht
    rcases ht with ⟨h0,h1⟩|⟨h0,h1⟩ <;> linarith
  rw [he,intervalIntegral.integral_const]
  simp
lemma capPrimitive_constant {u : ℝ} (hu : 1/5000≤ u) : capPrimitive u=capBase := by
  have he := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (capSlope_continuous.intervalIntegrable 0 (1/5000)) (capSlope_continuous.intervalIntegrable (1/5000) u)
  have hzero : (∫ t in (1/5000:ℝ)..u,capSlope t)=0 := by
    calc
      (∫ t in (1/5000:ℝ)..u,capSlope t)=(∫ _t in (1/5000:ℝ)..u,(0:ℝ)) := by
        apply intervalIntegral.integral_congr
        intro t ht
        exact capSlope_zero (by rw [uIcc_of_le hu] at ht; exact ht.1)
      _=0 := by simp
  rw [hzero,add_zero] at he
  exact he.symm
lemma capBase_bounds : (1/10000:ℝ)≤ capBase ∧ capBase≤1/5000 := by
  constructor
  · have hh := capPrimitive_monotone (by norm_num : (1/10000:ℝ)≤1/5000)
    rwa [capPrimitive_linear (by norm_num : (1/10000:ℝ)≤1/10000)] at hh
  · unfold capBase capPrimitive
    calc
      (∫ t in (0:ℝ)..(1/5000:ℝ),capSlope t)≤∫ _t in (0:ℝ)..(1/5000:ℝ),(1:ℝ) := by
        apply intervalIntegral.integral_mono_on (by norm_num) (capSlope_continuous.intervalIntegrable _ _)
          (continuous_const.intervalIntegrable _ _)
        exact fun t _ => (capSlope_bounds t).2
      _=1/5000 := by simp
lemma entropyCap_contDiff (α : ℝ) : ContDiff ℝ 2 (entropyCap α) := by
  unfold entropyCap
  exact (contDiff_const.mul capPrimitive_contDiff).add
    (contDiff_const.mul (Real.smoothTransition.contDiff.comp ((contDiff_const.mul contDiff_id).sub contDiff_const)))
lemma entropyCap_linear {α u : ℝ} (hu : u≤1/10000) : entropyCap α u=α*u := by
  unfold entropyCap
  rw [capPrimitive_linear hu,Real.smoothTransition.zero_of_nonpos (by linarith)]
  ring
lemma entropyCap_one {α u : ℝ} (hu : 3/10000≤ u) : entropyCap α u=1 := by
  unfold entropyCap
  rw [capPrimitive_constant (by linarith),Real.smoothTransition.one_of_one_le (by linarith)]
  ring
lemma entropyCap_monotone {α : ℝ} (hα : 0≤α) (hα1 : α≤1) : Monotone (entropyCap α) := by
  have hc : 0≤1-α*capBase := by nlinarith [capBase_bounds.1,capBase_bounds.2]
  intro x y hxy
  unfold entropyCap
  exact add_le_add (mul_le_mul_of_nonneg_left (capPrimitive_monotone hxy) hα)
    (mul_le_mul_of_nonneg_left (Real.smoothTransition.monotone (by linarith)) hc)
lemma entropyCap_bounds {α u : ℝ} (hα : 0≤α) (hα1 : α≤1) (hu : u∈Icc (0:ℝ) 1) :
    0≤ entropyCap α u ∧ entropyCap α u≤1 := by
  have h0 := entropyCap_monotone hα hα1 hu.1
  have h1 := entropyCap_monotone hα hα1 hu.2
  rw [entropyCap_linear (by norm_num),mul_zero] at h0
  rw [entropyCap_one (u := 1) (by norm_num)] at h1
  exact ⟨h0,h1⟩
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_ArrayTests
attribute [-instance] _root_.OAI.StandardMapEntropy.CriticalScaleSequence.instRegularNonAffineArrayMulti _root_.OAI.StandardMapEntropy.CriticalScaleSequence.instRegularNonAffineArrayTerminal _root_.OAI.StandardMapEntropy.CriticalScaleSequence.multi_dilate_local _root_.OAI.StandardMapEntropy.CriticalScaleSequence.multi_terminal_local _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace _root_.OAI.StandardMapEntropy.instIsFiniteMeasureNonAffineArrayNonaffinePartOfDistanceArray _root_.OAI.StandardMapEntropy.instLocallyCompactSpaceNonAffineArray _root_.OAI.StandardMapEntropy.instPseudoMetrizableSpaceDistanceArray _root_.OAI.StandardMapEntropy.instPseudoMetrizableSpaceNonAffineArray _root_.OAI.StandardMapEntropy.instSecondCountableTopologyDistanceArray _root_.OAI.StandardMapEntropy.instSecondCountableTopologyNonAffineArray _root_.OAI.StandardMapEntropy.instSigmaCompactSpaceNonAffineArray
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open Set Filter MeasureTheory
open scoped ENNReal Topology
namespace StandardMapEntropy
lemma continuous_arrayShortfall (s t : DyadicTime) : Continuous (arrayShortfall s t) :=
  continuous_const.sub ((continuous_arrayEval s t).div_const _)
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_RealArrays
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open Set Filter MeasureTheory
open scoped Topology ENNReal
namespace StandardMapEntropy
lemma unitArray_diff (d : DistanceArray) (hd : UnitArray d) (s t u v : DyadicTime) :
    |d.val s t-d.val u v| ≤ |(s:ℝ)-(u:ℝ)|+|(t:ℝ)-(v:ℝ)| := by
  have ht := d.property.2.2.2.1
  have hsy := d.property.2.2.1
  have h1 := ht s u t
  have h2 := ht u v t
  have h3 := ht u s v
  have h4 := ht s t v
  have hsu := hd s u
  have htv := hd t v
  rw [abs_sub_comm] at hsu htv
  have hste : d.val u s=d.val s u := hsy _ _
  have hvte : d.val v t=d.val t v := hsy _ _
  rw [abs_le]
  constructor <;> linarith
lemma unitArray_lipschitz (d : DistanceArray) (hd : UnitArray d) :
    LipschitzWith 2 (fun p : DyadicTime × DyadicTime => d.val p.1 p.2) := by
  apply LipschitzWith.of_dist_le_mul
  intro p q
  have h := unitArray_diff d hd p.1 p.2 q.1 q.2
  rw [Real.dist_eq,Prod.dist_eq]
  change |d.val p.1 p.2-d.val q.1 q.2| ≤ (2:ℝ)*max |(p.1:ℝ)-(q.1:ℝ)| |(p.2:ℝ)-(q.2:ℝ)|
  linarith [le_max_left |(p.1:ℝ)-(q.1:ℝ)| |(p.2:ℝ)-(q.2:ℝ)|,
    le_max_right |(p.1:ℝ)-(q.1:ℝ)| |(p.2:ℝ)-(q.2:ℝ)|]
lemma continuous_realArray (d : DistanceArray) (hd : UnitArray d) :
    Continuous (fun p : ℝ × ℝ => realArray d p.1 p.2) :=
  (uniformContinuous_uniformly_extend
    ((isUniformInducing_val (dyadicTimes:Set ℝ)).prod (isUniformInducing_val (dyadicTimes:Set ℝ)))
    (denseRange_dyadicTime.prodMap denseRange_dyadicTime) (unitArray_lipschitz d hd).uniformContinuous).continuous
@[simp] lemma realArray_coe (d : DistanceArray) (hd : UnitArray d) (s t : DyadicTime) :
    realArray d (s:ℝ) (t:ℝ)=d.val s t :=
  uniformly_extend_of_ind
    ((isUniformInducing_val (dyadicTimes:Set ℝ)).prod (isUniformInducing_val (dyadicTimes:Set ℝ)))
    (denseRange_dyadicTime.prodMap denseRange_dyadicTime) (unitArray_lipschitz d hd).uniformContinuous (s,t)
lemma realArray_nonneg (d : DistanceArray) (hd : UnitArray d) (s t : ℝ) : 0 ≤ realArray d s t := by
  apply isClosed_property2 (p := fun s t => 0 ≤ realArray d s t) dyadicTime_dense (isClosed_le continuous_const (continuous_realArray d hd)) _ s t
  intro x y; simpa only [realArray_coe d hd] using d.property.1 x y
lemma realArray_le (d : DistanceArray) (hd : UnitArray d) (s t : ℝ) : realArray d s t ≤ |t-s| := by
  apply isClosed_property2 (p := fun s t => realArray d s t ≤ |t-s|) dyadicTime_dense (isClosed_le (continuous_realArray d hd) ((continuous_snd.sub continuous_fst).abs)) _ s t
  intro x y; simpa only [realArray_coe d hd] using hd x y
lemma realArray_symm (d : DistanceArray) (hd : UnitArray d) (s t : ℝ) : realArray d s t=realArray d t s := by
  apply isClosed_property2 (p := fun s t => realArray d s t=realArray d t s) dyadicTime_dense
    (isClosed_eq (continuous_realArray d hd) ((continuous_realArray d hd).comp (continuous_snd.prodMk continuous_fst))) _ s t
  intro x y; simpa only [realArray_coe d hd] using d.property.2.2.1 x y
lemma realArray_triangle (d : DistanceArray) (hd : UnitArray d) (s t u : ℝ) :
    realArray d s u ≤ realArray d s t+realArray d t u := by
  have hc := continuous_realArray d hd
  apply isClosed_property3 dyadicTime_dense
    (isClosed_le (hc.comp (continuous_fst.prodMk continuous_snd.snd))
      ((hc.comp (continuous_fst.prodMk continuous_snd.fst)).add (hc.comp (continuous_snd.fst.prodMk continuous_snd.snd)))) _ s t u
  intro x y z; simpa only [realArray_coe d hd] using d.property.2.2.2.1 x y z
lemma realArray_tree (d : DistanceArray) (hd : UnitArray d) (ht : TreeArray d) (v x y z : ℝ) :
    min (realArray d v x+realArray d v y-realArray d x y) (realArray d v y+realArray d v z-realArray d y z) ≤
      realArray d v x+realArray d v z-realArray d x z := by
  have hc := continuous_realArray d hd
  let e : DyadicTime × DyadicTime × DyadicTime × DyadicTime → ℝ × ℝ × ℝ × ℝ :=
    Prod.map ((↑) : DyadicTime → ℝ) (Prod.map ((↑) : DyadicTime → ℝ) (Prod.map ((↑) : DyadicTime → ℝ) ((↑) : DyadicTime → ℝ)))
  have he : DenseRange e := denseRange_dyadicTime.prodMap (denseRange_dyadicTime.prodMap (denseRange_dyadicTime.prodMap denseRange_dyadicTime))
  have hcl : IsClosed {p : ℝ × ℝ × ℝ × ℝ |
      min (realArray d p.1 p.2.1+realArray d p.1 p.2.2.1-realArray d p.2.1 p.2.2.1)
        (realArray d p.1 p.2.2.1+realArray d p.1 p.2.2.2-realArray d p.2.2.1 p.2.2.2) ≤
        realArray d p.1 p.2.1+realArray d p.1 p.2.2.2-realArray d p.2.1 p.2.2.2} := by
    apply isClosed_le
    · apply Continuous.min
      · exact ((hc.comp (continuous_fst.prodMk continuous_snd.fst)).add (hc.comp (continuous_fst.prodMk continuous_snd.snd.fst))).sub
          (hc.comp (continuous_snd.fst.prodMk continuous_snd.snd.fst))
      · exact ((hc.comp (continuous_fst.prodMk continuous_snd.snd.fst)).add (hc.comp (continuous_fst.prodMk continuous_snd.snd.snd))).sub
          (hc.comp (continuous_snd.snd.fst.prodMk continuous_snd.snd.snd))
    · exact ((hc.comp (continuous_fst.prodMk continuous_snd.fst)).add (hc.comp (continuous_fst.prodMk continuous_snd.snd.snd))).sub
        (hc.comp (continuous_snd.fst.prodMk continuous_snd.snd.snd))
  have hh := isClosed_property he hcl (fun p => by simpa only [e,Prod.map,realArray_coe d hd] using ht p.1 p.2.1 p.2.2.1 p.2.2.2) (v,x,y,z)
  exact hh
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_TreeLine
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open Set Filter
open scoped Topology
namespace StandardMapEntropy
lemma realArray_treeLine (d : DistanceArray) (hu : UnitArray d) (ht : TreeArray d) :
    TreeLine (realArray d) :=
  ⟨realArray_nonneg d hu,realArray_symm d hu,realArray_triangle d hu,
    realArray_le d hu,realArray_tree d hu ht⟩
namespace TreeLine
variable {d : ℝ → ℝ → ℝ} (hd : TreeLine d)
include hd
lemma b_symm (v x y : ℝ) : lineB d v x y=lineB d v y x := by
  unfold lineB; rw [hd.symm x y]; ring
lemma min_b (v x y z : ℝ) : min (lineB d v x y) (lineB d v y z) ≤ lineB d v x z :=
  hd.tree v x y z
end TreeLine

lemma matched_ray_distance {d : ℝ → ℝ → ℝ} (hd : TreeLine d) {a b u v s : ℝ}
    (_hab : a ≤ b) (hu : 0 ≤ u) (hv : 0 ≤ v) (hs : 0 ≤ s)
    (hsu : s ≤ u) (hsv : s ≤ v) (hr : ExteriorUnitRays d a b)
    (hmatch : d (a-u) (b+v)=u+v-d a b-2*s) :
    d (a-s) (b+s) ≤ 3*d a b := by
  have hu0 : d a (a-u)=u := by rw [hr.1 _ _ (le_refl _) (by linarith)]; rw [abs_of_nonpos (by linarith)]; ring
  have hs0 : d a (a-s)=s := by rw [hr.1 _ _ (le_refl _) (by linarith)]; rw [abs_of_nonpos (by linarith)]; ring
  have hus : d (a-u) (a-s)=u-s := by rw [hr.1 _ _ (by linarith) (by linarith)]; rw [abs_of_nonneg (by linarith)]; ring
  have hv0 : d b (b+v)=v := by rw [hr.2 _ _ (le_refl _) (by linarith)]; rw [abs_of_nonneg (by linarith)]; ring
  have hs1 : d b (b+s)=s := by rw [hr.2 _ _ (le_refl _) (by linarith)]; rw [abs_of_nonneg (by linarith)]; ring
  have hvs : d (b+v) (b+s)=v-s := by rw [hr.2 _ _ (by linarith) (by linarith)]; rw [abs_of_nonpos (by linarith)]; ring
  have hvlow : v-d a b ≤ d a (b+v) := by
    have h := hd.triangle b a (b+v)
    rw [hv0,hd.symm b a] at h
    linarith
  have hslow : s-d a b ≤ d a (b+s) := by
    have h := hd.triangle b a (b+s)
    rw [hs1,hd.symm b a] at h
    linarith
  have hshigh : d a (b+s) ≤ d a b+s := by simpa only [hs1] using hd.triangle a b (b+s)
  have hB1 : 2*s ≤ lineB d a (a-s) (a-u) := by
    rw [hd.b_symm a (a-s) (a-u)]
    simp only [lineB,hu0,hs0,hus]; linarith
  have hB2 : 2*s ≤ lineB d a (a-u) (b+v) := by simp only [lineB,hu0,hmatch]; linarith
  have hB3 : 2*s-2*d a b ≤ lineB d a (b+v) (b+s) := by simp only [lineB,hvs]; linarith
  have hB4 : 2*s ≤ lineB d a (a-s) (b+v) :=
    (le_min hB1 hB2).trans (hd.min_b a (a-s) (a-u) (b+v))
  have hB5 : 2*s-2*d a b ≤ lineB d a (a-s) (b+s) :=
    (le_min (by linarith [hd.nonneg a b]) hB3).trans (hd.min_b a (a-s) (b+v) (b+s))
  simp only [lineB,hs0] at hB5
  linarith
lemma crossing_excess_bound {d : ℝ → ℝ → ℝ} (hd : TreeLine d) {a b u v δ : ℝ}
    (hab : a ≤ b) (hu : 0 ≤ u) (hv : 0 ≤ v) (hδ : 0 < δ)
    (hr : ExteriorUnitRays d a b) (hc : NoFastCancellation d δ) :
    (u+v-d a b-d (a-u) (b+v))/2 ≤ 3*(b-a)/δ := by
  let s := (u+v-d a b-d (a-u) (b+v))/2
  have hD : d a b ≤ b-a := by simpa only [abs_of_nonneg (sub_nonneg.mpr hab)] using hd.unit a b
  by_contra hn
  have hbad : 3*(b-a)/δ < s := lt_of_not_ge hn
  have hs : 0 < s := lt_of_le_of_lt (div_nonneg (by linarith) hδ.le) hbad
  have hv0 : d b (b+v)=v := by rw [hr.2 _ _ (le_refl _) (by linarith),abs_of_nonneg (by linarith)]; ring
  have hu0 : d (a-u) a=u := by rw [hr.1 _ _ (by linarith) (le_refl _),abs_of_nonneg (by linarith)]; ring
  have hlowu : u-d a b-v ≤ d (a-u) (b+v) := by
    have h1 := hd.triangle (a-u) (b+v) a
    have h2 := hd.triangle (b+v) b a
    rw [hu0] at h1
    rw [hd.symm (b+v) b,hv0,hd.symm b a] at h2
    linarith
  have hlowv : v-d a b-u ≤ d (a-u) (b+v) := by
    have h1 := hd.triangle b (a-u) (b+v)
    have h2 := hd.triangle b a (a-u)
    rw [hv0] at h1
    rw [hd.symm b a,hd.symm a (a-u),hu0] at h2
    linarith
  have hsu : s ≤ u := by dsimp [s]; linarith
  have hsv : s ≤ v := by dsimp [s]; linarith
  have hmatch : d (a-u) (b+v)=u+v-d a b-2*s := by dsimp [s]; ring
  have hm := matched_ray_distance hd hab hu hv hs.le hsu hsv hr hmatch
  let m := (a+b)/2
  let t := s+(b-a)/2
  have ht : 0 < t := by dsimp [t]; linarith
  have hxl : m-t=a-s := by dsimp [m,t]; ring
  have hxr : m+t=b+s := by dsimp [m,t]; ring
  have hsa : d (a-s) a=s := by rw [hr.1 _ _ (by linarith) (le_refl _),abs_of_nonneg (by linarith)]; ring
  have hbs : d b (b+s)=s := by rw [hr.2 _ _ (le_refl _) (by linarith),abs_of_nonneg (by linarith)]; ring
  have hma : d m a ≤ (b-a)/2 := by
    have h := hd.unit m a
    rw [abs_of_nonpos (by dsimp [m]; linarith)] at h
    dsimp [m] at h; linarith
  have hmb : d m b ≤ (b-a)/2 := by
    have h := hd.unit m b
    rw [abs_of_nonneg (by dsimp [m]; linarith)] at h
    dsimp [m] at h; linarith
  have hl := hd.triangle (a-s) m a
  have hh := hd.triangle b m (b+s)
  rw [hsa] at hl
  rw [hbs,hd.symm b m] at hh
  have hprod : 3*(b-a) < δ*s := by simpa only [mul_comm] using (div_lt_iff₀ hδ).mp hbad
  apply hc m t ht
  rw [hxl,hxr]
  refine ⟨?_,?_,?_⟩
  · dsimp [t]; nlinarith [mul_nonneg hδ.le (sub_nonneg.mpr hab)]
  · dsimp [t]; nlinarith [mul_nonneg hδ.le (sub_nonneg.mpr hab)]
  · dsimp [t]; nlinarith [mul_nonneg hδ.le (sub_nonneg.mpr hab)]
lemma exterior_ray_crossloss {d : ℝ → ℝ → ℝ} (hd : TreeLine d) {a b δ : ℝ}
    (hab : a ≤ b) (hδ : 0 < δ) (hr : ExteriorUnitRays d a b) (hc : NoFastCancellation d δ)
    (x y : ℝ) (hxy : x ≤ y) :
    0 ≤ (y-x)-d x y ∧ (y-x)-d x y ≤ (2+6/δ)*(b-a) := by
  have hL : 0 ≤ b-a := sub_nonneg.mpr hab
  have hC : 2*(b-a) ≤ (2+6/δ)*(b-a) := by
    have hz : 0 ≤ 6/δ := by positivity
    nlinarith
  have hunit : d x y ≤ y-x := by simpa only [abs_of_nonneg (sub_nonneg.mpr hxy)] using hd.unit x y
  refine ⟨by linarith,?_⟩
  by_cases hya : y ≤ a
  · rw [hr.1 x y (hxy.trans hya) hya,abs_of_nonneg (sub_nonneg.mpr hxy)]
    nlinarith
  by_cases hbx : b ≤ x
  · rw [hr.2 x y hbx (hbx.trans hxy),abs_of_nonneg (sub_nonneg.mpr hxy)]
    nlinarith
  have hay : a ≤ y := le_of_lt (lt_of_not_ge hya)
  have hxb : x ≤ b := le_of_lt (lt_of_not_ge hbx)
  by_cases hxa : x ≤ a
  · by_cases hby : b ≤ y
    · have hh := crossing_excess_bound hd hab (sub_nonneg.mpr hxa) (sub_nonneg.mpr hby) hδ hr hc
      rw [show a-(a-x)=x by ring,show b+(y-b)=y by ring] at hh
      have hD : d a b ≤ b-a := by simpa only [abs_of_nonneg hL] using hd.unit a b
      have he : 6*(b-a)/δ=(6/δ)*(b-a) := by ring
      have he3 : 2*(3*(b-a)/δ)=6*(b-a)/δ := by ring
      nlinarith
    · have hyb : y ≤ b := le_of_lt (lt_of_not_ge hby)
      have hxaD : d x a=a-x := by rw [hr.1 x a hxa (le_refl _),abs_of_nonneg (sub_nonneg.mpr hxa)]
      have hyaD : d y a ≤ y-a := by
        have hh := hd.unit y a
        rw [abs_of_nonpos (by linarith)] at hh
        linarith
      have hh := hd.triangle x y a
      rw [hxaD] at hh
      linarith
  · have hax : a ≤ x := le_of_lt (lt_of_not_ge hxa)
    by_cases hby : b ≤ y
    · have hbyD : d b y=y-b := by rw [hr.2 b y (le_refl _) hby,abs_of_nonneg (sub_nonneg.mpr hby)]
      have hbxD : d b x ≤ b-x := by
        have hh := hd.unit b x
        rw [abs_of_nonpos (by linarith)] at hh
        linarith
      have hh := hd.triangle b x y
      rw [hbyD] at hh
      linarith
    · have hyb : y ≤ b := le_of_lt (lt_of_not_ge hby)
      linarith [hd.nonneg x y]
lemma exterior_ray_shortfall {d : ℝ → ℝ → ℝ} (hd : TreeLine d) {a b δ : ℝ}
    (hab : a ≤ b) (hδ : 0 < δ) (hr : ExteriorUnitRays d a b) (hc : NoFastCancellation d δ)
    (z t : ℝ) (ht : 0 < t) :
    0 ≤ 1-d z (z+t)/t ∧ 1-d z (z+t)/t ≤ (2+6/δ)*(b-a)/t := by
  obtain ⟨h0,h1⟩ := exterior_ray_crossloss hd hab hδ hr hc z (z+t) (by linarith)
  constructor
  · have hh := (div_le_one ht).mpr (show d z (z+t) ≤ t by linarith)
    linarith
  · apply (le_div_iff₀ ht).mpr
    have he : (1-d z (z+t)/t)*t=t-d z (z+t) := by field_simp
    rw [he]; linarith
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_TerminalShortfall
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter Topology
open scoped ENNReal Topology CompactlySupported Classical
namespace StandardMapEntropy
lemma shortfall_unit_mem (d : DistanceArray) (hu : UnitArray d) (s t : DyadicTime)
    (hst : (s:ℝ)<(t:ℝ)) : arrayShortfall s t d∈Icc (0:ℝ) 1 := by
  have hl : 0<(t:ℝ)-(s:ℝ) := sub_pos.mpr hst
  have hb := hu s t
  rw [abs_of_pos hl] at hb
  have h0 := d.property.1 s t
  unfold arrayShortfall
  constructor
  · have hh := (div_le_one hl).mpr hb; linarith
  · have hh := div_nonneg h0 hl.le; linarith
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_EndpointDefinition
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open Set Filter MeasureTheory
open scoped Topology Classical
namespace StandardMapEntropy

lemma measurable_leftEndpoint : Measurable leftEndpoint := by
  apply Measurable.iInf; intro s
  apply Measurable.iInf; intro t
  exact measurable_const.ite
    ((isClosed_eq (continuous_arrayEval s t) continuous_const).measurableSet.compl) measurable_const
lemma measurable_rightEndpoint : Measurable rightEndpoint := by
  apply Measurable.iSup; intro s
  apply Measurable.iSup; intro t
  exact measurable_const.ite
    ((isClosed_eq (continuous_arrayEval s t) continuous_const).measurableSet.compl) measurable_const
lemma leftEndpoint_le_of_nonunit (d : DistanceArray) {s t : DyadicTime}
    (h : d.val s t≠|(t:ℝ)-(s:ℝ)|) : leftEndpoint d≤((max (s:ℝ) (t:ℝ)):EReal) := by
  unfold leftEndpoint
  exact (iInf_le_of_le s (iInf_le_of_le t (by rw [ite_eq_left h])))
lemma le_rightEndpoint_of_nonunit (d : DistanceArray) {s t : DyadicTime}
    (h : d.val s t≠|(t:ℝ)-(s:ℝ)|) : ((min (s:ℝ) (t:ℝ)):EReal) ≤ rightEndpoint d := by
  unfold rightEndpoint
  exact (le_iSup_of_le s (le_iSup_of_le t (by rw [ite_eq_left h])))
lemma le_leftEndpoint_iff (d : DistanceArray) (a : EReal) : a≤leftEndpoint d ↔
    ∀s t:DyadicTime,d.val s t≠|(t:ℝ)-(s:ℝ)| → a≤((max (s:ℝ) (t:ℝ)):EReal) := by
  simp only [leftEndpoint,le_iInf_iff]
  constructor
  · intro h s t hn; simpa only [ite_eq_left hn] using h s t
  · intro h s t; split_ifs with hn
    · exact h s t hn
    · exact le_top
lemma rightEndpoint_le_iff (d : DistanceArray) (a : EReal) : rightEndpoint d≤a ↔
    ∀s t:DyadicTime,d.val s t≠|(t:ℝ)-(s:ℝ)| → ((min (s:ℝ) (t:ℝ)):EReal)≤a := by
  simp only [rightEndpoint,iSup_le_iff]
  constructor
  · intro h s t hn; simpa only [ite_eq_left hn] using h s t
  · intro h s t; split_ifs with hn
    · exact h s t hn
    · exact bot_le
lemma leftEndpoint_lower_ray (d : DistanceArray) {a : ℝ}
    (h : ∀s t:DyadicTime,(s:ℝ)≤a → (t:ℝ)≤a → d.val s t=|(t:ℝ)-(s:ℝ)|) : (a:EReal)≤leftEndpoint d := by
  apply (le_leftEndpoint_iff d a).mpr
  intro s t hn
  have hh : a < max (s:ℝ) (t:ℝ) := by
    by_contra hm
    have hm' := le_of_not_gt hm
    exact hn (h s t ((le_max_left _ _).trans hm') ((le_max_right _ _).trans hm'))
  exact EReal.coe_le_coe_iff.mpr hh.le
lemma rightEndpoint_upper_ray (d : DistanceArray) {b : ℝ}
    (h : ∀s t:DyadicTime,b≤(s:ℝ) → b≤(t:ℝ) → d.val s t=|(t:ℝ)-(s:ℝ)|) : rightEndpoint d≤(b:EReal) := by
  apply (rightEndpoint_le_iff d b).mpr
  intro s t hn
  have hh : min (s:ℝ) (t:ℝ)<b := by
    by_contra hm
    have hm' := le_of_not_gt hm
    exact hn (h s t (hm'.trans (min_le_left _ _)) (hm'.trans (min_le_right _ _)))
  exact EReal.coe_le_coe_iff.mpr hh.le
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_EndpointShapes
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open Set Filter MeasureTheory
open scoped Topology Classical
namespace StandardMapEntropy
lemma dyadic_between {a b : ℝ} (hab : a < b) : ∃s : DyadicTime,a < (s:ℝ) ∧ (s:ℝ) < b := by
  obtain ⟨x,⟨s,rfl⟩,ha,hb⟩ := dyadicTime_dense.exists_between hab
  exact ⟨s,ha,hb⟩
lemma dyadic_pair_between {a b : ℝ} (hab : a < b) :
    ∃s t : DyadicTime,a < (s:ℝ) ∧ (s:ℝ) < (t:ℝ) ∧ (t:ℝ) < b := by
  obtain ⟨s,has,hsb⟩ := dyadic_between hab
  obtain ⟨t,hst,htb⟩ := dyadic_between hsb
  exact ⟨s,t,has,hst,htb⟩
lemma nonunit_of_slow {d : DistanceArray} {c : ℝ} (hc : c < 1) {s t : DyadicTime}
    (hst : (s:ℝ) < (t:ℝ)) (h : d.val s t ≤ c*((t:ℝ)-(s:ℝ))) : d.val s t ≠ |(t:ℝ)-(s:ℝ)| := by
  rw [abs_of_pos (sub_pos.mpr hst)]
  intro he
  have hp := mul_lt_mul_of_pos_right hc (sub_pos.mpr hst)
  nlinarith
lemma leftEndpoint_le_of_slow_interval {d : DistanceArray} {a b c : ℝ} (hab : a < b) (hc : c < 1)
    (h : ∀s t:DyadicTime,(s:ℝ)∈Icc a b → (t:ℝ)∈Icc a b → d.val s t ≤ c*|(t:ℝ)-(s:ℝ)|) :
    leftEndpoint d ≤ (a:EReal) := by
  by_contra hn
  obtain ⟨r,har,hr⟩ := EReal.exists_between_coe_real (lt_of_not_ge hn)
  have har' : a < r := EReal.coe_lt_coe_iff.mp har
  obtain ⟨s,t,has,hst,htb⟩ := dyadic_pair_between (lt_min har' hab)
  have htb' := (lt_min_iff.mp htb).2
  have htr := (lt_min_iff.mp htb).1
  have hs := h s t ⟨has.le,(hst.trans htb').le⟩ ⟨(has.trans hst).le,htb'.le⟩
  rw [abs_of_pos (sub_pos.mpr hst)] at hs
  have hu := leftEndpoint_le_of_nonunit d (nonunit_of_slow hc hst hs)
  rw [max_eq_right (EReal.coe_le_coe_iff.mpr hst.le)] at hu
  exact (not_le_of_gt hr) (hu.trans (EReal.coe_le_coe_iff.mpr htr.le))
lemma rightEndpoint_ge_of_slow_interval {d : DistanceArray} {a b c : ℝ} (hab : a < b) (hc : c < 1)
    (h : ∀s t:DyadicTime,(s:ℝ)∈Icc a b → (t:ℝ)∈Icc a b → d.val s t ≤ c*|(t:ℝ)-(s:ℝ)|) :
    (b:EReal) ≤ rightEndpoint d := by
  by_contra hn
  obtain ⟨r,hr,hrb⟩ := EReal.exists_between_coe_real (lt_of_not_ge hn)
  have hrb' : r < b := EReal.coe_lt_coe_iff.mp hrb
  obtain ⟨s,t,has,hst,htb⟩ := dyadic_pair_between (max_lt hrb' hab)
  have has' := (max_lt_iff.mp has).2
  have hrs := (max_lt_iff.mp has).1
  have hs := h s t ⟨has'.le,(hst.trans htb).le⟩ ⟨(has'.trans hst).le,htb.le⟩
  rw [abs_of_pos (sub_pos.mpr hst)] at hs
  have hu := le_rightEndpoint_of_nonunit d (nonunit_of_slow hc hst hs)
  rw [min_eq_left (EReal.coe_le_coe_iff.mpr hst.le)] at hu
  exact (not_le_of_gt hr) ((EReal.coe_le_coe_iff.mpr hrs.le).trans hu)
lemma endpoints_slow {d : DistanceArray} {c : ℝ} (hc : c < 1)
    (h : ∀s t:DyadicTime,d.val s t ≤ c*|(t:ℝ)-(s:ℝ)|) : leftEndpoint d=⊥ ∧ rightEndpoint d=⊤ := by
  constructor
  · apply eq_bot_iff.mpr
    apply le_of_not_gt
    intro hh
    obtain ⟨r,_,hr⟩ := EReal.exists_between_coe_real hh
    exact (not_le_of_gt hr) (leftEndpoint_le_of_slow_interval (a := r) (b := r+1) (by linarith) hc (fun s t _ _ => h s t))
  · apply eq_top_iff.mpr
    apply le_of_not_gt
    intro hh
    obtain ⟨r,hr,_⟩ := EReal.exists_between_coe_real hh
    exact (not_le_of_gt hr) (rightEndpoint_ge_of_slow_interval (a := r-1) (b := r) (by linarith) hc (fun s t _ _ => h s t))
lemma endpoints_left_ray {d : DistanceArray} {a c : ℝ} (hc : c < 1)
    (hl : ∀s t:DyadicTime,(s:ℝ)≤a → (t:ℝ)≤a → d.val s t=|(t:ℝ)-(s:ℝ)|)
    (hs : ∀s t:DyadicTime,a≤(s:ℝ) → a≤(t:ℝ) → d.val s t ≤ c*|(t:ℝ)-(s:ℝ)|) :
    leftEndpoint d=(a:EReal) ∧ rightEndpoint d=⊤ := by
  constructor
  · exact le_antisymm (leftEndpoint_le_of_slow_interval (b := a+1) (by linarith) hc (fun s t hp hq => hs s t hp.1 hq.1))
      (leftEndpoint_lower_ray d hl)
  · apply eq_top_iff.mpr
    apply le_of_not_gt
    intro hh
    obtain ⟨r,hr,_⟩ := EReal.exists_between_coe_real hh
    have he := rightEndpoint_ge_of_slow_interval (d := d) (a := max r a) (b := max r a+1) (by linarith) hc
      (fun s t hp hq => hs s t ((le_max_right _ _).trans hp.1) ((le_max_right _ _).trans hq.1))
    exact (not_le_of_gt hr) ((EReal.coe_le_coe_iff.mpr (by linarith [le_max_left r a])).trans he)
lemma endpoints_right_ray {d : DistanceArray} {b c : ℝ} (hc : c < 1)
    (hr : ∀s t:DyadicTime,b≤(s:ℝ) → b≤(t:ℝ) → d.val s t=|(t:ℝ)-(s:ℝ)|)
    (hs : ∀s t:DyadicTime,(s:ℝ)≤b → (t:ℝ)≤b → d.val s t ≤ c*|(t:ℝ)-(s:ℝ)|) :
    leftEndpoint d=⊥ ∧ rightEndpoint d=(b:EReal) := by
  constructor
  · apply eq_bot_iff.mpr
    apply le_of_not_gt
    intro hh
    obtain ⟨r,_,hr'⟩ := EReal.exists_between_coe_real hh
    have he := leftEndpoint_le_of_slow_interval (d := d) (a := min r b-1) (b := min r b) (by linarith) hc
      (fun s t hp hq => hs s t (hp.2.trans (min_le_right _ _)) (hq.2.trans (min_le_right _ _)))
    exact (not_le_of_gt hr') (he.trans (EReal.coe_le_coe_iff.mpr (by linarith [min_le_left r b])))
  · exact le_antisymm (rightEndpoint_upper_ray d hr)
      (rightEndpoint_ge_of_slow_interval (a := b-1) (by linarith) hc (fun s t hp hq => hs s t hp.2 hq.2))
lemma endpoints_two_rays {d : DistanceArray} {a b c : ℝ} (hab : a < b) (hc : c < 1)
    (hl : ∀s t:DyadicTime,(s:ℝ)≤a → (t:ℝ)≤a → d.val s t=|(t:ℝ)-(s:ℝ)|)
    (hr : ∀s t:DyadicTime,b≤(s:ℝ) → b≤(t:ℝ) → d.val s t=|(t:ℝ)-(s:ℝ)|)
    (hs : ∀s t:DyadicTime,(s:ℝ)∈Icc a b → (t:ℝ)∈Icc a b → d.val s t ≤ c*|(t:ℝ)-(s:ℝ)|) :
    leftEndpoint d=(a:EReal) ∧ rightEndpoint d=(b:EReal) :=
  ⟨le_antisymm (leftEndpoint_le_of_slow_interval hab hc hs) (leftEndpoint_lower_ray d hl),
   le_antisymm (rightEndpoint_upper_ray d hr) (rightEndpoint_ge_of_slow_interval hab hc hs)⟩
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_EndpointCovariance
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open Set Filter MeasureTheory
open scoped Topology Classical
namespace StandardMapEntropy
lemma endpoints_reindex (d d' : DistanceArray) (e : ℝ ≃o ℝ) (b : DyadicTime ≃ DyadicTime)
    (hb : ∀s:DyadicTime,(b s:ℝ)=e (s:ℝ))
    (he : ∀s t:DyadicTime,d'.val (b s) (b t)≠|(b t:ℝ)-(b s:ℝ)| ↔ d.val s t≠|(t:ℝ)-(s:ℝ)|) :
    leftEndpoint d'=erealOrderIso e (leftEndpoint d) ∧ rightEndpoint d'=erealOrderIso e (rightEndpoint d) := by
  constructor
  · unfold leftEndpoint
    rw [←b.iInf_comp]
    simp_rw [←b.iInf_comp (g := fun t => if d'.val (b _) t≠|(t:ℝ)-(b _:ℝ)| then ((max (b _:ℝ) (t:ℝ)):EReal) else ⊤)]
    simp only [OrderIso.map_iInf]
    apply iInf_congr; intro s
    apply iInf_congr; intro t
    simp only [he s t]
    split_ifs
    · rcases le_total (s:ℝ) (t:ℝ) with h|h
      · rw [max_eq_right (EReal.coe_le_coe_iff.mpr h)]
        simp only [erealOrderIso_coe,hb]
        exact max_eq_right (EReal.coe_le_coe_iff.mpr (e.monotone h))
      · rw [max_eq_left (EReal.coe_le_coe_iff.mpr h)]
        simp only [erealOrderIso_coe,hb]
        exact max_eq_left (EReal.coe_le_coe_iff.mpr (e.monotone h))
    · rfl
  · unfold rightEndpoint
    rw [←b.iSup_comp]
    simp_rw [←b.iSup_comp (g := fun t => if d'.val (b _) t≠|(t:ℝ)-(b _:ℝ)| then ((min (b _:ℝ) (t:ℝ)):EReal) else ⊥)]
    simp only [OrderIso.map_iSup]
    apply iSup_congr; intro s
    apply iSup_congr; intro t
    simp only [he s t]
    split_ifs
    · rcases le_total (s:ℝ) (t:ℝ) with h|h
      · rw [min_eq_left (EReal.coe_le_coe_iff.mpr h)]
        simp only [erealOrderIso_coe,hb]
        exact min_eq_left (EReal.coe_le_coe_iff.mpr (e.monotone h))
      · rw [min_eq_right (EReal.coe_le_coe_iff.mpr h)]
        simp only [erealOrderIso_coe,hb]
        exact min_eq_right (EReal.coe_le_coe_iff.mpr (e.monotone h))
    · rfl
lemma endpoints_translate (r : DyadicTime) (d : DistanceArray) :
    leftEndpoint (arrayTranslate r d)=erealOrderIso (OrderIso.addRight (-(r:ℝ))) (leftEndpoint d) ∧
    rightEndpoint (arrayTranslate r d)=erealOrderIso (OrderIso.addRight (-(r:ℝ))) (rightEndpoint d) := by
  apply endpoints_reindex d _ _ (Equiv.addRight (-r))
  · intro s; rfl
  · intro s t
    change d.val (s+-r+r) (t+-r+r)≠|((t:ℝ)+-(r:ℝ))-((s:ℝ)+-(r:ℝ))| ↔ _
    rw [show s+-r+r=s by abel,show t+-r+r=t by abel]
    rw [show ((t:ℝ)+-(r:ℝ))-((s:ℝ)+-(r:ℝ))=(t:ℝ)-(s:ℝ) by ring]
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_EndpointClasses
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open Set Filter MeasureTheory
open scoped Topology Classical
namespace StandardMapEntropy
lemma measurable_endpointLeft : Measurable endpointLeft := measurable_ereal_toReal.comp measurable_leftEndpoint
lemma measurable_endpointRight : Measurable endpointRight := measurable_ereal_toReal.comp measurable_rightEndpoint
lemma measurableSet_twoRayClass : MeasurableSet twoRayClass :=
  ((measurable_leftEndpoint (measurableSet_singleton ⊥)).compl).inter
    (((measurable_leftEndpoint (measurableSet_singleton ⊤)).compl).inter
      (((measurable_rightEndpoint (measurableSet_singleton ⊥)).compl).inter ((measurable_rightEndpoint (measurableSet_singleton ⊤)).compl)))
lemma slowShape_dyadic {d : DistanceArray} {c:ℝ} (hu:UnitArray d) (h:SlowShape (realArray d) c) :
    (∀s t:DyadicTime,d.val s t ≤ c*|(t:ℝ)-(s:ℝ)|) ∨
    (∃a:ℝ,(∀s t:DyadicTime,(s:ℝ)≤a → (t:ℝ)≤a → d.val s t=|(t:ℝ)-(s:ℝ)|) ∧
      (∀s t:DyadicTime,a≤(s:ℝ) → a≤(t:ℝ) → d.val s t ≤ c*|(t:ℝ)-(s:ℝ)|)) ∨
    (∃b:ℝ,(∀s t:DyadicTime,b≤(s:ℝ) → b≤(t:ℝ) → d.val s t=|(t:ℝ)-(s:ℝ)|) ∧
      (∀s t:DyadicTime,(s:ℝ)≤b → (t:ℝ)≤b → d.val s t ≤ c*|(t:ℝ)-(s:ℝ)|)) ∨
    (∃a b:ℝ,a<b ∧
      (∀s t:DyadicTime,(s:ℝ)≤a → (t:ℝ)≤a → d.val s t=|(t:ℝ)-(s:ℝ)|) ∧
      (∀s t:DyadicTime,b≤(s:ℝ) → b≤(t:ℝ) → d.val s t=|(t:ℝ)-(s:ℝ)|) ∧
      (∀s t:DyadicTime,(s:ℝ)∈Icc a b → (t:ℝ)∈Icc a b → d.val s t ≤ c*|(t:ℝ)-(s:ℝ)|)) := by
  rcases h with hs|⟨a,hl,hs⟩|⟨b,hr,hs⟩|⟨a,b,hab,⟨hl,hr⟩,hs⟩
  · exact Or.inl (fun s t => by simpa only [realArray_coe d hu] using hs s t)
  · exact Or.inr (Or.inl ⟨a,fun s t hp hq => by simpa only [realArray_coe d hu] using hl s hp t hq,
      fun s t hp hq => by simpa only [realArray_coe d hu] using hs s hp t hq⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨b,fun s t hp hq => by simpa only [realArray_coe d hu] using hr s hp t hq,
      fun s t hp hq => by simpa only [realArray_coe d hu] using hs s hp t hq⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨a,b,hab,fun s t hp hq => by simpa only [realArray_coe d hu] using hl s t hp hq,
      fun s t hp hq => by simpa only [realArray_coe d hu] using hr s t hp hq,
      fun s t hp hq => by simpa only [realArray_coe d hu] using hs s hp t hq⟩))
lemma twoRay_properties {d:DistanceArray} {c:ℝ} (hu:UnitArray d) (hc:c<1) (hs:SlowShape (realArray d) c)
    (hd:d∈twoRayClass) : endpointLeft d<endpointRight d ∧
    (∀s t:DyadicTime,(s:ℝ)≤endpointLeft d → (t:ℝ)≤endpointLeft d → d.val s t=|(t:ℝ)-(s:ℝ)|) ∧
    (∀s t:DyadicTime,endpointRight d≤(s:ℝ) → endpointRight d≤(t:ℝ) → d.val s t=|(t:ℝ)-(s:ℝ)|) ∧
    (∀s t:DyadicTime,(s:ℝ)∈Icc (endpointLeft d) (endpointRight d) → (t:ℝ)∈Icc (endpointLeft d) (endpointRight d) → d.val s t ≤ c*|(t:ℝ)-(s:ℝ)|) := by
  rcases slowShape_dyadic hu hs with hs|⟨a,hl,hs⟩|⟨b,hr,hs⟩|⟨a,b,hab,hl,hr,hs⟩
  · exact (hd.1 (endpoints_slow hc hs).1).elim
  · exact (hd.2.2.2 (endpoints_left_ray hc hl hs).2).elim
  · exact (hd.1 (endpoints_right_ray hc hr hs).1).elim
  · have he := endpoints_two_rays hab hc hl hr hs
    have ha : endpointLeft d=a := by simp only [endpointLeft,he.1,EReal.toReal_coe]
    have hb : endpointRight d=b := by simp only [endpointRight,he.2,EReal.toReal_coe]
    simpa only [ha,hb] using And.intro hab (And.intro hl (And.intro hr hs))
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_EndpointActions
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal Classical
namespace StandardMapEntropy
lemma erealOrderIso_eq_bot (e:ℝ≃oℝ) (x:EReal) : erealOrderIso e x=⊥ ↔ x=⊥ := by
  constructor
  · intro h; apply (erealOrderIso e).injective; simpa only [erealOrderIso_bot] using h
  · intro h; rw [h,erealOrderIso_bot]
lemma erealOrderIso_eq_top (e:ℝ≃oℝ) (x:EReal) : erealOrderIso e x=⊤ ↔ x=⊤ := by
  constructor
  · intro h; apply (erealOrderIso e).injective; simpa only [erealOrderIso_top] using h
  · intro h; rw [h,erealOrderIso_top]
lemma twoRayClass_translate (r:DyadicTime) (d:DistanceArray) : arrayTranslate r d∈twoRayClass ↔ d∈twoRayClass := by
  change (_≠⊥ ∧ _≠⊤ ∧ _≠⊥ ∧ _≠⊤) ↔ _
  rw [(endpoints_translate r d).1,(endpoints_translate r d).2]
  simp only [ne_eq,erealOrderIso_eq_bot,erealOrderIso_eq_top]
  rfl
lemma endpointLeft_translate (r:DyadicTime) (d:DistanceArray) (ht:leftEndpoint d≠⊤) (hb:leftEndpoint d≠⊥) :
    endpointLeft (arrayTranslate r d)=endpointLeft d-(r:ℝ) := by
  unfold endpointLeft
  rw [(endpoints_translate r d).1,←EReal.coe_toReal ht hb,erealOrderIso_coe]
  simp only [EReal.toReal_coe]
  rfl
lemma endpointRight_translate (r:DyadicTime) (d:DistanceArray) (ht:rightEndpoint d≠⊤) (hb:rightEndpoint d≠⊥) :
    endpointRight (arrayTranslate r d)=endpointRight d-(r:ℝ) := by
  unfold endpointRight
  rw [(endpoints_translate r d).2,←EReal.coe_toReal ht hb,erealOrderIso_coe]
  simp only [EReal.toReal_coe]
  rfl
lemma map_restrict_invariant {X:Type*} [MeasurableSpace X] (μ:Measure X) (f:X→X) (hf:Measurable f)
    (hm:μ.map f=μ) (A:Set X) (hA:MeasurableSet A) (hfA:f⁻¹'A=A) : (μ.restrict A).map f=μ.restrict A := by
  rw [←hfA,←Measure.restrict_map hf hA,hm,hfA]
lemma push_invariant {X Y:Type*} [MeasurableSpace X] [MeasurableSpace Y] (μ:Measure X)
    (f:X→X) (hf:Measurable f) (hm:μ.map f=μ) (e:X→Y) (he:Measurable e) (g:Y→Y) (hg:Measurable g)
    (hc:∀ᵐx ∂μ,g (e x)=e (f x)) : (μ.map e).map g=μ.map e := by
  rw [Measure.map_map hg he]
  calc
    μ.map (g ∘ e)=μ.map (e ∘ f) := Measure.map_congr hc
    _=(μ.map f).map e := (Measure.map_map he hf).symm
    _=μ.map e := by rw [hm]
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_ScaleEndpoints
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open Set Filter MeasureTheory Topology
open scoped Classical
namespace StandardMapEntropy
lemma measurable_coreLength : Measurable coreLength := measurable_endpointRight.sub measurable_endpointLeft
lemma coreLength_translate (r:DyadicTime) (d:DistanceArray) (hd:d∈twoRayClass) : coreLength (arrayTranslate r d)=coreLength d := by
  unfold coreLength
  rw [endpointRight_translate r d hd.2.2.2 hd.2.2.1,endpointLeft_translate r d hd.2.1 hd.1]
  ring
lemma measurableSet_lengthBand (j:ℤ) : MeasurableSet (lengthBand j) :=
  (isClosed_unitArray.preimage continuous_subtype_val).measurableSet.inter
    ((measurableSet_twoRayClass.preimage measurable_subtype_coe).inter
      (((measurable_coreLength.comp measurable_subtype_coe) measurableSet_Ici).inter ((measurable_coreLength.comp measurable_subtype_coe) measurableSet_Iio)))
lemma lengthBand_translate (j:ℤ) (r:DyadicTime) : (nonaffineTranslation r)⁻¹'lengthBand j=lengthBand j := by
  ext d
  change (UnitArray (arrayTranslate r d.val) ∧ arrayTranslate r d.val∈twoRayClass ∧ (2:ℝ)^j ≤ coreLength (arrayTranslate r d.val) ∧ coreLength (arrayTranslate r d.val)<(2:ℝ)^(j+1)) ↔ (UnitArray d.val ∧ d.val∈twoRayClass ∧ (2:ℝ)^j ≤ coreLength d.val ∧ coreLength d.val<(2:ℝ)^(j+1))
  have hu : UnitArray (arrayTranslate r d.val) ↔ UnitArray d.val := by
    constructor
    · intro h s t
      have hh := h (s-r) (t-r)
      change d.val.val (s-r+r) (t-r+r)≤|(t:ℝ)-(r:ℝ)-((s:ℝ)-(r:ℝ))| at hh
      simpa only [sub_add_cancel,sub_sub_sub_cancel_right] using hh
    · intro h s t
      have hh := h (s+r) (t+r)
      change d.val.val (s+r) (t+r)≤|(t:ℝ)+(r:ℝ)-((s:ℝ)+(r:ℝ))| at hh
      change d.val.val (s+r) (t+r)≤|(t:ℝ)-(s:ℝ)|
      simpa only [add_sub_add_right_eq_sub] using hh
  rw [hu,twoRayClass_translate]
  constructor <;> rintro ⟨hu,hd,hl,hr⟩
  · rw [coreLength_translate r d.val hd] at hl hr; exact ⟨hu,hd,hl,hr⟩
  · exact ⟨hu,hd,by simpa only [coreLength_translate r d.val hd] using hl,by simpa only [coreLength_translate r d.val hd] using hr⟩
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_EndpointCompact
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal Classical
namespace StandardMapEntropy
lemma separated_secants_compact (p q u v:DyadicTime) (hpq:(p:ℝ)<(q:ℝ)) (huv:(u:ℝ)<(v:ℝ))
    (c:ℝ) (hc:c<1) : IsCompact {d:NonAffineArray | d.val.val p q=(q:ℝ)-(p:ℝ) ∧ d.val.val u v ≤ c*((v:ℝ)-(u:ℝ))} := by
  let K:Set DistanceArray := {d | d.val p q=(q:ℝ)-(p:ℝ) ∧ d.val u v ≤ c*((v:ℝ)-(u:ℝ))}
  have hK : IsCompact K := ((isClosed_eq (continuous_arrayEval p q) continuous_const).inter
    (isClosed_le (continuous_arrayEval u v) continuous_const)).isCompact
  have hsub : K⊆(affineLocus)ᶜ := by
    intro d hd ⟨w,hw⟩
    subst d
    have h1 : w.val*((q:ℝ)-(p:ℝ))=(q:ℝ)-(p:ℝ) := by
      simpa only [affineArray,abs_of_pos (sub_pos.mpr hpq)] using hd.1
    have hw1 : w.val=1 := by nlinarith [sub_pos.mpr hpq]
    have h2 : w.val*((v:ℝ)-(u:ℝ)) ≤ c*((v:ℝ)-(u:ℝ)) := by
      simpa only [affineArray,abs_of_pos (sub_pos.mpr huv)] using hd.2
    rw [hw1,one_mul] at h2
    exact (not_le_of_gt (mul_lt_of_lt_one_left (sub_pos.mpr huv) hc)) h2
  have hsub' : K⊆Set.range ((↑):NonAffineArray→DistanceArray) := fun d hd => ⟨⟨d,hsub hd⟩,rfl⟩
  exact IsEmbedding.subtypeVal.isInducing.isCompact_preimage' hK hsub'
lemma separated_secants_finite (μ:Measure NonAffineArray) [IsFiniteMeasureOnCompacts μ]
    (p q u v:DyadicTime) (hpq:(p:ℝ)<(q:ℝ)) (huv:(u:ℝ)<(v:ℝ)) (c:ℝ) (hc:c<1) :
    μ {d:NonAffineArray | d.val.val p q=(q:ℝ)-(p:ℝ) ∧ d.val.val u v ≤ c*((v:ℝ)-(u:ℝ))}<∞ :=
  (separated_secants_compact p q u v hpq huv c hc).measure_lt_top
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_EndpointIntensity
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter
open scoped ENNReal Topology Classical
namespace StandardMapEntropy
lemma preimage_sub_Ico (a b r:ℝ) : (fun x:ℝ => x-r)⁻¹'Ico a b=Ico (a+r) (b+r) := by
  ext x; simp only [mem_preimage,mem_Ico]; constructor <;> rintro ⟨h1,h2⟩ <;> constructor <;> linarith
lemma invariant_Ico_translate (μ:Measure ℝ) (r:ℝ) (h:μ.map (fun x:ℝ => x-r)=μ) (a b:ℝ) :
    μ (Ico (a+r) (b+r))=μ (Ico a b) := by
  rw [←preimage_sub_Ico,←Measure.map_apply (show Measurable (fun x:ℝ => x-r) from measurable_id.sub measurable_const) measurableSet_Ico,h]
lemma measure_Ico_split (μ:Measure ℝ) {a b c:ℝ} (hab:a≤b) (hbc:b ≤ c) :
    μ (Ico a c)=μ (Ico a b)+μ (Ico b c) := by
  have hu : Ico a c=Ico a b∪Ico b c := by
    ext x; simp only [mem_Ico,mem_union]; constructor
    · rintro ⟨ha,hc⟩; by_cases h:x<b
      · exact Or.inl ⟨ha,h⟩
      · exact Or.inr ⟨le_of_not_gt h,hc⟩
    · rintro (⟨ha,hb⟩|⟨hb,hc⟩)
      · exact ⟨ha,hb.trans_le hbc⟩
      · exact ⟨hab.trans hb,hc⟩
  rw [hu,measure_union (by rw [disjoint_left]; intro x hx hy; exact (not_lt_of_ge hy.1) hx.2) measurableSet_Ico]
lemma stationary_Ico_nat (μ:Measure ℝ)
    (ht:∀r:DyadicTime,μ.map (fun x:ℝ => x-(r:ℝ))=μ) (a:ℤ) (n:ℕ) :
    μ (Ico (a:ℝ) ((a:ℝ)+(n:ℝ)))=(n:ℝ≥0∞)*μ (Ico 0 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have he : μ (Ico ((a:ℝ)+(n:ℝ)) ((a:ℝ)+(n+1:ℕ)))=μ (Ico 0 1) := by
      have hh := invariant_Ico_translate μ (dyadicInt (a+n):ℝ) (ht (dyadicInt (a+n))) 0 1
      convert! hh using 2 ; simp only [dyadicInt_val,Int.cast_add,Int.cast_natCast,Nat.cast_add,Nat.cast_one] ; ring_nf
    rw [show ((a:ℝ)+(n+1:ℕ))=(a:ℝ)+(n:ℝ)+1 by push_cast; ring,
      measure_Ico_split μ (show (a:ℝ)≤(a:ℝ)+(n:ℝ) from le_add_of_nonneg_right (Nat.cast_nonneg n)) (by linarith),ih]
    have he' : μ (Ico ((a:ℝ)+(n:ℝ)) ((a:ℝ)+(n:ℝ)+1))=μ (Ico 0 1) := by convert! he using 2 ; push_cast ; ring_nf
    rw [he',Nat.cast_add,Nat.cast_one,add_mul,one_mul]
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_BandIntensity
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open Set Filter MeasureTheory Topology
open scoped ENNReal Classical
namespace StandardMapEntropy
lemma bandLaw_translate (μ:Measure NonAffineArray) (ht:∀r:DyadicTime,μ.map (nonaffineTranslation r)=μ) (r:DyadicTime) : (bandLaw μ).map (nonaffineTranslation r)=bandLaw μ :=
  map_restrict_invariant μ _ (nonaffineTranslation r).continuous.measurable (ht r) _ (measurableSet_lengthBand 0) (lengthBand_translate 0 r)
lemma bandIntensity_translate (μ:Measure NonAffineArray) (ht:∀r:DyadicTime,μ.map (nonaffineTranslation r)=μ) (r:DyadicTime) : (bandIntensity μ).map (fun x:ℝ => x-(r:ℝ))=bandIntensity μ := by
  apply push_invariant _ _ (nonaffineTranslation r).continuous.measurable (bandLaw_translate μ ht r)
    _ (measurable_endpointLeft.comp measurable_subtype_coe) _ (measurable_id.sub measurable_const)
  exact (ae_restrict_mem (measurableSet_lengthBand 0)).mono (fun d hd => (endpointLeft_translate r d.val hd.2.1.2.1 hd.2.1.1).symm)
lemma bandIntensity_finite (μ:Measure NonAffineArray) [IsFiniteMeasureOnCompacts μ]
    (hs:∀ᵐd ∂μ,SlowShape (realArray d.val) (999/1000)) : bandIntensity μ (Ico 0 1)<∞ := by
  have hbin (x:DyadicTime) (hx:0≤(x:ℝ)) :
      μ {d:NonAffineArray | d∈lengthBand 0 ∧ endpointLeft d.val∈Ico (x:ℝ) ((x:ℝ)+1/2)}<∞ := by
    apply lt_of_le_of_lt (measure_mono_ae ?_) (separated_secants_finite μ (dyadicInt (-1)) 0
      (x+dyadicHalf (dyadicInt 1)) (x+dyadicInt 1) (by norm_num) (by simp only [AddSubgroup.coe_add,dyadicHalf_val,dyadicInt_val,Int.cast_one]; linarith) (999/1000) (by norm_num))
    filter_upwards [hs] with d hsd
    rintro ⟨hd,ha⟩
    obtain ⟨hab,hl,hr,hslow⟩ := twoRay_properties hd.1 (by norm_num) hsd hd.2.1
    have hlen : 1≤endpointRight d.val-endpointLeft d.val := by simpa only [lengthBand,zpow_zero,coreLength] using hd.2.2.1
    refine ⟨?_,?_⟩
    · have hh := hl (dyadicInt (-1)) 0 (by norm_num; linarith [ha.1]) (by change (0:ℝ)≤endpointLeft d.val; linarith [ha.1])
      simpa only [dyadicInt_val,Int.cast_neg,Int.cast_one,ZeroMemClass.coe_zero,sub_neg_eq_add,zero_add,abs_of_pos (by norm_num : (0:ℝ)<1)] using hh
    · have hp : ((x+dyadicHalf (dyadicInt 1):DyadicTime):ℝ)=(x:ℝ)+1/2 := by simp only [AddSubgroup.coe_add,dyadicHalf_val,dyadicInt_val,Int.cast_one]
      have hq : ((x+dyadicInt 1:DyadicTime):ℝ)=(x:ℝ)+1 := by simp only [AddSubgroup.coe_add,dyadicInt_val,Int.cast_one]
      have hh := hslow (x+dyadicHalf (dyadicInt 1)) (x+dyadicInt 1)
        (by rw [hp]; constructor <;> linarith [ha.1,ha.2]) (by rw [hq]; constructor <;> linarith [ha.1,ha.2])
      rw [abs_of_pos (by rw [hp,hq]; linarith)] at hh
      exact hh
  have h0 := hbin 0 (by norm_num)
  have h1 := hbin (dyadicHalf (dyadicInt 1)) (by norm_num)
  change ((bandLaw μ).map (endpointLeft ∘ Subtype.val)) (Ico 0 1)<∞
  rw [Measure.map_apply (measurable_endpointLeft.comp measurable_subtype_coe) measurableSet_Ico,bandLaw,Measure.restrict_apply ((measurable_endpointLeft.comp measurable_subtype_coe) measurableSet_Ico)]
  apply lt_of_le_of_lt (measure_mono ?_) ((measure_union_le _ _).trans_lt (ENNReal.add_lt_top.mpr ⟨h0,h1⟩))
  rintro d ⟨ha,hd⟩
  by_cases h: endpointLeft d.val<1/2
  · exact Or.inl ⟨hd,by simpa only [mem_Ico,ZeroMemClass.coe_zero,zero_add,Function.comp_apply] using And.intro ha.1 h⟩
  · exact Or.inr ⟨hd,by simp only [mem_Ico,dyadicHalf_val,dyadicInt_val,Int.cast_one]; constructor; exact le_of_not_gt h; have ha1 : endpointLeft d.val<1 := ha.2; linarith⟩
lemma stationary_Ico_finite (μ:Measure ℝ)
    (ht:∀r:DyadicTime,μ.map (fun x:ℝ => x-(r:ℝ))=μ) (hf:μ (Ico 0 1)<∞) (a b:ℝ) : μ (Icc a b)<∞ := by
  obtain ⟨n,hn⟩ := exists_nat_gt (b-(⌊a⌋:ℤ))
  have he := stationary_Ico_nat μ ht ⌊a⌋ n
  apply lt_of_le_of_lt (measure_mono (t:=Ico (⌊a⌋:ℝ) ((⌊a⌋:ℝ)+n)) ?_) ?_
  · exact fun x hx => ⟨(Int.floor_le a).trans hx.1,by linarith [hx.2]⟩
  · rw [he]; exact ENNReal.mul_lt_top (by simp) hf
lemma bandLaw_endpoint_finite (μ:Measure NonAffineArray) [IsFiniteMeasureOnCompacts μ]
    (hs:∀ᵐd ∂μ,SlowShape (realArray d.val) (999/1000))
    (ht:∀r:DyadicTime,μ.map (nonaffineTranslation r)=μ) (a b:ℝ) :
    bandLaw μ {d:NonAffineArray | endpointLeft d.val∈Icc a b}<∞ := by
  have hh := stationary_Ico_finite (bandIntensity μ) (bandIntensity_translate μ ht) (bandIntensity_finite μ hs) a b
  change ((bandLaw μ).map (endpointLeft ∘ Subtype.val)) (Icc a b)<∞ at hh
  rw [Measure.map_apply (measurable_endpointLeft.comp measurable_subtype_coe) measurableSet_Icc] at hh
  exact hh
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_ScaleEvaluation
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open Set Filter MeasureTheory Topology
open scoped Classical
namespace StandardMapEntropy
lemma dyadicZoom_val (j:ℤ) (s:DyadicTime) : (dyadicZoom j s:ℝ)=(2:ℝ)^j*(s:ℝ) := by
  cases j with
  | ofNat n => simp only [dyadicZoom,AddSubgroup.coe_nsmul,nsmul_eq_mul,Nat.cast_pow,Nat.cast_ofNat,Int.ofNat_eq_natCast,zpow_natCast]
  | negSucc n =>
    rw [dyadicZoom,dyadicFine_val,Int.negSucc_eq,zpow_neg,zpow_add₀ (by norm_num : (2:ℝ)≠0),zpow_natCast,zpow_one,pow_succ]
    ring
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_BandGeometry
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open Set Filter MeasureTheory Topology
open scoped ENNReal Classical
namespace StandardMapEntropy
lemma twoRay_real_properties {d:DistanceArray} {c:ℝ} (hu:UnitArray d) (hc:c<1) (hs:SlowShape (realArray d) c)
    (hd:d∈twoRayClass) : ExteriorUnitRays (realArray d) (endpointLeft d) (endpointRight d) ∧
    (∀s t:ℝ,s∈Icc (endpointLeft d) (endpointRight d) → t∈Icc (endpointLeft d) (endpointRight d) → realArray d s t ≤ c*|t-s|) := by
  rcases hs with hs|⟨a,hl,hs⟩|⟨b,hr,hs⟩|⟨a,b,hab,⟨hl,hr⟩,hs⟩
  · have hh := endpoints_slow (d:=d) hc (fun s t => by simpa only [realArray_coe d hu] using hs s t)
    exact (hd.1 hh.1).elim
  · have hh := endpoints_left_ray (d:=d) hc
      (fun s t hp hq => by simpa only [realArray_coe d hu] using hl s hp t hq)
      (fun s t hp hq => by simpa only [realArray_coe d hu] using hs s hp t hq)
    exact (hd.2.2.2 hh.2).elim
  · have hh := endpoints_right_ray (d:=d) hc
      (fun s t hp hq => by simpa only [realArray_coe d hu] using hr s hp t hq)
      (fun s t hp hq => by simpa only [realArray_coe d hu] using hs s hp t hq)
    exact (hd.1 hh.1).elim
  · have hh := endpoints_two_rays (d:=d) hab hc
      (fun s t hp hq => by simpa only [realArray_coe d hu] using hl s t hp hq)
      (fun s t hp hq => by simpa only [realArray_coe d hu] using hr s t hp hq)
      (fun s t hp hq => by simpa only [realArray_coe d hu] using hs s hp t hq)
    have ha : endpointLeft d=a := by simp only [endpointLeft,hh.1,EReal.toReal_coe]
    have hb : endpointRight d=b := by simp only [endpointRight,hh.2,EReal.toReal_coe]
    rw [ha,hb]
    exact ⟨⟨hl,hr⟩,fun s t hp hq => hs s hp t hq⟩
lemma band_shortfall_bound (d:NonAffineArray) (hd:d∈lengthBand 0)
    (hs:SlowShape (realArray d.val) (999/1000)) (ht:TreeArray d.val)
    (hc:NoFastCancellation (realArray d.val) (1/100000000)) (t:DyadicTime) (hp:0<(t:ℝ)) :
    arrayShortfall 0 t d.val≤1200000004/(t:ℝ) := by
  have hh := twoRay_real_properties hd.1 (by norm_num) hs hd.2.1
  have hab := (twoRay_properties hd.1 (by norm_num) hs hd.2.1).1
  have hb := (exterior_ray_shortfall (realArray_treeLine d.val hd.1 ht) hab.le (by norm_num) hh.1 hc 0 t hp).2
  have hlen : coreLength d.val<2 := by simpa only [lengthBand,zpow_zero,zero_add,zpow_one] using hd.2.2.2
  have hreal : realArray d.val 0 (0+(t:ℝ))=d.val.val 0 t := by
    simpa only [ZeroMemClass.coe_zero,zero_add] using realArray_coe d.val hd.1 (0:DyadicTime) t
  rw [hreal] at hb
  change 1-d.val.val 0 t/((t:ℝ)-0)≤_
  rw [sub_zero]
  apply hb.trans
  apply (div_le_div_iff_of_pos_right hp).mpr
  unfold coreLength at hlen
  norm_num at *
  linarith
lemma band_cap_support (α:ℝ) (d:NonAffineArray) (hd:d∈lengthBand 0)
    (hs:SlowShape (realArray d.val) (999/1000)) (t:DyadicTime) (hp:0<(t:ℝ))
    (he:endpointLeft d.val∉Icc (-2) (t:ℝ)) : entropyCap α (arrayShortfall 0 t d.val)=0 := by
  obtain ⟨hab,hl,hr,hslow⟩ := twoRay_properties hd.1 (by norm_num) hs hd.2.1
  have hlen : endpointRight d.val-endpointLeft d.val<2 := by simpa only [lengthBand,zpow_zero,zero_add,zpow_one,coreLength] using hd.2.2.2
  have hh : d.val.val 0 t=(t:ℝ) := by
    by_cases h:endpointLeft d.val<(t:ℝ)
    · have ha : endpointLeft d.val< -2 := by by_contra hn; exact he ⟨le_of_not_gt hn,h.le⟩
      have hrr := hr 0 t (by change endpointRight d.val≤0; linarith) (by linarith)
      simpa only [ZeroMemClass.coe_zero,sub_zero,abs_of_pos hp] using hrr
    · have hll := hl 0 t (by change (0:ℝ)≤endpointLeft d.val; linarith) (le_of_not_gt h)
      simpa only [ZeroMemClass.coe_zero,sub_zero,abs_of_pos hp] using hll
  have heq : arrayShortfall 0 t d.val=0 := by
    unfold arrayShortfall; rw [hh,ZeroMemClass.coe_zero,sub_zero,div_self hp.ne']; ring
  rw [heq,entropyCap_linear (by norm_num),mul_zero]
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_BandCap
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open Set Filter MeasureTheory Topology
open scoped ENNReal Classical
namespace StandardMapEntropy
lemma measurable_bandCap (α:ℝ) (t:DyadicTime) : Measurable (bandCap α t) :=
  ((entropyCap_contDiff α).continuous.comp ((continuous_arrayShortfall 0 t).comp continuous_subtype_val)).measurable
lemma bandCap_nonneg {μ:Measure NonAffineArray} {α:ℝ} (ha:0≤α) (ha1:α≤1) (t:DyadicTime) (ht:0<(t:ℝ)) :
    0≤ᵐ[bandLaw μ] bandCap α t := by
  filter_upwards [ae_restrict_mem (measurableSet_lengthBand 0)] with d hd
  exact (entropyCap_bounds ha ha1 (shortfall_unit_mem d.val hd.1 0 t (by simpa only [ZeroMemClass.coe_zero]))).1
lemma bandCap_integrable (μ:Measure NonAffineArray) [IsFiniteMeasureOnCompacts μ]
    (hs:∀ᵐd ∂μ,SlowShape (realArray d.val) (999/1000))
    (hT:∀r:DyadicTime,μ.map (nonaffineTranslation r)=μ) {α:ℝ} (ha:0≤α) (ha1:α≤1)
    (t:DyadicTime) (ht:0<(t:ℝ)) : Integrable (bandCap α t) (bandLaw μ) := by
  let E:Set NonAffineArray := {d | endpointLeft d.val∈Icc (-2) (t:ℝ)}
  have hE : MeasurableSet E := (measurable_endpointLeft.comp measurable_subtype_coe) measurableSet_Icc
  have hf : bandLaw μ E<∞ := bandLaw_endpoint_finite μ hs hT _ _
  have : IsFiniteMeasure ((bandLaw μ).restrict E) := ⟨by simpa only [Measure.restrict_apply_univ] using hf⟩
  have hi : Integrable (E.indicator (fun _ => (1:ℝ))) (bandLaw μ) := IntegrableOn.integrable_indicator (integrable_const (μ:=(bandLaw μ).restrict E) (1:ℝ)) hE
  apply hi.mono' (measurable_bandCap α t).aestronglyMeasurable
  filter_upwards [ae_restrict_mem (measurableSet_lengthBand 0),ae_restrict_of_ae hs] with d hd hsd
  rw [Real.norm_eq_abs,bandCap,abs_of_nonneg ((entropyCap_bounds ha ha1 (shortfall_unit_mem d.val hd.1 0 t (by simpa only [ZeroMemClass.coe_zero]))).1)]
  by_cases he:d∈E
  · rw [indicator_of_mem he]; exact (entropyCap_bounds ha ha1 (shortfall_unit_mem d.val hd.1 0 t (by simpa only [ZeroMemClass.coe_zero]))).2
  · rw [indicator_of_notMem he]
    exact le_of_eq (band_cap_support α d hd hsd t ht he)
lemma bandCap_one_fine {α:ℝ} (d:NonAffineArray) (hd:d∈lengthBand 0)
    (hs:SlowShape (realArray d.val) (999/1000)) (he:endpointLeft d.val∈Ico (-1/2) 0)
    (t:DyadicTime) (ht:0<(t:ℝ)) (ht1:(t:ℝ)≤1/2) : bandCap α t d=1 := by
  obtain ⟨hab,hl,hr,hslow⟩ := twoRay_properties hd.1 (by norm_num) hs hd.2.1
  have hlen : 1≤endpointRight d.val-endpointLeft d.val := by simpa only [lengthBand,zpow_zero,coreLength] using hd.2.2.1
  have hb := hslow 0 t (by change (0:ℝ)∈Icc (endpointLeft d.val) (endpointRight d.val); constructor <;> linarith [he.1,he.2])
    (by constructor <;> linarith [he.1,he.2])
  rw [ZeroMemClass.coe_zero,sub_zero,abs_of_pos ht] at hb
  have hr := (div_le_iff₀ ht).mpr hb
  apply entropyCap_one
  change 3/10000≤1-d.val.val 0 t/((t:ℝ)-(0:DyadicTime))
  rw [ZeroMemClass.coe_zero,sub_zero]
  linarith
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_IntensityBounds
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open Set Filter MeasureTheory Topology
open scoped ENNReal Classical
namespace StandardMapEntropy
lemma stationary_half_real (μ:Measure ℝ)
    (ht:∀r:DyadicTime,μ.map (fun x:ℝ => x-(r:ℝ))=μ) (hf:μ (Ico 0 1)<∞) :
    (μ (Ico (-1/2) 0)).toReal=(μ (Ico 0 1)).toReal/2 := by
  have h1 : μ (Ico (1/2) 1)=μ (Ico 0 (1/2)) := by
    convert! invariant_Ico_translate μ (dyadicHalf (dyadicInt 1):ℝ) (ht _) 0 (1/2) using 2 ; norm_num
  have h2 : μ (Ico (-1/2) 0)=μ (Ico 0 (1/2)) := by
    have hh := invariant_Ico_translate μ (dyadicHalf (dyadicInt 1):ℝ) (ht _) (-1/2) 0
    convert! hh.symm using 2 ; norm_num
  have hzero : μ (Ico 0 (1/2))<∞ := lt_of_le_of_lt (measure_mono (Ico_subset_Ico_right (by norm_num : (1/2:ℝ)≤1))) hf
  have hh := measure_Ico_split μ (by norm_num : (0:ℝ)≤1/2) (by norm_num : (1/2:ℝ)≤1)
  rw [h1] at hh
  have hr := congrArg ENNReal.toReal hh
  rw [ENNReal.toReal_add hzero.ne hzero.ne] at hr
  rw [h2]; linarith
lemma stationary_interval_real_upper (μ:Measure ℝ)
    (ht:∀r:DyadicTime,μ.map (fun x:ℝ => x-(r:ℝ))=μ) (hf:μ (Ico 0 1)<∞) (n:ℕ) :
    (μ (Icc (-2) (n:ℝ))).toReal≤((n:ℝ)+3)*(μ (Ico 0 1)).toReal := by
  have hh : μ (Icc (-2) (n:ℝ))≤μ (Ico (-2) ((n:ℝ)+1)) := measure_mono (fun x hx => ⟨hx.1,by linarith [hx.2]⟩)
  have he : μ (Ico (-2) ((n:ℝ)+1))=(n+3:ℝ≥0∞)*μ (Ico 0 1) := by
    convert! stationary_Ico_nat μ ht (-2) (n+3) using 2 <;> push_cast <;> ring_nf
  rw [he] at hh
  have hb := ENNReal.toReal_mono (ENNReal.mul_ne_top (by simp) hf.ne) hh
  rw [ENNReal.toReal_mul,ENNReal.toReal_add (by simp : (n:ℝ≥0∞)≠∞) (by norm_num : (3:ℝ≥0∞)≠∞)] at hb
  simpa only [ENNReal.toReal_natCast,ENNReal.toReal_ofNat] using hb
lemma bandLaw_endpoint_map (μ:Measure NonAffineArray) (E:Set ℝ) (hE:MeasurableSet E) :
    bandLaw μ {d:NonAffineArray | endpointLeft d.val∈E}=bandIntensity μ E := by
  change (bandLaw μ) ((endpointLeft ∘ Subtype.val)⁻¹'E)=((bandLaw μ).map (endpointLeft ∘ Subtype.val)) E
  exact (Measure.map_apply (measurable_endpointLeft.comp measurable_subtype_coe) hE).symm
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_BandFlux
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open Set Filter MeasureTheory Topology
open scoped ENNReal Classical
namespace StandardMapEntropy
lemma band_fine_lower (μ:Measure NonAffineArray) [IsFiniteMeasureOnCompacts μ]
    (hs:∀ᵐd ∂μ,SlowShape (realArray d.val) (999/1000))
    (hT:∀r:DyadicTime,μ.map (nonaffineTranslation r)=μ) {α:ℝ} (ha:0≤α) (ha1:α≤1)
    (t:DyadicTime) (ht:0<(t:ℝ)) (ht1:(t:ℝ)≤1/2) :
    (bandIntensity μ (Ico 0 1)).toReal/2≤∫d,bandCap α t d ∂bandLaw μ := by
  let E:Set NonAffineArray := {d | endpointLeft d.val∈Ico (-1/2) 0}
  have hE : MeasurableSet E := (measurable_endpointLeft.comp measurable_subtype_coe) measurableSet_Ico
  have hh := setIntegral_le_integral (s:=E) (bandCap_integrable μ hs hT ha ha1 t ht) (bandCap_nonneg ha ha1 t ht)
  have he : bandCap α t=ᵐ[(bandLaw μ).restrict E] (fun _ => (1:ℝ)) := by
    filter_upwards [ae_restrict_mem hE,ae_restrict_of_ae (ae_restrict_mem (measurableSet_lengthBand 0)),ae_restrict_of_ae (ae_restrict_of_ae hs)] with d he hd hsd
    exact bandCap_one_fine d hd hsd he t ht ht1
  rw [integral_congr_ae he,integral_const] at hh
  simp only [smul_eq_mul,mul_one,measureReal_def,Measure.restrict_apply_univ] at hh
  rw [bandLaw_endpoint_map μ _ measurableSet_Ico,stationary_half_real _ (bandIntensity_translate μ hT) (bandIntensity_finite μ hs)] at hh
  exact hh
lemma band_coarse_upper (μ:Measure NonAffineArray) [IsFiniteMeasureOnCompacts μ]
    (hs:∀ᵐd ∂μ,SlowShape (realArray d.val) (999/1000))
    (hT:∀r:DyadicTime,μ.map (nonaffineTranslation r)=μ)
    (htree:∀ᵐd ∂μ,TreeArray d.val) (hcan:∀ᵐd ∂μ,NoFastCancellation (realArray d.val) (1/100000000))
    {α:ℝ} (ha:0≤α) (ha1:α≤1) (n:ℕ) (hn:0<n) (hsmall:1200000004/(n:ℝ)≤1/10000) :
    (∫d,bandCap α (dyadicInt n) d ∂bandLaw μ)≤
      (α*1200000004/(n:ℝ))*((n:ℝ)+3)*(bandIntensity μ (Ico 0 1)).toReal := by
  let t:DyadicTime := dyadicInt n
  have ht:0<(t:ℝ) := by simpa only [t,dyadicInt_val,Int.cast_natCast] using (Nat.cast_pos.mpr hn : (0:ℝ)<n)
  let E:Set NonAffineArray := {d | endpointLeft d.val∈Icc (-2) (n:ℝ)}
  have hE : MeasurableSet E := (measurable_endpointLeft.comp measurable_subtype_coe) measurableSet_Icc
  have hf : bandLaw μ E<∞ := bandLaw_endpoint_finite μ hs hT _ _
  have : IsFiniteMeasure ((bandLaw μ).restrict E) := ⟨by simpa only [Measure.restrict_apply_univ] using hf⟩
  let C:ℝ := α*1200000004/(n:ℝ)
  have hC:0≤C := by dsimp [C]; positivity
  have hi : Integrable (E.indicator (fun _ => C)) (bandLaw μ) := IntegrableOn.integrable_indicator (integrable_const (μ:=(bandLaw μ).restrict E) C) hE
  have hg : bandCap α t≤ᵐ[bandLaw μ] E.indicator (fun _ => C) := by
    filter_upwards [ae_restrict_mem (measurableSet_lengthBand 0),ae_restrict_of_ae hs,ae_restrict_of_ae htree,ae_restrict_of_ae hcan] with d hd hsd htd hcd
    by_cases he:d∈E
    · rw [indicator_of_mem he]
      have hb := band_shortfall_bound d hd hsd htd hcd t ht
      have hx : (t:ℝ)=(n:ℝ) := by simp only [t,dyadicInt_val,Int.cast_natCast]
      rw [hx] at hb
      rw [bandCap,entropyCap_linear (hb.trans hsmall)]
      exact (mul_le_mul_of_nonneg_left hb ha).trans_eq (by unfold C; ring)
    · rw [indicator_of_notMem he]
      exact le_of_eq (band_cap_support α d hd hsd t ht he)
  have hb := integral_mono_ae (bandCap_integrable μ hs hT ha ha1 t ht) hi hg
  rw [integral_indicator hE,integral_const] at hb
  simp only [smul_eq_mul,measureReal_def,Measure.restrict_apply_univ] at hb
  have hm : (bandLaw μ E).toReal≤((n:ℝ)+3)*(bandIntensity μ (Ico 0 1)).toReal := by
    rw [bandLaw_endpoint_map μ _ measurableSet_Icc]
    exact stationary_interval_real_upper _ (bandIntensity_translate μ hT) (bandIntensity_finite μ hs) n
  exact hb.trans ((mul_le_mul_of_nonneg_right hm hC).trans_eq (by unfold C; ring))
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_BandCoboundary
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open Set Filter MeasureTheory Topology
open scoped ENNReal Classical
namespace StandardMapEntropy
lemma zoom_one_pos (j:ℤ) : 0<(dyadicZoom j (dyadicInt 1):ℝ) := by
  rw [dyadicZoom_val,dyadicInt_val,Int.cast_one,mul_one]; positivity
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_BandComparison
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open Set Filter MeasureTheory Topology
open scoped ENNReal Classical
namespace StandardMapEntropy
lemma zoom_nat_one (n:ℕ) : dyadicZoom (n:ℤ) (dyadicInt 1)=dyadicInt ((2:ℕ)^n) := by
  apply Subtype.ext
  simp only [dyadicZoom_val,dyadicInt_val,Int.cast_one,mul_one,zpow_natCast,Nat.cast_ofNat,Int.cast_pow,Int.cast_ofNat]
lemma zoom_neg_one_le (n:ℕ) (hn:1≤n) : (dyadicZoom (-(n:ℤ)) (dyadicInt 1):ℝ)≤1/2 := by
  rw [dyadicZoom_val,dyadicInt_val,Int.cast_one,mul_one]
  have hh : (2:ℝ)^(-(n:ℤ))≤2^(-1:ℤ) := (zpow_right_strictMono₀ (by norm_num : (1:ℝ)<2)).monotone (by omega)
  norm_num at hh ⊢; exact hh
lemma bandMoment_fine (μ:Measure NonAffineArray) [IsFiniteMeasureOnCompacts μ]
    (hs:∀ᵐd ∂μ,SlowShape (realArray d.val) (999/1000))
    (hT:∀r:DyadicTime,μ.map (nonaffineTranslation r)=μ) {α:ℝ} (ha:0≤α) (ha1:α≤1) (n:ℕ) (hn:1≤n) :
    (bandIntensity μ (Ico 0 1)).toReal/2≤bandMoment μ α (-(n:ℤ)) :=
  band_fine_lower μ hs hT ha ha1 _ (zoom_one_pos _) (zoom_neg_one_le n hn)
lemma bandMoment_coarse (μ:Measure NonAffineArray) [IsFiniteMeasureOnCompacts μ]
    (hs:∀ᵐd ∂μ,SlowShape (realArray d.val) (999/1000))
    (hT:∀r:DyadicTime,μ.map (nonaffineTranslation r)=μ)
    (htree:∀ᵐd ∂μ,TreeArray d.val) (hcan:∀ᵐd ∂μ,NoFastCancellation (realArray d.val) (1/100000000))
    {α:ℝ} (ha:0≤α) (ha1:α≤1) (n:ℕ) (hn:1200000004/((2:ℝ)^n)≤1/10000) :
    bandMoment μ α (n:ℤ)≤4*(α*1200000004)*(bandIntensity μ (Ico 0 1)).toReal := by
  unfold bandMoment
  rw [zoom_nat_one]
  have hp:0<(2:ℕ)^n := pow_pos (by norm_num) _
  have hb:=band_coarse_upper μ hs hT htree hcan ha ha1 (2^n) hp (by exact_mod_cast hn)
  refine hb.trans ?_
  have hh:(1:ℝ)≤2^n := one_le_pow₀ (by norm_num)
  have haC:0≤α*1200000004 := mul_nonneg ha (by norm_num)
  have hv : (α*1200000004/(2:ℝ)^n)*((2:ℝ)^n+3)≤4*(α*1200000004) := by
    rw [div_mul_eq_mul_div,div_le_iff₀ (pow_pos (by norm_num) _)]; nlinarith
  convert mul_le_mul_of_nonneg_right hv (ENNReal.toReal_nonneg) using 1 ; norm_cast
lemma bandMoment_order_q44_oai (μ:Measure NonAffineArray) [IsFiniteMeasureOnCompacts μ]
    (hs:∀ᵐd ∂μ,SlowShape (realArray d.val) (999/1000))
    (hT:∀r:DyadicTime,μ.map (nonaffineTranslation r)=μ)
    (htree:∀ᵐd ∂μ,TreeArray d.val) (hcan:∀ᵐd ∂μ,NoFastCancellation (realArray d.val) (1/100000000))
    {α:ℝ} (ha:0≤α) (ha1:α≤1) (hasmall:α*1200000004≤1/16) :
    ∀ᶠn:ℕ in atTop, bandMoment μ α (n:ℤ)≤bandMoment μ α (-(n:ℤ)) := by
  have hp:Tendsto (fun n:ℕ => (2:ℝ)^n) atTop atTop := tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  have he:∀ᶠn:ℕ in atTop,1200000004/(2:ℝ)^n≤1/10000 := by
    filter_upwards [hp.eventually (eventually_ge_atTop (1200000004*10000:ℝ))] with n hn
    rw [div_le_iff₀ (pow_pos (by norm_num) _)]; linarith
  filter_upwards [he,eventually_ge_atTop (1:ℕ)] with n hn hn1
  have h1:=bandMoment_coarse μ hs hT htree hcan ha ha1 n hn
  have h2:=bandMoment_fine μ hs hT ha ha1 n hn1
  refine le_trans h1 (le_trans ?_ h2)
  have hI:=ENNReal.toReal_nonneg (a:=bandIntensity μ (Ico 0 1))
  nlinarith [mul_nonneg (by linarith : 0≤1/2-4*(α*1200000004)) hI]
end StandardMapEntropy

end OAI
end

theorem solution : type_of% @OAI.StandardMapEntropy.bandMoment_order_q44_oai := @OAI.StandardMapEntropy.bandMoment_order_q44_oai
