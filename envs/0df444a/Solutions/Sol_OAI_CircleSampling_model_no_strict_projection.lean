-- Prove2me | solution 1 for OAI.CircleSampling.model_no_strict_projection
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-25T22:15:28.221056+00:00
-- url     : https://prove2.me/submissions/4d1af762-6018-4144-9b92-f1aa2556fbf4

import Mathlib
import Definitions.Def_OAIQ2Rw002
import Theorems.Thm_OAI_CircleSampling_integrated_retained_bound

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

lemma block_number_equiv (j : ℕ) (i : Fin (blockLength j)) :
    coordinateBlock (blocks.equiv ⟨j,i⟩)=j := by
  exact blocks.number_eq (by change blockEnd j≤blockEnd j+i.val; omega)
    (by change blockEnd j+i.val<blockEnd j+blockLength j; omega)


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
end

open MeasureTheory Set Filter
open scoped ENNReal Topology

open CircleModel Set MeasureTheory
open scoped BigOperators

lemma sampleBound_pos (j : ℕ) : 0  <  sampleBound j :=
  Real.rpow_pos_of_pos (Nat.cast_pos.mpr (scaleStep j).mpos) _


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
lemma measure_Xi_lower {q : ℕ → ℕ} (hq : ∀ i, q i≠0) (i : ℕ) (r : ℝ) :
    volume {x : CircleX | Xi q i x < r} ≤ ENNReal.ofReal r := by
  change volume ((fun x : CircleX => q i • x) ⁻¹' (repr ⁻¹' Iio r)) ≤ _
  rw [(measurePreserving_XiMap hq i).measure_preimage (measurable_repr measurableSet_Iio).nullMeasurableSet]
  exact measure_repr_lower
end CircleModel

namespace CircleSampling

section
open CircleModel Set MeasureTheory Filter
open scoped ENNReal Topology BigOperators

lemma measure_iUnion_le_ofReal_tsum {ι : Type uι} {X : Type uX} [Countable ι] [MeasurableSpace X]
    (μ : Measure X) (A : ι → Set X) (b : ι → ℝ) (hb : ∀ i, 0 ≤ b i)
    (hs : Summable b) (h : ∀ i, μ (A i) ≤ ENNReal.ofReal (b i)) :
    μ (⋃ i, A i) ≤ ENNReal.ofReal (∑' i, b i) := by
  calc
    _ ≤ ∑' i, μ (A i) := measure_iUnion_le _
    _ ≤ ∑' i, ENNReal.ofReal (b i) := ENNReal.tsum_le_tsum h
    _ = _ := (ENNReal.ofReal_tsum_of_nonneg hb hs).symm

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
end
open Set
end CircleSampling

open MeasureTheory Set

end

end OAI
end

section
-- module Solutions.OAIQ2_Rot.RotationWeights_DigitCouplings
attribute [-instance] _root_.OAI.CircleCoupling.CoordinateParameters.instIsProbabilityMeasureSampleLaw _root_.OAI.CircleCoupling.DigitSystem.instIsProbabilityMeasureSampleLaw _root_.OAI.CircleCoupling.DigitSystem.instIsProbabilityMeasureSamplesProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CircleCoupling

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
section

lemma sixLaw_tag (l t u r : ℕ) [NeZero l] (ht : 0<t ∧ t<l) (hu : 0<u ∧ u<l)
    (hr : 0<r ∧ r<l) (p q τ : ℝ≥0∞) :
    sixLaw l t u r ht hu hr p q τ {ω | ω.1 = some (4 : Fin 5)} = τ := by
  have h := mixture_fiber_label (sixWeights p q τ) (1-(2*p+2*q+τ)) (diagonal l)
    (components l t u r ht hu hr) (fun _ => (0 : Fin l)) measurable_const 0 (4 : Fin 5)
  simpa [sixLaw,sixWeights,measure_univ] using h
end


end CircleCoupling

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

namespace CircleSampling
open MeasureTheory Set Filter ContinuousCircleWeight CircleCoupling
open scoped Topology ENNReal ComplexInnerProductSpace
lemma firstEndpoint_measurable : Measurable firstEndpoint := actualSystem.measurable_endpoint _
lemma lastEndpoint_measurable : Measurable lastEndpoint := actualSystem.measurable_endpoint _

lemma ae_endpoint_good (j : ℕ) (e : ℕ → Bool) :
    ∀ᵐ ω ∂actualSystem.probability (stageTagged j), actualSystem.endpoint e ω∈modelGood :=
  ae_of_ae_map (actualSystem.measurable_endpoint e).aemeasurable
    ((actualSystem.hybrid_ac (stageTagged j) e (summable_actual_error j)).ae_le model_good_ae)
end CircleSampling

end

end OAI
end

section
-- module Solutions.OAIQ2_Rot.RotationWeights_TaggedEvents
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

universe uι uX uΩ

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
namespace CircleCoupling

lemma independent_one_tag_bound {ι : Type uι} [DecidableEq ι] {X : ι → Type uX}
    [∀ i,MeasurableSpace (X i)] (μ : (i : ι) → Measure (X i)) [∀ i,IsProbabilityMeasure (μ i)]
    (s : Finset ι) (tag good : (i : ι) → Set (X i))
    (htag : ∀ i,MeasurableSet (tag i)) (hgood : ∀ i,MeasurableSet (good i))
    (hdis : ∀ i∈s,Disjoint (tag i) (good i)) {p a : ℝ} (hp : 0≤p) (ha : 0≤a)
    (ht : ∀ i∈s,p≤(μ i).real (tag i)) (hg : ∀ i∈s,a≤(μ i).real (good i)) :
    (s.card:ℝ)*p*a^(s.card-1) ≤
      (Measure.infinitePi μ).real (⋃ i∈s, Set.pi (s:Set ι) (fun k => if k=i then tag k else good k)) := by
  classical
  let A (i : ι) : Set (∀ k,X k) := Set.pi (s:Set ι) (fun k => if k=i then tag k else good k)
  have hA (i : ι) : MeasurableSet (A i) := by
    apply MeasurableSet.pi s.countable_toSet
    intro k _
    by_cases h:k=i <;> simp only [h,ite_true,ite_false] <;> first | exact htag k | exact hgood k
  have hd : (s:Set ι).PairwiseDisjoint A := by
    intro i hi j hj hij
    apply Set.disjoint_left.mpr
    intro ω hωi hωj
    have hx : ω i∈tag i := by simpa [A] using hωi i hi
    have hy : ω i∈good i := by simpa [A,hij] using hωj i hi
    exact Set.disjoint_left.mp (hdis i hi) hx hy
  change _≤(Measure.infinitePi μ).real (⋃ i∈s,A i)
  rw [measureReal_biUnion_finset hd (fun i _ => hA i)]
  calc
    _ = ∑ _i∈s,p*a^(s.card-1) := by simp; ring
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro i hi
      have he : (Measure.infinitePi μ).real (A i)=
          ∏ k∈s, (μ k).real (if k=i then tag k else good k) := by
        unfold Measure.real A
        rw [Measure.infinitePi_pi μ (by
          intro k _; by_cases h:k=i <;> simp only [h,ite_true,ite_false] <;> first | exact htag k | exact hgood k)]
        exact ENNReal.toReal_prod _ _
      rw [he]
      have hv : (∏ k∈s,if k=i then p else a)=p*a^(s.card-1) := by
        rw [←Finset.mul_prod_erase s (fun k => if k=i then p else a) hi]
        simp only [ite_true]
        have hn : ∀ k∈s.erase i,k≠i := fun k hk => (Finset.mem_erase.mp hk).1
        simp only [Finset.mem_erase] at hn
        simp_rw [Finset.prod_congr rfl (fun k hk => ite_eq_right ((Finset.mem_erase.mp hk).1))]
        simp [Finset.card_erase_of_mem hi]
      rw [←hv]
      apply Finset.prod_le_prod
      · intro k _; split <;> assumption
      · intro k hk
        by_cases h:k=i <;> simp only [h,ite_true,ite_false] <;> first | exact ht k hk | exact hg k hk

lemma log_one_sub_lower {t : ℝ} (ht : 0≤t) (ht1 : t≤1/2) : -2*t≤Real.log (1-t) := by
  have hp : 0<1-t := by linarith
  have hh := Real.one_sub_inv_le_log_of_pos hp
  have he : 1-(1-t)⁻¹= -t/(1-t) := by field_simp; ring
  rw [he] at hh
  apply le_trans _ hh
  rw [le_div_iff₀ hp]
  nlinarith

lemma one_tag_survival (m : ℕ) (hm : 200 ≤ m) : Real.exp (-86)≤(1-43/(m:ℝ))^(m-1) := by
  have hm0 : 0<(m:ℝ) := by exact_mod_cast (show 0 < m by omega)
  have ht : 0≤43/(m:ℝ) := by positivity
  have ht1 : 43/(m:ℝ) ≤ 1/2 := by
    rw [div_le_iff₀ hm0]
    have hh : (200:ℝ) ≤ m := by exact_mod_cast hm
    linarith
  have hb : 0<1-43/(m:ℝ) := by linarith
  rw [←Real.exp_log (pow_pos hb _),Real.log_pow,Real.exp_le_exp]
  calc
    -(86:ℝ) ≤ ((m-1:ℕ):ℝ)*(-2*(43/(m:ℝ))) := by
      rw [Nat.cast_sub (by omega : 1 ≤ m),Nat.cast_one]
      field_simp
      nlinarith
    _ ≤ _ := mul_le_mul_of_nonneg_left (log_one_sub_lower ht ht1) (Nat.cast_nonneg _)

open MeasureTheory Set
open scoped BigOperators ENNReal

lemma count_fin_lower (l : ℕ) {a : ℝ} (ha : 0 ≤ a) :
    ((Finset.univ.filter fun d : Fin l => (d.val:ℝ)<a).card:ℝ) ≤ a+1 := by
  classical
  have hc : (Finset.univ.filter fun d : Fin l => (d.val:ℝ)<a).card ≤ ⌈a⌉₊ := by
    calc
      _ ≤ (Finset.range ⌈a⌉₊).card := by
        apply Finset.card_le_card_of_injOn Fin.val
        · intro i hi
          exact Finset.mem_range.mpr (Nat.lt_ceil.mpr (Finset.mem_filter.mp hi).2)
        · exact Fin.val_injective.injOn
      _ = _ := Finset.card_range _
  exact (Nat.cast_le.mpr hc).trans (Nat.ceil_lt_add_one ha).le

lemma finite_fiber_mass {Ω : Type uΩ} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    {l : ℕ} (f : Ω → Fin l) (_hf : Measurable f) {B : ℝ} (hB : ∀ d,μ.real {ω | f ω=d} ≤ B)
    (s : Finset (Fin l)) : μ.real {ω | f ω∈s} ≤ (s.card:ℝ)*B := by
  classical
  have he : {ω | f ω∈s}=⋃ d∈s,{ω | f ω=d} := by ext ω; simp
  rw [he]
  calc
    _ ≤ ∑ d∈s,μ.real {ω | f ω=d} := measureReal_biUnion_finset_le _ _
    _ ≤ ∑ _d∈s,B := Finset.sum_le_sum (fun d _ => hB d)
    _ = _ := by simp

lemma finite_lower_fiber_mass {Ω : Type uΩ} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    {l : ℕ} (f : Ω → Fin l) (hf : Measurable f) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ d,μ.real {ω | f ω=d} ≤ B) {a : ℝ} (ha : 0 ≤ a) :
    μ.real {ω | ((f ω).val:ℝ)<a} ≤ (a+1)*B := by
  classical
  have hh := finite_fiber_mass μ f hf hB (Finset.univ.filter fun d => (d.val:ℝ)<a)
  simp only [Finset.mem_filter,Finset.mem_univ,true_and] at hh
  exact hh.trans (mul_le_mul_of_nonneg_right (count_fin_lower l ha) hB0)

namespace CoordinateParameters
variable (P : CoordinateParameters)

lemma law_tag_mass : (P.law true).real P.tagEvent=1/(P.m:ℝ) := by
  rw [Measure.real,tagEvent,law,sixLaw_tag,ENNReal.toReal_ofReal (P.τ_nonneg true)]
  rfl

lemma law_lower_digit (tagged e : Bool) {t : ℝ} (ht : 0 ≤ t) :
    (P.law tagged).real {z | ((digitEndpoint e z.2).val:ℝ)/(P.l:ℝ)<t} ≤ 10*(t+1/(P.l:ℝ)) := by
  have hl : (0:ℝ)<P.l := by exact_mod_cast (NeZero.pos P.l)
  have hh := finite_lower_fiber_mass (P.law tagged) (fun z => digitEndpoint e z.2)
    ((digitEndpoint_measurable e).comp measurable_snd) (by positivity : 0 ≤ 10/(P.l:ℝ))
    (P.law_density_ten tagged e) (mul_nonneg ht hl.le)
  simp_rw [div_lt_iff₀ hl]
  convert hh using 1; field_simp

lemma law_upper_digit (tagged e : Bool) {t : ℝ} (ht : 0 ≤ t) :
    (P.law tagged).real {z | 1-t<((digitEndpoint e z.2).val+1:ℝ)/(P.l:ℝ)} ≤ 10*(t+1/(P.l:ℝ)) := by
  have hl : (0:ℝ)<P.l := by exact_mod_cast (NeZero.pos P.l)
  have hf : ∀ d : Fin P.l, (P.law tagged).real {z | (digitEndpoint e z.2).rev=d} ≤ 10/(P.l:ℝ) := by
    intro d
    have he : {z : P.Sample | (digitEndpoint e z.2).rev=d}={z | digitEndpoint e z.2=d.rev} := by
      ext z
      change (digitEndpoint e z.2).rev=d ↔ digitEndpoint e z.2=d.rev
      constructor <;> intro h
      · simpa using congrArg Fin.rev h
      · rw [h]; simp
    rw [he]
    exact P.law_density_ten tagged e d.rev
  have hh := finite_lower_fiber_mass (P.law tagged) (fun z => (digitEndpoint e z.2).rev)
    (by measurability) (by positivity : 0 ≤ 10/(P.l:ℝ)) hf (mul_nonneg ht hl.le)
  have he : {z : P.Sample | 1-t<((digitEndpoint e z.2).val+1:ℝ)/(P.l:ℝ)}=
      {z : P.Sample | (((digitEndpoint e z.2).rev).val:ℝ)<t*P.l} := by
    ext z
    simp only [Set.mem_ofPred_eq,lt_div_iff₀ hl,Fin.val_rev]
    rw [Nat.cast_sub (by omega : (digitEndpoint e z.2).val+1 ≤ P.l)]
    push_cast
    constructor <;> intro h <;> linarith
  rw [he]
  convert hh using 1; field_simp

lemma law_untagged_margin_mass : 1-43/(P.m:ℝ) ≤ (P.law true).real P.untaggedMargin := by
  have hl : (0:ℝ)<P.l := by exact_mod_cast (NeZero.pos P.l)
  have hm := P.m_pos
  have hh : (P.law true).real P.untaggedMarginᶜ ≤
      1/(P.m:ℝ)+10*(2/(P.m:ℝ)+1/(P.l:ℝ))+10*(2/(P.m:ℝ)+1/(P.l:ℝ)) := by
    have he : P.untaggedMarginᶜ=P.tagEvent ∪ {z | 1-2/(P.m:ℝ)<((z.2.1.val:ℝ)+1)/(P.l:ℝ)} ∪
        {z | (z.2.2.val:ℝ)/(P.l:ℝ)<2/(P.m:ℝ)} := by
      ext z
      simp only [untaggedMargin,marginEvent,Set.mem_compl_iff,Set.mem_inter_iff,Set.mem_ofPred_eq,Set.mem_union,not_and_or,not_not,not_le,or_assoc]
    rw [he]
    calc
      _ ≤ (P.law true).real (P.tagEvent ∪ {z | 1-2/(P.m:ℝ)<((z.2.1.val:ℝ)+1)/(P.l:ℝ)})+
          (P.law true).real {z | (z.2.2.val:ℝ)/(P.l:ℝ)<2/(P.m:ℝ)} := measureReal_union_le _ _
      _ ≤ ((P.law true).real P.tagEvent + (P.law true).real {z | 1-2/(P.m:ℝ)<((z.2.1.val:ℝ)+1)/(P.l:ℝ)})+
          (P.law true).real {z | (z.2.2.val:ℝ)/(P.l:ℝ)<2/(P.m:ℝ)} := add_le_add (measureReal_union_le _ _) le_rfl
      _ ≤ _ := by rw [P.law_tag_mass]; exact add_le_add (add_le_add le_rfl (P.law_upper_digit true false (t:=2/(P.m:ℝ)) (by positivity))) (P.law_lower_digit true true (t:=2/(P.m:ℝ)) (by positivity))
  rw [measureReal_compl (by measurability : MeasurableSet P.untaggedMargin)] at hh
  simp only [probReal_univ] at hh
  have hr : 1/(P.l:ℝ) ≤ 1/(100*(P.m:ℝ)) := by
    apply one_div_le_one_div_of_le (by positivity)
    exact_mod_cast P.hl
  have hb : 1/(P.m:ℝ)+20*(2/(P.m:ℝ)+1/(P.l:ℝ)) ≤ 43/(P.m:ℝ) := by
    calc
      _ ≤ 1/(P.m:ℝ)+20*(2/(P.m:ℝ)+1/(100*(P.m:ℝ))) := by gcongr
      _ ≤ _ := by field_simp; nlinarith
  linarith
end CoordinateParameters
end CircleCoupling

namespace CircleCoupling.DigitSystem
open MeasureTheory Set
open scoped BigOperators
variable (S : DigitSystem)

lemma measurableSet_coordinateTag (n : ℕ) : MeasurableSet (S.coordinateTag n) := by
  cases n <;> measurability
lemma measurableSet_coordinateMargin (n : ℕ) : MeasurableSet (S.coordinateMargin n) := by
  cases n <;> measurability
lemma measurableSet_coordinateUntaggedMargin (n : ℕ) : MeasurableSet (S.coordinateUntaggedMargin n) :=
  (S.measurableSet_coordinateTag n).compl.inter (S.measurableSet_coordinateMargin n)

lemma measurableSet_oneTagEvent (I : Finset ℕ) : MeasurableSet (S.oneTagEvent I) := by
  apply MeasurableSet.biUnion (Set.to_countable _)
  intro i _
  apply MeasurableSet.pi I.countable_toSet
  intro k _
  by_cases h:k=i <;> simp only [h,ite_true,ite_false] <;>
    first | exact S.measurableSet_coordinateTag k | exact S.measurableSet_coordinateUntaggedMargin k

lemma oneTagEvent_mass (tagged : ℕ → Bool) (I : Finset ℕ) (m : ℕ)
    (hm : 200 ≤ m) (hc : I.card=m) (hzero : 0∉I)
    (hmI : ∀ n, n+1∈I → (S.coord n).m=m)
    (htI : ∀ n, n+1∈I → tagged n=true) :
    Real.exp (-86) ≤ (S.probability tagged).real (S.oneTagEvent I) := by
  have hm0 : 0 < (m:ℝ) := by exact_mod_cast (by omega : 0 < m)
  have ha : 0 ≤ 1-43/(m:ℝ) := by
    have hh : (200:ℝ) ≤ m := by exact_mod_cast hm
    have hd : 43/(m:ℝ) ≤ 1 := (div_le_one hm0).mpr (by linarith)
    linarith
  have hh := independent_one_tag_bound (S.law tagged) I S.coordinateTag S.coordinateUntaggedMargin
    S.measurableSet_coordinateTag S.measurableSet_coordinateUntaggedMargin
    (fun i _ => Set.disjoint_left.mpr (fun _ ht hg => hg.1 ht))
    (by positivity : 0 ≤ 1/(m:ℝ)) ha (fun i hi => ?_) (fun i hi => ?_)
  · change _ ≤ (S.probability tagged).real (S.oneTagEvent I) at hh
    rw [hc] at hh
    have hid : (m:ℝ)*(1/(m:ℝ))=1 := by field_simp
    rw [hid,one_mul] at hh
    exact (one_tag_survival m hm).trans hh
  · cases i with
    | zero => exact False.elim (hzero hi)
    | succ n =>
      change 1/(m:ℝ) ≤ ((S.coord n).law (tagged n)).real (S.coord n).tagEvent
      rw [htI n hi,(S.coord n).law_tag_mass,hmI n hi]
  · cases i with
    | zero => exact False.elim (hzero hi)
    | succ n =>
      change 1-43/(m:ℝ) ≤ ((S.coord n).law (tagged n)).real (S.coord n).untaggedMargin
      rw [htI n hi,←hmI n hi]
      exact (S.coord n).law_untagged_margin_mass

end CircleCoupling.DigitSystem

namespace CircleSampling
open MeasureTheory Set CircleCoupling
open scoped BigOperators ENNReal

lemma stageTagEvent_measurable (j : ℕ) : MeasurableSet (stageTagEvent j) := actualSystem.measurableSet_oneTagEvent _
lemma stageTagEvent_mass (j : ℕ) : Real.exp (-86) ≤ (actualSystem.probability (stageTagged j)).real (stageTagEvent j) := by
  apply actualSystem.oneTagEvent_mass (stageTagged j) (blockCoordinates j) (blockLength j)
    (blockLength_ge_twoHundred j) (blockCoordinates_card j) (blockCoordinates_zero j)
  · intro n hn
    change blockLength (coordinateBlock n)=_
    rw [blockCoordinates_block j n hn]
  · intro n hn
    simp only [stageTagged,blockCoordinates_block j n hn,decide_true]

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
-- module Solutions.OAIQ2_Rot.RotationWeights_TailBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CircleSampling

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
open MeasureTheory Set
open scoped BigOperators ENNReal

section
open CircleModel Set
open scoped BigOperators

lemma sum_drop_prefix (j : ℕ) : (∑ i∈Finset.range (blockEnd j),coordinateDrop i)=(scaleState j).1.E := by
  induction j with
  | zero => rfl
  | succ j ih =>
    change (∑ i∈Finset.range (blockEnd j+blockLength j),coordinateDrop i)=(scaleState j).1.E+dropSize j*blockLength j
    rw [Finset.sum_range_add,ih]
    congr 1
    have he (i : ℕ) (hi : i∈Finset.range (blockLength j)) : coordinateDrop (blockEnd j+i)=dropSize j := by
      change dropSize (blocks.number (blockEnd j+i))=dropSize j
      congr 1
      apply blocks.number_eq (by change blockEnd j ≤ blockEnd j+i; omega)
      change blockEnd j+i<blockEnd j+blockLength j
      exact Nat.add_lt_add_left (Finset.mem_range.mp hi) _
    rw [Finset.sum_congr rfl he]
    simp [mul_comm]

lemma floor_abs_bound (k : ℤ) (K : ℕ) (hk : |(k:ℝ)| ≤ (K:ℝ)) (x : CircleX) (i : ℕ) :
    |(floorTerm modelFrequency modelAngle k x i:ℝ)| ≤ (K:ℝ)+1 := by
  let z := Xi modelFrequency i x+(k:ℝ)*beta modelFrequency modelAngle i
  have hx := repr_mem (modelFrequency i • x)
  have hb := repr_mem (modelFrequency i • modelAngle)
  change 0 ≤ Xi modelFrequency i x ∧ Xi modelFrequency i x<1 at hx
  change 0 ≤ beta modelFrequency modelAngle i ∧ beta modelFrequency modelAngle i<1 at hb
  have hp : |(k:ℝ)*beta modelFrequency modelAngle i| ≤ (K:ℝ) := by
    rw [abs_mul,abs_of_nonneg hb.1]
    exact (mul_le_mul_of_nonneg_left hb.2.le (abs_nonneg _)).trans (by simpa using hk)
  have hzlo : -(K:ℝ) ≤ z := by have hh := (abs_le.mp hp).1; dsimp [z]; linarith
  have hzhi : z ≤ (K:ℝ)+1 := by have hh := (abs_le.mp hp).2; dsimp [z]; linarith
  change |(⌊z⌋:ℝ)| ≤ _
  exact abs_le.mpr ⟨by linarith [Int.lt_floor_add_one z],(Int.floor_le z).trans hzhi⟩

lemma exponent_prefix_bound (j : ℕ) (k : ℤ) (x : CircleX) (hk : |(k:ℝ)| ≤ (polynomialWindow j:ℝ))
    (ht : ∀ i,blockEnd j ≤ i → floorTerm modelFrequency modelAngle k x i=0) :
    |exponent modelFrequency modelAngle coordinateDrop k x| ≤ ((polynomialWindow j:ℝ)+1)*(scaleState j).1.E := by
  have he : exponent modelFrequency modelAngle coordinateDrop k x =
      ∑ i∈Finset.range (blockEnd j),coordinateDrop i*(floorTerm modelFrequency modelAngle k x i:ℝ) := by
    apply tsum_eq_sum
    intro i hi
    rw [ht i (by simpa using hi),Int.cast_zero,mul_zero]
  rw [he]
  calc
    _ ≤ ∑ i∈Finset.range (blockEnd j),|coordinateDrop i*(floorTerm modelFrequency modelAngle k x i:ℝ)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i∈Finset.range (blockEnd j),coordinateDrop i*((polynomialWindow j:ℝ)+1) := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul,abs_of_nonneg (show 0 ≤ coordinateDrop i from dropSize_nonneg (coordinateBlock i))]
      exact mul_le_mul_of_nonneg_left (floor_abs_bound k _ hk x i) (dropSize_nonneg (coordinateBlock i))
    _ = _ := by rw [←Finset.sum_mul,sum_drop_prefix]; ring

lemma coefficientCap_ge_one (j : ℕ) : 1 ≤ coefficientCap j := Real.one_le_exp (mul_nonneg (by positivity) (scaleState j).2.Ege)
lemma modelF_prefix_bound (j : ℕ) (k : ℤ) {x : CircleX} (hx : x∈modelGood)
    (hk : |(k:ℝ)| ≤ (polynomialWindow j:ℝ))
    (ht : ∀ i,blockEnd j ≤ i → floorTerm modelFrequency modelAngle k x i=0) :
    modelF k x≤coefficientCap j ∧ 1/modelF k x≤coefficientCap j := by
  have hb := exponent_prefix_bound j k x hk ht
  change x∈good modelFrequency modelAngle at hx
  simp only [modelF,cocycle,ite_eq_left hx]
  constructor
  · apply Real.exp_le_exp.mpr
    have hh := (abs_le.mp hb).1
    linarith
  · rw [one_div,←Real.exp_neg,neg_neg]
    apply Real.exp_le_exp.mpr
    exact le_of_abs_le hb
end

section
open CircleModel MeasureTheory Set Filter
open scoped Topology ENNReal BigOperators

lemma futureBad_measurable (j : ℕ) (e : Bool) : MeasurableSet (futureBad j e) := by
  apply MeasurableSet.iUnion; intro s
  apply MeasurableSet.iUnion; intro a
  cases e
  · exact measurableSet_le measurable_const (measurable_Xi _ _)
  · exact measurableSet_lt (measurable_Xi _ _) measurable_const
lemma futureBad_bound (j : ℕ) (e : Bool) : volume.real (futureBad j e) ≤ 4*(polynomialWindow j:ℝ)/(polynomialWindow (j+1):ℝ) := by
  have hq : ∀ i,modelFrequency i≠0 := fun i => (frequency_pos (i+1)).ne'
  have hblock (s : ℕ) : volume (⋃ a : Fin (blockLength (j+1+s)),
      {x : CircleX | if e then Xi modelFrequency (blocks.equiv ⟨j+1+s,a⟩) x < 2*(polynomialWindow j:ℝ)/blockScale (j+1+s)
      else 1-2*(polynomialWindow j:ℝ)/blockScale (j+1+s) ≤ Xi modelFrequency (blocks.equiv ⟨j+1+s,a⟩) x}) ≤ ENNReal.ofReal (2*(polynomialWindow j:ℝ)/(polynomialWindow (j+1+s):ℝ)) := by
    have hm : (blockLength (j+1+s):ℝ)≠0 := (Nat.cast_pos.mpr (scaleStep (j+1+s)).mpos).ne'
    apply (measure_iUnion_le_ofReal_tsum volume _ (fun _ => 2*(polynomialWindow j:ℝ)/blockScale (j+1+s))
      (fun _ => div_nonneg (by positivity) (blockScale_pos _).le) (Summable.of_finite) ?_).trans
    · apply ENNReal.ofReal_le_ofReal
      rw [tsum_fintype]
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,blockScale]
      field_simp
      rfl
    · intro a
      cases e
      · exact measure_Xi_upper hq _ _
      · exact measure_Xi_lower hq _ _
  have hs : Summable (fun s => 2*(polynomialWindow j:ℝ)/(polynomialWindow (j+1+s):ℝ)) := by
    simpa only [div_eq_mul_inv,one_mul] using (summable_window_inverse (j+1)).mul_left (2*(polynomialWindow j:ℝ))
  have hm := measure_iUnion_le_ofReal_tsum volume _ _ (fun s => by positivity) hs hblock
  apply (ENNReal.toReal_le_of_le_ofReal (tsum_nonneg (fun _ => by positivity)) hm).trans
  simp_rw [div_eq_mul_inv]
  rw [tsum_mul_left]
  calc
    _ ≤ 2*(polynomialWindow j:ℝ)*(2/(polynomialWindow (j+1):ℝ)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      simpa only [one_div] using tsum_window_inverse (j+1)
    _ = _ := by ring
lemma window_div_next (j : ℕ) : (polynomialWindow j:ℝ)/(polynomialWindow (j+1):ℝ) ≤ 1/(blockLength j:ℝ) := by
  apply le_trans _ (sampleBound_div_window j)
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  have hm : (1:ℝ) ≤ blockLength j := by exact_mod_cast (scaleStep j).mpos
  have hm200 : (200:ℝ) ≤ blockLength j := by exact_mod_cast blockLength_ge j
  apply (Nat.cast_le.mpr (polynomialWindow_le_length j)).trans
  calc
    (blockLength j:ℝ) = (blockLength j:ℝ)^(1:ℝ) := (Real.rpow_one _).symm
    _ ≤ sampleBound j := Real.rpow_le_rpow_of_exponent_le hm (by linarith)
lemma futureBad_tendsto (e : Bool) : Tendsto (fun j => volume.real (futureBad j e)) atTop (𝓝 0) := by
  have hupper (j : ℕ) : volume.real (futureBad j e) ≤ 4/(blockLength j:ℝ) := by
    apply (futureBad_bound j e).trans
    have h := mul_le_mul_of_nonneg_left (window_div_next j) (by norm_num : (0:ℝ) ≤ 4)
    simpa only [div_eq_mul_inv,mul_assoc,mul_one,one_mul] using h
  apply squeeze_zero (fun _ => measureReal_nonneg) hupper
  simpa only [div_eq_mul_inv,one_mul,mul_zero,Function.comp_def] using
    ((tendsto_one_div_atTop_nhds_zero_nat (𝕜:=ℝ)).comp blockLength_strictMono.tendsto_atTop).const_mul 4

lemma measure_small_positive_tendsto {X : Type uX} [MeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]
    (r : X → ℝ) (hr : Measurable r) (hp : ∀ᵐ x ∂μ,0<r x) :
    Tendsto (fun j : ℕ => μ.real {x | r x<1/((j:ℝ)+1)}) atTop (𝓝 0) := by
  have hm : Antitone (fun j : ℕ => {x | r x<1/((j:ℝ)+1)}) := by
    intro j k hjk x hx
    change r x<1/((k:ℝ)+1) at hx
    change r x<1/((j:ℝ)+1)
    exact hx.trans_le (one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hjk 1))
  have hi : μ (⋂ j : ℕ,{x | r x<1/((j:ℝ)+1)})=0 := by
    apply measure_mono_null _ (ae_iff.mp hp)
    intro x hx
    simp only [mem_iInter,mem_ofPred_eq] at hx ⊢
    by_contra! hp'
    have he : ∀ᶠ j : ℕ in atTop,1/((j:ℝ)+1)<r x := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜:=ℝ)).eventually (gt_mem_nhds hp')
    obtain ⟨j,hj⟩ := he.exists
    exact (hx j).not_gt hj
  have hh := tendsto_measure_iInter_atTop (μ:=μ) (fun j => (measurableSet_lt hr measurable_const).nullMeasurableSet) hm ⟨0,measure_ne_top _ _⟩
  rw [hi] at hh
  simpa only [Function.comp_def,ENNReal.toReal_zero,Measure.real] using (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hh
end

section
open MeasureTheory Set Filter CircleCoupling
open scoped Topology ENNReal

lemma endpointBad_measurable {r : CircleX → ℝ} (hr : Measurable r) (j : ℕ) (e : Bool) : MeasurableSet (endpointBad r j e) := by
  apply (futureBad_measurable j e).union
  apply measurableSet_lt _ measurable_const
  cases e
  · exact hr
  · exact measurable_const.sub hr
lemma projectionEvent_measurable {r : CircleX → ℝ} (hr : Measurable r) (j : ℕ) : MeasurableSet (projectionEvent r j) :=
  (stageTagEvent_measurable j).diff (((endpointBad_measurable hr j false).preimage firstEndpoint_measurable).union
    ((endpointBad_measurable hr j true).preimage lastEndpoint_measurable))
lemma endpointBad_tendsto {r : CircleX → ℝ} (hr : Measurable r) (hp : ∀ᵐ x,0<r x ∧ r x<1) (e : Bool) :
    Tendsto (fun j => volume.real (endpointBad r j e)) atTop (𝓝 0) := by
  have hpos : ∀ᵐ x,0<(if e then 1-r x else r x) := by
    filter_upwards [hp] with x hx
    cases e <;> simp only [Bool.false_eq_true,↓reduceIte] <;> linarith [hx.1,hx.2]
  have hm : Measurable (fun x => if e then 1-r x else r x) := by cases e <;> first | exact hr | exact measurable_const.sub hr
  apply squeeze_zero (fun _ => measureReal_nonneg) (fun j => measureReal_union_le _ _) ?_
  simpa using (futureBad_tendsto e).add (measure_small_positive_tendsto volume _ hm hpos)
lemma endpointBad_loss_tendsto {r : CircleX → ℝ} (hr : Measurable r) (hp : ∀ᵐ x,0<r x ∧ r x<1) (e : Bool) :
    Tendsto (fun j => (actualSystem.probability (stageTagged j)).real ((actualSystem.endpoint (fun _ => e)) ⁻¹' endpointBad r j e)) atTop (𝓝 0) := by
  apply squeeze_zero (fun _ => measureReal_nonneg) (fun j => actual_hybrid_bound j (fun _ => e) _ (endpointBad_measurable hr j e)) ?_
  simpa using ((Real.continuous_sqrt.tendsto 0).comp (endpointBad_tendsto hr hp e)).const_mul marginalConstant
lemma projectionEvent_mass {r : CircleX → ℝ} (hr : Measurable r) (hp : ∀ᵐ x,0<r x ∧ r x<1) :
    ∀ᶠ j in atTop, Real.exp (-86)/2 ≤ (actualSystem.probability (stageTagged j)).real (projectionEvent r j) := by
  have hl : Tendsto (fun j => (actualSystem.probability (stageTagged j)).real (firstEndpoint ⁻¹' endpointBad r j false)+
      (actualSystem.probability (stageTagged j)).real (lastEndpoint ⁻¹' endpointBad r j true)) atTop (𝓝 0) := by
    simpa only [add_zero,firstEndpoint,lastEndpoint] using (endpointBad_loss_tendsto hr hp false).add (endpointBad_loss_tendsto hr hp true)
  have he := hl.eventually (gt_mem_nhds (by positivity : (0:ℝ)<Real.exp (-86)/2))
  filter_upwards [he] with j hj
  have hm := stageTagEvent_mass j
  have hd : (actualSystem.probability (stageTagged j)).real (stageTagEvent j)-
      (actualSystem.probability (stageTagged j)).real (firstEndpoint ⁻¹' endpointBad r j false ∪ lastEndpoint ⁻¹' endpointBad r j true) ≤
      (actualSystem.probability (stageTagged j)).real (projectionEvent r j) := le_measureReal_sdiff
  have hu := measureReal_union_le (μ:=actualSystem.probability (stageTagged j))
    (firstEndpoint ⁻¹' endpointBad r j false) (lastEndpoint ⁻¹' endpointBad r j true)
  linarith
lemma projectionEvent_mem {r : CircleX → ℝ} {j : ℕ} {ω : ActualSamples} (hω : ω∈projectionEvent r j) :
    ω∈stageTagEvent j ∧ firstEndpoint ω∉futureBad j false ∧ lastEndpoint ω∉futureBad j true ∧
    1/((j:ℝ)+1) ≤ r (firstEndpoint ω) ∧ 1/((j:ℝ)+1) ≤ 1-r (lastEndpoint ω) := by
  have h := hω.2
  simp only [Set.mem_union,Set.mem_preimage,endpointBad,Set.mem_ofPred_eq,Bool.false_eq_true,↓reduceIte,not_or,not_lt] at h
  exact ⟨hω.1,h.1.1,h.2.1,h.1.2,h.2.2⟩
end

open MeasureTheory Set CircleCoupling CircleDigits CircleModel
open scoped ENNReal

lemma not_futureBad_iff (j s : ℕ) (hjs : j<s) (a : Fin (blockLength s)) (x : CircleX) (e : Bool)
    (hx : x∉futureBad j e) :
    if e then 2*(polynomialWindow j:ℝ)/blockScale s ≤ Xi modelFrequency (blocks.equiv ⟨s,a⟩) x
    else Xi modelFrequency (blocks.equiv ⟨s,a⟩) x<1-2*(polynomialWindow j:ℝ)/blockScale s := by
  obtain ⟨t,rfl⟩ := Nat.exists_eq_add_of_le (by omega : j+1 ≤ s)
  have hh : ¬(if e then Xi modelFrequency (blocks.equiv ⟨j+1+t,a⟩) x<2*(polynomialWindow j:ℝ)/blockScale (j+1+t)
      else 1-2*(polynomialWindow j:ℝ)/blockScale (j+1+t) ≤ Xi modelFrequency (blocks.equiv ⟨j+1+t,a⟩) x) := by
    intro h
    apply hx
    exact mem_iUnion.mpr ⟨t,mem_iUnion.mpr ⟨a,h⟩⟩
  cases e <;> simpa only [Bool.false_eq_true,↓reduceIte,not_lt,not_le] using hh

lemma event_tail_margins {r : CircleX → ℝ} (j : ℕ) {ω : ActualSamples}
    (hω : ω∈regularSamples) (he : ω∈projectionEvent r j) (s : ℕ) (hjs : j ≤ s) (a : Fin (blockLength s)) :
    Xi modelFrequency (blocks.equiv ⟨s,a⟩) (firstEndpoint ω)<1-2*(polynomialWindow j:ℝ)/blockScale s ∧
    2*(polynomialWindow j:ℝ)/blockScale s ≤ Xi modelFrequency (blocks.equiv ⟨s,a⟩) (lastEndpoint ω) := by
  have hh := projectionEvent_mem he
  rcases hjs.eq_or_lt with rfl | hjs
  · have hi : blocks.equiv ⟨j,a⟩+1∈blockCoordinates j := by
      simp only [blockCoordinates,Finset.mem_Ico]
      change blockEnd j+1 ≤ blockEnd j+a.val+1 ∧ blockEnd j+a.val+1<blockEnd (j+1)+1
      have hs := blocks.step j
      change blockEnd (j+1)=blockEnd j+blockLength j at hs
      have ha := a.isLt
      omega
    have hm := (stageTagEvent_margins j hω.1 hh.1).2 _ hi
    have hx := (digit_interval actualSystem.radix_ge_two (fun i => (ω i).2.1) hω.2.2.2.1 (blocks.equiv ⟨j,a⟩+1)).2
    have hy := (digit_interval actualSystem.radix_ge_two (fun i => (ω i).2.2) hω.2.2.2.2 (blocks.equiv ⟨j,a⟩+1)).1
    rw [(actual_Xi_tail hω _).1,(actual_Xi_tail hω _).2]
    have hr : 2*(polynomialWindow j:ℝ)/blockScale j=2/(blockLength j:ℝ) := by
      have hK : (polynomialWindow j:ℝ)≠0 := (Nat.cast_pos.mpr (polynomialWindow_pos j)).ne'
      unfold blockScale; field_simp
    rw [hr]
    exact ⟨hx.trans_le hm.1,hm.2.trans hy⟩
  · exact ⟨not_futureBad_iff j s hjs a _ false hh.2.1,not_futureBad_iff j s hjs a _ true hh.2.2.1⟩

lemma event_floor_tail {r : CircleX → ℝ} (j : ℕ) {ω : ActualSamples}
    (hω : ω∈regularSamples) (he : ω∈projectionEvent r j) (k : ℤ)
    (hk0 : 0 ≤ k) (hk : k ≤ (polynomialWindow j:ℤ)) (n : ℕ) (hn : blockEnd j ≤ n) :
    floorTerm modelFrequency modelAngle k (firstEndpoint ω) n=0 ∧
    floorTerm modelFrequency modelAngle (-k) (lastEndpoint ω) n=0 := by
  obtain ⟨⟨s,a⟩,rfl⟩ := blocks.equiv.surjective n
  change Fin (blockLength s) at a
  have hjs : j ≤ s := by
    by_contra! hsj
    have hs := blocks.strictMono.monotone (by omega : s+1 ≤ j)
    have ha := a.isLt
    have ht := blocks.step s
    change blockEnd (s+1) ≤ blockEnd j at hs
    change blockEnd (s+1)=blockEnd s+blockLength s at ht
    change blockEnd j ≤ blockEnd s+a.val at hn
    omega
  have hm := event_tail_margins j hω he s hjs a
  have hb := coordinatePhase_bounds (blocks.equiv ⟨s,a⟩)
  rw [block_number_equiv s a] at hb
  have hk0' : (0:ℝ) ≤ k := by exact_mod_cast hk0
  have hk' : (k:ℝ) ≤ polynomialWindow j := by exact_mod_cast hk
  have hmul0 : 0 ≤ (k:ℝ)*coordinatePhase (blocks.equiv ⟨s,a⟩) := mul_nonneg hk0' (coordinatePhase_pos _).le
  have hmul : (k:ℝ)*coordinatePhase (blocks.equiv ⟨s,a⟩) ≤ 2*(polynomialWindow j:ℝ)/blockScale s := by
    calc
      _ ≤ (polynomialWindow j:ℝ)*(2/blockScale s) := mul_le_mul hk' hb.2.le (coordinatePhase_pos _).le (Nat.cast_nonneg _)
      _ = _ := by ring
  have hx := repr_mem (modelFrequency (blocks.equiv ⟨s,a⟩) • firstEndpoint ω)
  have hy := repr_mem (modelFrequency (blocks.equiv ⟨s,a⟩) • lastEndpoint ω)
  change 0 ≤ Xi modelFrequency _ (firstEndpoint ω) ∧ Xi modelFrequency _ (firstEndpoint ω)<1 at hx
  change 0 ≤ Xi modelFrequency _ (lastEndpoint ω) ∧ Xi modelFrequency _ (lastEndpoint ω)<1 at hy
  simp only [floorTerm,model_beta,Int.cast_neg]
  constructor <;> apply Int.floor_eq_iff.mpr <;> norm_num only [Int.cast_zero,zero_add] <;>
    constructor <;> nlinarith [hm.1,hm.2]

lemma event_window_bounds {r : CircleX → ℝ} (j : ℕ) {ω : ActualSamples}
    (hω : ω∈regularSamples) (he : ω∈projectionEvent r j) (k : ℤ)
    (hk : |k| ≤ (polynomialWindow j:ℤ)) :
    1/modelF k (firstEndpoint ω) ≤ coefficientCap j ∧ modelF (-k) (lastEndpoint ω) ≤ coefficientCap j := by
  have hk' : |(k:ℝ)| ≤ (polynomialWindow j:ℝ) := by exact_mod_cast hk
  by_cases hk0 : 0 ≤ k
  · have hb := event_floor_tail j hω he k hk0 (le_trans (le_abs_self _) hk)
    exact ⟨(modelF_prefix_bound j k hω.2.1 hk' (fun i hi => (hb i hi).1)).2,
      (modelF_prefix_bound j (-k) hω.2.2.1 (by simpa using hk') (fun i hi => (hb i hi).2)).1⟩
  · have hx : 1 ≤ modelF k (firstEndpoint ω) := by
      rw [←modelF_zero (firstEndpoint ω)]
      exact modelF_antitone _ (by omega)
    have hy : modelF (-k) (lastEndpoint ω) ≤ 1 := by
      rw [←modelF_zero (lastEndpoint ω)]
      exact modelF_antitone _ (by omega)
    exact ⟨((div_le_one (modelF_pos _ _)).mpr hx).trans (coefficientCap_ge_one j),hy.trans (coefficientCap_ge_one j)⟩


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

lemma projection_vector_norm (q : FiberOperator) (hq : IsStarProjection q) (k : ℤ) :
    ‖q (lp.single 2 k 1)‖ ≤ 1 := by
  have hh := q.le_opNorm (lp.single 2 k 1)
  have he : ‖(lp.single 2 k (1:ℂ):FiberHilbert)‖=1 := by simp
  rw [he,mul_one] at hh
  exact hh.trans (hq.norm_le q)
end

open scoped BigOperators

lemma laurent_coeff (K : ℕ) (a : ℤ → ℂ) (i : ℕ) (hi : i ≤ 2*K) :
    (shiftedPolynomial K (laurentArray K a)).coeff i=a ((i:ℤ)-(K:ℤ)) := by
  exact coeff_shiftedPolynomial K (laurentArray K a) ⟨i,by omega⟩
lemma lowProduct_convolution (K : ℕ) (a b : ℤ → ℂ) (t : Fin (2*K+1)) :
    lowProduct K (laurentArray K a,laurentArray K b) t =
      ∑ v∈retainedIndices K (2*K-t.val), a v*b (-((2*K-t.val:ℕ):ℤ)-v) := by
  classical
  unfold lowProduct
  rw [Polynomial.coeff_mul,Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  have ht := t.isLt
  have hs : (∑ i∈Finset.range (t.val+1),
      (shiftedPolynomial K (laurentArray K a)).coeff i*(shiftedPolynomial K (laurentArray K b)).coeff (t.val-i)) =
      ∑ i∈Finset.range (t.val+1), a ((i:ℤ)-(K:ℤ))*b (((t.val-i:ℕ):ℤ)-(K:ℤ)) := by
    apply Finset.sum_congr rfl
    intro i hi
    have hh := Finset.mem_range.mp hi
    rw [laurent_coeff K a i (by omega),laurent_coeff K b (t.val-i) (by omega)]
  rw [hs]
  apply Finset.sum_bij (fun (i:ℕ) _ => (i:ℤ)-(K:ℤ))
  · intro i hi
    simp only [retainedIndices,Finset.mem_Icc]
    have hh := Finset.mem_range.mp hi
    omega
  · intro i hi k hk he
    omega
  · intro v hv
    have hv' := Finset.mem_Icc.mp hv
    refine ⟨(v+(K:ℤ)).toNat,?_,?_⟩
    · simp only [Finset.mem_range]
      omega
    · omega
  · intro i hi
    have hh := Finset.mem_range.mp hi
    congr 2
    omega
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
lemma modelDiagonal_measurable (P : ModelProjectionField) : Measurable (modelDiagonal P) := (modelColumn_coordinate P 0).re

lemma modelTerm_measurable (P : ModelProjectionField) (n : ℕ) (v : ℤ) : Measurable (modelTerm P n v) := by
  exact (((((modelF_measurable _).comp lastEndpoint_measurable).div
    ((modelF_measurable v).comp firstEndpoint_measurable)).complex_ofReal.mul
    ((modelColumn_coordinate P v).comp firstEndpoint_measurable)).mul
    (Complex.continuous_conj.measurable.comp ((modelComplement_coordinate P _).comp lastEndpoint_measurable)))

lemma modelRetained_measurable (P : ModelProjectionField) (j n : ℕ) : Measurable (modelRetained P j n) :=
  Finset.measurable_sum _ (fun v _ => modelTerm_measurable P n v)

lemma modelCoefficient_identity (P : ModelProjectionField) (j : ℕ) (ω : ActualSamples) (t : Fin (2*polynomialWindow j+1)) :
    lowProduct (polynomialWindow j) (modelCoefficientPair P j ω) t=modelRetained P j (2*polynomialWindow j-t.val) ω := by
  rw [modelCoefficientPair,lowProduct_convolution]
  apply Finset.sum_congr rfl
  intro v _
  simp only [neg_sub,modelTerm]
  push_cast
  ring_nf
end

open MeasureTheory Set Filter ContinuousCircleWeight
open scoped ENNReal ComplexInnerProductSpace BigOperators

lemma modelColumn_coordinate_bound (P : ModelProjectionField) (x : CircleX) (v : ℤ) :
    ‖modelColumn P x v‖ ≤ 1 := (lp.norm_apply_le_norm (by norm_num) _ _).trans (modelColumn_norm P x)
lemma modelComplement_coordinate_bound (P : ModelProjectionField) (x : CircleX) (v : ℤ) :
    ‖modelComplement P x v‖ ≤ 1 := (lp.norm_apply_le_norm (by norm_num) _ _).trans (modelComplement_norm P x)
lemma modelComplement_zero_re (P : ModelProjectionField) (x : CircleX) :
    (modelComplement P x 0).re=1-modelDiagonal P x := by
  change (((lp.single 2 0 1: FiberHilbert)-modelColumn P x) 0).re=_
  simp [modelDiagonal]

lemma modelCoefficient_bounds (P : ModelProjectionField) (j : ℕ) {ω : ActualSamples}
    (hω : ω∈regularSamples) (he : ω∈projectionEvent (modelDiagonal P) j) :
    (∀ i,‖(modelCoefficientPair P j ω).1 i‖ ≤ coefficientCap j) ∧
    (∀ i,‖(modelCoefficientPair P j ω).2 i‖ ≤ coefficientCap j) := by
  constructor
  · intro i
    have hi : |(i.val:ℤ)-(polynomialWindow j:ℤ)| ≤ (polynomialWindow j:ℤ) := by
      rw [abs_le]; have hh := i.isLt; omega
    have hh := (event_window_bounds j hω he _ hi).1
    change ‖((1/modelF _ (firstEndpoint ω):ℝ):ℂ)*modelColumn P (firstEndpoint ω) _‖ ≤ _
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (one_div_pos.mpr (modelF_pos _ _))]
    exact (mul_le_mul_of_nonneg_left (modelColumn_coordinate_bound P _ _) ((one_div_pos.mpr (modelF_pos _ _)).le)).trans (by simpa using hh)
  · intro i
    have hi : |(i.val:ℤ)-(polynomialWindow j:ℤ)| ≤ (polynomialWindow j:ℤ) := by
      rw [abs_le]; have hh := i.isLt; omega
    have hh := (event_window_bounds j hω he _ hi).2
    change ‖(modelF _ (lastEndpoint ω):ℂ)*starRingEnd ℂ (modelComplement P (lastEndpoint ω) _)‖ ≤ _
    rw [norm_mul,Complex.norm_conj,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (modelF_pos _ _)]
    exact (mul_le_mul_of_nonneg_left (modelComplement_coordinate_bound P _ _) (modelF_pos _ _).le).trans (by simpa using hh)

lemma modelCoefficient_centers (P : ModelProjectionField) (j : ℕ) {ω : ActualSamples}
    (he : ω∈projectionEvent (modelDiagonal P) j) :
    1/((j:ℝ)+1) ≤ ‖(modelCoefficientPair P j ω).1 (centerIndex (polynomialWindow j))‖ ∧
    1/((j:ℝ)+1) ≤ ‖(modelCoefficientPair P j ω).2 (centerIndex (polynomialWindow j))‖ := by
  have hh := projectionEvent_mem he
  have ha : (modelCoefficientPair P j ω).1 (centerIndex (polynomialWindow j))=modelColumn P (firstEndpoint ω) 0 := by
    simp [modelCoefficientPair,laurentArray,centerIndex,modelF_zero]
  have hb : (modelCoefficientPair P j ω).2 (centerIndex (polynomialWindow j))=starRingEnd ℂ (modelComplement P (lastEndpoint ω) 0) := by
    simp [modelCoefficientPair,laurentArray,centerIndex,modelF_zero]
  rw [ha,hb,Complex.norm_conj]
  exact ⟨hh.2.2.2.1.trans (Complex.re_le_norm _),hh.2.2.2.2.trans (by rw [←modelComplement_zero_re]; exact Complex.re_le_norm _)⟩

lemma model_coefficient_lower (P : ModelProjectionField) (j : ℕ) {ω : ActualSamples}
    (hω : ω∈regularSamples) (he : ω∈projectionEvent (modelDiagonal P) j) :
    ∃ t : Fin (2*polynomialWindow j+1), (scaleStep j).ε ≤ ‖modelRetained P j (2*polynomialWindow j-t.val) ω‖ := by
  have hb := modelCoefficient_bounds P j hω he
  have hc := modelCoefficient_centers P j he
  obtain ⟨t,ht⟩ := (scaleStep j).coefficients (modelCoefficientPair P j ω) hb.1 hb.2 hc.1 hc.2
  change Fin (2*polynomialWindow j+1) at t
  change (scaleStep j).ε ≤ ‖lowProduct (polynomialWindow j) (modelCoefficientPair P j ω) t‖ at ht
  rw [modelCoefficient_identity] at ht
  exact ⟨t,ht⟩
end

open MeasureTheory Set Filter CircleCoupling CircleDigits
open scoped ENNReal

end CircleSampling

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

open MeasureTheory Set Filter ContinuousCircleWeight
open scoped ENNReal BigOperators Topology

lemma convolutionError_pos (j : ℕ) : 0<convolutionError j := by unfold convolutionError; positivity
lemma convolutionError_bound (j : ℕ) : convolutionError j ≤ 3*Real.exp (-crossingBudget j/10000) := by
  have hL : 0 ≤ crossingBudget j := (scaleStep j).Lge.trans' (by norm_num)
  have h₁ : Real.exp (-crossingBudget j) ≤ Real.exp (-crossingBudget j/10000) := Real.exp_le_exp.mpr (by linarith)
  have h₂ : Real.exp (-crossingBudget j/800) ≤ Real.exp (-crossingBudget j/10000) := Real.exp_le_exp.mpr (by linarith)
  unfold convolutionError
  linarith

lemma projectionEvent_upper (P : ModelProjectionField) (j : ℕ) :
    (actualSystem.probability (stageTagged j)).real (projectionEvent (modelDiagonal P) j) ≤ 1/((j:ℝ)+1) := by
  let μ := actualSystem.probability (stageTagged j)
  let E := projectionEvent (modelDiagonal P) j
  have hE : MeasurableSet E := projectionEvent_measurable (modelDiagonal_measurable P) j
  have hlow : (ENNReal.ofReal (scaleStep j).ε)*μ E ≤
      ∫⁻ ω,∑ t : Fin (2*polynomialWindow j+1),E.indicator (fun ω => ‖modelRetained P j (2*polynomialWindow j-t.val) ω‖ₑ) ω ∂μ := by
    rw [←lintegral_indicator_const hE]
    apply lintegral_mono_ae
    filter_upwards [ae_regularSamples j] with ω hω
    by_cases he : ω∈E
    · rw [Set.indicator_of_mem he]
      obtain ⟨t,ht⟩ := model_coefficient_lower P j hω he
      calc
        _ ≤ ‖modelRetained P j (2*polynomialWindow j-t.val) ω‖ₑ := by simpa only [ofReal_norm] using ENNReal.ofReal_le_ofReal ht
        _ = E.indicator (fun ω => ‖modelRetained P j (2*polynomialWindow j-t.val) ω‖ₑ) ω := by rw [Set.indicator_of_mem he]
        _ ≤ _ := Finset.single_le_sum (f := fun t : Fin (2*polynomialWindow j+1) => E.indicator (fun ω => ‖modelRetained P j (2*polynomialWindow j-t.val) ω‖ₑ) ω) (fun _ _ => zero_le) (Finset.mem_univ t)
    · simp [he]
  have hu : (ENNReal.ofReal (scaleStep j).ε)*μ E ≤ ENNReal.ofReal ((2*(polynomialWindow j:ℝ)+1)*convolutionError j) := by
    apply hlow.trans
    rw [lintegral_finsetSum _ (fun t _ => (modelRetained_measurable P j _).enorm.indicator hE)]
    calc
      _ ≤ ∑ _t : Fin (2*polynomialWindow j+1), ENNReal.ofReal (convolutionError j) := Finset.sum_le_sum (fun t _ => integrated_retained_bound P j _)
      _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]; rw [ENNReal.ofReal_mul (by positivity)]; norm_cast
  have hreal : (scaleStep j).ε*μ.real E ≤ (2*(polynomialWindow j:ℝ)+1)*convolutionError j := by
    have hh := ENNReal.toReal_mono (ENNReal.ofReal_ne_top) hu
    simpa only [ENNReal.toReal_mul,ENNReal.toReal_ofReal (scaleStep j).εpos.le,
      ENNReal.toReal_ofReal (mul_nonneg (by positivity : (0:ℝ)≤2*(polynomialWindow j:ℝ)+1) (convolutionError_pos j).le),measureReal_def] using hh
  have hb := (scaleStep j).exponential
  have hc : (2*(polynomialWindow j:ℝ)+1)*convolutionError j ≤ (scaleStep j).ε/((j:ℝ)+1) := by
    apply le_trans (mul_le_mul_of_nonneg_left (convolutionError_bound j) (by positivity))
    change (2*(polynomialWindow j:ℝ)+1)*3*Real.exp (-crossingBudget j/10000) ≤ (scaleStep j).ε/((j:ℝ)+1) at hb
    simpa only [mul_assoc] using hb
  have hh := hreal.trans hc
  have hε := (scaleStep j).εpos
  change μ.real E ≤ _
  nlinarith [show (scaleStep j).ε/((j:ℝ)+1)=(scaleStep j).ε*(1/((j:ℝ)+1)) by ring]

theorem model_no_strict_projection_oai (P : ModelProjectionField)
    (hp : ∀ᵐ x,0 < modelDiagonal P x ∧ modelDiagonal P x<1) : False := by
  have hm := projectionEvent_mass (modelDiagonal_measurable P) hp
  have ht : Tendsto (fun j : ℕ => 1/((j:ℝ)+1)) atTop (𝓝 0) := by
    exact tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  have he := ht.eventually (gt_mem_nhds (by positivity : (0:ℝ)<Real.exp (-86)/2))
  obtain ⟨j,hj,hj'⟩ := (hm.and he).exists
  exact (not_lt_of_ge (hj.trans (projectionEvent_upper P j))) hj'


end CircleSampling

end

end OAI
end

theorem solution : type_of% @OAI.CircleSampling.model_no_strict_projection_oai := @OAI.CircleSampling.model_no_strict_projection_oai
