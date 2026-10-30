-- Prove2me | solution 1 for OAI.HigherDimensionalBallPacking.Rigidity.affine_c1_regular
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T03:54:55.564988+00:00
-- url     : https://prove2.me/submissions/c874eb67-6297-409e-87df-53acf77e9858

import Mathlib
import Definitions.Def_BallPackingNecessity
import Definitions.Def_OAIQ10Bp009
import Theorems.Thm_OAI_HigherDimensionalBallPacking_Rigidity_c1_orbit_regular
import Theorems.Thm_OAI_HigherDimensionalBallPacking_Rigidity_cutoffFrozen_invertible
import Theorems.Thm_OAI_HigherDimensionalBallPacking_Rigidity_orbitCoefficient_support
import Theorems.Thm_OAI_HigherDimensionalBallPacking_Rigidity_orbitResponseDensity_contDiffAt
import Theorems.Thm_OAI_HigherDimensionalBallPacking_Rigidity_orbitResponse_identity

section
-- module Solutions.OAIQ10_BP.BallPacking_Necessity_OrbitRegularity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Topology
open Set Function Filter
open scoped ContDiff Topology Manifold
open Set Function Filter MeasureTheory
open Set Function MeasureTheory
open Set Function
open SymplecticBallPacking.Hamiltonian (Plane planarCurl)
open SymplecticBallPacking.Hamiltonian (Plane planarCurl angularOneForm radiusSq planarArea planarArea_apply)
open SymplecticBallPacking.Hamiltonian (Plane planarCurl angularOneForm)
open SymplecticBallPacking.Hamiltonian (Plane angularOneForm)
open SymplecticBallPacking.Hamiltonian
open SymplecticBallPacking.Hamiltonian (Plane)
open Set Filter Function
open Set Filter MeasureTheory
open scoped Topology
open Set Filter Finset
open scoped ContDiff Topology Classical
open Set Filter
open scoped BoundedContinuousFunction ContDiff Topology
open Set Function Filter Topology
open scoped NNReal
open scoped ContDiff Topology BoundedContinuousFunction
open Function
open scoped Topology ContDiff
open scoped ContDiff Topology Convolution
open Set Filter Function MeasureTheory _root_.ContinuousLinearMap
open Set Filter Function MeasureTheory

open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter Function





open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter Function





open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter Function





open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter Function
namespace HigherDimensionalBallPacking.Rigidity
open HigherDimensionalBallPacking.Rigidity

 theorem orbitCoefficient_value {n : ℕ} (f : Phase n → End n) (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f)
    (c a : Phase n) (v : C1HolderSpace (Phase n) ((1:ℝ)/3)) (h z : ℂ) :
    holderValue ((1:ℝ)/3) (orbitCoefficient f hf hc c a (h,holderShift ((1:ℝ)/3) h (c1HolderValue ((1:ℝ)/3) v))) z=
      f (c1HolderAffineCurve ((1:ℝ)/3) c (affineSlope a) v (z+h)) := by
  change f (c+h • a+z • a+holderValue ((1:ℝ)/3) (c1HolderValue ((1:ℝ)/3) v) (z+h))=_
  congr 1
  unfold c1HolderAffineCurve
  rw [affineSlope_apply,add_smul]
  abel

 theorem orbitCoefficient_C1 {n : ℕ} (f : Phase n → End n) (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f)
    (c a : Phase n) (v : C1HolderSpace (Phase n) ((1:ℝ)/3)) (h : ℂ) :
    ∃ H : C1HolderSpace (End n) ((1:ℝ)/3), c1HolderValue ((1:ℝ)/3) H=
      orbitCoefficient f hf hc c a (h,holderShift ((1:ℝ)/3) h (c1HolderValue ((1:ℝ)/3) v)) :=
  ⟨c1HolderAffineCompose ((1:ℝ)/3) (by norm_num) (by norm_num) f hf hc
    (c+h • a) (affineSlope a) (c1HolderShift ((1:ℝ)/3) h v),rfl⟩

end HigherDimensionalBallPacking.Rigidity

 

 

open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter Function
namespace HigherDimensionalBallPacking.Rigidity
open HigherDimensionalBallPacking.Rigidity

 attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.regularHGroup
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.regularHSpace
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.regularCGroup
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.regularCSpace
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.regularCompactGroup
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.regularCompactSpace
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.AffineC1RegularityLocal1
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.AffineC1RegularityLocal2
local instance AffineC1RegularityLocal3_rdd376d_1 (n : ℕ) : NormedAddCommGroup (HolderSpace ℂ (End n) ((1:ℝ)/3)) := inferInstance
local instance AffineC1RegularityLocal4_rdd376d_1 (n : ℕ) : NormedSpace ℝ (HolderSpace ℂ (End n) ((1:ℝ)/3)) := inferInstance
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.AffineC1RegularityLocal5
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.AffineC1RegularityLocal6
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.AffineC1RegularityLocal7
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.AffineC1RegularityLocal8
theorem orbitResponse_contDiffAt {n : ℕ} (b : ContDiffBump (0:ℂ))
    (f : Phase n → End n) (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) (c a : Phase n) (ha : a≠0)
    (p : ℂ × HolderSpace ℂ (Phase n) ((1:ℝ)/3))
    (hi : (cutoffFrozen b (orbitCoefficient f hf hc c a p)).IsInvertible) :
    ContDiffAt ℝ ∞ (orbitResponse b f hf hc c a) p := by
  unfold orbitResponse
  have hC : ContDiff ℝ ∞ (compactCRInverse (E := Phase n) b.rOut) := ContinuousLinearMap.contDiff _
  exact hC.contDiffAt.comp p (orbitResponseDensity_contDiffAt b f hf hc c a ha p hi)



 theorem affine_c1_regular_oai {n : ℕ}
    (f : Phase n → End n) (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f)
    (hK : ∀ x, Compatible (standardJ n+f x))
    (c a : Phase n) (ha : a≠0) (v : C1HolderSpace (Phase n) ((1:ℝ)/3))
    (hcurl : ∀ z, holderValue ((1:ℝ)/3) (c1StandardCurl v) z=
      f (c1HolderAffineCurve ((1:ℝ)/3) c (affineSlope a) v z)
        (a+holderValue ((1:ℝ)/3) (c1HolderDeriv ((1:ℝ)/3) v) z 1))
    (hlim : Tendsto (holderValue ((1:ℝ)/3) (c1HolderValue ((1:ℝ)/3) v)) (cocompact ℂ) (𝓝 0)) :
    ContDiff ℝ ∞ (holderValue ((1:ℝ)/3) (c1HolderValue ((1:ℝ)/3) v)) := by
  obtain ⟨b,hb⟩ := orbitCoefficient_support f hf hc c a ha v
  have hi (h : ℂ) (hh : ‖h‖<1) :
      (cutoffFrozen b (orbitCoefficient f hf hc c a (h,holderShift ((1:ℝ)/3) h (c1HolderValue ((1:ℝ)/3) v)))).IsInvertible := by
    obtain ⟨H,hH⟩ := orbitCoefficient_C1 f hf hc c a v h
    rw [←hH]
    apply cutoffFrozen_invertible b H
    · simpa only [hH] using hb h hh
    · intro z
      rw [hH,orbitCoefficient_value]
      exact hK _
  apply c1_orbit_regular ((1:ℝ)/3) (by norm_num) v (Metric.ball 0 1) Metric.isOpen_ball
    (Metric.mem_ball_self (by norm_num)) (orbitResponse b f hf hc c a)
  · intro h hh
    exact orbitResponse_contDiffAt b f hf hc c a ha _ (hi h (by simpa using hh))
  · intro h hh
    have hh' : ‖h‖<1 := by simpa using hh
    exact orbitResponse_identity b f hf hc c a v h (hb h hh') (hi h hh') hcurl hlim

end HigherDimensionalBallPacking.Rigidity

end

end OAI
end

theorem solution : type_of% @OAI.HigherDimensionalBallPacking.Rigidity.affine_c1_regular_oai := @OAI.HigherDimensionalBallPacking.Rigidity.affine_c1_regular_oai
