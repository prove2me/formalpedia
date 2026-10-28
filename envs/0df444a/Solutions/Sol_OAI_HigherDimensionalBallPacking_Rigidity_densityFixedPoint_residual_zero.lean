-- Prove2me | solution 1 for OAI.HigherDimensionalBallPacking.Rigidity.densityFixedPoint_residual_zero
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T17:09:40.663336+00:00
-- url     : https://prove2.me/submissions/c9031c53-f043-4f1b-b2aa-bc497af8c146

import Mathlib
import Definitions.Def_BallPackingNecessity
import Definitions.Def_OAIQ10Bp007

section
-- module Solutions.OAIQ10_BP.BallPacking_Necessity_NonlinearCR
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



namespace HigherDimensionalBallPacking.Rigidity
open scoped BoundedContinuousFunction ContDiff Topology
open Set Filter
universe u v
variable {K : Type u} [MetricSpace K]
variable {E F : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

variable [CompleteSpace E]

theorem c1HolderAffineCurve_hasFDerivAt (α : ℝ) (c : E) (A : ℂ →L[ℝ] E)
    (u : C1HolderSpace E α) (z : ℂ) :
    HasFDerivAt (c1HolderAffineCurve α c A u) (A+holderValue α (c1HolderDeriv α u) z) z :=
  (A.hasFDerivAt.const_add c).add (c1Holder_hasFDerivAt α u z)

@[simp] theorem c1HolderAffineCurve_fderiv (α : ℝ) (c : E) (A : ℂ →L[ℝ] E)
    (u : C1HolderSpace E α) (z : ℂ) :
    fderiv ℝ (c1HolderAffineCurve α c A u) z = A+holderValue α (c1HolderDeriv α u) z :=
  (c1HolderAffineCurve_hasFDerivAt α c A u z).fderiv

end HigherDimensionalBallPacking.Rigidity

end

end OAI
end

section
-- module Solutions.OAIQ10_BP.BallPacking_Necessity_DensityResidual
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

open scoped ContDiff Topology
open Set Filter Function
namespace HigherDimensionalBallPacking.Rigidity








open scoped ContDiff Topology
open Set Filter Function
open HigherDimensionalBallPacking.Rigidity

 theorem timeDensityProfile_value {n : ℕ} (p q : Phase n) (R : ℝ)
    (y : ℝ × CompactHolderSpace (Phase n) R) (z : ℂ) :
    (timeDensityProfile p q R y).1.1+(timeDensityProfile p q R y).1.2 z+
      holderValue ((1:ℝ)/3) (timeDensityProfile p q R y).2 z=(y.1,densityCurve p q R y.2 z) := by
  apply Prod.ext
  · change y.1+0+(holderValue ((1:ℝ)/3) (holderLinearPost ((1:ℝ)/3)
      (ContinuousLinearMap.inr ℝ ℝ (Phase n))
      (c1HolderValue ((1:ℝ)/3) (compactCRInverse R y.2))) z).1=y.1
    rw [holderLinearPost_apply]
    simp
  · change p-compactCRInverseValue R y.2 0+z • densitySlope p q R y.2+
      compactCRInverseValue R y.2 z=p+z • (q-p)+markedCRInverse R y.2 z
    simp only [densitySlope,markedCRInverse,smul_sub]
    abel

 theorem densityCoefficient_value {n : ℕ} (p q : Phase n) (R : ℝ)
    (A : ℝ × Phase n → End n) (hA : ContDiff ℝ ∞ A) (hc : HasCompactSupport A)
    (y : ℝ × CompactHolderSpace (Phase n) R) (z : ℂ) :
    holderValue ((1:ℝ)/3) (densityCoefficient p q R A hA hc y) z=A (y.1,densityCurve p q R y.2 z) := by
  rw [densityCoefficient,holderAffineFamily_apply,timeDensityProfile_value]

 theorem densityCurve_eq_profile {n : ℕ} (p q : Phase n) (R : ℝ)
    (g : CompactHolderSpace (Phase n) R) :
    densityCurve p q R g=c1HolderAffineCurve ((1:ℝ)/3)
      (p-compactCRInverseValue R g 0) (densityLinearSlope p q R g) (compactCRInverse R g) := by
  funext z
  change p+z • (q-p)+(compactCRInverseValue R g z-compactCRInverseValue R g 0-
    z • (compactCRInverseValue R g 1-compactCRInverseValue R g 0))=
    p-compactCRInverseValue R g 0+z • densitySlope p q R g+compactCRInverseValue R g z
  simp only [densitySlope,smul_sub]
  abel

 theorem densityJet_value {n : ℕ} (p q : Phase n) (R : ℝ)
    (g : CompactHolderSpace (Phase n) R) (z : ℂ) :
    holderValue ((1:ℝ)/3) (densityJet p q R g) z=fderiv ℝ (densityCurve p q R g) z := by
  rw [densityCurve_eq_profile,c1HolderAffineCurve_fderiv]
  change holderValue ((1:ℝ)/3) (holderConst ((1:ℝ)/3) (densityLinearSlope p q R g)) z+
    holderValue ((1:ℝ)/3) (c1HolderDeriv ((1:ℝ)/3) (compactCRInverse R g)) z=_
  rw [holderConst_apply]

end HigherDimensionalBallPacking.Rigidity

end

end OAI
end

section
-- module Solutions.OAIQ10_BP.BallPacking_Necessity_FrozenResponse
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
namespace HigherDimensionalBallPacking.Rigidity

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

 theorem cutoffFrozen_value (b : ContDiffBump (0:ℂ))
    (H : HolderSpace ℂ (E →L[ℝ] E) ((1:ℝ)/3)) (g : CompactHolderSpace E b.rOut) (z : ℂ) :
    compactHolderValue b.rOut (cutoffFrozen b H g) z=compactHolderValue b.rOut g z-
      b z • holderValue ((1:ℝ)/3) H z (fderiv ℝ (compactCRInverseValue b.rOut g) z 1) := by
  have hd : fderiv ℝ (compactCRInverseValue b.rOut g) z=
      holderValue ((1:ℝ)/3) (c1HolderDeriv ((1:ℝ)/3) (compactCRInverse b.rOut g)) z :=
    (c1Holder_hasFDerivAt ((1:ℝ)/3) (compactCRInverse b.rOut g) z).fderiv
  rw [hd]
  rfl

end HigherDimensionalBallPacking.Rigidity





open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter Function

end

end OAI
end

section
-- module Solutions.OAIQ10_BP.BallPacking_Necessity_DensityMaps
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
namespace HigherDimensionalBallPacking.Rigidity
open HigherDimensionalBallPacking.Rigidity FramedCR

 theorem densityCurve_deriv_one {n : ℕ} (p q : Phase n) (R : ℝ)
    (g : CompactHolderSpace (Phase n) R) (z : ℂ) :
    fderiv ℝ (densityCurve p q R g) z 1=densitySlope p q R g+
      holderValue ((1:ℝ)/3) (c1HolderDeriv ((1:ℝ)/3) (compactCRInverse R g)) z 1 := by
  rw [densityCurve_eq_profile,c1HolderAffineCurve_fderiv]
  change (1:ℂ) • densitySlope p q R g+_=_
  rw [one_smul]
  rfl

end HigherDimensionalBallPacking.Rigidity

 

 

open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter Function





open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter Function
namespace HigherDimensionalBallPacking.Rigidity
open HigherDimensionalBallPacking.Rigidity

 theorem responseCoefficient_value {n : ℕ} (b B : ContDiffBump (0:ℂ)) (hbB : b.rOut≤B.rIn)
    (p q : Phase n) (A : ℝ × Phase n → End n) (hA : ContDiff ℝ ∞ A) (hc : HasCompactSupport A)
    (y : ℝ × CompactHolderSpace (Phase n) b.rOut) (z : ℂ) :
    holderValue ((1:ℝ)/3) (responseCoefficient b B A hA hc (responseCoords B p q b.rOut y)) z=
      b z • A (y.1,densityCurve p q b.rOut y.2 z) := by
  change b z • holderValue ((1:ℝ)/3) (holderPost ((1:ℝ)/3) (by norm_num) A hA hc _) z=_
  rw [holderPost_apply]
  by_cases hz : b z=0
  · rw [hz]
    ext v
    simp
  have hzz : ‖z‖≤b.rOut := by
    by_contra hn
    exact hz (b.zero_of_le_dist (by simpa using (le_of_not_ge hn)))
  have hB : B z=1 := B.one_of_mem_closedBall (by simpa using hzz.trans hbB)
  congr 2
  rw [responseProfile,map_add,BoundedContinuousFunction.add_apply,holderConstantCLM_value,
    holderLinearPost_apply, map_add, BoundedContinuousFunction.add_apply, holderCutoffAffine_apply]
  change (y.1,0)+(ContinuousLinearMap.inr ℝ ℝ (Phase n))
    (B z • ((p-compactCRInverseValue b.rOut y.2 0)+affineSlope (densitySlope p q b.rOut y.2) z)+
      B z • compactCRInverseValue b.rOut y.2 z)=_
  rw [hB,one_smul,one_smul]
  apply Prod.ext
  · simp
  · simp only [Prod.snd_add, ContinuousLinearMap.inr_apply, zero_add]
    rw [densityCurve_eq_profile]
    rfl

end HigherDimensionalBallPacking.Rigidity

end

end OAI
end

section
-- module Solutions.OAIQ10_BP.BallPacking_Necessity_DensityExistence
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

open scoped ContDiff Topology
open Set Filter Function





open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter Function
namespace HigherDimensionalBallPacking.Rigidity
open HigherDimensionalBallPacking.Rigidity

 theorem responseCoefficient_uncut {n : ℕ} (b B : ContDiffBump (0:ℂ)) (hbB : b.rOut≤B.rIn)
    (p q : Phase n) (A : ℝ × Phase n → End n) (hA : ContDiff ℝ ∞ A) (hc : HasCompactSupport A)
    (y : ℝ × CompactHolderSpace (Phase n) b.rOut)
    (hs : ∀ z : ℂ, b.rIn<‖z‖ → A (y.1,densityCurve p q b.rOut y.2 z)=0) (z : ℂ) :
    holderValue ((1:ℝ)/3) (responseCoefficient b B A hA hc (responseCoords B p q b.rOut y)) z=
      A (y.1,densityCurve p q b.rOut y.2 z) := by
  rw [responseCoefficient_value b B hbB p q A hA hc y z]
  by_cases hz : ‖z‖≤b.rIn
  · rw [b.one_of_mem_closedBall (by simpa using hz),one_smul]
  · rw [hs z (lt_of_not_ge hz)]
    ext v
    simp

 theorem densityFixedPoint_residual_zero_oai {n : ℕ} (b B : ContDiffBump (0:ℂ)) (hbB : b.rOut≤B.rIn)
    (p q : Phase n) (A : ℝ × Phase n → End n) (hA : ContDiff ℝ ∞ A) (hc : HasCompactSupport A)
    (y : ℝ × CompactHolderSpace (Phase n) b.rOut)
    (hs : ∀ z : ℂ, b.rIn<‖z‖ → A (y.1,densityCurve p q b.rOut y.2 z)=0)
    (hi : (cutoffFrozen b (responseCoefficient b B A hA hc (responseCoords B p q b.rOut y))).IsInvertible)
    (hfix : densityResponse b B p q A hA hc y=y.2) : densityResidual p q b.rOut A hA hc y=0 := by
  let H := responseCoefficient b B A hA hc (responseCoords B p q b.rOut y)
  have he : cutoffFrozen b H y.2=cutoffCompact b (holderCLM ((1:ℝ)/3) H (holderConstantCLM ((1:ℝ)/3) (densitySlope p q b.rOut y.2))) := by
    change (cutoffFrozen b H).inverse _=y.2 at hfix
    exact (hi.inverse_apply_eq.mp hfix).symm
  have hpoint (z : ℂ) : compactHolderValue b.rOut y.2 z=
      A (y.1,densityCurve p q b.rOut y.2 z) (fderiv ℝ (densityCurve p q b.rOut y.2) z 1) := by
    have hez := congrArg (fun g => compactHolderValue b.rOut g z) he
    rw [cutoffFrozen_value,cutoffCompact_value,holderCLM_apply,holderConstantCLM_value] at hez
    change compactHolderValue b.rOut y.2 z-b z • holderValue ((1:ℝ)/3) H z _=b z • holderValue ((1:ℝ)/3) H z _ at hez
    have hH := responseCoefficient_uncut b B hbB p q A hA hc y hs z
    change holderValue ((1:ℝ)/3) H z=_ at hH
    rw [hH] at hez
    by_cases hz : ‖z‖≤b.rIn
    · rw [b.one_of_mem_closedBall (by simpa using hz),one_smul,one_smul] at hez
      rw [densityCurve_deriv_one,map_add]
      have hd := (c1Holder_hasFDerivAt ((1:ℝ)/3) (compactCRInverse (E := Phase n) b.rOut y.2) z).fderiv
      change fderiv ℝ (compactCRInverseValue b.rOut y.2) z=_ at hd
      rw [hd] at hez
      exact sub_eq_iff_eq_add.mp hez
    · rw [hs z (lt_of_not_ge hz)] at hez ⊢
      simpa using hez
  apply holderValue_injective
  apply BoundedContinuousFunction.ext
  intro z
  change compactHolderValue b.rOut y.2 z-holderValue ((1:ℝ)/3)
    (holderCLM ((1:ℝ)/3) (densityCoefficient p q b.rOut A hA hc y)
      (holderJetEval ((1:ℝ)/3) 1 (densityJet p q b.rOut y.2))) z=0
  rw [holderCLM_apply,densityCoefficient_value,holderJetEval_apply,densityJet_value,hpoint]
  exact sub_self _

end HigherDimensionalBallPacking.Rigidity

 

 

 

open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter Function

end

end OAI
end

theorem solution : type_of% @OAI.HigherDimensionalBallPacking.Rigidity.densityFixedPoint_residual_zero_oai := @OAI.HigherDimensionalBallPacking.Rigidity.densityFixedPoint_residual_zero_oai
