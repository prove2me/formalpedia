-- Prove2me | solution 1 for OAI.HigherDimensionalBallPacking.Rigidity.cutoff_curl_reconstruct
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T17:00:04.250719+00:00
-- url     : https://prove2.me/submissions/ad8aa358-fee9-4e45-bde8-e30b1e2d6c4a

import Mathlib
import Definitions.Def_BallPackingNecessity
import Definitions.Def_OAIQ10Bp004
import Definitions.Def_OAIQ10Bp005

section
-- module Solutions.OAIQ10_BP.BallPacking_Necessity_MarkedInverse
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

namespace HigherDimensionalBallPacking.Rigidity
open scoped BoundedContinuousFunction ContDiff Topology
open Set Filter
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem c1Holder_contDiff (α : ℝ) (u : C1HolderSpace E α) :
    ContDiff ℝ 1 (holderValue α (c1HolderValue α u)) := by
  apply contDiff_one_iff_hasFDerivAt.mpr
  exact ⟨holderValue α (c1HolderDeriv α u),
    (holderValue α (c1HolderDeriv α u)).continuous,c1Holder_hasFDerivAt α u⟩

end HigherDimensionalBallPacking.Rigidity

open scoped BoundedContinuousFunction ContDiff Topology
open Set Filter

open scoped BoundedContinuousFunction ContDiff Topology
open Set Filter

open scoped BoundedContinuousFunction ContDiff Topology
open Set Function Filter

open scoped BoundedContinuousFunction ContDiff Topology
open Set Filter

open scoped BoundedContinuousFunction ContDiff Topology
open Set Function Filter
namespace HigherDimensionalBallPacking.Rigidity
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]


lemma compactCRInverse_rightInverse (R : ℝ) (u : CompactHolderSpace E R) (x : ℂ) :
    fderiv ℝ (compactCRInverseValue R u) x Complex.I -
      Complex.I • fderiv ℝ (compactCRInverseValue R u) x 1 = compactHolderValue R u x := by
  let v := compactHolderMap R (((Complex.I/2) • ContinuousLinearMap.id ℂ E).restrictScalars ℝ) u
  have hh := cauchyTransform_holder_complexCurl (compactHolderValue R v).continuous
    (compactHolderValue_compactSupport R v) (compactHolderValue_bound R v) (norm_nonneg v)
    (compactHolderValue_holder R v) x
  have he : (compactCRInverseValue R u : ℂ → E) = cauchyTransform (compactHolderValue R v) := by
    funext z
    exact compactHolderCauchyCLM_value R v z
  rw [he]
  have hs : (2*Complex.I) • compactHolderValue R v x = -compactHolderValue R u x := by
    change (2*Complex.I) • ((Complex.I/2) • compactHolderValue R u x) = _
    rw [smul_smul,show (2*Complex.I)*(Complex.I/2)=(-1:ℂ) by ring_nf;simp,neg_one_smul]
  rw [hs] at hh
  change Complex.I • _ - _ = _ at hh
  apply neg_injective
  simpa only [neg_sub] using hh

lemma compactCRInverse_contDiff (R : ℝ) (u : CompactHolderSpace E R) :
    ContDiff ℝ 1 (compactCRInverseValue R u) := c1Holder_contDiff _ _

lemma compactCRInverse_tendsto_zero (R : ℝ) (u : CompactHolderSpace E R) :
    Tendsto (compactCRInverseValue R u) (cocompact ℂ) (𝓝 0) := by
  let v := compactHolderMap R (((Complex.I/2) • ContinuousLinearMap.id ℂ E).restrictScalars ℝ) u
  have he : (compactCRInverseValue R u : ℂ → E) = cauchyTransform (compactHolderValue R v) := by
    funext z
    exact compactHolderCauchyCLM_value R v z
  rw [he]
  exact cauchyTransform_tendsto_zero (compactHolderValue R v).continuous
    (compactHolderValue_compactSupport R v)



end HigherDimensionalBallPacking.Rigidity

end

end OAI
end

section
-- module Solutions.OAIQ10_BP.BallPacking_Necessity_FrozenOperators
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
open Set Filter Function MeasureTheory
open SymplecticBallPacking.Hamiltonian





open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter Function





open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter Function
open SymplecticBallPacking.Hamiltonian
namespace HigherDimensionalBallPacking.Rigidity
open HigherDimensionalBallPacking.Rigidity

 theorem c1_decay_cauchy_representation {n : ℕ} (R : ℝ)
    (g : CompactHolderSpace (Phase n) R) {v : ℂ → Phase n} (hv : ContDiff ℝ 1 v)
    (hcurl : ∀ z, fderiv ℝ v z Complex.I-Complex.I • fderiv ℝ v z 1=compactHolderValue R g z)
    (hlim : Tendsto v (cocompact ℂ) (𝓝 0)) : v=compactCRInverseValue R g := by
  let w : ℂ → Phase n := fun z => v z-compactCRInverseValue R g z
  have hd : Differentiable ℂ w := by
    intro z
    have hvd := hv.differentiable one_ne_zero z
    have hgd := (compactCRInverse_contDiff R g).differentiable one_ne_zero z
    apply differentiableAt_complex_iff_differentiableAt_real.mpr
    refine ⟨hvd.sub hgd,?_⟩
    change fderiv ℝ (v-_) z Complex.I=Complex.I • fderiv ℝ (v-_) z 1
    rw [fderiv_sub hvd hgd]
    simp only [sub_apply,smul_sub]
    have h1 := hcurl z
    have h2 := compactCRInverse_rightInverse R g z
    exact sub_eq_sub_iff_sub_eq_sub.mp (h1.trans h2.symm)
  have hl : Tendsto w (cocompact ℂ) (𝓝 0) := by
    simpa only [sub_self] using hlim.sub (compactCRInverse_tendsto_zero R g)
  have he := hd.eq_const_of_tendsto_cocompact hl
  funext z
  exact sub_eq_zero.mp (congrFun he z)

 theorem c1StandardCurl_value {n : ℕ} (u : C1HolderSpace (Phase n) ((1:ℝ)/3)) (z : ℂ) :
    holderValue ((1:ℝ)/3) (c1StandardCurl u) z =
    fderiv ℝ (holderValue ((1:ℝ)/3) (c1HolderValue ((1:ℝ)/3) u)) z Complex.I-
      Complex.I • fderiv ℝ (holderValue ((1:ℝ)/3) (c1HolderValue ((1:ℝ)/3) u)) z 1 := by
  rw [(c1Holder_hasFDerivAt ((1:ℝ)/3) u z).fderiv]
  rfl

end HigherDimensionalBallPacking.Rigidity

 

 

open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter Function
open SymplecticBallPacking.Hamiltonian

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





open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter Function
namespace HigherDimensionalBallPacking.Rigidity
open HigherDimensionalBallPacking.Rigidity

 theorem cutoff_curl_value {n : ℕ} (b : ContDiffBump (0:ℂ))
    (v : C1HolderSpace (Phase n) ((1:ℝ)/3))
    (hs : ∀ z : ℂ, b.rIn<‖z‖ → holderValue ((1:ℝ)/3) (c1StandardCurl v) z=0) (z : ℂ) :
    compactHolderValue b.rOut (cutoffCompact b (c1StandardCurl v)) z=
      holderValue ((1:ℝ)/3) (c1StandardCurl v) z := by
  rw [cutoffCompact_value]
  by_cases hz : ‖z‖≤b.rIn
  · rw [b.one_of_mem_closedBall (by simpa using hz),one_smul]
  · rw [hs z (lt_of_not_ge hz),smul_zero]

 theorem cutoff_curl_reconstruct_oai {n : ℕ} (b : ContDiffBump (0:ℂ))
    (v : C1HolderSpace (Phase n) ((1:ℝ)/3))
    (hs : ∀ z : ℂ, b.rIn<‖z‖ → holderValue ((1:ℝ)/3) (c1StandardCurl v) z=0)
    (hlim : Tendsto (holderValue ((1:ℝ)/3) (c1HolderValue ((1:ℝ)/3) v)) (cocompact ℂ) (𝓝 0)) :
    v=compactCRInverse b.rOut (cutoffCompact b (c1StandardCurl v)) := by
  let g := cutoffCompact b (c1StandardCurl v)
  have hv : (holderValue ((1:ℝ)/3) (c1HolderValue ((1:ℝ)/3) v) : ℂ → Phase n)=compactCRInverseValue b.rOut g := by
    apply c1_decay_cauchy_representation b.rOut g (c1Holder_contDiff _ v) _ hlim
    intro z
    rw [cutoff_curl_value b v hs z,c1StandardCurl_value]
  apply c1HolderValue_injective
  apply holderValue_injective
  exact BoundedContinuousFunction.ext (congrFun hv)

end HigherDimensionalBallPacking.Rigidity

end

end OAI
end

theorem solution : type_of% @OAI.HigherDimensionalBallPacking.Rigidity.cutoff_curl_reconstruct_oai := @OAI.HigherDimensionalBallPacking.Rigidity.cutoff_curl_reconstruct_oai
