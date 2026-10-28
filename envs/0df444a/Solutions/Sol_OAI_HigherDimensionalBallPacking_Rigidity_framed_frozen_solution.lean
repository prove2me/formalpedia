-- Prove2me | solution 1 for OAI.HigherDimensionalBallPacking.Rigidity.framed_frozen_solution
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T16:54:08.683279+00:00
-- url     : https://prove2.me/submissions/ff3dbd62-78f4-4e0e-aa79-e54d01d5a12b

import Mathlib
import Definitions.Def_BallPackingNecessity
import Definitions.Def_OAIQ10Bp002
import Theorems.Thm_OAI_HigherDimensionalBallPacking_Rigidity_framed_density_equation

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
open SymplecticBallPacking.Hamiltonian (Plane planarCurl radiusSq planarArea planarArea_apply)
open SymplecticBallPacking.Hamiltonian (Plane planarCurl )
open SymplecticBallPacking.Hamiltonian (Plane )
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
open SymplecticBallPacking.Hamiltonian (Plane planarCurl radiusSq planarArea planarArea_apply)
open SymplecticBallPacking.Hamiltonian (Plane planarCurl )
open SymplecticBallPacking.Hamiltonian (Plane )
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

 theorem frame_product_CR {n : ℕ} {a : ℂ → End n} {v : ℂ → Phase n} {z : ℂ}
    (ha : DifferentiableAt ℝ a z) (hv : DifferentiableAt ℝ v z) (K M : End n)
    (hint : ∀ x, a z (Complex.I • x)=K (a z x))
    (hM : ∀ x, fderiv ℝ a z Complex.I x-K (fderiv ℝ a z 1 x)=a z (M x)) :
    fderiv ℝ (fun w => a w (v w)) z Complex.I-
      K (fderiv ℝ (fun w => a w (v w)) z 1)=
    a z (fderiv ℝ v z Complex.I-Complex.I • fderiv ℝ v z 1+M (v z)) := by
  have hd (w : ℂ) : fderiv ℝ (fun w => a w (v w)) z w=
      a z (fderiv ℝ v z w)+fderiv ℝ a z w (v z) := by
    rw [fderiv_clm_apply ha hv]
    rfl
  rw [hd Complex.I,hd 1,map_add,←hint (fderiv ℝ v z 1),map_add,map_sub]
  calc
    _ = (a z (fderiv ℝ v z Complex.I)-a z (Complex.I • fderiv ℝ v z 1))+
      (fderiv ℝ a z Complex.I (v z)-K (fderiv ℝ a z 1 (v z))) := by abel
    _ = _ := by rw [hM]

end HigherDimensionalBallPacking.Rigidity

 

 

open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter Function
open SymplecticBallPacking.Hamiltonian

end

end OAI
end

section
-- module Solutions.OAIQ10_BP.BallPacking_Necessity_FrozenInverse
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
open SymplecticBallPacking.Hamiltonian (Plane planarCurl radiusSq planarArea planarArea_apply)
open SymplecticBallPacking.Hamiltonian (Plane planarCurl )
open SymplecticBallPacking.Hamiltonian (Plane )
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
open SymplecticBallPacking.Hamiltonian
namespace HigherDimensionalBallPacking.Rigidity
open HigherDimensionalBallPacking.Rigidity

 theorem frame_product_decay {n : ℕ} (R : ℝ) (a : ℂ → End n) (v : ℂ → Phase n)
    (hout : ∀ z, R<‖z‖ → a z=ContinuousLinearMap.id ℝ (Phase n))
    (hv : Tendsto v (cocompact ℂ) (𝓝 0)) :
    Tendsto (fun z => a z (v z)) (cocompact ℂ) (𝓝 0) := by
  apply hv.congr'
  filter_upwards [(isCompact_closedBall (0:ℂ) R).compl_mem_cocompact] with z hz
  have hzR : R<‖z‖ := by simpa only [mem_compl_iff,Metric.mem_closedBall,dist_zero_right,not_le] using hz
  rw [hout z hzR,ContinuousLinearMap.id_apply]

 theorem frame_product_inhomogeneous {n : ℕ} (a : ℂ → End n) (v : ℂ → Phase n)
    (ha : ContDiff ℝ 1 a) (hv : ContDiff ℝ 1 v) (K M : ℂ → End n) (d f : ℂ → Phase n)
    (hi : ∀ z, (a z).IsInvertible)
    (hint : ∀ z x, a z (Complex.I • x)=K z (a z x))
    (hM : ∀ z x, fderiv ℝ a z Complex.I x-K z (fderiv ℝ a z 1 x)=a z (M z x))
    (hCR : ∀ z, fderiv ℝ v z Complex.I-Complex.I • fderiv ℝ v z 1=d z)
    (hd : ∀ z, d z+M z (v z)=(a z).inverse (f z)) :
    ∀ z, fderiv ℝ (fun z => a z (v z)) z Complex.I-
      K z (fderiv ℝ (fun z => a z (v z)) z 1)=f z := by
  intro z
  rw [frame_product_CR (ha.differentiable one_ne_zero z)
    (hv.differentiable one_ne_zero z) (K z) (M z) (hint z) (hM z),
      hCR z,hd z,(hi z).self_apply_inverse]

 theorem framed_frozen_solution_oai {n : ℕ} (R : ℝ) (K : ℂ → End n)
    (hK : ∀ z, Compatible (K z)) (hKout : ∀ z : ℂ, R<‖z‖ → K z=standardJ n)
    (A : C1HolderSpace (End n) ((1:ℝ)/3)) (M : HolderSpace ℂ (End n) ((1:ℝ)/3))
    (hs : ∀ z : ℂ, R<‖z‖ → holderValue ((1:ℝ)/3) M z=0)
    (hAout : ∀ z : ℂ, R<‖z‖ → holderValue ((1:ℝ)/3) (c1HolderValue ((1:ℝ)/3) A) z=ContinuousLinearMap.id ℝ _)
    (hi : ∀ z, (holderValue ((1:ℝ)/3) (c1HolderValue ((1:ℝ)/3) A) z).IsInvertible)
    (hint : ∀ z x, holderValue ((1:ℝ)/3) (c1HolderValue ((1:ℝ)/3) A) z (Complex.I • x)=
      K z (holderValue ((1:ℝ)/3) (c1HolderValue ((1:ℝ)/3) A) z x))
    (hM : ∀ z x, fderiv ℝ (holderValue ((1:ℝ)/3) (c1HolderValue ((1:ℝ)/3) A)) z Complex.I x-
      K z (fderiv ℝ (holderValue ((1:ℝ)/3) (c1HolderValue ((1:ℝ)/3) A)) z 1 x)=
      holderValue ((1:ℝ)/3) (c1HolderValue ((1:ℝ)/3) A) z (holderValue ((1:ℝ)/3) M z x))
    (f : CompactHolderSpace (Phase n) R) :
    ∃ U : C1HolderSpace (Phase n) ((1:ℝ)/3),
      let u := holderValue ((1:ℝ)/3) (c1HolderValue ((1:ℝ)/3) U)
      (∀ z, fderiv ℝ u z Complex.I-K z (fderiv ℝ u z 1)=compactHolderValue R f z) ∧
        Tendsto u (cocompact ℂ) (𝓝 0) := by
  obtain ⟨d,hd⟩ := framed_density_equation R K hK hKout A M hs hAout hi hint hM f
  let U := c1HolderMultiply ((1:ℝ)/3) A (compactCRInverse R d)
  refine ⟨U,?_,?_⟩
  · exact frame_product_inhomogeneous
      (holderValue ((1:ℝ)/3) (c1HolderValue ((1:ℝ)/3) A)) (compactCRInverseValue R d)
      (c1Holder_contDiff _ A) (compactCRInverse_contDiff R d) K
      (holderValue ((1:ℝ)/3) M) (compactHolderValue R d) (compactHolderValue R f)
      hi hint hM (compactCRInverse_rightInverse R d) hd
  · exact frame_product_decay R _ (compactCRInverseValue R d) hAout (compactCRInverse_tendsto_zero R d)

end HigherDimensionalBallPacking.Rigidity

 

 

open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter Function
open SymplecticBallPacking.Hamiltonian





open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter Function

end

end OAI
end

theorem solution : type_of% @OAI.HigherDimensionalBallPacking.Rigidity.framed_frozen_solution_oai := @OAI.HigherDimensionalBallPacking.Rigidity.framed_frozen_solution_oai
