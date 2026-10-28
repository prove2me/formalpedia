-- Prove2me | solution 1 for OAI.HigherDimensionalBallPacking.Rigidity.frozenPrincipal_isInvertible
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T17:04:17.163989+00:00
-- url     : https://prove2.me/submissions/d65d1603-5017-4c3f-b171-6c5e480c58fd

import Mathlib
import Definitions.Def_BallPackingNecessity
import Definitions.Def_OAIQ10Bp005
import Theorems.Thm_OAI_HigherDimensionalBallPacking_Rigidity_c1_decaying_CR_zero
import Theorems.Thm_OAI_HigherDimensionalBallPacking_Rigidity_frozenPrincipal_surjective

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
namespace HigherDimensionalBallPacking.Rigidity
open HigherDimensionalBallPacking.Rigidity

 theorem compactCRInverse_frozen_kernel {n : ℕ} (R : ℝ) (K : ℂ → End n)
    (hK : ∀ z, Compatible (K z)) (g : CompactHolderSpace (Phase n) R)
    (hCR : ∀ z, fderiv ℝ (compactCRInverseValue R g) z Complex.I=
      K z (fderiv ℝ (compactCRInverseValue R g) z 1)) : g=0 := by
  have hholo : ∀ᶠ z in cocompact ℂ, DifferentiableAt ℂ (compactCRInverseValue R g) z := by
    have he := hasCompactSupport_iff_eventuallyEq.mp (compactHolderValue_compactSupport R g)
    rw [coclosedCompact_eq_cocompact] at he
    filter_upwards [he] with z hz
    apply differentiableAt_complex_iff_differentiableAt_real.mpr
    refine ⟨(compactCRInverse_contDiff R g).differentiable one_ne_zero z,?_⟩
    exact sub_eq_zero.mp ((compactCRInverse_rightInverse R g z).trans hz)
  have hu := c1_decaying_CR_zero K hK (compactCRInverse_contDiff R g) hCR hholo
    (compactCRInverse_tendsto_zero R g)
  apply Subtype.ext
  apply holderValue_injective ((1:ℝ)/3)
  apply BoundedContinuousFunction.ext
  intro z
  have he := compactCRInverse_rightInverse R g z
  rw [hu] at he
  simpa using he.symm

end HigherDimensionalBallPacking.Rigidity

 

 

open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter Function





open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter Function
open SymplecticBallPacking.Hamiltonian





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
open SymplecticBallPacking.Hamiltonian
namespace HigherDimensionalBallPacking.Rigidity
open HigherDimensionalBallPacking.Rigidity

 theorem frozenPrincipal_value {n : ℕ} (R : ℝ) (H : HolderSpace ℂ (End n) ((1:ℝ)/3))
    (hs : ∀ z : ℂ, R<‖z‖ → holderValue ((1:ℝ)/3) H z=0)
    (g : CompactHolderSpace (Phase n) R) (z : ℂ) :
    compactHolderValue R (frozenPrincipal R H hs g) z=compactHolderValue R g z-
      holderValue ((1:ℝ)/3) H z (fderiv ℝ (compactCRInverseValue R g) z 1) := by
  have hd : fderiv ℝ (compactCRInverseValue R g) z=
      holderValue ((1:ℝ)/3) (c1HolderDeriv ((1:ℝ)/3) (compactCRInverse R g)) z :=
    (c1Holder_hasFDerivAt ((1:ℝ)/3) (compactCRInverse R g) z).fderiv
  rw [hd]
  rfl

end HigherDimensionalBallPacking.Rigidity

 

 

open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter Function
open SymplecticBallPacking.Hamiltonian





open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter Function
namespace HigherDimensionalBallPacking.Rigidity
open HigherDimensionalBallPacking.Rigidity

 attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.FrozenIsomorphismLocal1
theorem frozenPrincipal_injective {n : ℕ} (R : ℝ)
    (H : HolderSpace ℂ (End n) ((1:ℝ)/3))
    (hs : ∀ z : ℂ, R<‖z‖ → holderValue ((1:ℝ)/3) H z=0)
    (hK : ∀ z, Compatible (standardJ n+holderValue ((1:ℝ)/3) H z)) :
    Injective (frozenPrincipal R H hs) := by
  apply (LinearMap.ker_eq_bot (f := (frozenPrincipal R H hs).toLinearMap)).mp
  apply LinearMap.ker_eq_bot'.mpr
  intro g hg
  apply compactCRInverse_frozen_kernel R (fun z => standardJ n+holderValue ((1:ℝ)/3) H z) hK g
  intro z
  change frozenPrincipal R H hs g=0 at hg
  have he := congrArg (fun g => compactHolderValue R g z) hg
  rw [frozenPrincipal_value] at he
  have hr := compactCRInverse_rightInverse R g z
  change fderiv ℝ (compactCRInverseValue R g) z Complex.I-
    standardJ n (fderiv ℝ (compactCRInverseValue R g) z 1)=_ at hr
  change compactHolderValue R g z-holderValue ((1:ℝ)/3) H z (fderiv ℝ (compactCRInverseValue R g) z 1)=0 at he
  rw [add_apply]
  have hh := sub_eq_zero.mp he
  rw [←hr] at hh
  exact sub_eq_iff_eq_add.mp hh |>.trans (add_comm _ _)

 attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.FrozenIsomorphismLocal5
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.FrozenIsomorphismLocal6
theorem frozenPrincipal_isInvertible_oai {n : ℕ} (R : ℝ)
    (K : C1HolderSpace (End n) ((1:ℝ)/3))
    (H : HolderSpace ℂ (End n) ((1:ℝ)/3))
    (hs : ∀ z : ℂ, R<‖z‖ → holderValue ((1:ℝ)/3) H z=0)
    (he : ∀ z, holderValue ((1:ℝ)/3) (c1HolderValue ((1:ℝ)/3) K) z=standardJ n+holderValue ((1:ℝ)/3) H z)
    (hK : ∀ z, Compatible (holderValue ((1:ℝ)/3) (c1HolderValue ((1:ℝ)/3) K) z)) :
    (frozenPrincipal R H hs).IsInvertible := by
  have hinj := frozenPrincipal_injective R H hs (fun z => he z ▸ hK z)
  have hsurj := frozenPrincipal_surjective R K H hs he hK
  exact ⟨ContinuousLinearEquiv.ofBijective (frozenPrincipal R H hs)
    (LinearMap.ker_eq_bot.mpr hinj) (LinearMap.range_eq_top.mpr hsurj),rfl⟩

end HigherDimensionalBallPacking.Rigidity

end

end OAI
end

theorem solution : type_of% @OAI.HigherDimensionalBallPacking.Rigidity.frozenPrincipal_isInvertible_oai := @OAI.HigherDimensionalBallPacking.Rigidity.frozenPrincipal_isInvertible_oai
