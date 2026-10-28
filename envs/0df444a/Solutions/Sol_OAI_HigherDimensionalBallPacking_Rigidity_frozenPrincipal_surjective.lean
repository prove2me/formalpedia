-- Prove2me | solution 1 for OAI.HigherDimensionalBallPacking.Rigidity.frozenPrincipal_surjective
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T17:04:18.34707+00:00
-- url     : https://prove2.me/submissions/3556bcba-b10f-4bda-97b7-02fdbaaf1ec3

import Mathlib
import Definitions.Def_BallPackingNecessity
import Definitions.Def_OAIQ10Bp005
import Theorems.Thm_OAI_HigherDimensionalBallPacking_Rigidity_compatible_frozen_solution

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

 theorem compactHolderValue_injective {n : ℕ} (R : ℝ) :
    Injective (compactHolderValue (E := Phase n) R) := by
  intro g h he
  apply Subtype.ext
  exact holderValue_injective ((1:ℝ)/3) he

 theorem c1_potential_yields_frozen_density {n : ℕ} (R : ℝ)
    (H : HolderSpace ℂ (End n) ((1:ℝ)/3))
    (hs : ∀ z : ℂ, R<‖z‖ → holderValue ((1:ℝ)/3) H z=0)
    (f : CompactHolderSpace (Phase n) R) (U : C1HolderSpace (Phase n) ((1:ℝ)/3))
    (hCR : ∀ z, fderiv ℝ (holderValue ((1:ℝ)/3) (c1HolderValue ((1:ℝ)/3) U)) z Complex.I-
      (standardJ n+holderValue ((1:ℝ)/3) H z)
        (fderiv ℝ (holderValue ((1:ℝ)/3) (c1HolderValue ((1:ℝ)/3) U)) z 1)=compactHolderValue R f z)
    (hlim : Tendsto (holderValue ((1:ℝ)/3) (c1HolderValue ((1:ℝ)/3) U)) (cocompact ℂ) (𝓝 0)) :
    ∃ g : CompactHolderSpace (Phase n) R, frozenPrincipal R H hs g=f := by
  let u := holderValue ((1:ℝ)/3) (c1HolderValue ((1:ℝ)/3) U)
  have hu : ContDiff ℝ 1 u := c1Holder_contDiff _ U
  have hc (z : ℂ) : holderValue ((1:ℝ)/3) (c1StandardCurl U) z=
      compactHolderValue R f z+holderValue ((1:ℝ)/3) H z (fderiv ℝ u z 1) := by
    rw [c1StandardCurl_value]
    have hh := hCR z
    change fderiv ℝ u z Complex.I-(Complex.I • fderiv ℝ u z 1+holderValue ((1:ℝ)/3) H z (fderiv ℝ u z 1))=_ at hh
    change fderiv ℝ u z Complex.I-Complex.I • fderiv ℝ u z 1=_
    rw [sub_add_eq_sub_sub] at hh
    exact sub_eq_iff_eq_add.mp hh
  let g : CompactHolderSpace (Phase n) R := ⟨c1StandardCurl U,by
    intro z hz
    have hf0 : compactHolderValue R f z=0 := f.property z hz
    rw [hc z,hs z hz,hf0,zero_apply,add_zero]⟩
  have hrep : (u : ℂ → Phase n)=compactCRInverseValue R g :=
    c1_decay_cauchy_representation R g hu (fun z => (c1StandardCurl_value U z).symm) hlim
  refine ⟨g,compactHolderValue_injective R ?_⟩
  apply BoundedContinuousFunction.ext
  intro z
  rw [frozenPrincipal_value]
  change holderValue ((1:ℝ)/3) (c1StandardCurl U) z-_=_
  rw [hc z,←hrep,add_sub_cancel_right]

end HigherDimensionalBallPacking.Rigidity

 

 

open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter Function
open SymplecticBallPacking.Hamiltonian





open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter Function
namespace HigherDimensionalBallPacking.Rigidity
open HigherDimensionalBallPacking.Rigidity

 theorem frozenPrincipal_surjective_oai {n : ℕ} (R : ℝ)
    (K : C1HolderSpace (End n) ((1:ℝ)/3))
    (H : HolderSpace ℂ (End n) ((1:ℝ)/3))
    (hs : ∀ z : ℂ, R<‖z‖ → holderValue ((1:ℝ)/3) H z=0)
    (he : ∀ z, holderValue ((1:ℝ)/3) (c1HolderValue ((1:ℝ)/3) K) z=standardJ n+holderValue ((1:ℝ)/3) H z)
    (hK : ∀ z, Compatible (holderValue ((1:ℝ)/3) (c1HolderValue ((1:ℝ)/3) K) z)) :
    Surjective (frozenPrincipal R H hs) := by
  intro f
  have ho (z : ℂ) (hz : R<‖z‖) :
      holderValue ((1:ℝ)/3) (c1HolderValue ((1:ℝ)/3) K) z=standardJ n := by rw [he z,hs z hz,add_zero]
  obtain ⟨U,hU,hlim⟩ := compatible_frozen_solution R K hK ho f
  apply c1_potential_yields_frozen_density R H hs f U _ hlim
  intro z
  rw [←he z]
  exact hU z

end HigherDimensionalBallPacking.Rigidity

end

end OAI
end

theorem solution : type_of% @OAI.HigherDimensionalBallPacking.Rigidity.frozenPrincipal_surjective_oai := @OAI.HigherDimensionalBallPacking.Rigidity.frozenPrincipal_surjective_oai
