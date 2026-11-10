-- Prove2me | solution 1 for OAI.CubicEisenstein.full_high_locally_finite
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T11:44:20.364198+00:00
-- url     : https://prove2.me/submissions/96edd049-eedf-4572-a4dd-2fad75361e40

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_ReflectedBranches
import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_CuspHeight
import Theorems.Thm_OAI_CubicEisenstein_principal_high_locally_finite
import Theorems.Thm_OAI_CubicEisenstein_fullCuspFromPrincipal_height
import Theorems.Thm_OAI_CubicEisenstein_fullCusp_finite_principal_cover
import Theorems.Thm_OAI_CubicEisenstein_continuous_hyperbolic_action


set_option autoImplicit false
open OAI
noncomputable section
open OAI.CubicEisenstein
open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical
open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups ContDiff
namespace OAI.CubicEisenstein
theorem _root_.solution (w : HyperbolicSpace) :
    ∃U : Set HyperbolicSpace,IsOpen U ∧ w∈U ∧ ∃T : Finset FullCuspClasses,
      ∀z∈U,∀x∉T,fullCuspHeight x z<1 := by
  obtain ⟨S,hS⟩ := fullCusp_finite_principal_cover
  choose U hU hw T hT using fun r : S => principal_high_locally_finite (integralComplexMatrix r.1⁻¹ • w)
  let V : Set HyperbolicSpace := ⋂r : S,(fun z => integralComplexMatrix r.1⁻¹ • z) ⁻¹' U r
  let B : Finset FullCuspClasses := Finset.univ.biUnion (fun r : S => (T r).image (fullCuspFromPrincipal r.1))
  refine ⟨V,isOpen_iInter_of_finite (fun r => (hU r).preimage (continuous_hyperbolic_action _)),?_,B,?_⟩
  · exact Set.mem_iInter.mpr hw
  · intro z hz x hx
    obtain ⟨r,hr,y,hxy⟩ := hS x
    let i : S := ⟨r,hr⟩
    have hy : y∉T i := by
      intro hy
      apply hx
      exact Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,Finset.mem_image.mpr ⟨y,hy,hxy⟩⟩
    rw [←hxy,fullCuspFromPrincipal_height]
    exact hT i _ (Set.mem_iInter.mp hz i) y hy
end OAI.CubicEisenstein
