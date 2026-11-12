-- Prove2me | solution 1 for OAI.CubicEisenstein.integralCoverTrace_cusp_representative
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T09:49:32.368956+00:00
-- url     : https://prove2.me/submissions/64f8c872-e0e2-4bef-aa3d-e410e70d4e5c

import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_CubeCuspAverage
import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_InverseCorrespondence
import Theorems.Thm_OAI_CubicEisenstein_integralCoverTrace_representative
import Theorems.Thm_OAI_CubicEisenstein_integralCoverTraceFunction_cusp_decay
import Theorems.Thm_OAI_CubicEisenstein_integralCoverTraceFunction_measurable


set_option autoImplicit false
open OAI
noncomputable section
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
open OAI.CubicEisenstein
open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups
open Finset AddChar MulChar EisensteinEmbedding
local notation "O" => ActualEisensteinCubic.O
namespace OAI.CubicEisenstein
theorem _root_.solution {H K : Subgroup (SL(2,ActualEisensteinCubic.O))}
    (hHK : H≤K) (hK : K≤CubicKubota.levelThree) [H.IsFiniteRelIndex K]
    (G : IntegralQuotientL2 H) (f : IntegralOrbitQuotient H→ℂ) (hmeas : Measurable f)
    (hrep : G=ᵐ[integralQuotientVolume H]f) (C : ℝ)
    (hdec : ∀M : CubicKubota.levelThree,∀z : ℂ,∀v : ℝ,∀hv : 0<v,1<v→
      ‖f (integralOrbitProjection H (complexMatrix M•upperPoint z v hv))‖≤C/v^3) :
    ∃g : IntegralOrbitQuotient K→ℂ,Measurable g ∧
      integralCoverTrace hHK hK G=ᵐ[integralQuotientVolume K]g ∧
      ∀M : CubicKubota.levelThree,∀z : ℂ,∀v : ℝ,∀hv : 0<v,1<v→
        ‖g (integralOrbitProjection K (complexMatrix M•upperPoint z v hv))‖≤
          (H.relIndex K:ℝ)*C/v^3 := by
  refine ⟨integralCoverTraceFunction H K f,
    integralCoverTraceFunction_measurable H K f hmeas,
    integralCoverTrace_representative hHK hK G f hmeas hrep,?_⟩
  exact integralCoverTraceFunction_cusp_decay H K hK f C hdec
end OAI.CubicEisenstein
