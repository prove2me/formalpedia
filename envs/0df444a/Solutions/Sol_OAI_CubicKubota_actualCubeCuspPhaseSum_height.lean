-- Prove2me | solution 1 for OAI.CubicKubota.actualCubeCuspPhaseSum_height
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T07:54:59.322273+00:00
-- url     : https://prove2.me/submissions/e358179f-0b93-4357-be0f-bac0ea9b1023

import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_AffineCuspFourier
import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_IntegralCover
import Theorems.Thm_OAI_CubicKubota_cubeCuspHeightWeight_zero
import Theorems.Thm_OAI_CubicKubota_cubeCuspHeightWeight_three
import Theorems.Thm_OAI_ConcreteTraceCRT_finite_quotient_span
import Theorems.Thm_OAI_CubicKubota_actualCubeCuspPhaseSum_coprime
import Theorems.Thm_OAI_CubicKubota_actualCubeCuspPhaseSum_dvd


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
open scoped Classical MatrixGroups BigOperators
open OAI.CubicKubota
open ActualEisensteinCubic ConcreteTraceCRT CubicEisenstein CubicJacobiGlobal
local notation "Eis" => ActualEisensteinCubic.O
namespace OAI.CubicKubota
theorem _root_.solution (A:levelTwo) (p:Eis) (hp:Prime p)
    (hprimary:lambda^2∣p-1) (hA:lambda^2∣((A:SL(2,Eis)) 0 0)-1) :
    actualCubeCuspPhaseSum A p hp hprimary (cubeCuspHeightWeight p)=
      (Ideal.absNorm (Ideal.span {p}):ℂ)^2 := by
  have hqN:Ideal.absNorm (Ideal.span {p})≠0:=
    (Ideal.absNorm_ne_zero_iff _).mpr (finite_quotient_span hp.ne_zero)
  have hq:(Ideal.absNorm (Ideal.span {p}):ℂ)≠0:=by exact_mod_cast hqN
  by_cases hc:p∣((A:SL(2,Eis)) 1 0)
  · rw [actualCubeCuspPhaseSum_dvd A p hp hprimary hA hc,
      cubeCuspHeightWeight_zero]
    field_simp
  · have hcop:IsCoprime ((A:SL(2,Eis)) 1 0) p:=(hp.coprime_iff_not_dvd.mpr hc).symm
    rw [actualCubeCuspPhaseSum_coprime A p hp hprimary hA hcop,
      cubeCuspHeightWeight_zero,cubeCuspHeightWeight_three]
    field_simp
    ; ring
end OAI.CubicKubota
