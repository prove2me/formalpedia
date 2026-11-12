-- Prove2me | solution 1 for OAI.CubicKubota.actualCubeCuspPhaseSum_coprime
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T06:43:12.226993+00:00
-- url     : https://prove2.me/submissions/de9cc366-b162-4d90-a618-a21fa38ecdf2

import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_CubeResidueStrata
import Definitions.Def_OAI_NumberTheory_DirichletL_Reciprocity_RamifiedCuspPhases
import Theorems.Thm_OAI_ConcreteTraceCRT_finite_quotient_span
import Theorems.Thm_OAI_CubicEisenstein_cubeCuspAffineEquiv_mk
import Theorems.Thm_OAI_CubicEisenstein_cubeStrata_weighted_sum
import Theorems.Thm_OAI_CubicKubota_CubeCuspData_comparison_phase
import Theorems.Thm_OAI_CubicKubota_CubeCuspData_stratum_map
import Theorems.Thm_OAI_GaussianShiftedPartition_representative_spec


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
open OAI.CubicKubota
open scoped Classical MatrixGroups BigOperators
open ActualEisensteinCubic ConcreteTraceCRT CubicEisenstein CubicJacobiGlobal
local notation "Eis" => ActualEisensteinCubic.O
namespace OAI.CubicKubota
theorem _root_.solution (A:levelTwo) (p:Eis) (hp:Prime p)
    (hprimary:lambda^2∣p-1) (hA:lambda^2∣((A:SL(2,Eis)) 0 0)-1)
    (hC:IsCoprime ((A:SL(2,Eis)) 1 0) p) (w:Fin 4→ℂ) :
    actualCubeCuspPhaseSum A p hp hprimary w =
      w 0*(Ideal.absNorm (Ideal.span {p}):ℂ)^2*((Ideal.absNorm (Ideal.span {p}):ℂ)-1)+w 3 := by
  let e:=cubeResidueStrataEquiv p hp hprimary
  let a:=cubeCuspAffineEquiv p ((A:SL(2,Eis)) 0 0) ((A:SL(2,Eis)) 1 0) hprimary hC
  let d (r:Eis⧸Ideal.span {p^3}):=actualCubeCuspData (A:SL(2,Eis)) p
    (GaussianShiftedPartition.representative (p^3) r) hp hprimary
  let phi (s:CubeResidueStrata p):=w s.1*cubeStratumSymbol p ((A:SL(2,Eis)) 1 0) s.1 s.2
  have hpoint (r:Eis⧸Ideal.span {p^3}):
      w (d r).exponent*complexCharacter ⟨(d r).matrix*(A:SL(2,Eis))⁻¹,(d r).congruent⟩=
        phi (e.symm (a r)) := by
    rw [(d r).comparison_phase A hp hprimary hA hC]
    change phi ((d r).stratum hp.ne_zero)=phi (e.symm (a r))
    apply congrArg phi
    apply e.injective
    rw [e.apply_symm_apply]
    change cubeResidueStratumMap p ((d r).stratum hp.ne_zero)=a r
    rw [(d r).stratum_map hp.ne_zero]
    rw [←cubeCuspAffineEquiv_mk p ((A:SL(2,Eis)) 0 0) ((A:SL(2,Eis)) 1 0)
      (GaussianShiftedPartition.representative (p^3) r) hprimary hC,
      GaussianShiftedPartition.representative_spec]
  let (j:Fin 4):Finite (Eis⧸Ideal.span {p^(3-j.val)}) :=
    finite_quotient_span (pow_ne_zero _ hp.ne_zero)
  let (j:Fin 4):Finite (CubicUnitResidue (p^(3-j.val))) := inferInstance
  have hphi:Summable phi:=Summable.of_finite
  calc
    actualCubeCuspPhaseSum A p hp hprimary w = ∑' r,phi (e.symm (a r)) := by
      unfold actualCubeCuspPhaseSum
      exact tsum_congr hpoint
    _ = ∑' r,phi (e.symm r) := a.tsum_eq (fun r => phi (e.symm r))
    _ = ∑' s,phi s := e.symm.tsum_eq phi
    _ = ∑j:Fin 4,w j*∑' b:CubicUnitResidue (p^(3-j.val)),cubeStratumSymbol p ((A:SL(2,Eis)) 1 0) j b := by
      rw [hphi.tsum_sigma,tsum_fintype]
      apply Finset.sum_congr rfl
      intro j hj
      exact tsum_mul_left (f := fun b:CubicUnitResidue (p^(3-j.val)) =>
        cubeStratumSymbol p ((A:SL(2,Eis)) 1 0) j b) (a := w j)
    _ = _ := cubeStrata_weighted_sum p ((A:SL(2,Eis)) 1 0) hp hprimary hC w
end OAI.CubicKubota
