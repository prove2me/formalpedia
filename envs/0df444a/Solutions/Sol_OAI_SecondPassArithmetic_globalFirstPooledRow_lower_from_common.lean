-- Prove2me | solution 1 for OAI.SecondPassArithmetic.globalFirstPooledRow_lower_from_common
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T12:01:48.85325+00:00
-- url     : https://prove2.me/submissions/1d57b994-2e75-493a-b33d-1d25c1e5fc56

import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_DirichletForm
import Definitions.Def_OAI_NumberTheory_DirichletL_MeanSquare_InputEnergy
import Theorems.Thm_OAI_SecondPassArithmetic_globalLogRep_ge_one
import Theorems.Thm_OAI_SecondPassArithmetic_globalLogRep_pos
import Theorems.Thm_OAI_SecondPassArithmetic_globalPooled_J_bound
import Theorems.Thm_OAI_SecondPassArithmetic_globalScaleIndex_bounds


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
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap
open OAI.SecondPassArithmetic
open ActualEisensteinCubic
open FirstPassCubeLabels (primeProductNorm primeProduct)
open ConcreteTraceCRT (eisEmbedding)
variable {ι : Type*} [DecidableEq ι]
  (p : ι → OAI.SecondPassArithmetic.O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
include hp
namespace OAI.SecondPassArithmetic
theorem _root_.solution (b : GlobalFirstData ι)
    (K ell B F U : ℝ) (hK : 0<K) (hell : 0<ell) (hB : 0<B) (hF : 0<F) (hU : 0<U)
    (hc : primeProductNorm p b.common≤U)
    (hb1 : ‖eisEmbedding (primeProduct p b.cube.support b.cube.leftExponent)‖^2≤B)
    (hb2 : ‖eisEmbedding (primeProduct p b.cube.support b.cube.rightExponent)‖^2≤B) (side : Bool) :
    ell^2*B^2*F^2/(K*U^2)≤globalFirstPooledRow p K ell B F side b := by
  let x := b.append (⟨∅,∅,∅,1⟩ : SecondExpansionData ι)
  let j := globalScaleIndex p side x
  have hC : globalLogRep j 1≤U := (globalScaleIndex_bounds p hp side x one_ne_zero 1).1.trans hc
  have hJ := globalPooled_J_bound p hp B hB side x one_ne_zero hb1 hb2
  have hcp := globalLogRep_pos j 1
  have hjp := globalLogRep_pos j 4
  have hd := globalLogRep_ge_one j 5
  have he : 1≤Real.exp 1 := Real.one_le_exp (by norm_num)
  change _≤Real.exp 1*ell^2*B^4*F^2*globalLogRep j 5/(K*(globalLogRep j 1)^2*globalLogRep j 4)
  calc
    _ = ell^2*B^4*F^2/(K*U^2*B^2) := by field_simp
    _ ≤ _ := by
      apply div_le_div₀ (by positivity)
      · calc
          ell^2*B^4*F^2 = 1*ell^2*B^4*F^2*1 := by ring
          _ ≤ _ := by gcongr
      · positivity
      · gcongr
end OAI.SecondPassArithmetic
