-- Prove2me | solution 1 for OAI.SecondPassArithmetic.globalFirstCoreRow_zero_off_support
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T12:18:06.832216+00:00
-- url     : https://prove2.me/submissions/439efb55-7e01-4cef-8347-21ecac5320ed

import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_DirichletForm
import Definitions.Def_OAI_NumberTheory_DirichletL_MeanSquare_InputEnergy
import Theorems.Thm_OAI_SecondPassArithmetic_inputConjugateRow_zero_of_mass_zero
import Theorems.Thm_OAI_FirstPassCubeLabels_primeProductNorm_pos
import Theorems.Thm_OAI_SecondPassArithmetic_firstCoreInputRow_eq_mode_row
import Theorems.Thm_OAI_SecondPassArithmetic_firstCoreModeProfile_support
import Theorems.Thm_OAI_SecondPassArithmetic_globalFirstColumnMass_zero_off_support


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
open FirstPassCubeLabels (primeProductNorm normalizedColumn columnLog)
open RayFourExpansion (RayCharacter)
variable {ι : Type*} [DecidableEq ι]
  (p : ι → OAI.SecondPassArithmetic.O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
  (hg : ∀i,lambda∉Ideal.span {p i})
include hp
namespace OAI.SecondPassArithmetic
theorem _root_.solution (pool : Finset ι) (b : GlobalFirstData ι)
    (Ψ : O →* ℂ) (m : O) (g V : 𝓢(ℝ,ℂ)) (ell M U : ℝ) (hell : 0<ell)
    (hM : ∀t,g t≠0 → |t|≤M) (hU : ell*Real.exp M≤U)
    (side : Bool) (χ : RayCharacter) (r : FirstCoreIndex) (t : ℝ) (z : O)
    (hoff : ¬(primeProductNorm p b.common≤U ∧ primeProductNorm p b.firstCommon≤U)) :
    globalFirstCoreRow p hg pool Ψ m g V ell side χ r t b z=0 := by
  have hX : 0<globalFirstBlockColumnScale p ell side b :=
    div_pos hell (mul_pos (FirstPassCubeLabels.primeProductNorm_pos p hp _) (FirstPassCubeLabels.primeProductNorm_pos p hp _))
  have hm := globalFirstColumnMass_zero_off_support p hp hg pool b (firstCoreTwist side χ Ψ r) m
    (firstCoreModeProfile g V side t) ell M U hell
    (fun u hu => hM u (firstCoreModeProfile_support g V side t u hu).1) hU side hoff
  have hz := inputConjugateRow_zero_of_mass_zero p hg (globalFirstRawPool pool b)
    (firstCoreTwist side χ Ψ r) (m*globalFirstBlockBadLabel p b) (globalFirstBlockLabel p b)
    (primeSubsetGenerator (fun i => Ideal.span {p i}) b.firstDivisor)
    (globalFirstBlockTest p (firstCoreModeProfile g V side t) ell side b) hm (if side then -z else z)
  unfold globalFirstCoreRow
  rw [firstCoreInputRow_eq_mode_row p hp hg _ _ _ _ _ _ side χ Ψ m g V _ hX]
  change _*inputConjugateRow p hg (globalFirstRawPool pool b) (firstCoreTwist side χ Ψ r)
    (m*globalFirstBlockBadLabel p b) (globalFirstBlockLabel p b)
    (primeSubsetGenerator (fun i => Ideal.span {p i}) b.firstDivisor)
    (globalFirstBlockTest p (firstCoreModeProfile g V side t) ell side b) (if side then -z else z)=0
  rw [hz,mul_zero]
end OAI.SecondPassArithmetic
