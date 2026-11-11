-- Prove2me | solution 1 for OAI.CanonicalRowCompletion.corrected_weighted_mellin_identity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T19:22:59.120834+00:00
-- url     : https://prove2.me/submissions/8edab109-efd8-46e5-a954-86f7731f4adf

import Definitions.Def_OAI_NumberTheory_DirichletL_Hecke_MobiusEulerCorrection
import Definitions.Def_OAI_NumberTheory_DirichletL_RowCompletion_ThetaNonvanishing
import Theorems.Thm_OAI_ShortDraftHeckeBridge_normFiberCoeff_baseChange_eq_pairInverseCoeff
import Theorems.Thm_OAI_ShortDraftHeckeBridge_normFiber_LSeries_eq_pair_inverse
import Theorems.Thm_OAI_ShortDraftHeckeBridge_pair_inverse_euler_identity
import Theorems.Thm_OAI_SixthPowerAverage_weightedCompactMellin_eq_series
import Theorems.Thm_OAI_SmoothMobiusCorrection_full_LSeries_correction


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
open scoped BigOperators Classical ContDiff Topology
open OAI.CanonicalRowCompletion
open ActualEisensteinCubic
open ConcretePrimeRowBridge hiding O
open ShortDraftHeckeBridge
open CanonicalQuadraticSieve hiding O
open SecondPassArithmetic hiding O
open SixthPowerAverage CompactMellinBridge InitialMeanSquare
namespace OAI.CanonicalRowCompletion
theorem _root_.solution {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (S : Finset (Ideal ActualEisensteinCubic.O))
    (hS : ∀P∈S,Prime P) (W : ℝ→ℂ) (hW : ContDiff ℝ ∞ W)
    (hs : ∀x,x≤1 ∨ 2≤x→W x=0) (s : ℂ) (hRe : 2<s.re) :
    (χ.LFunction s*(baseChangeChar χ).LFunction s)*
      ((finiteEulerFactor χ S s*SmoothMobiusCorrection.eulerCorrection χ S s)*
        mellin (fun Z : ℝ=>weightedCompactSum χ S W Z⁻¹) (-s))=
      mellin W s := by
  rw [weightedCompactMellin_eq_series χ S W hW hs s hRe]
  have hc:=SmoothMobiusCorrection.full_LSeries_correction χ S hS s hRe
  have hp:=normFiber_LSeries_eq_pair_inverse χ (baseChangeChar χ) (baseChangeWeight χ)
    (normFiberCoeff_baseChange_eq_pairInverseCoeff χ) s
  have he:=pair_inverse_euler_identity χ (baseChangeChar χ) s (by linarith : 1<s.re)
  rw [←hp,hc] at he
  calc
    _=((χ.LFunction s*(baseChangeChar χ).LFunction s)*
      ((finiteEulerFactor χ S s*SmoothMobiusCorrection.eulerCorrection χ S s)*
        LSeries (weightedCoeff χ S) s))*mellin W s := by ring
    _=mellin W s := by rw [he,one_mul]
end OAI.CanonicalRowCompletion
