-- Prove2me | solution 1 for OAI.CanonicalRowCompletion.dirichlet_open_strip_of_theta_models
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T19:30:21.291207+00:00
-- url     : https://prove2.me/submissions/bd50b0fa-8b1e-44c9-bdde-dc0a3b8f6241

import Definitions.Def_OAI_NumberTheory_DirichletL_Hecke_MobiusEulerCorrection
import Definitions.Def_OAI_NumberTheory_DirichletL_RowCompletion_ThetaNonvanishing
import Theorems.Thm_OAI_CanonicalRowCompletion_corrected_weighted_mellin_identity
import Theorems.Thm_OAI_CompactMellinBridge_compact_weight_mellin_analytic
import Theorems.Thm_OAI_CompactMellinBridge_finiteEulerFactor_analytic
import Theorems.Thm_OAI_CompactMellinBridge_pair_zero_free_of_identity_gt_two
import Theorems.Thm_OAI_ConcreteCompactWeight_weight_mellin_ne_zero
import Theorems.Thm_OAI_ConcreteCompactWeight_weight_smooth
import Theorems.Thm_OAI_ConcreteCompactWeight_weight_support
import Theorems.Thm_OAI_ShortDraftHeckeBridge_baseChangeChar_ne_one_of_one
import Theorems.Thm_OAI_SixthPowerAverage_weightedCompactMellin_analytic
import Theorems.Thm_OAI_SmoothMobiusCorrection_eulerCorrection_analytic


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
theorem _root_.solution {q₀ : ℕ} [NeZero q₀]
    (χ : DirichletCharacter ℂ q₀)
    (S : Finset (Ideal ActualEisensteinCubic.O))
    (hbad : fixedBadPrimes⊆S) (hSp : ∀P∈S,Prime P)
    (ρ q levelBound : ℝ) (hρ : 0<ρ) (hq : 1<q) (hlevel : 1≤levelBound)
    (hmodels : HasCanonicalThetaModels S (conjugateMonoid (normCharacter χ)) ρ q levelBound)
    (z : ℂ) (hz : (23:ℝ)/24<z.re) (hz1 : z.re<1) : χ.LFunction z≠0 := by
  let W : ℝ→ℂ:=ConcreteCompactWeight.weight z
  have hW : ContDiff ℝ ∞ W:=ConcreteCompactWeight.weight_smooth z
  have hWs : ∀x,x≤1 ∨ 2≤x→W x=0:=ConcreteCompactWeight.weight_support z
  have hM:=weightedCompactMellin_analytic χ S hbad hSp ρ q levelBound hρ hq hlevel hmodels W hW hWs
  have hE:=finiteEulerFactor_analytic χ S hSp ((23:ℝ)/24)
  have hH : AnalyticOnNhd ℂ (SmoothMobiusCorrection.eulerCorrection χ S)
      {s : ℂ | (23:ℝ)/24<s.re} :=
    (SmoothMobiusCorrection.eulerCorrection_analytic χ S).mono (by intro s hs;change 0<s.re;change (23:ℝ)/24<s.re at hs;linarith)
  have hWanalytic:=compact_weight_mellin_analytic W hW hWs ((23:ℝ)/24)
  have hnotboth : χ≠1 ∨ baseChangeChar χ≠1 := by
    by_cases hc : χ=1
    · exact Or.inr (baseChangeChar_ne_one_of_one χ hc)
    · exact Or.inl hc
  have hzneq : z≠1 := by intro he;subst z;norm_num at hz1
  exact (pair_zero_free_of_identity_gt_two χ (baseChangeChar χ) hnotboth
    ((23:ℝ)/24) (by norm_num)
    (fun s=>(finiteEulerFactor χ S s*SmoothMobiusCorrection.eulerCorrection χ S s)*
      mellin (fun Z : ℝ=>weightedCompactSum χ S W Z⁻¹) (-s))
    (mellin W) ((hE.mul hH).mul hM) hWanalytic
    (corrected_weighted_mellin_identity χ S hSp W hW hWs)
    z hz hzneq (ConcreteCompactWeight.weight_mellin_ne_zero z)).1
end OAI.CanonicalRowCompletion
