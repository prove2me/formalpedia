-- Prove2me | solution 1 for OAI.ShortDraftHeckeBridge.baseChange_normFiber_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:17:10.498496+00:00
-- url     : https://prove2.me/submissions/e6e99077-39d2-46b4-82d4-8fc5aea9b617

import Definitions.Def_OAI_NumberTheory_DirichletL_Hecke_NormFiberCharacters
import Definitions.Def_OAI_NumberTheory_DirichletL_Hecke_LocalEulerIdentities
import Theorems.Thm_OAI_NormFiberMult_weighted_norm_fiber_mul
import Theorems.Thm_OAI_ShortDraftHeckeBridge_baseChangeWeight_mul_of_coprime_norms


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
open OAI.ShortDraftHeckeBridge
namespace OAI.ShortDraftHeckeBridge
theorem _root_.solution {q : ℕ}
    (χ : DirichletCharacter ℂ q) (m n : ℕ) (hcop : m.Coprime n) :
    normFiberCoeff (baseChangeWeight χ) (m * n) =
      normFiberCoeff (baseChangeWeight χ) m *
        normFiberCoeff (baseChangeWeight χ) n := by
  exact NormFiberMult.weighted_norm_fiber_mul (baseChangeWeight χ)
    (fun I J h => baseChangeWeight_mul_of_coprime_norms χ I J h) m n hcop
end OAI.ShortDraftHeckeBridge
