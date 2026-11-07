-- Prove2me | solution 1 for OAI.ShortDraftHeckeBridge.baseChangeWeight_prime
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T06:50:06.272198+00:00
-- url     : https://prove2.me/submissions/42271592-6bfb-477f-8ed1-ded5f0071a16

import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_LocalNonvanishing
import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_NormFiberMellin

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
open OAI.ShortDraftHeckeBridge
namespace OAI.ShortDraftHeckeBridge
theorem _root_.solution {q : ℕ} (χ : DirichletCharacter ℂ q)
    (P : Ideal O) (hP : Prime P) :
    baseChangeWeight χ P = -χ (Ideal.absNorm P) := by
  rw [baseChangeWeight, hP.irreducible.moebius_eq]
  norm_num
end OAI.ShortDraftHeckeBridge
