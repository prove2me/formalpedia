-- Prove2me | solution 1 for OAI.ShortDraftHeckeBridge.norm_p_fiber_inert
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T06:54:30.012632+00:00
-- url     : https://prove2.me/submissions/76a34057-ab3c-40f7-a159-c411f81ee5ff

import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_NormFiberMellin
import Definitions.Def_OAI_NumberTheory_DirichletL_Hecke_NormFiberCharacters
import Theorems.Thm_OAI_ShortDraftHeckeBridge_absNorm_inert
import Theorems.Thm_OAI_ShortDraftHeckeBridge_norm_prime_implies_over
import Theorems.Thm_OAI_IdealGaussCRT_traceProdChar_mk
attribute [local simp] OAI.IdealGaussCRT.traceProdChar_mk



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
theorem _root_.solution {p : ℕ} (hp : p.Prime) (hmod : p % 3 = 2) :
    {I : Ideal O | Ideal.absNorm I = p} = ∅ := by
  ext I
  simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
  intro hI
  have hOver := norm_prime_implies_over hp I hI
  let : I.IsPrime := hOver.1
  let : I.LiesOver (Ideal.span {(p : ℤ)}) := hOver.2
  have hNorm := absNorm_inert hp hmod I
  have hpge := hp.two_le
  nlinarith
end OAI.ShortDraftHeckeBridge
