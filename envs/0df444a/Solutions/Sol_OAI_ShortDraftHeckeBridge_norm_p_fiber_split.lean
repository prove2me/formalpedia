-- Prove2me | solution 1 for OAI.ShortDraftHeckeBridge.norm_p_fiber_split
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T06:54:19.798937+00:00
-- url     : https://prove2.me/submissions/1da18283-7fc1-4586-9dd3-896d3e91e837

import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_NormFiberMellin
import Definitions.Def_OAI_NumberTheory_DirichletL_Hecke_NormFiberCharacters
import Theorems.Thm_OAI_ShortDraftHeckeBridge_absNorm_split
import Theorems.Thm_OAI_ShortDraftHeckeBridge_norm_prime_implies_over

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
theorem _root_.solution {p : ℕ} (hp : p.Prime) (hmod : p % 3 = 1) :
    {I : Ideal O | Ideal.absNorm I = p} =
      (Ideal.span {(p : ℤ)}).primesOver O := by
  ext I
  constructor
  · exact norm_prime_implies_over hp I
  · intro hI
    let : I.IsPrime := hI.1
    let : I.LiesOver (Ideal.span {(p : ℤ)}) := hI.2
    exact absNorm_split hp hmod I
end OAI.ShortDraftHeckeBridge
