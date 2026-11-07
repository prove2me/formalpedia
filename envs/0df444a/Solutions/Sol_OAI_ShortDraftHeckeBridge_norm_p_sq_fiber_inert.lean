-- Prove2me | solution 1 for OAI.ShortDraftHeckeBridge.norm_p_sq_fiber_inert
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T06:54:30.745029+00:00
-- url     : https://prove2.me/submissions/352c7ffc-95da-4c39-ac02-d16799f5488e

import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_NormFiberMellin
import Definitions.Def_OAI_NumberTheory_DirichletL_Hecke_NormFiberCharacters
import Theorems.Thm_OAI_ShortDraftHeckeBridge_absNorm_inert
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
    {I : Ideal O | Ideal.absNorm I = p ^ 2} =
      (Ideal.span {(p : ℤ)}).primesOver O := by
  ext I
  constructor
  · intro hI
    have hdiv : p ∣ Ideal.absNorm I := by
      rw [hI]
      exact dvd_pow_self p (by decide)
    obtain ⟨P, hPmax, hPunder, hPdiv⟩ :=
      Ideal.exists_isMaximal_dvd_of_dvd_absNorm' hp I hdiv
    have : P.IsPrime := hPmax.isPrime
    have : P.LiesOver (Ideal.span {(p : ℤ)}) := ⟨hPunder.symm⟩
    have hPN : Ideal.absNorm P = p ^ 2 := absNorm_inert hp hmod P
    obtain ⟨J, hIJ⟩ := hPdiv
    have hJN : Ideal.absNorm J = 1 := by
      have heq := congrArg Ideal.absNorm hIJ
      simp only [map_mul] at heq
      rw [hI, hPN] at heq
      have hp2 : 0 < p ^ 2 := pow_pos hp.pos 2
      nlinarith
    have hJtop : J = ⊤ := Ideal.absNorm_eq_one_iff.mp hJN
    subst J
    simp only [Ideal.mul_top] at hIJ
    subst I
    exact ⟨inferInstance, inferInstance⟩
  · intro hI
    let : I.IsPrime := hI.1
    let : I.LiesOver (Ideal.span {(p : ℤ)}) := hI.2
    exact absNorm_inert hp hmod I
end OAI.ShortDraftHeckeBridge
