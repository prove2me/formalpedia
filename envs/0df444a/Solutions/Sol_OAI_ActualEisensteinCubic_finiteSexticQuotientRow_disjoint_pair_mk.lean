-- Prove2me | solution 1 for OAI.ActualEisensteinCubic.finiteSexticQuotientRow_disjoint_pair_mk
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:03:26.093096+00:00
-- url     : https://prove2.me/submissions/00e0f982-bc55-4af2-8353-811926475c0c

import Definitions.Def_OAI_NumberTheory_DirichletL_Poisson_EisensteinLattice
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_SexticRadialPoisson
import Theorems.Thm_OAI_ActualEisensteinCubic_canonicalSextic_conj_as_row_label
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_verticalSlice_apply
import Theorems.Thm_OAI_IdealGaussCRT_quotientProdEquivPi_mk
import Theorems.Thm_OAI_IdealGaussCRT_traceProdChar_mk
attribute [local simp] OAI.EisensteinSchwartzPoisson.verticalSlice_apply
attribute [local simp] OAI.IdealGaussCRT.quotientProdEquivPi_mk
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
open OAI.ActualEisensteinCubic
namespace OAI.ActualEisensteinCubic
theorem _root_.solution
    {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hc : Pairwise (Function.onFun IsCoprime P))
    (hgood : ∀ i, lambda ∉ P i) (S : Finset ι) (a : O) :
    finiteSexticQuotientRow P hc hgood (fun i => if i ∈ S then 1 else 5)
      (Ideal.Quotient.mk (∏ i, P i) a) =
      finiteSquarefreeRow P hgood S a *
        star (finiteSquarefreeRow P hgood (Finset.univ \ S) a) := by
  classical
  have hpow5 (i : ι) :
      (canonicalSextic (P i) (hgood i) ^ 5) (Ideal.Quotient.mk (P i) a) =
        star (canonicalSextic (P i) (hgood i) (Ideal.Quotient.mk (P i) a)) := by
    rw [MulChar.pow_apply' _ (by decide : (5 : ℕ) ≠ 0)]
    rw [canonicalSextic_conj_as_row_label]
    ring
  have hterm (i : ι) :
      (canonicalSextic (P i) (hgood i) ^ (if i ∈ S then 1 else 5))
          (Ideal.Quotient.mk (P i) a) =
        if i ∈ S then canonicalSextic (P i) (hgood i) (Ideal.Quotient.mk (P i) a)
        else star (canonicalSextic (P i) (hgood i) (Ideal.Quotient.mk (P i) a)) := by
    split_ifs <;> simp only [pow_one, hpow5]
  simp only [finiteSexticQuotientRow, IdealGaussCRT.quotientProdEquivPi_mk]
  simp_rw [hterm]
  rw [Finset.prod_ite, Finset.filter_mem_eq_inter, Finset.univ_inter,
    ← Finset.sdiff_eq_filter]
  simp only [finiteSquarefreeRow, star_prod]
end OAI.ActualEisensteinCubic
