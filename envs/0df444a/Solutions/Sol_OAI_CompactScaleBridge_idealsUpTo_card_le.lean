-- Prove2me | solution 1 for OAI.CompactScaleBridge.idealsUpTo_card_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:43:02.778205+00:00
-- url     : https://prove2.me/submissions/aad9964c-1dd4-4bcc-bc09-d5ab223ac4f1

import Definitions.Def_OAI_NumberTheory_DirichletL_PrimeRows_NormFiberExtraction
import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_FiniteEulerRestoration
import Definitions.Def_OAI_NumberTheory_DirichletL_Hecke_FiniteEulerFactors
import Theorems.Thm_OAI_ActualEisensteinCubic_qNat_eq_absNorm_span
import Theorems.Thm_OAI_ConcretePrimeRowBridge_idealGenerator_injective
import Theorems.Thm_OAI_ConcretePrimeRowBridge_span_idealGenerator
import Theorems.Thm_OAI_IdealGaussCRT_traceProdChar_mk
import Theorems.Thm_OAI_ShortDraftLatticeCount_actual_eisenstein_count
import Theorems.Thm_OAI_ShortDraftLatticeCount_qO_nonneg
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
open OAI.CompactScaleBridge
open ConcretePrimeRowBridge ShortDraftHeckeBridge
namespace OAI.CompactScaleBridge
theorem _root_.solution (N : ℕ) :
    (idealsUpTo N).card ≤ 64 * (N + 1) := by
  classical
  have himage : (columnsUpTo N).card = (idealsUpTo N).card := by
    unfold columnsUpTo
    exact Finset.card_image_of_injective _ idealGenerator_injective
  rw [← himage]
  apply ShortDraftLatticeCount.actual_eisenstein_count
  intro x hx
  obtain ⟨I, hI, rfl⟩ := Finset.mem_image.mp hx
  have hnorm : Ideal.absNorm I ≤ N := (mem_idealsUpTo.mp hI).2
  have hqNat : ShortDraftLatticeCount.qNat (idealGenerator I) ≤ N := by
    rw [ActualEisensteinCubic.qNat_eq_absNorm_span, span_idealGenerator]
    exact hnorm
  have hnonneg := ShortDraftLatticeCount.qO_nonneg (idealGenerator I)
  have hcast : ((ShortDraftLatticeCount.q
      (ActualEisensteinCoordinates.coords (idealGenerator I))).toNat : ℤ) =
      ShortDraftLatticeCount.q
        (ActualEisensteinCoordinates.coords (idealGenerator I)) :=
    Int.toNat_of_nonneg hnonneg
  change (ShortDraftLatticeCount.q
    (ActualEisensteinCoordinates.coords (idealGenerator I))).toNat ≤ N at hqNat
  have hqInt :
      ((ShortDraftLatticeCount.q
        (ActualEisensteinCoordinates.coords (idealGenerator I))).toNat : ℤ) ≤ N := by
    exact_mod_cast hqNat
  simpa only [hcast] using hqInt
end OAI.CompactScaleBridge
