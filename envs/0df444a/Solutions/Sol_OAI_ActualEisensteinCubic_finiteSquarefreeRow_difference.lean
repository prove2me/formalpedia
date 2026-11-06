-- Prove2me | solution 1 for OAI.ActualEisensteinCubic.finiteSquarefreeRow_difference
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T05:18:03.326962+00:00
-- url     : https://prove2.me/submissions/e646361d-276b-4917-a877-f2ffe94e5a7a

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_LocalProductAssembly
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_RamifiedTracePhase
import Theorems.Thm_OAI_ActualEisensteinCubic_finiteSquarefreeRow_sixth_power
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
open OAI.ActualEisensteinCubic
namespace OAI.ActualEisensteinCubic
theorem _root_.solution
    {ι N : Type*} [DecidableEq N]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hgood : ∀ i, lambda ∉ P i)
    (columns : Finset N) (support : N → Finset ι)
    (weight : N → ℂ) (a : O) :
    (∑ n ∈ columns, weight n) -
      (∑ n ∈ columns,
        weight n * finiteSquarefreeRow P hgood (support n) (a ^ 6)) =
      ∑ n ∈ columns.filter (fun n => ∃ i ∈ support n, a ∈ P i), weight n := by
  classical
  rw [← Finset.sum_sub_distrib]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro n hn
  rw [finiteSquarefreeRow_sixth_power]
  by_cases h : ∃ i ∈ support n, a ∈ P i <;> simp [h]
end OAI.ActualEisensteinCubic
