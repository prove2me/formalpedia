-- Prove2me | solution 1 for OAI.ActualEisensteinCubic.finiteSquarefreeRow_difference_norm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T05:19:04.371205+00:00
-- url     : https://prove2.me/submissions/dcd65707-790e-4838-aeb3-8b919f35b5a0

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_LocalProductAssembly
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_RamifiedTracePhase
import Theorems.Thm_OAI_ActualEisensteinCubic_finiteSquarefreeRow_difference

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
    ‖(∑ n ∈ columns, weight n) -
      (∑ n ∈ columns,
        weight n * finiteSquarefreeRow P hgood (support n) (a ^ 6))‖ ≤
      ∑ n ∈ columns.filter (fun n => ∃ i ∈ support n, a ∈ P i), ‖weight n‖ := by
  rw [finiteSquarefreeRow_difference]
  exact norm_sum_le _ _
end OAI.ActualEisensteinCubic
