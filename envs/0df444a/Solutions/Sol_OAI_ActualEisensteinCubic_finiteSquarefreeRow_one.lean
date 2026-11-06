-- Prove2me | solution 1 for OAI.ActualEisensteinCubic.finiteSquarefreeRow_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T05:22:37.018204+00:00
-- url     : https://prove2.me/submissions/35a00fe0-7fd6-4698-81d8-a17c43d727cc

import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_LatticeCount
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_QuadraticTrace
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
    {ι : Type*} (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hgood : ∀ i, lambda ∉ P i) (S : Finset ι) :
    finiteSquarefreeRow P hgood S 1 = 1 := by
  classical
  unfold finiteSquarefreeRow
  apply Finset.prod_eq_one
  intro i hi
  simp
end OAI.ActualEisensteinCubic
