-- Prove2me | solution 1 for OAI.FixedRayActiveSet.admissible_branch_count
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T05:12:45.292261+00:00
-- url     : https://prove2.me/submissions/b9838067-7820-4cfc-902e-3f25501730d2

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_CubicNormalization
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_SexticNormalization
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
open OAI.FixedRayActiveSet
open scoped BigOperators
namespace OAI.FixedRayActiveSet
theorem _root_.solution
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (j : ι → ℕ) :
    ((Finset.univ : Finset ι).powerset.filter
      (fun A => (Finset.univ.filter (fun i => j i ≠ 0)) ⊆ A)).card
      ≤ 2 ^ Fintype.card ι := by
  calc
    _ ≤ (Finset.univ : Finset ι).powerset.card := Finset.card_filter_le _ _
    _ = 2 ^ Fintype.card ι := by simp
end OAI.FixedRayActiveSet
