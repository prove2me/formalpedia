-- Prove2me | solution 1 for OAI.TraceLambdaPhase.breveE_traceLambda_square
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T05:18:23.277195+00:00
-- url     : https://prove2.me/submissions/99e9b768-3e5e-4b97-b928-d870f3e3df1a

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_LocalProductAssembly
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_RamifiedTracePhase
import Theorems.Thm_OAI_TraceLambdaPhase_eisLam_sq
import Theorems.Thm_OAI_TraceLambdaPhase_exp_minus_four_pi_div_three
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
open OAI.TraceLambdaPhase
open EisensteinEmbedding ConcreteTraceCRT Complex
open scoped ComplexConjugate
namespace OAI.TraceLambdaPhase
theorem _root_.solution :
    ShortDraftTrace.breveE (1 / (eisLam * eisLam)) = omega3 := by
  have harg : (1 : ℂ) / (eisLam * eisLam) = -(1 : ℂ) / 3 := by
    rw [← pow_two, eisLam_sq]
    ring
  rw [harg]
  change Complex.exp (2 * Real.pi * Complex.I *
    ((-(1 : ℂ) / 3) + conj (-(1 : ℂ) / 3))) = omega3
  have hconj : conj (-(1 : ℂ) / 3) = -(1 : ℂ) / 3 := by
    simp only [map_div₀, map_neg, map_one, map_ofNat]
  rw [hconj]
  convert exp_minus_four_pi_div_three using 1 ; ring_nf
end OAI.TraceLambdaPhase
