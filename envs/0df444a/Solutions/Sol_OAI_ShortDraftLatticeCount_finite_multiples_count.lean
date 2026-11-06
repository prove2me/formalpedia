-- Prove2me | solution 1 for OAI.ShortDraftLatticeCount.finite_multiples_count
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T05:22:57.754203+00:00
-- url     : https://prove2.me/submissions/ee094fe8-f3b9-4f6e-9349-c5566cc36e71

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_RamifiedTracePhase
import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_LatticeCount
import Theorems.Thm_OAI_ShortDraftLatticeCount_actual_eisenstein_count
import Theorems.Thm_OAI_ShortDraftLatticeCount_qO_nonneg
import Theorems.Thm_OAI_ShortDraftLatticeCount_qNat_mul
import Theorems.Thm_OAI_ShortDraftLatticeCount_qNat_pos
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
open OAI.ShortDraftLatticeCount
open ActualEisensteinCoordinates
namespace OAI.ShortDraftLatticeCount
theorem _root_.solution
    (p : O) (hp : p ≠ 0) (T : Finset O) (D : ℕ)
    (hT : ∀ x ∈ T, qNat (p * x) ≤ D) :
    T.card ≤ 64 * (D / qNat p + 1) := by
  have hbound : ∀ x ∈ T, q (coords x) ≤ (D / qNat p : ℕ) := by
    intro x hx
    have hmul := hT x hx
    rw [qNat_mul] at hmul
    have hdiv : qNat x ≤ D / qNat p :=
      (Nat.le_div_iff_mul_le (qNat_pos hp)).mpr (by
        simpa [mul_comm] using hmul)
    have hnat : qNat x = (q (coords x)) :=
      Int.toNat_of_nonneg (qO_nonneg x)
    have hdiv' : (qNat x : ℤ) ≤ (D / qNat p : ℕ) := by
      exact_mod_cast hdiv
    simpa only [hnat] using hdiv'
  exact actual_eisenstein_count T (D / qNat p) hbound
end OAI.ShortDraftLatticeCount
