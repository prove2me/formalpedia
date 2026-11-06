-- Prove2me | solution 1 for OAI.ShortDraftLatticeCount.finite_lattice_count_linear
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T05:21:07.483496+00:00
-- url     : https://prove2.me/submissions/ccf3eb66-1363-4efc-a8ef-851e9bed49a9

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_RamifiedTracePhase
import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_LatticeCount
import Theorems.Thm_OAI_ShortDraftLatticeCount_finite_lattice_count

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
namespace OAI.ShortDraftLatticeCount
theorem _root_.solution (S : Finset (ℤ × ℤ)) (D : ℕ)
    (hS : ∀ x ∈ S, q x ≤ D) :
    S.card ≤ 64 * (D + 1) := by
  have hR : 2 * D < (Nat.sqrt (2 * D) + 1) ^ 2 := by
    exact Nat.lt_succ_sqrt' _
  have hcount := finite_lattice_count S D (Nat.sqrt (2 * D) + 1) hR hS
  have hsquare : (Nat.sqrt (2 * D)) ^ 2 ≤ 2 * D := Nat.sqrt_le' _
  have hroot : Nat.sqrt (2 * D) ≤ 2 * D := Nat.sqrt_le_self _
  nlinarith
end OAI.ShortDraftLatticeCount
