-- Prove2me | solution 1 for Kac.iUnion_firstHit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T13:12:32.999979+00:00
-- url     : https://prove2.me/submissions/b2f6c902-bd06-40dc-9c0f-ea5b1966efc0

module
public import Definitions.Def_Kac_Defs
public import Mathlib.Data.Real.ENatENNReal
public import Mathlib.Dynamics.Ergodic.Conservative
public import Mathlib.Dynamics.Ergodic.Ergodic
public import Mathlib.MeasureTheory.Integral.Average
public import Definitions.Def_Kac_Basic
public import Theorems.Thm_Kac_notYet_zero
public import Theorems.Thm_Kac_notYet_succ
public import Theorems.Thm_Kac_mem_notYet_iff
attribute [local simp] Kac.notYet_zero
attribute [local simp] Kac.notYet_succ

set_option autoImplicit false
@[expose] public section
public section
open Set Filter MeasureTheory Topology
open scoped ENNReal
open Kac
variable {α : Type*} {f : α → α} {A : Set α}
namespace Kac
theorem _root_.solution : ⋃ n, firstHit f A n = ⋃ k : ℕ, f^[k] ⁻¹' A := by
  classical
  ext x
  simp only [mem_iUnion, firstHit, mem_inter_iff, mem_preimage]
  constructor
  · rintro ⟨n, -, hn⟩
    exact ⟨n, hn⟩
  · intro h
    exact ⟨Nat.find h, (mem_notYet_iff _ x).mpr fun k hk => Nat.find_min h hk, Nat.find_spec h⟩
end Kac
