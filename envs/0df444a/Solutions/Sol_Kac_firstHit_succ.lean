-- Prove2me | solution 1 for Kac.firstHit_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T13:12:02.963364+00:00
-- url     : https://prove2.me/submissions/0aa0892d-9436-47f5-9cf5-f820a93d3a0a

module
public import Definitions.Def_Kac_Defs
public import Mathlib.Data.Real.ENatENNReal
public import Mathlib.Dynamics.Ergodic.Conservative
public import Mathlib.Dynamics.Ergodic.Ergodic
public import Mathlib.MeasureTheory.Integral.Average
public import Definitions.Def_Kac_Basic
public import Theorems.Thm_Kac_notYet_zero
public import Theorems.Thm_Kac_notYet_succ
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
theorem _root_.solution (n : ℕ) : firstHit f A (n + 1) = Aᶜ ∩ f ⁻¹' firstHit f A n := by
  ext x
  simp only [firstHit, notYet_succ, mem_inter_iff, mem_preimage, Function.iterate_succ_apply]
  tauto
end Kac
