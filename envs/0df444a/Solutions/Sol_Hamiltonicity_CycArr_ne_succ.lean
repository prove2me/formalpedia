-- Prove2me | solution 1 for Hamiltonicity.CycArr.ne_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:17:09.404835+00:00
-- url     : https://prove2.me/submissions/49692b20-1a0b-45d0-9109-81fa69ec4aca

module
public import Definitions.Def_MengerHamilton_LongerCycle
public import Definitions.Def_MengerHamilton_ChvatalErdosAux
public import Theorems.Thm_Hamiltonicity_CycArr_eq_iff
public import Theorems.Thm_Hamiltonicity_CycArr_pos
public import Theorems.Thm_Hamiltonicity_CycArr_succ_mod_of_eq
public import Theorems.Thm_Hamiltonicity_CycArr_succ_mod_of_lt


set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open Hamiltonicity
variable {V : Type*}
namespace Hamiltonicity
namespace CycArr
theorem _root_.solution {G : SimpleGraph V} {m : ℕ} {f : ℕ → V} (hC : CycArr G m f) (i : ℕ) :
    f i ≠ f (i + 1) := by
  intro h
  rw [hC.eq_iff] at h
  have hm := hC.three_le
  have hlt : i % m < m := Nat.mod_lt _ hC.pos
  by_cases hc : i % m + 1 < m
  · rw [CycArr.succ_mod_of_lt hc] at h
    omega
  · rw [CycArr.succ_mod_of_eq (by omega)] at h
    omega
end CycArr
end Hamiltonicity
