-- Prove2me | solution 1 for MellinDuality.bandSum_eq_Icc
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:51:11.659638+00:00
-- url     : https://prove2.me/submissions/e635ffbe-88b7-45c0-ac3b-6fb3e8fa6753

module
public import Definitions.Def_MellinDuality_Quartic
public import Definitions.Def_MellinDuality_Parseval
public import Definitions.Def_MellinDuality_Pairs
public import Theorems.Thm_MellinDuality_gi_im
public import Theorems.Thm_MellinDuality_gi_re
public import Theorems.Thm_MellinDuality_mem_half_iff
public import Theorems.Thm_MellinDuality_natCast_ne_zero_of_mem
public import Theorems.Thm_MellinDuality_odd_p
public import Theorems.Thm_MellinDuality_val_pos_of_ne_zero
attribute [local simp] MellinDuality.gi_im
attribute [local simp] MellinDuality.gi_re



set_option autoImplicit true
@[expose] public section
public section
open MellinDuality
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
namespace MellinDuality
theorem _root_.solution (hp2 : p ≠ 2) {R : Type*} [CommRing R] (χ : MulChar (ZMod p) R) :
    bandSumPow χ 2 = ∑ n ∈ Icc 1 ((p - 1) / 2), χ (n : ZMod p) * (eps p n : R) := by
  unfold bandSumPow
  rw [← sum_erase (half p) (a := 0) (by simp [MulChar.map_zero])]
  have hpo := odd_p hp2
  refine sum_nbij' (fun x => x.val) (fun n => (n : ZMod p)) ?_ ?_ ?_ ?_ ?_
  · intro x hx
    rw [mem_erase, mem_half_iff] at hx
    have := val_pos_of_ne_zero hx.1
    rw [mem_Icc]; obtain ⟨k, hk⟩ := hpo; omega
  · intro n hn
    have hn0 := natCast_ne_zero_of_mem (p := p) hn
    rw [mem_Icc] at hn
    rw [mem_erase, mem_half_iff, ZMod.val_natCast_of_lt (by omega)]
    exact ⟨hn0, by omega⟩
  · intro x _; simp
  · intro n hn
    rw [mem_Icc] at hn
    simp only [ZMod.val_natCast_of_lt (show n < p by omega)]
  · intro x _
    simp [bandSignE, eps]
end MellinDuality
