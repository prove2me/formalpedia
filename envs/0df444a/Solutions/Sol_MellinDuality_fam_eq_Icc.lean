-- Prove2me | solution 1 for MellinDuality.fam_eq_Icc
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:52:03.067516+00:00
-- url     : https://prove2.me/submissions/60965da5-b949-49c8-a587-36732cc366da

module
public import Definitions.Def_MellinDuality_Pairs
public import Definitions.Def_MellinDuality_MeanSquare
public import Theorems.Thm_MellinDuality_gi_im
public import Theorems.Thm_MellinDuality_gi_re
public import Theorems.Thm_MellinDuality_mem_half_iff
public import Theorems.Thm_MellinDuality_natCast_ne_zero_of_mem
public import Theorems.Thm_MellinDuality_odd_p
attribute [local simp] MellinDuality.gi_im
attribute [local simp] MellinDuality.gi_re



set_option autoImplicit true
@[expose] public section
public section
open MellinDuality
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
namespace MellinDuality
theorem _root_.solution (hp2 : p ≠ 2) {R : Type*} [CommRing R] (χ : MulChar (ZMod p) R) (a : ZMod p) :
    fam χ 2 a = ∑ n ∈ Icc 1 ((p - 1) / 2), χ (n : ZMod p) *
      (((-1 : ℤ) ^ ((n : ZMod p).val + (a * (n : ZMod p) ^ 2).val) : ℤ) : R) := by
  unfold fam
  rw [← sum_erase (half p) (a := 0) (by simp [MulChar.map_zero])]
  have hpo := odd_p hp2
  refine sum_nbij' (fun x => x.val) (fun n => (n : ZMod p)) ?_ ?_ ?_ ?_ ?_
  · intro x hx
    rw [mem_erase, mem_half_iff] at hx
    have := ZMod.val_pos.2 hx.1
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
    simp
end MellinDuality
