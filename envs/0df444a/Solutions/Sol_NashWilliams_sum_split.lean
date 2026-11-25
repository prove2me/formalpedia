-- Prove2me | solution 1 for NashWilliams.sum_split
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T17:55:17.007823+00:00
-- url     : https://prove2.me/submissions/39b6ecdf-ac78-4d12-ab0b-e44e282a537c

module
public import Definitions.Def_NashWilliamsLib_Basic
public import Definitions.Def_NashWilliamsLib_Splitting

set_option autoImplicit true
@[expose] public section
public section
open Finset
open NashWilliams
variable {V ι : Type*} [DecidableEq V]
namespace NashWilliams
theorem _root_.solution [DecidableEq ι] {f f1 : ι → ℕ} {F : Finset ι} {i j : ι} (hi : i ∈ F)
    (hj : j ∈ F) (hij : i ≠ j) (hf : ∀ l ∈ F, l ≠ i → l ≠ j → f1 l = f l) :
    ∑ l ∈ F, f l + f1 i = ∑ l ∈ F.erase j, f1 l + f i + f j := by
  have hi' : i ∈ F.erase j := mem_erase.2 ⟨hij, hi⟩
  have e1 := Finset.add_sum_erase F f hj
  have e2 := Finset.add_sum_erase (F.erase j) f hi'
  have e3 := Finset.add_sum_erase (F.erase j) f1 hi'
  have e4 : ∑ l ∈ (F.erase j).erase i, f1 l = ∑ l ∈ (F.erase j).erase i, f l := by
    refine Finset.sum_congr rfl fun l hl => ?_
    simp only [mem_erase] at hl
    exact hf l hl.2.2 hl.1 hl.2.1
  omega
end NashWilliams
