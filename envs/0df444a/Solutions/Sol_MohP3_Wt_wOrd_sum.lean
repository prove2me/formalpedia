-- Prove2me | solution 1 for MohP3.Wt.wOrd_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:00:12.16346+00:00
-- url     : https://prove2.me/submissions/dd6cbfd2-53f0-4d48-b392-0357a81bdbfe

module
public import Mathlib
public import Definitions.Def_MohP3_Order
public import Theorems.Thm_MohP3_Wt_wOrd_of_zero
public import Theorems.Thm_MohP3_Wt_wOrd_add

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open MvPowerSeries
open MohP3 MohP3.Wt
variable {k : Type*} [CommRing k]
namespace MohP3.Wt
theorem _root_.solution {ι : Type*} {s : Finset ι} {F : ι → MvPowerSeries (Fin 3) k} {n : ℕ}
    (h : ∀ i ∈ s, WOrd (F i) n) : WOrd (∑ i ∈ s, F i) n := by
  classical
  induction s using Finset.induction with
  | empty => simpa using (wOrd_of_zero (k := k) (n := n))
  | insert a s ha ih =>
      rw [Finset.sum_insert ha]
      exact wOrd_add (h a (Finset.mem_insert_self _ _))
        (ih fun i hi => h i (Finset.mem_insert_of_mem hi))
end MohP3.Wt
