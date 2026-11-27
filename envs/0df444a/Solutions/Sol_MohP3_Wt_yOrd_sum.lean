-- Prove2me | solution 1 for MohP3.Wt.yOrd_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:20:47.29067+00:00
-- url     : https://prove2.me/submissions/2cde9d1d-55ee-46fd-a063-e27bb1462f32

module
public import Mathlib
public import Definitions.Def_MohP3_Order
public import Theorems.Thm_MohP3_Wt_yOrd_of_zero
public import Theorems.Thm_MohP3_Wt_yOrd_add

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open MvPowerSeries
open MohP3 MohP3.Wt
variable {k : Type*} [CommRing k]
namespace MohP3.Wt
theorem _root_.solution {ι : Type*} {s : Finset ι} {p : ι → PowerSeries k} {n : ℕ}
    (h : ∀ i ∈ s, YOrd (p i) n) : YOrd (∑ i ∈ s, p i) n := by
  classical
  induction s using Finset.induction with
  | empty => simpa using (yOrd_of_zero (k := k) (n := n))
  | insert a s ha ih =>
      rw [Finset.sum_insert ha]
      exact yOrd_add (h a (Finset.mem_insert_self _ _))
        (ih fun i hi => h i (Finset.mem_insert_of_mem hi))
end MohP3.Wt
