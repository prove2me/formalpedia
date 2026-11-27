-- Prove2me | solution 1 for MohP3.Wt.mem_En_of
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:22:12.908811+00:00
-- url     : https://prove2.me/submissions/bfdd0466-ba77-4200-89f6-bf61f6898cde

module
public import Mathlib
public import Definitions.Def_MohP3_Order
public import Theorems.Thm_MohP3_Wt_dd_apply_zero
public import Theorems.Thm_MohP3_Wt_dd_apply_one
public import Theorems.Thm_MohP3_Wt_dd_apply_two
public import Theorems.Thm_MohP3_Wt_wt_dd
attribute [local simp] MohP3.Wt.dd_apply_zero
attribute [local simp] MohP3.Wt.dd_apply_one
attribute [local simp] MohP3.Wt.dd_apply_two
attribute [local simp] MohP3.Wt.wt_dd

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open MvPowerSeries
open MohP3 MohP3.Wt
variable {k : Type*} [CommRing k]
namespace MohP3.Wt
theorem _root_.solution {n a b c : ℕ} (h : 6 * a + 8 * b + 10 * c = n) : (a, b, c) ∈ En n := by
  simp only [En, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
  refine ⟨⟨by omega, by omega, by omega⟩, h⟩
end MohP3.Wt
