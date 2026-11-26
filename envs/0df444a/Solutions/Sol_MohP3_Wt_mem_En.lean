-- Prove2me | solution 1 for MohP3.Wt.mem_En
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:00:09.14266+00:00
-- url     : https://prove2.me/submissions/2c954f69-6acc-4239-8740-ec075f3f18f0

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
theorem _root_.solution {n : ℕ} {p : ℕ × ℕ × ℕ} (hp : p ∈ En n) :
    6 * p.1 + 8 * p.2.1 + 10 * p.2.2 = n := by
  simpa [En] using (Finset.mem_filter.mp hp).2
end MohP3.Wt
