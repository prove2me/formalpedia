-- Prove2me | solution 1 for MohP3.FormalLocal.iter_wOrd
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:30:43.707268+00:00
-- url     : https://prove2.me/submissions/85c47920-e21f-45e6-bdeb-1ba9ac6522b4

module
public import Definitions.Def_MohP3_FormalLocal
public import Definitions.Def_MohP3_GenClosure
public import Definitions.Def_MohP3_Order
public import Definitions.Def_MohP3_Generation
public import Theorems.Thm_MohP3_FormalLocal_stepFun_spec
public import Theorems.Thm_MohP3_Wt_wOrd_zero


set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open MvPowerSeries MohP3.Wt
open MohP3 MohP3.FormalLocal
variable (k : Type*) [Field k] [CharZero k]
namespace MohP3.FormalLocal
theorem _root_.solution (F : Sk k) (s : ℕ) : WOrd (iter k F s).1 s := by
  induction s with
  | zero => exact wOrd_zero _
  | succ s ih => exact (stepFun_spec k s _ ih).1
end MohP3.FormalLocal
