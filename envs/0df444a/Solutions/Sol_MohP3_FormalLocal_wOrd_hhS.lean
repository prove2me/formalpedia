-- Prove2me | solution 1 for MohP3.FormalLocal.wOrd_hhS
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:47:21.373785+00:00
-- url     : https://prove2.me/submissions/a94f7d00-591e-4bc6-ac5d-e31d9e570e36

module
public import Definitions.Def_MohP3_FormalLocal
public import Definitions.Def_MohP3_GenClosure
public import Definitions.Def_MohP3_Order
public import Definitions.Def_MohP3_Generation
public import Theorems.Thm_MohP3_Wt_dd_apply_one
public import Theorems.Thm_MohP3_Wt_dd_apply_two
public import Theorems.Thm_MohP3_Wt_dd_apply_zero
public import Theorems.Thm_MohP3_Wt_wOrd_mono
public import Theorems.Thm_MohP3_Wt_wOrd_pow
public import Theorems.Thm_MohP3_Wt_wOrd_sub
public import Theorems.Thm_MohP3_Wt_wOrd_zero
public import Theorems.Thm_MohP3_Wt_wt_dd
public import Theorems.Thm_P2M_MohP3_Wt_wOrd_mul__c4d0f86c750f
attribute [local simp] MohP3.Wt.dd_apply_one
attribute [local simp] MohP3.Wt.dd_apply_two
attribute [local simp] MohP3.Wt.dd_apply_zero
attribute [local simp] MohP3.Wt.wt_dd



set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open MvPowerSeries MohP3.Wt
open MohP3 MohP3.FormalLocal
variable (k : Type*) [Field k] [CharZero k]
omit [CharZero k]
namespace MohP3.FormalLocal
theorem _root_.solution (i : Fin 8) : WOrd (hhS k i) (Gen.sig i) := by
  have hx := wOrd_xs k
  have hy := wOrd_ys k
  have hz := wOrd_zs k
  fin_cases i
  · exact wOrd_zero _
  · simpa [hhS, Gen.sig] using hx
  · simpa [hhS, Gen.sig] using hz
  · simpa [hhS, Gen.sig] using wOrd_pow hx 2
  · show WOrd (xs k * zs k - ys k ^ 2) 16
    exact wOrd_sub (wOrd_mul' (by norm_num) hx hz) (wOrd_mono (by norm_num) (wOrd_pow hy 2))
  · show WOrd (xs k ^ 3 - ys k * zs k) 18
    exact wOrd_sub (wOrd_mono (by norm_num) (wOrd_pow hx 3)) (wOrd_mul' (by norm_num) hy hz)
  · show WOrd (zs k ^ 2 - ys k * xs k ^ 2) 20
    exact wOrd_sub (wOrd_mono (by norm_num) (wOrd_pow hz 2))
      (wOrd_mul' (by norm_num) hy (wOrd_pow hx 2))
  · show WOrd (xs k ^ 2 * zs k - ys k ^ 2 * xs k - ys k ^ 9) 22
    exact wOrd_sub (wOrd_sub (wOrd_mul' (by norm_num) (wOrd_pow hx 2) hz)
      (wOrd_mul' (by norm_num) (wOrd_pow hy 2) hx)) (wOrd_mono (by norm_num) (wOrd_pow hy 9))
end MohP3.FormalLocal
