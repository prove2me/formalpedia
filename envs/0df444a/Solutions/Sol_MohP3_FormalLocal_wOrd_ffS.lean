-- Prove2me | solution 1 for MohP3.FormalLocal.wOrd_ffS
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:47:24.423878+00:00
-- url     : https://prove2.me/submissions/1c3e161c-ec18-42e5-b044-368dd12b54b2

module
public import Definitions.Def_MohP3_FormalLocal
public import Definitions.Def_MohP3_GenClosure
public import Definitions.Def_MohP3_Order
public import Definitions.Def_MohP3_Generation
public import Theorems.Thm_MohP3_Wt_wOrd_add
public import Theorems.Thm_MohP3_Wt_wOrd_mono
public import Theorems.Thm_MohP3_Wt_wOrd_pow
public import Theorems.Thm_MohP3_Wt_wOrd_sub
public import Theorems.Thm_MohP3_Wt_wOrd_zero
public import Theorems.Thm_P2M_MohP3_Wt_wOrd_mul__c4d0f86c750f


set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open MvPowerSeries MohP3.Wt
open MohP3 MohP3.FormalLocal
variable (k : Type*) [Field k] [CharZero k]
omit [CharZero k]
namespace MohP3.FormalLocal
theorem _root_.solution (j : Fin 4) : WOrd (ffS k j) (Gen.tau j) := by
  have hx := wOrd_xs k
  have hy := wOrd_ys k
  have hz := wOrd_zs k
  have hc : ∀ (m : ℕ) (n : ℕ), WOrd ((m : Sk k)) n → True := fun _ _ _ => trivial
  fin_cases j
  · show WOrd (Gen.f1 (xs k) (ys k) (zs k)) 24
    rw [Gen.f1]
    refine wOrd_add (wOrd_sub (wOrd_sub (wOrd_sub (wOrd_sub
      (wOrd_mono (by norm_num) (wOrd_pow hx 4)) ?_) ?_) ?_) ?_) ?_
    · exact wOrd_mul' (by norm_num) (wOrd_mul' (le_refl _) (wOrd_pow hx 2) (wOrd_pow hy 4))
        (wOrd_pow hz 3)
    · exact wOrd_mul' (by norm_num)
        (wOrd_mul' (le_refl _) (wOrd_mul' (le_refl _) (wOrd_zero _) hx) (wOrd_pow hy 6))
        (wOrd_pow hz 2)
    · exact wOrd_mul' (by norm_num)
        (wOrd_mul' (le_refl _) (wOrd_mul' (le_refl _) (wOrd_zero _) hx) hy) hz
    · exact wOrd_mul' (by norm_num) (wOrd_mul' (le_refl _) (wOrd_zero _) (wOrd_pow hy 3))
        (wOrd_pow hz 5)
    · exact wOrd_mul' (by norm_num) (wOrd_zero _) (wOrd_pow hy 3)
  · show WOrd (Gen.f2 (xs k) (ys k) (zs k)) 26
    rw [Gen.f2]
    refine wOrd_add (wOrd_sub (wOrd_sub (wOrd_sub
      (wOrd_mul' (by norm_num) (wOrd_pow hx 3) hy) ?_) ?_) ?_) ?_
    · exact wOrd_mul' (by norm_num) (wOrd_mul' (le_refl _) hx (wOrd_pow hy 5)) (wOrd_pow hz 3)
    · exact wOrd_mul' (by norm_num) (wOrd_mul' (le_refl _) (wOrd_zero _) hx) (wOrd_pow hz 2)
    · exact wOrd_mul' (by norm_num) (wOrd_mul' (le_refl _) (wOrd_zero _) (wOrd_pow hy 7))
        (wOrd_pow hz 2)
    · exact wOrd_mul' (by norm_num) (wOrd_mul' (le_refl _) (wOrd_zero _) (wOrd_pow hy 2)) hz
  · show WOrd (Gen.f3 (xs k) (ys k) (zs k)) 28
    rw [Gen.f3]
    refine wOrd_add (wOrd_sub (wOrd_sub (wOrd_sub ?_ ?_) ?_) ?_) ?_
    · exact wOrd_mul' (by norm_num) (wOrd_mul' (le_refl _) (wOrd_zero _) (wOrd_pow hx 3)) hz
    · exact wOrd_mul' (by norm_num) (wOrd_mul' (le_refl _) (wOrd_zero _) (wOrd_pow hx 2))
        (wOrd_pow hy 2)
    · exact wOrd_mul' (by norm_num) (wOrd_mul' (le_refl _) (wOrd_mul' (le_refl _) (wOrd_zero _) hx)
        (wOrd_pow hy 4)) (wOrd_pow hz 4)
    · exact wOrd_mul' (by norm_num) (wOrd_pow hy 6) (wOrd_pow hz 3)
    · exact wOrd_mul' (by norm_num) hy (wOrd_pow hz 2)
  · show WOrd (Gen.f4 (xs k) (ys k) (zs k)) 30
    rw [Gen.f4]
    refine wOrd_add (wOrd_sub (wOrd_sub (wOrd_mul' (by norm_num)
      (wOrd_mul' (le_refl _) (wOrd_pow hx 2) hy) hz) ?_) ?_) ?_
    · exact wOrd_mul' (by norm_num) (wOrd_mul' (le_refl _) (wOrd_zero _) hx) (wOrd_pow hy 3)
    · exact wOrd_mul' (by norm_num) (wOrd_pow hy 5) (wOrd_pow hz 4)
    · exact wOrd_mono (by norm_num) (wOrd_pow hz 3)
end MohP3.FormalLocal
