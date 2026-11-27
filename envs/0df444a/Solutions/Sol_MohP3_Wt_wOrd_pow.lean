-- Prove2me | solution 1 for MohP3.Wt.wOrd_pow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:22:12.323801+00:00
-- url     : https://prove2.me/submissions/c4675bb1-9f78-4332-98d1-35cd00cac08d

module
public import Mathlib
public import Definitions.Def_MohP3_Order
public import Theorems.Thm_MohP3_Wt_wOrd_zero
public import Theorems.Thm_MohP3_Wt_wOrd_mono
public import Theorems.Thm_MohP3_Wt_wOrd_mul

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open MvPowerSeries
open MohP3 MohP3.Wt
variable {k : Type*} [CommRing k]
namespace MohP3.Wt
theorem _root_.solution {F : MvPowerSeries (Fin 3) k} {m : ℕ} (hF : WOrd F m) (e : ℕ) :
    WOrd (F ^ e) (e * m) := by
  induction e with
  | zero => simpa using wOrd_zero (1 : MvPowerSeries (Fin 3) k)
  | succ e ih =>
      have := wOrd_mul ih hF
      rw [pow_succ]
      exact wOrd_mono (by ring_nf; omega) this
end MohP3.Wt
