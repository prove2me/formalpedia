-- Prove2me | solution 1 for MohP3.Wt.yOrd_monomial
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:23:04.85594+00:00
-- url     : https://prove2.me/submissions/8323574f-cb84-4538-949a-81835227cc7d

module
public import Mathlib
public import Definitions.Def_MohP3_Order
public import Theorems.Thm_MohP3_Wt_yOrd_zero
public import Theorems.Thm_P2M_MohP3_Wt_yOrd_mul__b3d090251f18
public import Theorems.Thm_MohP3_Wt_yOrd_X_pow

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open MvPowerSeries
open MohP3 MohP3.Wt
variable {k : Type*} [CommRing k]
namespace MohP3.Wt
theorem _root_.solution (c : k) (e n : ℕ) (h : n ≤ 8 * e) :
    YOrd (PowerSeries.C c * (PowerSeries.X : PowerSeries k) ^ e) n :=
  yOrd_mul' (by omega) (yOrd_zero _) (yOrd_X_pow e)
end MohP3.Wt
