-- Prove2me | solution 1 for MohP3.FormalLocal.stepFun_spec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:29:02.983696+00:00
-- url     : https://prove2.me/submissions/d082b6ba-e7db-4cf5-9063-d2bd135578ad

module
public import Definitions.Def_MohP3_FormalLocal
public import Definitions.Def_MohP3_GenClosure
public import Definitions.Def_MohP3_Order
public import Definitions.Def_MohP3_Generation

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open MvPowerSeries MohP3.Wt
open MohP3 MohP3.FormalLocal
variable (k : Type*) [Field k] [CharZero k]
namespace MohP3.FormalLocal
theorem _root_.solution (n : ℕ) (F : Sk k) (h : WOrd F n) :
    WOrd (stepFun k n F).1 (n + 1) ∧
      (∀ i, YOrd ((stepFun k n F).2.1 i) (n - Gen.sig i)) ∧
      (∀ j, WOrd ((stepFun k n F).2.2 j) (n - Gen.tau j)) ∧
      F - (stepFun k n F).1 =
        (∑ i, iotaS k ((stepFun k n F).2.1 i) * hhS k i) + ∑ j, (stepFun k n F).2.2 j * ffS k j := by
  rw [stepFun, dif_pos h]
  exact (Rep_step k F n h).choose_spec
end MohP3.FormalLocal
