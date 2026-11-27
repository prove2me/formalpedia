-- Prove2me | solution 1 for MohP3.FormalLocal.formalLocal_radical_Qk
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:37:24.657995+00:00
-- url     : https://prove2.me/submissions/e348cf6c-811d-470a-9b5c-e286dbe18c1b

module
public import Definitions.Def_MohP3_FormalLocal
public import Definitions.Def_MohP3_GenClosure
public import Definitions.Def_MohP3_Order
public import Definitions.Def_MohP3_Generation
public import Theorems.Thm_MohP3_FormalLocal_generation
public import Theorems.Thm_MohP3_FormalLocal_radical_Qk_eq_ker_of_generation


set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open MvPowerSeries MohP3.Wt
open MohP3 MohP3.FormalLocal
variable (k : Type*) [Field k] [CharZero k]
namespace MohP3.FormalLocal
theorem _root_.solution (k : Type*) [Field k] [CharZero k] :
    (Qk k).radical = RingHom.ker (psi k) :=
  radical_Qk_eq_ker_of_generation k (generation k)
end MohP3.FormalLocal
