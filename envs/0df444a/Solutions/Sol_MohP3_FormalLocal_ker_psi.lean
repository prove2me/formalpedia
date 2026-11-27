-- Prove2me | solution 1 for MohP3.FormalLocal.ker_psi
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:37:20.594991+00:00
-- url     : https://prove2.me/submissions/a03daaf6-29f0-406d-81a5-6280df55a72a

module
public import Definitions.Def_MohP3_FormalLocal
public import Definitions.Def_MohP3_GenClosure
public import Definitions.Def_MohP3_Order
public import Definitions.Def_MohP3_Generation
public import Theorems.Thm_MohP3_FormalLocal_generation
public import Theorems.Thm_MohP3_FormalLocal_ker_eq_Pk_of_generation


set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open MvPowerSeries MohP3.Wt
open MohP3 MohP3.FormalLocal
variable (k : Type*) [Field k] [CharZero k]
namespace MohP3.FormalLocal
theorem _root_.solution (k : Type*) [Field k] [CharZero k] : RingHom.ker (psi k) = Pk k :=
  ker_eq_Pk_of_generation k (generation k)
end MohP3.FormalLocal
