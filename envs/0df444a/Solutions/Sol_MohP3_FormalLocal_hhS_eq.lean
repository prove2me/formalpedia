-- Prove2me | solution 1 for MohP3.FormalLocal.hhS_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:46:47.108575+00:00
-- url     : https://prove2.me/submissions/6d9ab59c-cc2c-4c06-af8b-f1cd31824980

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
omit [CharZero k]
namespace MohP3.FormalLocal
theorem _root_.solution (i : Fin 8) : hhS k i = Gen.hh (xs k) (ys k) (zs k) i := rfl
end MohP3.FormalLocal
