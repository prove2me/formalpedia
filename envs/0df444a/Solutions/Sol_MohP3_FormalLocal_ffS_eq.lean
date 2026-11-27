-- Prove2me | solution 1 for MohP3.FormalLocal.ffS_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:47:17.517558+00:00
-- url     : https://prove2.me/submissions/f6c57fed-b044-488b-b029-f72038bb4e6f

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
theorem _root_.solution (j : Fin 4) : ffS k j = Gen.ff (xs k) (ys k) (zs k) j := rfl
end MohP3.FormalLocal
