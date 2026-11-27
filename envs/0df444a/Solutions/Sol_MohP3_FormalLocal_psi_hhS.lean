-- Prove2me | solution 1 for MohP3.FormalLocal.psi_hhS
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:18:26.971417+00:00
-- url     : https://prove2.me/submissions/eaa53282-1fb9-4d97-b351-869f20d4a612

module
public import Definitions.Def_MohP3_Generic
public import Definitions.Def_MohP3_FormalLocal

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open MvPowerSeries
open MohP3 MohP3.FormalLocal
variable (k : Type*) [Field k] [CharZero k]
omit [CharZero k]
namespace MohP3.FormalLocal
theorem _root_.solution (i : Fin 8) : psi k (hhS k i) = vvS k i := by
  fin_cases i <;> simp [hhS, vvS] <;> ring
end MohP3.FormalLocal
