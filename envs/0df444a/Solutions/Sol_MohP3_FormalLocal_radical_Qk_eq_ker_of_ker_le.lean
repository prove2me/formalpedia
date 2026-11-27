-- Prove2me | solution 1 for MohP3.FormalLocal.radical_Qk_eq_ker_of_ker_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:46:28.217383+00:00
-- url     : https://prove2.me/submissions/1c0ec4fc-1d46-4a42-9454-721aef40f9aa

module
public import Definitions.Def_MohP3_Generic
public import Definitions.Def_MohP3_FormalLocal
public import Theorems.Thm_MohP3_FormalLocal_radical_Qk_eq_radical_Pk
public import Theorems.Thm_MohP3_FormalLocal_radical_Qk_le_ker

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open MvPowerSeries
open MohP3 MohP3.FormalLocal
variable (k : Type*) [Field k] [CharZero k]
namespace MohP3.FormalLocal
theorem _root_.solution (hker : RingHom.ker (psi k) ≤ Pk k) :
    (Qk k).radical = RingHom.ker (psi k) := by
  refine le_antisymm (radical_Qk_le_ker k) ?_
  refine hker.trans ?_
  rw [radical_Qk_eq_radical_Pk]
  exact Ideal.le_radical
end MohP3.FormalLocal
