-- Prove2me | solution 1 for MohP3.FormalLocal.radical_Qk_eq_ker_of_generation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:25:59.04845+00:00
-- url     : https://prove2.me/submissions/073bed4d-2906-4489-a6b7-86345a822627

module
public import Definitions.Def_MohP3_Generic
public import Definitions.Def_MohP3_FormalLocal
public import Theorems.Thm_MohP3_FormalLocal_radical_Qk_eq_radical_Pk
public import Theorems.Thm_MohP3_FormalLocal_radical_Qk_le_ker
public import Theorems.Thm_MohP3_FormalLocal_ker_eq_Pk_of_generation

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open MvPowerSeries
open MohP3 MohP3.FormalLocal
variable (k : Type*) [Field k] [CharZero k]
namespace MohP3.FormalLocal
theorem _root_.solution (hgen : Generation k) :
    (Qk k).radical = RingHom.ker (psi k) := by
  refine le_antisymm (radical_Qk_le_ker k) ?_
  rw [ker_eq_Pk_of_generation k hgen, radical_Qk_eq_radical_Pk]
  exact Ideal.le_radical
end MohP3.FormalLocal
