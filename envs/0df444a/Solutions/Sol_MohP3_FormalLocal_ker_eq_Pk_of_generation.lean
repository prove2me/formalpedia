-- Prove2me | solution 1 for MohP3.FormalLocal.ker_eq_Pk_of_generation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:24:34.435742+00:00
-- url     : https://prove2.me/submissions/46504ef7-2e39-4eef-a6bc-3a32b99eb48c

module
public import Definitions.Def_MohP3_Generic
public import Definitions.Def_MohP3_FormalLocal
public import Theorems.Thm_MohP3_FormalLocal_Pk_le_ker
public import Theorems.Thm_MohP3_FormalLocal_ker_le_Pk_of_generation

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open MvPowerSeries
open MohP3 MohP3.FormalLocal
variable (k : Type*) [Field k] [CharZero k]
namespace MohP3.FormalLocal
theorem _root_.solution (hgen : Generation k) : RingHom.ker (psi k) = Pk k :=
  le_antisymm (ker_le_Pk_of_generation k hgen) (Pk_le_ker k)
end MohP3.FormalLocal
