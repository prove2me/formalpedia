-- Prove2me | solution 1 for MohP3.FormalLocal.radical_Qk_le_ker
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:21:04.647215+00:00
-- url     : https://prove2.me/submissions/4ea347e6-f246-4bb2-8936-8ba53fd73ed4

module
public import Definitions.Def_MohP3_Generic
public import Definitions.Def_MohP3_FormalLocal
public import Theorems.Thm_MohP3_FormalLocal_radical_Qk_eq_radical_Pk
public import Theorems.Thm_MohP3_FormalLocal_Pk_le_ker
public import Theorems.Thm_MohP3_FormalLocal_ker_psi_isPrime

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open MvPowerSeries
open MohP3 MohP3.FormalLocal
variable (k : Type*) [Field k] [CharZero k]
namespace MohP3.FormalLocal
theorem _root_.solution : (Qk k).radical ≤ RingHom.ker (psi k) := by
  rw [radical_Qk_eq_radical_Pk]
  calc (Pk k).radical ≤ (RingHom.ker (psi k)).radical := Ideal.radical_mono (Pk_le_ker k)
    _ = RingHom.ker (psi k) := (ker_psi_isPrime k).radical
end MohP3.FormalLocal
