-- Prove2me | solution 1 for MohP3.FormalLocal.Pk_le_ker
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:19:32.760059+00:00
-- url     : https://prove2.me/submissions/26f6e27d-0ff0-46cc-82ed-c88916158bab

module
public import Definitions.Def_MohP3_Generic
public import Definitions.Def_MohP3_FormalLocal
public import Theorems.Thm_MohP3_FormalLocal_psi_f1
public import Theorems.Thm_MohP3_FormalLocal_psi_f2
public import Theorems.Thm_MohP3_FormalLocal_psi_f3
public import Theorems.Thm_MohP3_FormalLocal_psi_f4

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open MvPowerSeries
open MohP3 MohP3.FormalLocal
variable (k : Type*) [Field k] [CharZero k]
omit [CharZero k]
namespace MohP3.FormalLocal
theorem _root_.solution : Pk k ≤ RingHom.ker (psi k) := by
  rw [Pk, Gen.P, Ideal.span_le]
  intro g hg
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
  rcases hg with rfl | rfl | rfl | rfl
  · exact RingHom.mem_ker.mpr (psi_f1 k)
  · exact RingHom.mem_ker.mpr (psi_f2 k)
  · exact RingHom.mem_ker.mpr (psi_f3 k)
  · exact RingHom.mem_ker.mpr (psi_f4 k)
end MohP3.FormalLocal
