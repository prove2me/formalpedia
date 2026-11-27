-- Prove2me | solution 1 for MohP3.FormalLocal.ker_le_Pk_of_generation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:23:03.079009+00:00
-- url     : https://prove2.me/submissions/06697e2d-3094-4aeb-b00c-79ae2dbdc1c3

module
public import Definitions.Def_MohP3_Generic
public import Definitions.Def_MohP3_FormalLocal
public import Theorems.Thm_MohP3_FormalLocal_psi_iotaS
public import Theorems.Thm_MohP3_FormalLocal_Pk_le_ker
public import Theorems.Thm_MohP3_FormalLocal_psi_hhS
public import Theorems.Thm_MohP3_FormalLocal_indepS

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open MvPowerSeries
open MohP3 MohP3.FormalLocal
variable (k : Type*) [Field k] [CharZero k]
namespace MohP3.FormalLocal
theorem _root_.solution (hgen : Generation k) : RingHom.ker (psi k) ≤ Pk k := by
  intro F hF
  obtain ⟨p, hp⟩ := hgen F
  have h1 : (∑ i, iotaS k (p i) * hhS k i) ∈ RingHom.ker (psi k) := by
    simpa using sub_mem hF (Pk_le_ker k hp)
  have h2 : ∑ i, exp8 k (p i) * vvS k i = 0 := by
    have h := RingHom.mem_ker.mp h1
    rw [map_sum] at h
    simpa [map_mul, psi_iotaS, psi_hhS] using h
  have h3 := indepS k p h2
  have hzero : (∑ i, iotaS k (p i) * hhS k i) = 0 :=
    Finset.sum_eq_zero fun i _ => by simp [h3 i]
  rwa [hzero, sub_zero] at hp
end MohP3.FormalLocal
