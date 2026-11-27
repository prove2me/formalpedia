-- Prove2me | solution 1 for MohP3.FormalLocal.Psurfk_le_Pk
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:39:02.134735+00:00
-- url     : https://prove2.me/submissions/333dd582-cc01-4961-a750-ac457789da04

module
public import Definitions.Def_MohP3_Generation
public import Definitions.Def_MohP3_Ara
public import Definitions.Def_MohP3_MvPowerSeriesAux
public import Definitions.Def_MohP3_HeightLocal
public import Theorems.Thm_MohP3_FormalLocal_psi_eq_tauS_sigmaS
public import Theorems.Thm_MohP3_FormalLocal_mem_Psurfk_iff
public import Theorems.Thm_MohP3_FormalLocal_ker_psi


set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open MvPowerSeries
open MohP3 MohP3.FormalLocal
variable (k : Type*) [Field k] [CharZero k]
namespace MohP3.FormalLocal
theorem _root_.solution : Psurfk k ≤ Pk k := by
  rw [← ker_psi]
  intro g hg
  rw [mem_Psurfk_iff] at hg
  rw [RingHom.mem_ker, psi_eq_tauS_sigmaS, hg, map_zero]
end MohP3.FormalLocal
