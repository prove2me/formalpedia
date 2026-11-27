-- Prove2me | solution 1 for MohP3.FormalLocal.f4S_notMem_Psurfk
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:34:33.137459+00:00
-- url     : https://prove2.me/submissions/cc5f853a-92e1-463f-aa82-ec08bad86a69

module
public import Definitions.Def_MohP3_Generation
public import Definitions.Def_MohP3_Ara
public import Definitions.Def_MohP3_MvPowerSeriesAux
public import Definitions.Def_MohP3_HeightLocal
public import Theorems.Thm_MohP3_FormalLocal_mem_Psurfk_iff
public import Theorems.Thm_MohP3_FormalLocal_chiS_X0
public import Theorems.Thm_MohP3_FormalLocal_chiS_X1
public import Theorems.Thm_MohP3_Wt_dd_apply_one
public import Theorems.Thm_MohP3_Wt_dd_apply_two
public import Theorems.Thm_MohP3_Wt_dd_apply_zero
public import Theorems.Thm_MohP3_Wt_wt_dd
attribute [local simp] MohP3.Wt.dd_apply_one
attribute [local simp] MohP3.Wt.dd_apply_two
attribute [local simp] MohP3.Wt.dd_apply_zero
attribute [local simp] MohP3.Wt.wt_dd


attribute [local simp] MohP3.FormalLocal.chiS_X0
attribute [local simp] MohP3.FormalLocal.chiS_X1

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open MvPowerSeries
open MohP3 MohP3.FormalLocal
variable (k : Type*) [Field k] [CharZero k]
omit [CharZero k]
namespace MohP3.FormalLocal
theorem _root_.solution : Gen.f4 (xs k) (ys k) (zs k) ∉ Psurfk k := by
  intro h
  rw [mem_Psurfk_iff] at h
  have h2 : chiS k (sigmaS k (Gen.f4 (xs k) (ys k) (zs k))) = 0 := by rw [h, map_zero]
  rw [Gen.f4] at h2
  simp only [map_sub, map_add, map_mul, map_pow, map_ofNat, sigmaS_xs, sigmaS_ys, sigmaS_zs,
    chiS_X0, chiS_X1] at h2
  have h3 : ((PowerSeries.X : PowerSeries k)^11 - PowerSeries.X^13 - PowerSeries.X^13
      - PowerSeries.X^40 + PowerSeries.X^15) = 0 := by
    rw [← h2]; ring
  have h4 := congrArg (PowerSeries.coeff 11) h3
  simp [PowerSeries.coeff_X_pow] at h4
end MohP3.FormalLocal
