-- Prove2me | solution 1 for MohP3.FormalLocal.subst_cc_bb
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:33:24.549062+00:00
-- url     : https://prove2.me/submissions/ae4d9b8a-5f55-4d7a-9ea9-c1bc8f55e117

module
public import Definitions.Def_MohP3_Generation
public import Definitions.Def_MohP3_Ara
public import Definitions.Def_MohP3_MvPowerSeriesAux
public import Definitions.Def_MohP3_HeightLocal
public import Theorems.Thm_MohP3_Wt_dd_apply_one
public import Theorems.Thm_MohP3_Wt_dd_apply_two
public import Theorems.Thm_MohP3_Wt_dd_apply_zero
public import Theorems.Thm_MohP3_Wt_wt_dd
attribute [local simp] MohP3.Wt.dd_apply_one
attribute [local simp] MohP3.Wt.dd_apply_two
attribute [local simp] MohP3.Wt.dd_apply_zero
attribute [local simp] MohP3.Wt.wt_dd



set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open MvPowerSeries
open MohP3 MohP3.FormalLocal
variable (k : Type*) [Field k] [CharZero k]
omit [CharZero k]
namespace MohP3.FormalLocal
theorem _root_.solution (s : Fin 3) : MvPowerSeries.subst (cc k) (bb k s) = aa k s := by
  fin_cases s
  · rw [show ((bb k) ⟨0, by norm_num⟩) = (X 0 : MvPowerSeries (Fin 2) k) from by simp [bb],
      MvPowerSeries.subst_X (hasSubst_cc k)]
    simp [cc, aa]
  · rw [show ((bb k) ⟨1, by norm_num⟩) = (X 1 : MvPowerSeries (Fin 2) k)^4 from by simp [bb],
      ← MvPowerSeries.coe_substAlgHom (hasSubst_cc k), map_pow,
      MvPowerSeries.substAlgHom_X]
    simp [cc, aa, ← pow_mul]
  · rw [show ((bb k) ⟨2, by norm_num⟩) = (X 1 : MvPowerSeries (Fin 2) k)^5 from by simp [bb],
      ← MvPowerSeries.coe_substAlgHom (hasSubst_cc k), map_pow,
      MvPowerSeries.substAlgHom_X]
    simp [cc, aa, ← pow_mul]
end MohP3.FormalLocal
