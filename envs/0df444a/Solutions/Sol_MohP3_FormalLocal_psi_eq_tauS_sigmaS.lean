-- Prove2me | solution 1 for MohP3.FormalLocal.psi_eq_tauS_sigmaS
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:35:49.920288+00:00
-- url     : https://prove2.me/submissions/351cf0db-52ff-459f-a564-7f04f087739f

module
public import Definitions.Def_MohP3_Generation
public import Definitions.Def_MohP3_Ara
public import Definitions.Def_MohP3_MvPowerSeriesAux
public import Definitions.Def_MohP3_HeightLocal
public import Theorems.Thm_MohP3_FormalLocal_subst_cc_bb

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open MvPowerSeries
open MohP3 MohP3.FormalLocal
variable (k : Type*) [Field k] [CharZero k]
omit [CharZero k]
namespace MohP3.FormalLocal
theorem _root_.solution (f : Sk k) : psi k f = tauS k (sigmaS k f) := by
  rw [psi, tauS, sigmaS, MvPowerSeries.coe_substAlgHom, MvPowerSeries.coe_substAlgHom,
    MvPowerSeries.coe_substAlgHom, MvPowerSeries.subst_comp_subst_apply
      (hasSubst_bb k) (hasSubst_cc k)]
  congr 1
  funext s
  exact (subst_cc_bb k s).symm
end MohP3.FormalLocal
