-- Prove2me | solution 1 for MohP3.FormalLocal.psi_iotaS
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:17:44.849046+00:00
-- url     : https://prove2.me/submissions/aec4137d-155c-405d-9425-e8682c72461e

module
public import Definitions.Def_MohP3_Generic
public import Definitions.Def_MohP3_FormalLocal

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open MvPowerSeries
open MohP3 MohP3.FormalLocal
variable (k : Type*) [Field k] [CharZero k]
omit [CharZero k]
namespace MohP3.FormalLocal
theorem _root_.solution (q : PowerSeries k) : psi k (iotaS k q) = exp8 k q := by
  rw [exp8, PowerSeries.expand_apply, PowerSeries.subst, psi, iotaS, PowerSeries.substAlgHom,
    MvPowerSeries.coe_substAlgHom, MvPowerSeries.coe_substAlgHom,
    MvPowerSeries.subst_comp_subst_apply (hasSubst_ys k).const (hasSubst_aa k)]
  congr 1
  funext _
  have := psi_ys k
  rwa [psi, MvPowerSeries.coe_substAlgHom] at this
end MohP3.FormalLocal
