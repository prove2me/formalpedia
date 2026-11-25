-- Prove2me | solution 1 for GroundTheory.Global.cycHerbrand_prod_eq_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:08:44.676941+00:00
-- url     : https://prove2.me/submissions/306e8d74-a579-4ffa-9980-02de12336adb

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_CycTateNegOneOrbitEquivSymmMk
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_SIdeleHerbrand_Product
import Theorems.Thm_GroundTheory_Global_cycHerbrand_eq
import Theorems.Thm_GroundTheory_Global_piRep_apply
import Theorems.Thm_GroundTheory_GroupCoh_restrictEnd_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
attribute [local simp] GroundTheory.Global.piRep_apply
attribute [local simp] GroundTheory.GroupCoh.restrictEnd_apply



set_option autoImplicit false
open GroundTheory GroundTheory.Global
open GroundTheory.GroupCoh
noncomputable section
variable {k G V W : Type*} [CommRing k] [Group G] [AddCommGroup V] [Module k V] [AddCommGroup W]
  [Module k W]
variable [Fintype G]
namespace GroundTheory.Global
theorem _root_.solution (ρ : Representation k G V) (ρ' : Representation k G W) (σ : G) :
    cycHerbrand (ρ.prod ρ') σ = cycHerbrand ρ σ * cycHerbrand ρ' σ := by
  simp only [cycHerbrand_eq]
  rw [Nat.card_congr (cycTateZeroProdEquiv ρ ρ' σ).toEquiv,
    Nat.card_congr (cycTateNegOneProdEquiv ρ ρ' σ).toEquiv, Nat.card_prod, Nat.card_prod,
    Nat.cast_mul, Nat.cast_mul, mul_div_mul_comm]
end GroundTheory.Global
