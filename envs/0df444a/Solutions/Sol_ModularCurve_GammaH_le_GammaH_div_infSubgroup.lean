-- Prove2me | solution 1 for ModularCurve.GammaH_le_GammaH_div_infSubgroup
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/ad9150ae-48ab-527c-97f9-5f7a0af8fc30

import Mathlib
import Definitions.Def_ModularCurve_XH
import Definitions.Def_ModularCurve_XHDifferentialsModL
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_GammaH_le_GammaH_div_infSubgroup

set_option autoImplicit false

open ModularCurve
open scoped MatrixGroups

theorem Gamma0_le_of_dvd' (M : ℕ) {N : ℕ} (h : N ∣ M) : CongruenceSubgroup.Gamma0 M ≤ CongruenceSubgroup.Gamma0 N := by
  intro A hA
  rw [CongruenceSubgroup.Gamma0_mem] at hA ⊢
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at hA ⊢
  exact (Int.natCast_dvd_natCast.mpr h).trans hA

theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) :
    CohCarrier.GammaH M H ≤ CohCarrier.GammaH (M / p) (infSubgroup p M H hpM) := by
  intro A hA
  obtain ⟨hA0, hd⟩ := CohCarrier.mem_GammaH_iff.mp hA
  have hA0' : A ∈ CongruenceSubgroup.Gamma0 (M / p) := Gamma0_le_of_dvd' M (Nat.div_dvd_of_dvd hpM) hA0
  refine CohCarrier.mem_GammaH_iff.mpr ⟨hA0', ?_⟩
  have key : CohCarrier.gamma0Units (M / p) ⟨A, hA0'⟩ =
      ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) (CohCarrier.gamma0Units M ⟨A, hA0⟩) := by
    apply Units.ext
    rw [CohCarrier.val_gamma0Units, ZMod.unitsMap_def, Units.coe_map, CohCarrier.val_gamma0Units]
    simp [CongruenceSubgroup.Gamma0Map, ZMod.castHom_apply, ZMod.cast_intCast (Nat.div_dvd_of_dvd hpM)]
  rw [key]
  exact unitsMap_mem_infSubgroup p M H hpM hd

#print axioms solution

end S_ModularCurve_GammaH_le_GammaH_div_infSubgroup
end P2MW
export P2MW.S_ModularCurve_GammaH_le_GammaH_div_infSubgroup (solution)
