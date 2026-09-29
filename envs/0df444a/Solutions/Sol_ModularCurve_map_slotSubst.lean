-- Prove2me | solution 1 for ModularCurve.map_slotSubst
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/96562a66-5ac0-5ac6-a362-bf2f61881457

import Mathlib
import Definitions.Def_ModularCurve_TateSlots
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_map_slotSubst

set_option autoImplicit false

open ModularCurve

namespace SlotSubstMapAux

theorem hasSubst_slotFamily {K : Type*} [CommRing K] (p : ℕ) (c : Kˣ) (j : ℕ) (hj : 0 < j) (hjp : j < p) :
    MvPowerSeries.HasSubst (slotFamily K p c j) :=
  MvPowerSeries.hasSubst_of_constantCoeff_zero (fun i => by
    fin_cases i
    · show PowerSeries.constantCoeff (PowerSeries.C (c : K) * PowerSeries.X ^ j) = 0
      simp [hj.ne']
    · show PowerSeries.constantCoeff (PowerSeries.C ((c⁻¹ : Kˣ) : K) * PowerSeries.X ^ (p - j)) = 0
      simp [(Nat.sub_pos_of_lt hjp).ne'])

theorem slotSubst_eq_subst_map {K : Type*} [CommRing K] (p : ℕ) (c : Kˣ) (j : ℕ)
    (h : MvPowerSeries.HasSubst (slotFamily K p c j)) (f : MvPowerSeries (Fin 2) ℤ) :
    slotSubst K p c j f =
      MvPowerSeries.subst (slotFamily K p c j) (MvPowerSeries.map (algebraMap ℤ K) f) := by
  rw [MvPowerSeries.map_algebraMap_eq_subst_X,
    MvPowerSeries.subst_comp_subst_apply MvPowerSeries.HasSubst.X h, slotSubst]
  congr 1
  funext s
  rw [MvPowerSeries.subst_X h]

theorem map_slotFamily {A B : Type*} [CommRing A] [CommRing B] (g : A →+* B) (p : ℕ) (c : Aˣ) (j : ℕ)
    (i : Fin 2) : PowerSeries.map g (slotFamily A p c j i) = slotFamily B p (Units.map (g : A →* B) c) j i := by
  fin_cases i <;> simp [slotFamily, map_mul, map_pow, PowerSeries.map_C, PowerSeries.map_X, Units.coe_map,
    Units.coe_map_inv]

end SlotSubstMapAux

open SlotSubstMapAux in
theorem solution
    {A B : Type} [CommRing A] [CommRing B] (g : A →+* B) (p : ℕ) (c : Aˣ) (j : ℕ) (hj : 0 < j) (hjp : j < p)
    (f : MvPowerSeries (Fin 2) ℤ) :
    (ModularCurve.slotSubst A p c j f).map g = ModularCurve.slotSubst B p (Units.map (g : A →* B) c) j f := by
  have hA := hasSubst_slotFamily p c j hj hjp
  have hB := hasSubst_slotFamily p (Units.map (g : A →* B) c) j hj hjp
  rw [slotSubst_eq_subst_map _ _ _ hA, slotSubst_eq_subst_map _ _ _ hB, PowerSeries.map,
    MvPowerSeries.map_subst hA, MvPowerSeries.map_map]
  have hcomp : g.comp (algebraMap ℤ A) = algebraMap ℤ B := RingHom.ext_int _ _
  rw [hcomp]
  congr 1
  funext i
  exact map_slotFamily g p c j i

#print axioms solution

end S_ModularCurve_map_slotSubst
end P2MW
export P2MW.S_ModularCurve_map_slotSubst (solution)
