-- Prove2me | solution 1 for ModularCurve.exists_conj_mem_GammaH_div
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/032e0d5f-1c11-572e-8bfa-44332182d4d1

import Mathlib
import Definitions.Def_ModularCurve_XH
import Definitions.Def_ModularCurve_XHDifferentialsModL
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_conj_mem_GammaH_div

set_option autoImplicit false

open ModularCurve
open scoped MatrixGroups

theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
    (γ : SL(2, ℤ)) (hγ : γ ∈ CohCarrier.GammaH M H) :
    ∃ γ₁ ∈ CohCarrier.GammaH (M / p) (infSubgroup p M H hpM),
      γ₁ 0 0 = γ 0 0 ∧ γ₁ 0 1 = (p : ℤ) * γ 0 1 ∧ (p : ℤ) * γ₁ 1 0 = γ 1 0 ∧ γ₁ 1 1 = γ 1 1 := by
  obtain ⟨hγ0, hd⟩ := CohCarrier.mem_GammaH_iff.mp hγ

  have hc : ((γ 1 0 : ℤ) : ZMod M) = 0 := (CongruenceSubgroup.Gamma0_mem).mp hγ0
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at hc
  obtain ⟨c', hc'⟩ : (p : ℤ) ∣ γ 1 0 := (Int.natCast_dvd_natCast.mpr hpM).trans hc
  have hMp : ((M / p : ℕ) : ℤ) ∣ c' := by
    have hpos : (p : ℤ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
    have : (M : ℤ) = (p : ℤ) * ((M / p : ℕ) : ℤ) := by exact_mod_cast (Nat.mul_div_cancel' hpM).symm
    rw [this, hc'] at hc
    exact (mul_dvd_mul_iff_left hpos).mp hc

  have hdet : γ 0 0 * γ 1 1 - ((p : ℤ) * γ 0 1) * c' = 1 := by
    have h := Matrix.SpecialLinearGroup.det_coe γ
    rw [Matrix.det_fin_two] at h
    rw [hc'] at h
    linarith [h]
  let A : Matrix (Fin 2) (Fin 2) ℤ := !![γ 0 0, (p : ℤ) * γ 0 1; c', γ 1 1]
  have hA : A.det = 1 := by rw [Matrix.det_fin_two_of]; exact hdet
  let g : SL(2, ℤ) := ⟨A, hA⟩
  refine ⟨g, ?_, rfl, rfl, ?_, rfl⟩
  ·
    have hA0 : g ∈ CongruenceSubgroup.Gamma0 (M / p) := by
      apply (CongruenceSubgroup.Gamma0_mem).mpr
      show ((c' : ℤ) : ZMod (M / p)) = 0
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
      exact hMp
    refine CohCarrier.mem_GammaH_iff.mpr ⟨hA0, ?_⟩
    have key : CohCarrier.gamma0Units (M / p) ⟨g, hA0⟩ =
        ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) (CohCarrier.gamma0Units M ⟨γ, hγ0⟩) := by
      apply Units.ext
      rw [CohCarrier.val_gamma0Units, ZMod.unitsMap_def, Units.coe_map, CohCarrier.val_gamma0Units]
      simp [CongruenceSubgroup.Gamma0Map, ZMod.castHom_apply, ZMod.cast_intCast (Nat.div_dvd_of_dvd hpM), g, A]
    rw [key]
    exact unitsMap_mem_infSubgroup p M H hpM hd
  · show (p : ℤ) * c' = γ 1 0
    rw [hc']

#print axioms solution

end S_ModularCurve_exists_conj_mem_GammaH_div
end P2MW
export P2MW.S_ModularCurve_exists_conj_mem_GammaH_div (solution)
