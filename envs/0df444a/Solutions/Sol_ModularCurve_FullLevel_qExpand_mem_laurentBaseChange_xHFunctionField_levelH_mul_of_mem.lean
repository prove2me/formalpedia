-- Prove2me | solution 1 for ModularCurve.FullLevel.qExpand_mem_laurentBaseChange_xHFunctionField_levelH_mul_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/9629dbb0-c5fb-5d68-b4f0-dc7b81bd77b1

import Mathlib
import Definitions.Def_ModularCurve_XH
import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_ModularCurve_XHDifferentialsModL
import Theorems.Thm_ModularCurve_qExpand_mem_xHFunctionField_of_mem_div
import Theorems.Thm_ModularCurve_qExpand_mem_laurentBaseChange
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_qExpand_mem_laurentBaseChange_xHFunctionField_levelH_mul_of_mem

set_option autoImplicit false

open scoped MatrixGroups

namespace A0flat_node14

open ModularCurve ModularCurve.FullLevel CongruenceSubgroup

theorem intCast_zmod_eq_zero_of_dvd {m n : ℕ} (h : n ∣ m) (c : ℤ) (hc : ((c : ZMod m)) = 0) :
    ((c : ZMod n)) = 0 := by
  have h1 := congrArg (ZMod.castHom h (ZMod n)) hc
  rwa [map_intCast, map_zero] at h1

theorem val_unitsMap_intCast {m n : ℕ} (h : n ∣ m) (d : (ZMod m)ˣ) (z : ℤ) (hz : ((z : ZMod m)) = (d : ZMod m)) :
    ((ZMod.unitsMap h d : (ZMod n)ˣ) : ZMod n) = (z : ZMod n) := by
  rw [ZMod.unitsMap_def, Units.coe_map, ← hz]
  show ZMod.castHom h (ZMod n) (z : ZMod m) = (z : ZMod n)
  rw [map_intCast]

theorem unitsMap_gamma0Units_eq_one_iff {N n : ℕ} (h : n ∣ N) (A : SL(2, ℤ)) (hA : A ∈ Gamma0 N) :
    ZMod.unitsMap h (CohCarrier.gamma0Units N ⟨A, hA⟩) = 1 ↔
      ((((A : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℤ) : ZMod n) = 1 := by
  rw [← Units.val_eq_one, ZMod.unitsMap_def, Units.coe_map, CohCarrier.val_gamma0Units]
  show ZMod.castHom h (ZMod n) (((((A : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℤ) : ZMod N)) = 1 ↔ _
  rw [map_intCast]

theorem gammaH_inf_le (q M' ℓ' : ℕ) [Fact q.Prime] [NeZero M'] [Fact ℓ'.Prime]
    (hqM : q ∣ (q * ℓ') ^ 2 * M') :
    CohCarrier.GammaH ((q * ℓ') ^ 2 * M' / q) (infSubgroup q ((q * ℓ') ^ 2 * M') (levelH (q * ℓ') M') hqM) ≤
      CohCarrier.GammaH (ℓ' ^ 2 * M') (levelH ℓ' M') := by
  have hq0 : 0 < q := (Fact.out : q.Prime).pos
  have hdiv : (q * ℓ') ^ 2 * M' / q = q * (ℓ' ^ 2 * M') :=
    Nat.div_eq_of_eq_mul_left hq0 (by ring)
  haveI : NeZero (ℓ' ^ 2 * M') := ⟨mul_ne_zero (pow_ne_zero _ (Fact.out : ℓ'.Prime).ne_zero) (NeZero.ne M')⟩
  intro A hA
  rw [CohCarrier.mem_GammaH_iff] at hA ⊢
  obtain ⟨hA0, hAH⟩ := hA
  rw [mem_infSubgroup_iff] at hAH
  obtain ⟨d, hd, hde⟩ := hAH
  rw [mem_levelH_iff] at hd

  have hA0' : A ∈ Gamma0 (ℓ' ^ 2 * M') := by
    rw [Gamma0_mem] at hA0 ⊢
    exact intCast_zmod_eq_zero_of_dvd (by rw [hdiv]; exact Dvd.intro_left _ rfl) _ hA0
  refine ⟨hA0', ?_⟩
  rw [mem_levelH_iff]

  obtain ⟨z, hz⟩ := ZMod.intCast_surjective (d : ZMod ((q * ℓ') ^ 2 * M'))
  have h1 : ((z : ZMod ((q * ℓ') ^ 2 * M' / q))) = ((((A : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℤ) : ZMod _) := by
    rw [← val_unitsMap_intCast (Nat.div_dvd_of_dvd hqM) d z hz, hde, CohCarrier.val_gamma0Units]
    rfl
  have h2 : ((z : ZMod (q * ℓ'))) = 1 := by
    rw [← val_unitsMap_intCast (dvd_sq_mul (q * ℓ') M') d z hz, hd, Units.val_one]

  have hℓM : ℓ' ∣ (q * ℓ') ^ 2 * M' / q := by rw [hdiv]; exact Dvd.dvd.mul_left (Dvd.intro (ℓ' * M') (by ring)) q
  have h1' := congrArg (ZMod.castHom hℓM (ZMod ℓ')) h1
  have h2' := congrArg (ZMod.castHom (dvd_mul_left ℓ' q) (ZMod ℓ')) h2
  rw [map_intCast, map_intCast] at h1'
  rw [map_intCast, map_one] at h2'
  rw [unitsMap_gamma0Units_eq_one_iff]
  exact h1'.symm.trans h2'

end A0flat_node14

theorem solution
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (ℓ' : ℕ) [Fact ℓ'.Prime]
    (L : Type) [Field L] [CharZero L]
    (x : LaurentSeries L)
    (hx : x ∈ ModularCurve.laurentBaseChange L
      (ModularCurve.xHFunctionField (ℓ' ^ 2 * M') (ModularCurve.FullLevel.levelH ℓ' M'))) :
    ModularCurve.qExpand L q x ∈
      ModularCurve.laurentBaseChange L
        (ModularCurve.xHFunctionField ((q * ℓ') ^ 2 * M') (ModularCurve.FullLevel.levelH (q * ℓ') M')) := by
  classical
  have hqM : q ∣ (q * ℓ') ^ 2 * M' := Dvd.intro (q * ℓ' ^ 2 * M') (by ring)

  have hrat : ∀ y : LaurentSeries ℚ,
      y ∈ ModularCurve.xHFunctionField (ℓ' ^ 2 * M') (ModularCurve.FullLevel.levelH ℓ' M') →
      ModularCurve.qExpand ℚ q y ∈
        ModularCurve.xHFunctionField ((q * ℓ') ^ 2 * M') (ModularCurve.FullLevel.levelH (q * ℓ') M') := by
    intro y hy
    have hy' : y ∈ ModularCurve.xHFunctionField ((q * ℓ') ^ 2 * M' / q)
        (ModularCurve.infSubgroup q ((q * ℓ') ^ 2 * M') (ModularCurve.FullLevel.levelH (q * ℓ') M') hqM) := by
      have hle : ModularCurve.xHFunctionField (ℓ' ^ 2 * M') (ModularCurve.FullLevel.levelH ℓ' M') ≤
          ModularCurve.xHFunctionField ((q * ℓ') ^ 2 * M' / q)
            (ModularCurve.infSubgroup q ((q * ℓ') ^ 2 * M') (ModularCurve.FullLevel.levelH (q * ℓ') M') hqM) := by
        unfold ModularCurve.xHFunctionField ModularCurve.xHFunctionFieldC
        exact ModularCurve.qExpFunctionFieldC_mono ℚ (A0flat_node14.gammaH_inf_le q M' ℓ' hqM)
      exact hle hy
    exact ModularCurve.qExpand_mem_xHFunctionField_of_mem_div q ((q * ℓ') ^ 2 * M')
      (ModularCurve.FullLevel.levelH (q * ℓ') M') hqM hy'

  exact ModularCurve.qExpand_mem_laurentBaseChange q hrat hx

end S_ModularCurve_FullLevel_qExpand_mem_laurentBaseChange_xHFunctionField_levelH_mul_of_mem
end P2MW
export P2MW.S_ModularCurve_FullLevel_qExpand_mem_laurentBaseChange_xHFunctionField_levelH_mul_of_mem (solution)
