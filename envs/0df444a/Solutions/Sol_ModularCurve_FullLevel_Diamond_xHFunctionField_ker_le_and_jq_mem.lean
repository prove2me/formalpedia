-- Prove2me | solution 1 for ModularCurve.FullLevel.Diamond.xHFunctionField_ker_le_and_jq_mem
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.339302+00:00
-- url     : https://prove2.me/submissions/7535cee7-396d-5485-bca7-c06d30b7d75b

import Mathlib
import Definitions.Def_ModularCurve_XH
import Definitions.Def_ModularCurve_FullLevelJacobian
import Theorems.Thm_ModularCurve_jqModC_mem_intFormRatiosC
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_Diamond_xHFunctionField_ker_le_and_jq_mem

set_option autoImplicit false

namespace InclH1Aux

open CongruenceSubgroup ModularCurve ModularCurve.FullLevel
open scoped MatrixGroups

theorem intCast_zmod_eq_one_of_dvd {m n : ℕ} (h : n ∣ m) (d : ℤ) (hd : ((d : ZMod m)) = 1) :
    ((d : ZMod n)) = 1 := by
  have h1 := congrArg (ZMod.castHom h (ZMod n)) hd
  rwa [map_intCast, map_one] at h1

theorem intCast_zmod_eq_zero_of_dvd {m n : ℕ} (h : n ∣ m) (c : ℤ) (hc : ((c : ZMod m)) = 0) :
    ((c : ZMod n)) = 0 := by
  have h1 := congrArg (ZMod.castHom h (ZMod n)) hc
  rwa [map_intCast, map_zero] at h1

theorem unitsMap_gamma0Units_eq_one_iff {N n : ℕ} (h : n ∣ N) (A : SL(2, ℤ)) (hA : A ∈ Gamma0 N) :
    ZMod.unitsMap h (CohCarrier.gamma0Units N ⟨A, hA⟩) = 1 ↔
      ((((A : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℤ) : ZMod n) = 1 := by
  rw [← Units.val_eq_one, ZMod.unitsMap_def, Units.coe_map, CohCarrier.val_gamma0Units]
  show ZMod.castHom h (ZMod n) (((((A : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℤ) : ZMod N)) = 1 ↔ _
  rw [map_intCast]

theorem gammaH_H1_le (q M' ℓg : ℕ) (hℓgM' : ℓg ∣ M')
    (H₁ : Subgroup (ZMod (q ^ 2 * M'))ˣ)
    (hH₁ : H₁ = levelH q M' ⊓ (ZMod.unitsMap (Dvd.dvd.mul_left hℓgM' (q ^ 2))).ker) :
    CohCarrier.GammaH (q ^ 2 * M') H₁ ≤ CohCarrier.GammaH M' (ZMod.unitsMap hℓgM').ker := by
  intro A hA
  rw [CohCarrier.mem_GammaH_iff] at hA ⊢
  obtain ⟨hA0, hAH⟩ := hA
  rw [hH₁, Subgroup.mem_inf, MonoidHom.mem_ker, unitsMap_gamma0Units_eq_one_iff] at hAH
  have hdvd : M' ∣ q ^ 2 * M' := dvd_mul_left _ _
  have hA0' : A ∈ Gamma0 M' := by
    rw [Gamma0_mem] at hA0 ⊢
    exact intCast_zmod_eq_zero_of_dvd hdvd _ hA0
  refine ⟨hA0', ?_⟩
  rw [MonoidHom.mem_ker, unitsMap_gamma0Units_eq_one_iff]
  exact hAH.2

end InclH1Aux

theorem solution
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (ℓg : ℕ) (hℓg : ℓg.Prime) (hℓgM' : ℓg ∣ M')
    (H₁ : Subgroup (ZMod (q ^ 2 * M'))ˣ)
    (hH₁ : H₁ = ModularCurve.FullLevel.levelH q M' ⊓ (ZMod.unitsMap (Dvd.dvd.mul_left hℓgM' (q ^ 2))).ker) :
    ModularCurve.xHFunctionField M' (ZMod.unitsMap hℓgM').ker ≤ ModularCurve.xHFunctionField (q ^ 2 * M') H₁ ∧
      ModularCurve.jq ∈ ModularCurve.xHFunctionField M' (ZMod.unitsMap hℓgM').ker := by
  unfold ModularCurve.xHFunctionField ModularCurve.xHFunctionFieldC
  exact ⟨ModularCurve.qExpFunctionFieldC_mono ℚ (InclH1Aux.gammaH_H1_le q M' ℓg hℓgM' H₁ hH₁),
    ModularCurve.intFormRatiosC_subset ℚ _ (ModularCurve.jqModC_mem_intFormRatiosC ℚ _)⟩

end S_ModularCurve_FullLevel_Diamond_xHFunctionField_ker_le_and_jq_mem
end P2MW
export P2MW.S_ModularCurve_FullLevel_Diamond_xHFunctionField_ker_le_and_jq_mem (solution)
