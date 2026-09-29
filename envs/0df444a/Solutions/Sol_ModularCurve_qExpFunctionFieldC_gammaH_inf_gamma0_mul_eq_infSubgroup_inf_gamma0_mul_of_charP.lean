-- Prove2me | solution 1 for ModularCurve.qExpFunctionFieldC_gammaH_inf_gamma0_mul_eq_infSubgroup_inf_gamma0_mul_of_charP
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/51cc6bd4-e52f-5447-a40d-28d3e0d4c01b

import Mathlib
import Definitions.Def_ModularCurve_XHDifferentialsModL
import Theorems.Thm_ModularCurve_qExpFunctionFieldC_gammaH_le_qExpFunctionFieldC_gammaH_infSubgroup
import Theorems.Thm_CohCarrier_gammaH_inf_gamma0_mul_eq_gammaH_comap_unitsMap
import Theorems.Thm_ModularCurve_GammaH_le_GammaH_div_infSubgroup
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_qExpFunctionFieldC_gammaH_inf_gamma0_mul_eq_infSubgroup_inf_gamma0_mul_of_charP
p2m_attr_erase "simp" "ModularCurve.baseAut_x1ArithFrobC_apply ModularCurve.coe_qExpCoeffRingAut_apply ModularCurve.qExpCoeffSemilinearAutHom_apply ModularCurve.baseAut_x1x0ArithFrobC_apply ModularCurve.baseAut_qExpArithFrobC_apply ModularCurve.baseAut_qExpCoeffSemilinearAut ModularCurve.toRingAut_qExpCoeffSemilinearAut ModularForm.coe_atkinLehnerLin_apply CuspForm.coe_atkinLehnerLin_apply CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply"

set_option autoImplicit false

open scoped MatrixGroups
open CongruenceSubgroup

namespace ModularCurve
p2m_export "ModularCurve" "infSubgroup neZero_div qExpFunctionFieldC qExpFunctionFieldC_mono qExpFunctionFieldC_gammaH_le_qExpFunctionFieldC_gammaH_infSubgroup GammaH_le_GammaH_div_infSubgroup"
p2m_open "ModularCurve"

namespace DegRedL

theorem unitsMap_square {a b c d : ℕ} (hba : b ∣ a) (hcb : c ∣ b) (hda : d ∣ a) (hcd : c ∣ d) :
    (ZMod.unitsMap hcb).comp (ZMod.unitsMap hba) = (ZMod.unitsMap hcd).comp (ZMod.unitsMap hda) := by
  rw [ZMod.unitsMap_comp, ZMod.unitsMap_comp]

theorem gammaH_comap_congr {N L₁ L₂ : ℕ} (h : L₁ = L₂) (h₁ : N ∣ L₁) (h₂ : N ∣ L₂)
    (H' : Subgroup (ZMod N)ˣ) :
    CohCarrier.GammaH L₁ (H'.comap (ZMod.unitsMap h₁)) =
      CohCarrier.GammaH L₂ (H'.comap (ZMod.unitsMap h₂)) := by
  subst h
  rfl

theorem qExpFunctionFieldC_gammaH_eq_infSubgroup
    (K : Type*) [Field K] (p : ℕ) [Fact p.Prime] [CharP K p]
    (M : ℕ) [NeZero M] (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M) (H : Subgroup (ZMod M)ˣ)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) :
    qExpFunctionFieldC K (CohCarrier.GammaH M H) =
      qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM)) :=
  le_antisymm
    (ModularCurve.qExpFunctionFieldC_gammaH_le_qExpFunctionFieldC_gammaH_infSubgroup p M hpM hpM2 H hHp K)
    (qExpFunctionFieldC_mono K (ModularCurve.GammaH_le_GammaH_div_infSubgroup p M H hpM))

theorem infSubgroup_mul_comap_eq
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hpM : p ∣ M) (H : Subgroup (ZMod M)ˣ)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (ℓ : ℕ) [NeZero ℓ] (hpMℓ : p ∣ M * ℓ) (h₃ : M / p ∣ M * ℓ / p) :
    infSubgroup p (M * ℓ) (H.comap (ZMod.unitsMap (dvd_mul_right M ℓ))) hpMℓ =
      (infSubgroup p M H hpM).comap (ZMod.unitsMap h₃) := by
  haveI : NeZero (M * ℓ) := ⟨Nat.mul_ne_zero (NeZero.ne M) (NeZero.ne ℓ)⟩
  set u₁ : (ZMod (M * ℓ))ˣ →* (ZMod M)ˣ := ZMod.unitsMap (dvd_mul_right M ℓ) with hu₁
  set u₂ : (ZMod (M * ℓ))ˣ →* (ZMod (M * ℓ / p))ˣ := ZMod.unitsMap (Nat.div_dvd_of_dvd hpMℓ) with hu₂
  set u₃ : (ZMod (M * ℓ / p))ˣ →* (ZMod (M / p))ˣ := ZMod.unitsMap h₃ with hu₃
  set u₄ : (ZMod M)ˣ →* (ZMod (M / p))ˣ := ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) with hu₄
  have hsq : u₄.comp u₁ = u₃.comp u₂ := by
    rw [hu₁, hu₂, hu₃, hu₄]
    exact unitsMap_square _ _ _ _
  have hH : H = (H.map u₄).comap u₄ := by
    rw [Subgroup.comap_map_eq]
    refine le_antisymm le_sup_left (sup_le le_rfl ?_)
    intro u hu
    exact hHp u hu
  show (H.comap u₁).map u₂ = (H.map u₄).comap u₃
  conv_lhs => rw [hH]
  rw [Subgroup.comap_comap, hsq, ← Subgroup.comap_comap,
    Subgroup.map_comap_eq_self_of_surjective (ZMod.unitsMap_surjective _)]

theorem qExpFunctionFieldC_gammaH_inf_gamma0_mul_eq_infSubgroup
    (K : Type*) [Field K] (p : ℕ) [Fact p.Prime] [CharP K p]
    (M : ℕ) [NeZero M] (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M) (H : Subgroup (ZMod M)ˣ)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓp : ℓ ≠ p) :
    haveI : NeZero (M / p) := neZero_div p M hpM
    qExpFunctionFieldC K (CohCarrier.GammaH M H ⊓ Gamma0 (M * ℓ)) =
      qExpFunctionFieldC K
        (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM) ⊓ Gamma0 (M / p * ℓ)) := by
  haveI : NeZero (M / p) := neZero_div p M hpM
  haveI : NeZero (M * ℓ) := ⟨Nat.mul_ne_zero (NeZero.ne M) (NeZero.ne ℓ)⟩
  have hp : p.Prime := Fact.out
  have hℓ : ℓ.Prime := Fact.out
  have hpMℓ : p ∣ M * ℓ := dvd_mul_of_dvd_left hpM ℓ
  have hpℓ : p.Coprime ℓ := (Nat.coprime_primes hp hℓ).mpr (Ne.symm hℓp)
  have hpMℓ2 : ¬ p ^ 2 ∣ M * ℓ := fun h =>
    hpM2 ((Nat.Coprime.pow_left 2 hpℓ).dvd_of_dvd_mul_right h)
  have hlev : M / p * ℓ = M * ℓ / p := Nat.div_mul_right_comm hpM ℓ
  have h₃ : M / p ∣ M * ℓ / p := Dvd.intro ℓ hlev
  have hHtp : ∀ u : (ZMod (M * ℓ))ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpMℓ) u = 1 →
      u ∈ H.comap (ZMod.unitsMap (dvd_mul_right M ℓ)) := by
    intro u hu
    rw [Subgroup.mem_comap]
    apply hHp
    have hsq := congrArg (fun f => f u)
      (unitsMap_square (dvd_mul_right M ℓ) (Nat.div_dvd_of_dvd hpM) (Nat.div_dvd_of_dvd hpMℓ) h₃)
    simp only [MonoidHom.comp_apply] at hsq
    rw [hsq, hu, map_one]
  calc qExpFunctionFieldC K (CohCarrier.GammaH M H ⊓ Gamma0 (M * ℓ))
      = qExpFunctionFieldC K
          (CohCarrier.GammaH (M * ℓ) (H.comap (ZMod.unitsMap (dvd_mul_right M ℓ)))) := by
        rw [CohCarrier.gammaH_inf_gamma0_mul_eq_gammaH_comap_unitsMap]
    _ = qExpFunctionFieldC K (CohCarrier.GammaH (M * ℓ / p)
          (infSubgroup p (M * ℓ) (H.comap (ZMod.unitsMap (dvd_mul_right M ℓ))) hpMℓ)) :=
        qExpFunctionFieldC_gammaH_eq_infSubgroup K p (M * ℓ) hpMℓ hpMℓ2 _ hHtp
    _ = qExpFunctionFieldC K (CohCarrier.GammaH (M * ℓ / p)
          ((infSubgroup p M H hpM).comap (ZMod.unitsMap h₃))) := by
        rw [infSubgroup_mul_comap_eq p M hpM H hHp ℓ hpMℓ h₃]
    _ = qExpFunctionFieldC K (CohCarrier.GammaH (M / p * ℓ)
          ((infSubgroup p M H hpM).comap (ZMod.unitsMap (dvd_mul_right (M / p) ℓ)))) := by
        rw [gammaH_comap_congr hlev.symm h₃ (dvd_mul_right (M / p) ℓ)]
    _ = qExpFunctionFieldC K
          (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM) ⊓ Gamma0 (M / p * ℓ)) := by
        rw [CohCarrier.gammaH_inf_gamma0_mul_eq_gammaH_comap_unitsMap]

end DegRedL

end ModularCurve

theorem solution
    (K : Type*) [Field K] (p : ℕ) [Fact p.Prime] [CharP K p]
    (M : ℕ) [NeZero M] (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M) (H : Subgroup (ZMod M)ˣ)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓp : ℓ ≠ p) :
    ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH M H ⊓ CongruenceSubgroup.Gamma0 (M * ℓ)) =
      ModularCurve.qExpFunctionFieldC K
        (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM) ⊓
          CongruenceSubgroup.Gamma0 (M / p * ℓ)) := by
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  exact ModularCurve.DegRedL.qExpFunctionFieldC_gammaH_inf_gamma0_mul_eq_infSubgroup K p M hpM hpM2 H hHp ℓ hℓp

end S_ModularCurve_qExpFunctionFieldC_gammaH_inf_gamma0_mul_eq_infSubgroup_inf_gamma0_mul_of_charP
end P2MW
export P2MW.S_ModularCurve_qExpFunctionFieldC_gammaH_inf_gamma0_mul_eq_infSubgroup_inf_gamma0_mul_of_charP (solution)
