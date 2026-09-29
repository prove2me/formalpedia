-- Prove2me | solution 1 for ModularCurve.FullLevel.exists_fieldBar_mul_intSeriesC_eq_and_reduction_eisensteinRatio
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.339302+00:00
-- url     : https://prove2.me/submissions/69263ede-d452-5067-a79f-eabf581acc6e

import Definitions.Def_ModularCurve_FullLevelJacobian
import Theorems.Thm_ModularForm_exists_isIntegralQExp_gamma1_weight_add_one_map_zmod_eq
import Theorems.Thm_ModularCurve_qExpansion_discriminant_eq_map_X_mul_dedekindEtaUnit
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_exists_fieldBar_mul_intSeriesC_eq_and_reduction_eisensteinRatio

set_option autoImplicit false

p2m_open "ModularCurve P2MW.S_ModularCurve_FullLevel_exists_fieldBar_mul_intSeriesC_eq_and_reduction_eisensteinRatio.ModularCurve ModularCurve.FullLevel P2MW.S_ModularCurve_FullLevel_exists_fieldBar_mul_intSeriesC_eq_and_reduction_eisensteinRatio.ModularCurve.FullLevel CongruenceSubgroup UpperHalfPlane"
open scoped MatrixGroups ArithmeticFunction.sigma ModularForm

noncomputable section

namespace ModularCurve
p2m_export "ModularCurve" "restrictForm coe_restrictForm IsIntegralQExp isIntegralQExp_iff intSeriesC intSeriesC_mul div_mem_qExpFunctionFieldC dedekindEtaUnit constantCoeff_dedekindEtaUnit ofPowerSeries_coeff_of_neg coeffMap_coeff coeffEmb coeffEmb_mem_laurentBaseChange qExpansion_discriminant_eq_map_X_mul_dedekindEtaUnit"
namespace FullLevel
p2m_export "ModularCurve.FullLevel" "dvd_sq_mul levelH mem_levelH_iff fieldBar"
namespace HasseLift
p2m_open "ModularCurve.FullLevel ModularCurve"

private theorem gammaH_levelH_le_Gamma1 (q M' : ℕ) [Fact q.Prime] :
    CohCarrier.GammaH (q ^ 2 * M') (levelH q M') ≤ Gamma1 q := by
  intro γ hγ
  obtain ⟨h0, hH⟩ := CohCarrier.mem_GammaH_iff.mp hγ
  rw [mem_levelH_iff] at hH
  rw [Gamma0_mem] at h0
  have hdvd : q ∣ q ^ 2 * M' := dvd_sq_mul q M'

  have hd : (((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℤ) : ZMod q) = 1 := by
    have h1 := congrArg (fun u : (ZMod q)ˣ => (u : ZMod q)) hH
    simp only [ZMod.unitsMap, Units.coe_map, MonoidHom.coe_coe, CohCarrier.val_gamma0Units,
      Gamma0Map, Units.val_one] at h1
    simpa [ZMod.castHom_apply, ZMod.cast_intCast hdvd] using h1

  have hc : (((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℤ) : ZMod q) = 0 := by
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h0 ⊢
    exact (Int.natCast_dvd_natCast.mpr hdvd).trans h0

  have ha : (((γ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ℤ) : ZMod q) = 1 := by
    have hdet := Matrix.SpecialLinearGroup.det_coe γ
    rw [Matrix.det_fin_two] at hdet
    have := congrArg (fun z : ℤ => (z : ZMod q)) hdet
    simp only [Int.cast_sub, Int.cast_mul, Int.cast_one] at this
    rw [hd, hc, mul_one, mul_zero, sub_zero] at this
    exact this
  exact (Gamma1_mem q γ).mpr ⟨ha, hd, hc⟩

private theorem gammaH_levelH_le_Gamma1_GL (q M' : ℕ) [Fact q.Prime] :
    ((CohCarrier.GammaH (q ^ 2 * M') (levelH q M') : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) ≤
      ((Gamma1 q : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) :=
  Subgroup.map_mono (gammaH_levelH_le_Gamma1 q M')

private def restrictSL {k : ℤ} (F : ModularForm 𝒮ℒ k) (Γ : Subgroup SL(2, ℤ)) :
    ModularForm ((Γ : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) k where
  toFun := ⇑F
  slash_action_eq' A hA := SlashInvariantFormClass.slash_action_eq F A (Subgroup.map_le_range _ _ hA)
  holo' := ModularFormClass.holo F
  bdd_at_cusps' hc := ModularFormClass.bdd_at_cusps F (hc.mono (Subgroup.map_le_range _ _))

@[scoped simp] private theorem coe_restrictSL {k : ℤ} (F : ModularForm 𝒮ℒ k) (Γ : Subgroup SL(2, ℤ)) :
    (⇑(restrictSL F Γ) : ℍ → ℂ) = ⇑F := rfl

private def ofCuspSL {k : ℤ} (F : CuspForm 𝒮ℒ k) : ModularForm 𝒮ℒ k where
  toFun := ⇑F
  slash_action_eq' := fun γ hγ => SlashInvariantFormClass.slash_action_eq F γ hγ
  holo' := ModularFormClass.holo F
  bdd_at_cusps' := fun hc => ModularFormClass.bdd_at_cusps F hc

private def P₄ : PowerSeries ℤ := PowerSeries.mk fun n => if n = 0 then 1 else 240 * (σ 3 n : ℤ)

private def P₆ : PowerSeries ℤ := PowerSeries.mk fun n => if n = 0 then 1 else -504 * (σ 5 n : ℤ)

private theorem isIntegralQExp_E4 : IsIntegralQExp (ModularForm.E₄ : ℍ → ℂ) P₄ := by
  rw [isIntegralQExp_iff]
  intro n
  rw [EisensteinSeries.E_qExpansion_coeff (by norm_num) (by decide) n, P₄, PowerSeries.coeff_mk]
  split_ifs with h
  · simp
  · rw [show _root_.bernoulli 4 = -1 / 30 by decide +kernel]
    push_cast
    ring

private theorem isIntegralQExp_E6 : IsIntegralQExp (ModularForm.E₆ : ℍ → ℂ) P₆ := by
  rw [isIntegralQExp_iff]
  intro n
  rw [EisensteinSeries.E_qExpansion_coeff (by norm_num) (by decide) n, P₆, PowerSeries.coeff_mk]
  split_ifs with h
  · simp
  · rw [show _root_.bernoulli 6 = 1 / 42 by decide +kernel]
    push_cast
    ring

private theorem isIntegralQExp_discriminant :
    IsIntegralQExp (ModularForm.discriminant : ℍ → ℂ) (PowerSeries.X * dedekindEtaUnit) :=
  ModularCurve.qExpansion_discriminant_eq_map_X_mul_dedekindEtaUnit.symm

private theorem intSeriesC_eq_of_map_zmod_eq {q : ℕ} (κ : Type*) [Field κ] [CharP κ q] {p p' : PowerSeries ℤ}
    (h : p.map (Int.castRingHom (ZMod q)) = p'.map (Int.castRingHom (ZMod q))) :
    intSeriesC κ p = intSeriesC κ p' := by
  have hφ : Int.castRingHom κ = (ZMod.castHom (dvd_refl q) κ).comp (Int.castRingHom (ZMod q)) :=
    RingHom.ext_int _ _
  have h' : p.map (Int.castRingHom κ) = p'.map (Int.castRingHom κ) := by
    ext n
    have := congrArg (PowerSeries.coeff n) h
    simp only [PowerSeries.coeff_map] at this ⊢
    rw [hφ, RingHom.comp_apply, RingHom.comp_apply, this]
  simp only [intSeriesC, h']

private theorem intSeriesC_ne_zero_of_map_zmod_ne_zero {q : ℕ} [Fact q.Prime] (κ : Type*) [Field κ] [CharP κ q]
    {p : PowerSeries ℤ} (h : p.map (Int.castRingHom (ZMod q)) ≠ 0) : intSeriesC κ p ≠ 0 := by
  have hφ : Int.castRingHom κ = (ZMod.castHom (dvd_refl q) κ).comp (Int.castRingHom (ZMod q)) :=
    RingHom.ext_int _ _
  intro h0
  apply h
  rw [intSeriesC] at h0
  have hinj : Function.Injective (ZMod.castHom (dvd_refl q) κ) := RingHom.injective _
  have h1 : p.map (Int.castRingHom κ) = 0 :=
    HahnSeries.ofPowerSeries_injective (h0.trans (map_zero _).symm)
  ext n
  apply hinj
  have := congrArg (PowerSeries.coeff n) h1
  rw [PowerSeries.coeff_map, hφ, RingHom.comp_apply] at this
  simpa using this

private theorem intSeriesC_X_mul_dedekindEtaUnit_ne_zero (κ : Type*) [Field κ] :
    intSeriesC κ (PowerSeries.X * dedekindEtaUnit) ≠ 0 := by
  intro h
  have h1 := congrArg (fun z : LaurentSeries κ => z.coeff 1) h
  simp only [intSeriesC, HahnSeries.coeff_zero] at h1
  have h2 : (HahnSeries.ofPowerSeries ℤ κ
      ((PowerSeries.X * dedekindEtaUnit).map (Int.castRingHom κ))).coeff ((1 : ℕ) : ℤ) = 1 := by
    rw [HahnSeries.ofPowerSeries_apply_coeff, PowerSeries.coeff_map,
      show (1 : ℕ) = 0 + 1 from rfl, PowerSeries.coeff_succ_X_mul,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, constantCoeff_dedekindEtaUnit, map_one]
  rw [show ((1 : ℕ) : ℤ) = 1 from rfl] at h2
  rw [h2] at h1
  exact one_ne_zero h1

private theorem coeffEmb_intSeriesC (L : Type*) [Field L] [Algebra ℚ L] (p : PowerSeries ℤ) :
    coeffEmb L (intSeriesC ℚ p) = intSeriesC L p := by
  ext n
  simp only [coeffEmb, intSeriesC, coeffMap_coeff]
  by_cases hn : 0 ≤ n
  · lift n to ℕ using hn
    rw [HahnSeries.ofPowerSeries_apply_coeff, HahnSeries.ofPowerSeries_apply_coeff, PowerSeries.coeff_map,
      PowerSeries.coeff_map, eq_intCast, eq_intCast, map_intCast]
  · rw [ofPowerSeries_coeff_of_neg _ (not_le.mp hn), ofPowerSeries_coeff_of_neg _ (not_le.mp hn), map_zero]

end ModularCurve.FullLevel.HasseLift
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_exists_fieldBar_mul_intSeriesC_eq_and_reduction_eisensteinRatio.ModularCurve P2MW.S_ModularCurve_FullLevel_exists_fieldBar_mul_intSeriesC_eq_and_reduction_eisensteinRatio.ModularCurve.FullLevel P2MW.S_ModularCurve_FullLevel_exists_fieldBar_mul_intSeriesC_eq_and_reduction_eisensteinRatio.ModularCurve.FullLevel.HasseLift"
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_exists_fieldBar_mul_intSeriesC_eq_and_reduction_eisensteinRatio.ModularCurve P2MW.S_ModularCurve_FullLevel_exists_fieldBar_mul_intSeriesC_eq_and_reduction_eisensteinRatio.ModularCurve.FullLevel"
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_exists_fieldBar_mul_intSeriesC_eq_and_reduction_eisensteinRatio.ModularCurve"

end
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_exists_fieldBar_mul_intSeriesC_eq_and_reduction_eisensteinRatio.ModularCurve P2MW.S_ModularCurve_FullLevel_exists_fieldBar_mul_intSeriesC_eq_and_reduction_eisensteinRatio.ModularCurve.FullLevel P2MW.S_ModularCurve_FullLevel_exists_fieldBar_mul_intSeriesC_eq_and_reduction_eisensteinRatio.ModularCurve.FullLevel.HasseLift"

p2m_open "ModularCurve P2MW.S_ModularCurve_FullLevel_exists_fieldBar_mul_intSeriesC_eq_and_reduction_eisensteinRatio.ModularCurve ModularCurve.FullLevel P2MW.S_ModularCurve_FullLevel_exists_fieldBar_mul_intSeriesC_eq_and_reduction_eisensteinRatio.ModularCurve.FullLevel CongruenceSubgroup UpperHalfPlane P2MW.S_ModularCurve_FullLevel_exists_fieldBar_mul_intSeriesC_eq_and_reduction_eisensteinRatio.ModularCurve.FullLevel.HasseLift"
open scoped MatrixGroups ArithmeticFunction.sigma ModularForm

theorem solution
    (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q) (M' : ℕ) [NeZero M'] :
    ∃ (u : fieldBar q M') (X Y : PowerSeries ℤ),
      (u : LaurentSeries (AlgebraicClosure ℚ)) * intSeriesC (AlgebraicClosure ℚ) Y =
        intSeriesC (AlgebraicClosure ℚ) X ∧
      ∀ (κ : Type) [Field κ] [CharP κ q],
        intSeriesC κ Y ≠ 0 ∧
        intSeriesC κ X * intSeriesC κ (PowerSeries.X * dedekindEtaUnit) =
          intSeriesC κ Y *
            (intSeriesC κ (PowerSeries.mk fun n => if n = 0 then 1 else 240 * (σ 3 n : ℤ)) *
              intSeriesC κ (PowerSeries.mk fun n => if n = 0 then 1 else -504 * (σ 5 n : ℤ))) := by
  classical
  obtain ⟨k, G, H, pG, pH, hG, hH, hH0, hGH⟩ :=
    ModularForm.exists_isIntegralQExp_gamma1_weight_add_one_map_zmod_eq q hq

  let E4 : ModularForm ((Gamma1 q : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) 4 :=
    restrictSL ModularForm.E₄ (Gamma1 q)
  let E6 : ModularForm ((Gamma1 q : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) 6 :=
    restrictSL ModularForm.E₆ (Gamma1 q)
  let Dl : ModularForm ((Gamma1 q : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) 12 :=
    restrictSL (ofCuspSL CuspForm.discriminant) (Gamma1 q)
  have hDl : (⇑Dl : ℍ → ℂ) = ModularForm.discriminant := by
    show ⇑(CuspForm.discriminant) = _
    exact CuspForm.coe_discriminant

  let Fn : ModularForm ((Gamma1 q : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) (2 * k + 12) :=
    ((G.mul G).mul (E4.mul E6)).mcast (by ring)
  let Fd : ModularForm ((Gamma1 q : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) (2 * k + 12) :=
    ((H.mul H).mul Dl).mcast (by ring)
  have h1 : (1 : ℝ) ∈ ((Gamma1 q : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
    rw [CongruenceSubgroup.strictPeriods_Gamma1]; exact AddSubgroup.mem_zmultiples _
  have hqn : qExpansion 1 (⇑Fn : ℍ → ℂ) =
      qExpansion 1 ⇑G * qExpansion 1 ⇑G * (qExpansion 1 ⇑E4 * qExpansion 1 ⇑E6) := by
    show qExpansion 1 ⇑(((G.mul G).mul (E4.mul E6)).mcast _) = _
    rw [ModularForm.qExpansion_mcast, ModularForm.qExpansion_mul one_pos h1,
      ModularForm.qExpansion_mul one_pos h1, ModularForm.qExpansion_mul one_pos h1]
  have hqd : qExpansion 1 (⇑Fd : ℍ → ℂ) = qExpansion 1 ⇑H * qExpansion 1 ⇑H * qExpansion 1 ⇑Dl := by
    show qExpansion 1 ⇑(((H.mul H).mul Dl).mcast _) = _
    rw [ModularForm.qExpansion_mcast, ModularForm.qExpansion_mul one_pos h1,
      ModularForm.qExpansion_mul one_pos h1]

  set X : PowerSeries ℤ := pG * pG * (P₄ * P₆) with hX
  set Y : PowerSeries ℤ := pH * pH * (PowerSeries.X * dedekindEtaUnit) with hY
  have hIn : IsIntegralQExp Fn X := by
    rw [IsIntegralQExp, hqn, hX, map_mul, map_mul, map_mul, hG, isIntegralQExp_E4, isIntegralQExp_E6]
    rfl
  have hId : IsIntegralQExp Fd Y := by
    rw [IsIntegralQExp, hqd, hY, map_mul, map_mul, hH, hDl, isIntegralQExp_discriminant]
  have hY0Q : intSeriesC ℚ Y ≠ 0 := by
    rw [hY, intSeriesC_mul, intSeriesC_mul]
    haveI : CharP (ZMod q) q := ZMod.charP q
    have hHQ : intSeriesC ℚ pH ≠ 0 := by
      intro h0
      apply hH0
      have : pH = 0 := by
        ext n
        have := congrArg (fun z : LaurentSeries ℚ => z.coeff n) h0
        simp only [intSeriesC, HahnSeries.ofPowerSeries_apply_coeff, PowerSeries.coeff_map, eq_intCast,
          HahnSeries.coeff_zero, Int.cast_eq_zero] at this
        simpa using this
      rw [this, map_zero]
    exact mul_ne_zero (mul_ne_zero hHQ hHQ) (intSeriesC_X_mul_dedekindEtaUnit_ne_zero ℚ)

  let Fn' := ModularCurve.restrictForm (gammaH_levelH_le_Gamma1_GL q M') Fn
  let Fd' := ModularCurve.restrictForm (gammaH_levelH_le_Gamma1_GL q M') Fd
  have hIn' : IsIntegralQExp Fn' X := by rw [IsIntegralQExp, ModularCurve.coe_restrictForm]; exact hIn
  have hId' : IsIntegralQExp Fd' Y := by rw [IsIntegralQExp, ModularCurve.coe_restrictForm]; exact hId
  refine ⟨⟨coeffEmb (AlgebraicClosure ℚ) (intSeriesC ℚ X / intSeriesC ℚ Y),
    coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (div_mem_qExpFunctionFieldC Fn' Fd' hIn' hId' hY0Q)⟩,
    X, Y, ?_, ?_⟩
  ·
    show coeffEmb (AlgebraicClosure ℚ) (intSeriesC ℚ X / intSeriesC ℚ Y) * _ = _
    rw [map_div₀, coeffEmb_intSeriesC, coeffEmb_intSeriesC, div_mul_cancel₀]
    rw [← coeffEmb_intSeriesC]
    exact (map_ne_zero_iff _ (RingHom.injective _)).mpr hY0Q
  · intro κ _ _
    have hGHκ : intSeriesC κ pG = intSeriesC κ pH := intSeriesC_eq_of_map_zmod_eq κ hGH
    have hHκ : intSeriesC κ pH ≠ 0 := intSeriesC_ne_zero_of_map_zmod_ne_zero κ hH0
    refine ⟨?_, ?_⟩
    · rw [hY, intSeriesC_mul, intSeriesC_mul]
      exact mul_ne_zero (mul_ne_zero hHκ hHκ) (intSeriesC_X_mul_dedekindEtaUnit_ne_zero κ)
    · rw [hX, hY]
      simp only [intSeriesC_mul, hGHκ]
      show _ = _ * (intSeriesC κ P₄ * intSeriesC κ P₆)
      ring

end S_ModularCurve_FullLevel_exists_fieldBar_mul_intSeriesC_eq_and_reduction_eisensteinRatio
end P2MW
export P2MW.S_ModularCurve_FullLevel_exists_fieldBar_mul_intSeriesC_eq_and_reduction_eisensteinRatio (solution)
