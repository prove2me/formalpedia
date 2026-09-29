-- Prove2me | solution 1 for ModularCurve.FullLevel.Diamond.exists_modularForm_mul_qExpansion_eq_tateToricPoint_and_slash_conjElemN_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.339302+00:00
-- url     : https://prove2.me/submissions/ed054402-daaa-5afb-89a6-2f968c1c8480

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_XH
import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_ModularCurve_FullLevelLevelAutAt
import Definitions.Def_ModularCurve_TateSlots
import Definitions.Def_ModularCurve_KatzLevelPCusps
import Definitions.Def_ModularCurve_WeierstrassGamma0Pow
import Theorems.Thm_ModularCurve_exists_modularForm_gamma1_inf_gamma0_mul_qExpansion_eq_tateToricPoint_fst_and_slash_conjElemN_eq
import Theorems.Thm_ModularCurve_exists_modularForm_gamma1_inf_gamma0_mul_weight_three_qExpansion_eq_tateToricPoint_and_slash_conjElemN_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_Diamond_exists_modularForm_mul_qExpansion_eq_tateToricPoint_and_slash_conjElemN_eq
p2m_attr_erase "simp" "ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"

set_option autoImplicit false

noncomputable section

open scoped MatrixGroups ModularForm
open CongruenceSubgroup

namespace ToricFormsH1

section CoeffMap

variable {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)

theorem coeffMap_ofPowerSeries (φ : PowerSeries R) :
    ModularCurve.coeffMap f (HahnSeries.ofPowerSeries ℤ R φ) = HahnSeries.ofPowerSeries ℤ S (φ.map f) := by
  ext m
  rw [ModularCurve.coeffMap_coeff]
  change f (((φ : PowerSeries R) : LaurentSeries R).coeff m) =
    ((PowerSeries.map f φ : PowerSeries S) : LaurentSeries S).coeff m
  rw [PowerSeries.coeff_coe, PowerSeries.coeff_coe]
  split_ifs with h
  · exact map_zero f
  · exact (PowerSeries.coeff_map _ _ _).symm

theorem coeffMap_C' (a : R) :
    ModularCurve.coeffMap f (HahnSeries.C a) = HahnSeries.C (f a) := by
  rw [HahnSeries.C_apply, HahnSeries.C_apply, ModularCurve.coeffMap_single]

end CoeffMap

section Toric

variable {F F' : Type*} [Field F] [Field F'] (f : F →+* F')

theorem coeffMap_toricPoint_fst (p : ℕ) (c : F) :
    ModularCurve.coeffMap f (ModularCurve.toricPoint F p c).1 = (ModularCurve.toricPoint F' p (f c)).1 := by
  rw [ModularCurve.toricPoint_fst, ModularCurve.toricPoint_fst, coeffMap_ofPowerSeries]
  congr 1
  ext m
  rw [PowerSeries.coeff_map, PowerSeries.coeff_mk, PowerSeries.coeff_mk]
  by_cases hm : m = 0
  · rw [if_pos hm, if_pos hm, map_div₀, map_pow, map_sub, map_one]
  · rw [if_neg hm, if_neg hm]
    simp only [map_sub, map_sum, map_mul, map_add, map_pow, map_natCast, apply_ite f, map_zero,
      map_ofNat, map_inv₀]

theorem coeffMap_toricPoint_snd (p : ℕ) (c : F) :
    ModularCurve.coeffMap f (ModularCurve.toricPoint F p c).2 = (ModularCurve.toricPoint F' p (f c)).2 := by
  rw [ModularCurve.toricPoint_snd, ModularCurve.toricPoint_snd, coeffMap_ofPowerSeries]
  congr 1
  ext m
  rw [PowerSeries.coeff_map, PowerSeries.coeff_mk, PowerSeries.coeff_mk]
  by_cases hm : m = 0
  · rw [if_pos hm, if_pos hm, map_div₀, map_pow, map_pow, map_sub, map_one]
  · rw [if_neg hm, if_neg hm]
    simp only [map_sub, map_sum, map_mul, map_add, map_pow, map_natCast, apply_ite f, map_zero,
      map_inv₀]

theorem coeffMap_tateToricPoint_fst (p : ℕ) (c : Fˣ) :
    ModularCurve.coeffMap f (ModularCurve.tateToricPoint F p c).1 =
      (ModularCurve.tateToricPoint F' p (Units.map (f : F →* F') c)).1 := by
  rw [ModularCurve.tateToricPoint_eq_toricPoint, ModularCurve.tateToricPoint_eq_toricPoint,
    coeffMap_toricPoint_fst]
  rfl

theorem coeffMap_tateToricPoint_snd (p : ℕ) (c : Fˣ) :
    ModularCurve.coeffMap f (ModularCurve.tateToricPoint F p c).2 =
      (ModularCurve.tateToricPoint F' p (Units.map (f : F →* F') c)).2 := by
  rw [ModularCurve.tateToricPoint_eq_toricPoint, ModularCurve.tateToricPoint_eq_toricPoint,
    coeffMap_toricPoint_snd]
  rfl

theorem coeff_toricPoint_fst_add_C (p : ℕ) (hp : p.Prime) (c : F) :
    ((ModularCurve.toricPoint F p c).1 + HahnSeries.C ((12 : F)⁻¹)).coeff (p : ℤ) = c + c⁻¹ - 2 := by
  have hp0 : p ≠ 0 := hp.ne_zero
  rw [HahnSeries.coeff_add, ModularCurve.toricPoint_fst, HahnSeries.ofPowerSeries_apply_coeff,
    PowerSeries.coeff_mk, if_neg hp0]
  have hC : (HahnSeries.C ((12 : F)⁻¹) : LaurentSeries F).coeff (p : ℤ) = 0 := by
    rw [HahnSeries.C_apply, HahnSeries.coeff_single_of_ne]
    exact_mod_cast hp0
  rw [hC, add_zero, if_pos (dvd_refl p), Nat.div_self hp.pos, Nat.Prime.divisors hp,
    Finset.sum_pair hp.one_lt.ne, if_neg, if_pos (dvd_refl p), Nat.div_self hp.pos]
  · simp
  · intro h
    exact hp.one_lt.ne' (Nat.dvd_one.mp h)

theorem toricPoint_fst_add_C_ne_zero (p : ℕ) (hp : p.Prime) (c : F) (hc0 : c ≠ 0) (hc1 : c ≠ 1) :
    (ModularCurve.toricPoint F p c).1 + HahnSeries.C ((12 : F)⁻¹) ≠ 0 := by
  intro h
  have := coeff_toricPoint_fst_add_C p hp c
  rw [h] at this
  have h0 : c + c⁻¹ - 2 = 0 := by rw [← this]; rfl
  have h2 : (c - 1) ^ 2 = 0 := by
    have : c * (c + c⁻¹ - 2) = 0 := by rw [h0, mul_zero]
    rw [mul_sub, mul_add, mul_inv_cancel₀ hc0] at this
    linear_combination this
  exact hc1 (sub_eq_zero.mp (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h2))

end Toric

section Groups

theorem gammaH_le_gamma1_inf_gamma0 (M ℓ m : ℕ) (hℓ : ℓ ∣ M) (hm : m ∣ M)
    (H : Subgroup (ZMod M)ˣ) (hH : H ≤ (ZMod.unitsMap hℓ).ker) :
    CohCarrier.GammaH M H ≤ Gamma1 ℓ ⊓ Gamma0 m := by
  intro A hA
  obtain ⟨hA0, hAH⟩ := CohCarrier.mem_GammaH_iff.mp hA
  have hc : (((A : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℤ) : ZMod M) = 0 := Gamma0_mem.mp hA0
  have hcM : (M : ℤ) ∣ (A : Matrix (Fin 2) (Fin 2) ℤ) 1 0 := (CharP.intCast_eq_zero_iff (ZMod M) M _).mp hc
  have hcℓ : (((A : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℤ) : ZMod ℓ) = 0 :=
    (CharP.intCast_eq_zero_iff (ZMod ℓ) ℓ _).mpr (dvd_trans (Int.natCast_dvd_natCast.mpr hℓ) hcM)
  have hcm : (((A : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℤ) : ZMod m) = 0 :=
    (CharP.intCast_eq_zero_iff (ZMod m) m _).mpr (dvd_trans (Int.natCast_dvd_natCast.mpr hm) hcM)
  have hd : (((A : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℤ) : ZMod ℓ) = 1 := by
    have h1 := hH hAH
    rw [MonoidHom.mem_ker] at h1
    have h2 := congrArg (fun u : (ZMod ℓ)ˣ => (u : ZMod ℓ)) h1
    simp only [ZMod.unitsMap_val, Units.val_one, CohCarrier.val_gamma0Units] at h2
    change ZMod.cast ((((A : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℤ) : ZMod M)) = (1 : ZMod ℓ) at h2
    rwa [ZMod.cast_intCast hℓ] at h2
  have ha : (((A : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ℤ) : ZMod ℓ) = 1 := by
    have hdet := Matrix.SpecialLinearGroup.det_coe A
    rw [Matrix.det_fin_two] at hdet
    have h := congrArg (Int.cast : ℤ → ZMod ℓ) hdet
    push_cast at h
    rw [hd, hcℓ, mul_one, mul_zero, sub_zero] at h
    exact h
  refine Subgroup.mem_inf.mpr ⟨?_, Gamma0_mem.mpr hcm⟩
  rw [Gamma1_mem]
  exact ⟨ha, hd, hcℓ⟩

end Groups

section Conj

variable (m : ℕ) [NeZero m]

theorem mne : (m : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne m

def Dr : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![(m : ℝ), 0; 0, 1]
    (by rw [Matrix.det_fin_two_of]; simp [mne m])

@[scoped simp] theorem Dr_coe : ((Dr m : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = !![(m : ℝ), 0; 0, 1] := rfl

@[scoped simp] theorem conjElemN_coe (γ : SL(2, ℤ)) :
    ((ModularCurve.FullLevel.conjElemN m γ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
      !![((γ 0 0 : ℤ) : ℝ), ((γ 0 1 : ℤ) : ℝ) / m; (m : ℝ) * ((γ 1 0 : ℤ) : ℝ), ((γ 1 1 : ℤ) : ℝ)] := rfl

theorem Dr_mul_conjElem (γ : SL(2, ℤ)) :
    Dr m * ModularCurve.FullLevel.conjElemN m γ = (γ : GL (Fin 2) ℝ) * Dr m := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  simp only [Matrix.GeneralLinearGroup.coe_mul, Dr_coe, conjElemN_coe]
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, mul_div_assoc', mul_div_cancel_left₀ _ (mne m), mul_comm]

theorem conjElemN_eq (γ : SL(2, ℤ)) :
    ModularCurve.FullLevel.conjElemN m γ = (Dr m)⁻¹ * (γ : GL (Fin 2) ℝ) * Dr m := by
  rw [mul_assoc, ← Dr_mul_conjElem, inv_mul_cancel_left]

theorem det_coeSL (γ : SL(2, ℤ)) : ((γ : GL (Fin 2) ℝ)).det = 1 := by
  ext
  simp

theorem det_conjElemN (γ : SL(2, ℤ)) : (ModularCurve.FullLevel.conjElemN m γ).det = 1 := by
  rw [conjElemN_eq, map_mul, map_mul, map_inv, det_coeSL, mul_one, inv_mul_cancel]

theorem det_conjElemN_val (γ : SL(2, ℤ)) : ((ModularCurve.FullLevel.conjElemN m γ).det : ℝ) = 1 := by
  rw [det_conjElemN]; rfl

end Conj

theorem T_mem_GammaH (N : ℕ) (H : Subgroup (ZMod N)ˣ) : ModularGroup.T ∈ CohCarrier.GammaH N H := by
  rw [CohCarrier.mem_GammaH_iff]
  have hT : ModularGroup.T ∈ CongruenceSubgroup.Gamma0 N := by
    rw [CongruenceSubgroup.Gamma0_mem, ModularGroup.coe_T]
    simp
  refine ⟨hT, ?_⟩
  have : CohCarrier.gamma0Units N ⟨ModularGroup.T, hT⟩ = 1 := by
    ext
    rw [CohCarrier.val_gamma0Units]
    change (((ModularGroup.T : SL(2, ℤ)) 1 1 : ℤ) : ZMod N) = ((1 : (ZMod N)ˣ) : ZMod N)
    rw [ModularGroup.coe_T]
    simp
  rw [this]
  exact one_mem H

theorem one_mem_strictPeriods_GammaH (N : ℕ) (H : Subgroup (ZMod N)ˣ) :
    (1 : ℝ) ∈ (CohCarrier.GammaH N H : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
  rw [Subgroup.strictPeriods_eq_zmultiples_one_of_T_mem (T_mem_GammaH N H)]
  exact AddSubgroup.mem_zmultiples _

theorem main
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (ℓg : ℕ) (hℓg : ℓg.Prime) (hℓg12 : ℓg % 12 = 11) (hℓgM' : ℓg ∣ M')
    (L : Type) [Field L] [CharZero L]
    (ξ : L) (hξ : IsPrimitiveRoot ξ (q * ℓg))
    (ι : L →+* ℂ) (hι : ι ξ = Complex.exp (2 * Real.pi * Complex.I / (q * ℓg)))
    (H₁ : Subgroup (ZMod (q ^ 2 * M'))ˣ)
    (hH₁ : H₁ = ModularCurve.FullLevel.levelH q M' ⊓ (ZMod.unitsMap (Dvd.dvd.mul_left hℓgM' (q ^ 2))).ker) :
    haveI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
    ∃ (At : Lˣ → ModularForm (CohCarrier.GammaH (q ^ 2 * M') H₁ :
            Subgroup (GL (Fin 2) ℝ)) 6)
      (Bt : Lˣ → ModularForm (CohCarrier.GammaH (q ^ 2 * M') H₁ :
            Subgroup (GL (Fin 2) ℝ)) 4)
      (Rt : Lˣ → ModularForm (CohCarrier.GammaH (q ^ 2 * M') H₁ :
            Subgroup (GL (Fin 2) ℝ)) 3),
      (∀ c : Lˣ, c ^ ℓg = 1 → c ≠ 1 →
        HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 (⇑(Bt c))) ≠ 0 ∧
        (∃ b : LaurentSeries L, HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 (⇑(Bt c))) = ModularCurve.coeffMap ι b) ∧
        ModularCurve.coeffMap ι ((ModularCurve.tateToricPoint L q c).1 + HahnSeries.C ((12 : L)⁻¹)) *
            HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 (⇑(Bt c))) =
          HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 (⇑(At c))) ∧
        HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 (⇑(Rt c))) =
          ModularCurve.coeffMap ι (2 * (ModularCurve.tateToricPoint L q c).2 + (ModularCurve.tateToricPoint L q c).1)) ∧
      (∀ ρ : SL(2, ℤ), ρ ∈ CongruenceSubgroup.Gamma0 M' → ∀ c : Lˣ, c ^ ℓg = 1 → c ≠ 1 →
        (⇑(At c) ∣[(6 : ℤ)] ModularCurve.FullLevel.conjElemN q ρ) = ⇑(At (c ^ ((ρ 1 1 : ℤ)))) ∧
        (⇑(Bt c) ∣[(4 : ℤ)] ModularCurve.FullLevel.conjElemN q ρ) = ⇑(Bt (c ^ ((ρ 1 1 : ℤ)))) ∧
        (⇑(Rt c) ∣[(3 : ℤ)] ModularCurve.FullLevel.conjElemN q ρ) = ⇑(Rt (c ^ ((ρ 1 1 : ℤ))))) := by
  haveI hq0 : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
  haveI : NeZero ℓg := ⟨hℓg.ne_zero⟩
  obtain ⟨X, hXq, hXs⟩ :=
    ModularCurve.exists_modularForm_gamma1_inf_gamma0_mul_qExpansion_eq_tateToricPoint_fst_and_slash_conjElemN_eq q ℓg
  obtain ⟨Y, hYq, hYs⟩ :=
    ModularCurve.exists_modularForm_gamma1_inf_gamma0_mul_weight_three_qExpansion_eq_tateToricPoint_and_slash_conjElemN_eq q ℓg

  have hleSL : CohCarrier.GammaH (q ^ 2 * M') H₁ ≤ Gamma1 ℓg ⊓ Gamma0 (q * ℓg) := by
    refine gammaH_le_gamma1_inf_gamma0 (q ^ 2 * M') ℓg (q * ℓg) (Dvd.dvd.mul_left hℓgM' (q ^ 2))
      (mul_dvd_mul (dvd_pow_self q two_ne_zero) hℓgM') H₁ ?_
    rw [hH₁]
    exact inf_le_right
  have hle : (CohCarrier.GammaH (q ^ 2 * M') H₁ : Subgroup (GL (Fin 2) ℝ)) ≤
      ((Gamma1 ℓg ⊓ Gamma0 (q * ℓg) : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) :=
    Subgroup.map_mono hleSL
  have h1 := one_mem_strictPeriods_GammaH (q ^ 2 * M') H₁

  let u : Lˣ → ℂˣ := fun c => Units.map (ι : L →* ℂ) c
  have hu_val : ∀ c : Lˣ, ((u c : ℂˣ) : ℂ) = ι (c : L) := fun c => rfl
  have hu_pow : ∀ c : Lˣ, c ^ ℓg = 1 → (u c) ^ ℓg = 1 := fun c hc => by
    show (Units.map (ι : L →* ℂ) c) ^ ℓg = 1
    rw [← map_pow, hc, map_one]
  have hu_ne : ∀ c : Lˣ, c ≠ 1 → u c ≠ 1 := fun c hc1 h => by
    apply hc1
    have h' : ι (c : L) = 1 := by rw [← hu_val, h, Units.val_one]
    exact Units.ext (ι.injective (by rw [h', Units.val_one, map_one]))
  have hu_zpow : ∀ (c : Lˣ) (d : ℤ), u (c ^ d) = (u c) ^ d := fun c d => by
    show Units.map (ι : L →* ℂ) (c ^ d) = (Units.map (ι : L →* ℂ) c) ^ d
    exact map_zpow _ c d

  let Xr : Lˣ → ModularForm (CohCarrier.GammaH (q ^ 2 * M') H₁ : Subgroup (GL (Fin 2) ℝ)) 2 :=
    fun c => ModularCurve.restrictForm hle (X (u c))
  let Rt : Lˣ → ModularForm (CohCarrier.GammaH (q ^ 2 * M') H₁ : Subgroup (GL (Fin 2) ℝ)) 3 :=
    fun c => ModularCurve.restrictForm hle (Y (u c))
  let Bt : Lˣ → ModularForm (CohCarrier.GammaH (q ^ 2 * M') H₁ : Subgroup (GL (Fin 2) ℝ)) 4 :=
    fun c => ((Xr c).mul (Xr c)).mcast (by norm_num)
  let At : Lˣ → ModularForm (CohCarrier.GammaH (q ^ 2 * M') H₁ : Subgroup (GL (Fin 2) ℝ)) 6 :=
    fun c => (((Xr c).mul (Xr c)).mul (Xr c)).mcast (by norm_num)
  have hXr_coe : ∀ c, (⇑(Xr c) : UpperHalfPlane → ℂ) = ⇑(X (u c)) := fun c => rfl
  have hRt_coe : ∀ c, (⇑(Rt c) : UpperHalfPlane → ℂ) = ⇑(Y (u c)) := fun c => rfl
  have hBt_coe : ∀ c, (⇑(Bt c) : UpperHalfPlane → ℂ) = ⇑(X (u c)) * ⇑(X (u c)) := fun c => by
    show (⇑(((Xr c).mul (Xr c)).mcast _) : UpperHalfPlane → ℂ) = _
    rw [ModularForm.coe_mcast, ModularForm.coe_mul, hXr_coe]
  have hAt_coe : ∀ c, (⇑(At c) : UpperHalfPlane → ℂ) = ⇑(X (u c)) * ⇑(X (u c)) * ⇑(X (u c)) := fun c => by
    show (⇑((((Xr c).mul (Xr c)).mul (Xr c)).mcast _) : UpperHalfPlane → ℂ) = _
    rw [ModularForm.coe_mcast, ModularForm.coe_mul, ModularForm.coe_mul, hXr_coe]

  have hBtq : ∀ c, HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 (⇑(Bt c))) =
      HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 (⇑(Xr c))) *
        HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 (⇑(Xr c))) := fun c => by
    show HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 (⇑(((Xr c).mul (Xr c)).mcast _))) = _
    rw [ModularForm.coe_mcast, ModularForm.qExpansion_mul one_pos h1, map_mul]
  have hAtq : ∀ c, HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 (⇑(At c))) =
      HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 (⇑(Xr c))) *
        HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 (⇑(Xr c))) *
        HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 (⇑(Xr c))) := fun c => by
    show HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 (⇑((((Xr c).mul (Xr c)).mul (Xr c)).mcast _))) = _
    rw [ModularForm.coe_mcast, ModularForm.qExpansion_mul one_pos h1, map_mul,
      ModularForm.qExpansion_mul one_pos h1, map_mul]
  refine ⟨At, Bt, Rt, ?_, ?_⟩
  · intro c hc hc1
    have huc := hu_pow c hc
    have huc1 := hu_ne c hc1
    set T : LaurentSeries ℂ := (ModularCurve.tateToricPoint ℂ q (u c)).1 + HahnSeries.C ((12 : ℂ)⁻¹) with hT
    have hXrq : HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 (⇑(Xr c))) = T := by
      rw [hXr_coe]; exact hXq (u c) huc huc1
    have hTmap : ModularCurve.coeffMap ι ((ModularCurve.tateToricPoint L q c).1 + HahnSeries.C ((12 : L)⁻¹)) = T := by
      rw [map_add, coeffMap_tateToricPoint_fst, coeffMap_C', map_inv₀, map_ofNat]
    have hT0 : T ≠ 0 := by
      rw [hT, ModularCurve.tateToricPoint_eq_toricPoint]
      refine toricPoint_fst_add_C_ne_zero q (Fact.out : q.Prime) ((u c : ℂˣ) : ℂ) (u c).ne_zero ?_
      intro h
      exact huc1 (Units.ext (by rw [h, Units.val_one]))
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hBtq, hXrq]
      exact mul_ne_zero hT0 hT0
    · refine ⟨((ModularCurve.tateToricPoint L q c).1 + HahnSeries.C ((12 : L)⁻¹)) ^ 2, ?_⟩
      rw [hBtq, hXrq, map_pow, hTmap, sq]
    · rw [hBtq, hAtq, hXrq, hTmap, mul_assoc]
    · rw [hRt_coe, hYq (u c) huc huc1, map_add, map_mul, map_ofNat, coeffMap_tateToricPoint_fst,
        coeffMap_tateToricPoint_snd]
  · intro ρ hρ c hc hc1
    have huc := hu_pow c hc
    have huc1 := hu_ne c hc1
    have hρℓ : ρ ∈ Gamma0 ℓg := by
      rw [Gamma0_mem] at hρ ⊢
      have h := (CharP.intCast_eq_zero_iff (ZMod M') M' _).mp hρ
      exact (CharP.intCast_eq_zero_iff (ZMod ℓg) ℓg _).mpr (dvd_trans (Int.natCast_dvd_natCast.mpr hℓgM') h)
    have hdet : |((ModularCurve.FullLevel.conjElemN q ρ).det : ℝ)| = 1 := by
      rw [det_conjElemN_val, abs_one]
    have hX1 : (⇑(X (u c)) ∣[(2 : ℤ)] ModularCurve.FullLevel.conjElemN q ρ) = ⇑(X (u (c ^ ((ρ 1 1 : ℤ))))) := by
      rw [hu_zpow]; exact hXs ρ hρℓ (u c) huc huc1
    refine ⟨?_, ?_, ?_⟩
    · rw [hAt_coe, hAt_coe, show (6 : ℤ) = 2 + 2 + 2 by norm_num, ModularForm.mul_slash, ModularForm.mul_slash,
        hdet, one_smul, one_smul, hX1]
    · rw [hBt_coe, hBt_coe, show (4 : ℤ) = 2 + 2 by norm_num, ModularForm.mul_slash, hdet, one_smul, hX1]
    · rw [hRt_coe, hRt_coe, hu_zpow]
      exact hYs ρ hρℓ (u c) huc huc1

end ToricFormsH1
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_Diamond_exists_modularForm_mul_qExpansion_eq_tateToricPoint_and_slash_conjElemN_eq.ToricFormsH1"

open scoped MatrixGroups ModularForm in
theorem solution
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (ℓg : ℕ) (hℓg : ℓg.Prime) (hℓg12 : ℓg % 12 = 11) (hℓgM' : ℓg ∣ M')
    (L : Type) [Field L] [CharZero L]
    (ξ : L) (hξ : IsPrimitiveRoot ξ (q * ℓg))
    (ι : L →+* ℂ) (hι : ι ξ = Complex.exp (2 * Real.pi * Complex.I / (q * ℓg)))
    (H₁ : Subgroup (ZMod (q ^ 2 * M'))ˣ)
    (hH₁ : H₁ = ModularCurve.FullLevel.levelH q M' ⊓ (ZMod.unitsMap (Dvd.dvd.mul_left hℓgM' (q ^ 2))).ker) :
    haveI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
    ∃ (At : Lˣ → ModularForm (CohCarrier.GammaH (q ^ 2 * M') H₁ :
            Subgroup (GL (Fin 2) ℝ)) 6)
      (Bt : Lˣ → ModularForm (CohCarrier.GammaH (q ^ 2 * M') H₁ :
            Subgroup (GL (Fin 2) ℝ)) 4)
      (Rt : Lˣ → ModularForm (CohCarrier.GammaH (q ^ 2 * M') H₁ :
            Subgroup (GL (Fin 2) ℝ)) 3),
      (∀ c : Lˣ, c ^ ℓg = 1 → c ≠ 1 →
        HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 (⇑(Bt c))) ≠ 0 ∧
        (∃ b : LaurentSeries L, HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 (⇑(Bt c))) = ModularCurve.coeffMap ι b) ∧
        ModularCurve.coeffMap ι ((ModularCurve.tateToricPoint L q c).1 + HahnSeries.C ((12 : L)⁻¹)) *
            HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 (⇑(Bt c))) =
          HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 (⇑(At c))) ∧
        HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 (⇑(Rt c))) =
          ModularCurve.coeffMap ι (2 * (ModularCurve.tateToricPoint L q c).2 + (ModularCurve.tateToricPoint L q c).1)) ∧
      (∀ ρ : SL(2, ℤ), ρ ∈ CongruenceSubgroup.Gamma0 M' → ∀ c : Lˣ, c ^ ℓg = 1 → c ≠ 1 →
        (⇑(At c) ∣[(6 : ℤ)] ModularCurve.FullLevel.conjElemN q ρ) = ⇑(At (c ^ ((ρ 1 1 : ℤ)))) ∧
        (⇑(Bt c) ∣[(4 : ℤ)] ModularCurve.FullLevel.conjElemN q ρ) = ⇑(Bt (c ^ ((ρ 1 1 : ℤ)))) ∧
        (⇑(Rt c) ∣[(3 : ℤ)] ModularCurve.FullLevel.conjElemN q ρ) = ⇑(Rt (c ^ ((ρ 1 1 : ℤ))))) :=
  ToricFormsH1.main q M' hqM' ℓg hℓg hℓg12 hℓgM' L ξ hξ ι hι H₁ hH₁

end
end S_ModularCurve_FullLevel_Diamond_exists_modularForm_mul_qExpansion_eq_tateToricPoint_and_slash_conjElemN_eq
end P2MW
export P2MW.S_ModularCurve_FullLevel_Diamond_exists_modularForm_mul_qExpansion_eq_tateToricPoint_and_slash_conjElemN_eq (solution)
