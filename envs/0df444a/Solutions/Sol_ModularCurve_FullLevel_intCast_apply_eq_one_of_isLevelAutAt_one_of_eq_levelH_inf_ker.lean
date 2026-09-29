-- Prove2me | solution 1 for ModularCurve.FullLevel.intCast_apply_eq_one_of_isLevelAutAt_one_of_eq_levelH_inf_ker
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/14329c8e-af88-54e2-9882-3bf2b21d1cc1

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_ModularCurve_FullLevelLevelAutAt
import Definitions.Def_CohCarrier_Level
import Theorems.Thm_ModularCurve_exists_intSeriesC_mul_ne_of_gamma0Units_not_mem
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_intCast_apply_eq_one_of_isLevelAutAt_one_of_eq_levelH_inf_ker

set_option autoImplicit false

open scoped MatrixGroups ModularForm
open Matrix ModularCurve ModularCurve.FullLevel CongruenceSubgroup

noncomputable section

namespace K2A
variable (m : ℕ) [NeZero m]

theorem mpos : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
theorem mne : (m : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne m
theorem mneZ : (m : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne m

def Dr : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![(m : ℝ), 0; 0, 1]
    (by rw [Matrix.det_fin_two_of]; simp [mne m])

@[scoped simp] theorem Dr_coe : ((Dr m : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = !![(m : ℝ), 0; 0, 1] := rfl

@[scoped simp] theorem conjElemN_coe (γ : SL(2, ℤ)) : ((conjElemN m γ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
    !![((γ 0 0 : ℤ) : ℝ), ((γ 0 1 : ℤ) : ℝ) / m; (m : ℝ) * ((γ 1 0 : ℤ) : ℝ), ((γ 1 1 : ℤ) : ℝ)] := rfl

theorem Dr_mul_conjElem (γ : SL(2, ℤ)) : Dr m * conjElemN m γ = (γ : GL (Fin 2) ℝ) * Dr m := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  simp only [Matrix.GeneralLinearGroup.coe_mul, Dr_coe, conjElemN_coe]
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, mul_div_assoc', mul_div_cancel_left₀ _ (mne m), mul_comm]

theorem conjElemN_eq (γ : SL(2, ℤ)) : conjElemN m γ = (Dr m)⁻¹ * (γ : GL (Fin 2) ℝ) * Dr m := by
  rw [mul_assoc, ← Dr_mul_conjElem, inv_mul_cancel_left]

theorem conjElemN_mul (γ δ : SL(2, ℤ)) : conjElemN m (γ * δ) = conjElemN m γ * conjElemN m δ := by
  simp only [conjElemN_eq, map_mul]; group

theorem conjElemN_one : conjElemN m 1 = 1 := by
  simp only [conjElemN_eq, map_one]; group

theorem conjElemN_inv (γ : SL(2, ℤ)) : conjElemN m γ⁻¹ = (conjElemN m γ)⁻¹ := by
  simp only [conjElemN_eq, map_inv]; group

theorem det_coeSL (γ : SL(2, ℤ)) : ((γ : GL (Fin 2) ℝ)).det = 1 := by
  ext
  simp

theorem det_conjElemN (γ : SL(2, ℤ)) : (conjElemN m γ).det = 1 := by
  rw [conjElemN_eq, map_mul, map_mul, map_inv, det_coeSL, mul_one, inv_mul_cancel]

theorem det_conjElemN_val (γ : SL(2, ℤ)) : ((conjElemN m γ).det : ℝ) = 1 := by
  rw [det_conjElemN]; rfl

variable {m}

def upMat (δ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ := !![δ 0 0, (m : ℤ) * δ 0 1; δ 1 0 / m, δ 1 1]

theorem det_upMat (δ : SL(2, ℤ)) (h : (m : ℤ) ∣ δ 1 0) : (upMat (m := m) δ).det = 1 := by
  obtain ⟨c, hc⟩ := h
  have hdet := Matrix.SpecialLinearGroup.det_coe δ
  rw [Matrix.det_fin_two] at hdet ⊢
  have h1 : (m : ℤ) * c / m = c := by rw [mul_comm]; exact Int.mul_ediv_cancel c (mneZ m)
  simp only [upMat, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, hc, h1] at hdet ⊢
  linear_combination hdet

def upSL (δ : SL(2, ℤ)) (h : (m : ℤ) ∣ δ 1 0) : SL(2, ℤ) := ⟨upMat (m := m) δ, det_upMat δ h⟩

def downMat (ε : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ := !![ε 0 0, ε 0 1 / m; (m : ℤ) * ε 1 0, ε 1 1]

theorem det_downMat (ε : SL(2, ℤ)) (h : (m : ℤ) ∣ ε 0 1) : (downMat (m := m) ε).det = 1 := by
  obtain ⟨b, hb⟩ := h
  have hdet := Matrix.SpecialLinearGroup.det_coe ε
  rw [Matrix.det_fin_two] at hdet ⊢
  have h1 : (m : ℤ) * b / m = b := by rw [mul_comm]; exact Int.mul_ediv_cancel b (mneZ m)
  simp only [downMat, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, hb, h1] at hdet ⊢
  linear_combination hdet

def downSL (ε : SL(2, ℤ)) (h : (m : ℤ) ∣ ε 0 1) : SL(2, ℤ) := ⟨downMat (m := m) ε, det_downMat ε h⟩

theorem upSL_coe (δ : SL(2, ℤ)) (h : (m : ℤ) ∣ δ 1 0) :
    ((upSL δ h : SL(2, ℤ)) : GL (Fin 2) ℝ) * Dr m = Dr m * (δ : GL (Fin 2) ℝ) := by
  obtain ⟨c, hc⟩ := h
  have h1 : (m : ℤ) * c / m = c := by rw [mul_comm]; exact Int.mul_ediv_cancel c (mneZ m)
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  simp only [Matrix.GeneralLinearGroup.coe_mul, Dr_coe]
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, upSL, upMat, hc, h1] <;> ring

theorem downSL_coe (ε : SL(2, ℤ)) (h : (m : ℤ) ∣ ε 0 1) :
    Dr m * ((downSL ε h : SL(2, ℤ)) : GL (Fin 2) ℝ) = (ε : GL (Fin 2) ℝ) * Dr m := by
  obtain ⟨b, hb⟩ := h
  have h1 : (m : ℤ) * b / m = b := by rw [mul_comm]; exact Int.mul_ediv_cancel b (mneZ m)
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  simp only [Matrix.GeneralLinearGroup.coe_mul, Dr_coe]
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, downSL, downMat, hb, h1] <;> ring

theorem downSL_eq (ε : SL(2, ℤ)) (h : (m : ℤ) ∣ ε 0 1) :
    ((downSL ε h : SL(2, ℤ)) : GL (Fin 2) ℝ) = (Dr m)⁻¹ * (ε : GL (Fin 2) ℝ) * Dr m := by
  rw [mul_assoc, ← downSL_coe ε h, inv_mul_cancel_left]

theorem downSL_eq_conjElemN (ε : SL(2, ℤ)) (h : (m : ℤ) ∣ ε 0 1) :
    ((downSL ε h : SL(2, ℤ)) : GL (Fin 2) ℝ) = conjElemN m ε := by
  rw [downSL_eq, conjElemN_eq]

theorem downSL_apply_10 (ε : SL(2, ℤ)) (h : (m : ℤ) ∣ ε 0 1) : (downSL ε h) 1 0 = (m : ℤ) * ε 1 0 := rfl

theorem downSL_apply_11 (ε : SL(2, ℤ)) (h : (m : ℤ) ∣ ε 0 1) : (downSL ε h) 1 1 = ε 1 1 := rfl

theorem σ_conjElemN_apply (γ : SL(2, ℤ)) (z : ℂ) : UpperHalfPlane.σ (conjElemN m γ) z = z := by
  rw [UpperHalfPlane.σ, if_pos (by rw [det_conjElemN_val]; exact one_pos)]
  rfl

omit [NeZero m] in
theorem one_mem_strictPeriods (N : ℕ) (H : Subgroup (ZMod N)ˣ) :
    (1 : ℝ) ∈ ((CohCarrier.GammaH N H : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
  rw [Subgroup.strictPeriods_eq_zmultiples_one_of_T_mem (translation_mem_GammaH _ _)]
  exact AddSubgroup.mem_zmultiples _

omit [NeZero m] in

theorem coeffMap_intSeriesC (p : PowerSeries ℤ) :
    coeffMap (algebraMap ℚ ℂ) (intSeriesC ℚ p) = intSeriesC ℂ p := by
  ext n
  simp only [intSeriesC, coeffMap_coeff, PowerSeries.coeff_coe]
  split_ifs
  · exact map_zero _
  · simp [PowerSeries.coeff_map]

end K2A
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_intCast_apply_eq_one_of_isLevelAutAt_one_of_eq_levelH_inf_ker.K2A"

end
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_intCast_apply_eq_one_of_isLevelAutAt_one_of_eq_levelH_inf_ker.K2A"

open K2A in

theorem solution
    (q : ℕ) [Fact q.Prime] (hq2 : q ≠ 2) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (ℓg : ℕ) (hℓgM' : ℓg ∣ M')
    (L : Type) [Field L] [CharZero L]
    (ξ : L) (hξ : IsPrimitiveRoot ξ q)
    (hι : ∃ ι : L →+* ℂ, ι ξ = Complex.exp (2 * Real.pi * Complex.I / q))
    (H₁ : Subgroup (ZMod (q ^ 2 * M'))ˣ)
    (hH₁ : H₁ = ModularCurve.FullLevel.levelH q M' ⊓ (ZMod.unitsMap (Dvd.dvd.mul_left hℓgM' (q ^ 2))).ker)
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L
      (ModularCurve.xHFunctionField (q ^ 2 * M') H₁)) :
    ∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma q → γ ∈ CongruenceSubgroup.Gamma0 M' →
      ModularCurve.FullLevel.IsLevelAutAt L q ξ q (q ^ 2 * M') H₁ γ K 1 →
      ((γ 1 1 : ℤ) : ZMod ℓg) = 1 := by
  intro γ hγq hγ0 hid
  classical
  by_contra hne
  haveI hq0 : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
  obtain ⟨ι, hι⟩ := hι
  subst hK

  obtain ⟨h00, h01, h10, h11⟩ := CongruenceSubgroup.Gamma_mem.mp hγq
  have hd01 : (q : ℤ) ∣ γ 0 1 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h01
  have hd10q : (q : ℤ) ∣ γ 1 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h10
  have hd10M : (M' : ℤ) ∣ γ 1 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (CongruenceSubgroup.Gamma0_mem.mp hγ0)
  have hcop : IsCoprime (q : ℤ) (M' : ℤ) := by
    rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd_natCast_natCast]
    exact (Nat.Prime.coprime_iff_not_dvd Fact.out).mpr hqM'

  set γ' : SL(2, ℤ) := K2A.downSL (m := q) γ hd01 with hγ'def
  have hγ'0 : γ' ∈ CongruenceSubgroup.Gamma0 (q ^ 2 * M') := by
    rw [CongruenceSubgroup.Gamma0_mem, hγ'def, K2A.downSL_apply_10, ZMod.intCast_zmod_eq_zero_iff_dvd]
    obtain ⟨e, he⟩ := hcop.mul_dvd hd10q hd10M
    exact ⟨e, by rw [he]; push_cast; ring⟩
  have hγ'GL : ((γ' : SL(2, ℤ)) : GL (Fin 2) ℝ) = conjElemN q γ := K2A.downSL_eq_conjElemN γ hd01
  have hγ'11 : (γ' 1 1 : ℤ) = γ 1 1 := K2A.downSL_apply_11 γ hd01

  have hval : ((CohCarrier.gamma0Units (q ^ 2 * M') ⟨γ', hγ'0⟩ : (ZMod (q ^ 2 * M'))ˣ) : ZMod (q ^ 2 * M')) =
      ((γ 1 1 : ℤ) : ZMod (q ^ 2 * M')) := by
    simp [CohCarrier.gamma0Units, Gamma0Map, hγ'11]
  have hnot : CohCarrier.gamma0Units (q ^ 2 * M') ⟨γ', hγ'0⟩ ∉
      H₁ ⊔ Subgroup.zpowers (-1 : (ZMod (q ^ 2 * M'))ˣ) := by
    intro hmem
    rw [Subgroup.mem_sup] at hmem
    obtain ⟨y, hy, z, hz, hyz⟩ := hmem
    rw [Subgroup.mem_zpowers_iff] at hz
    obtain ⟨n, rfl⟩ := hz
    rw [hH₁, Subgroup.mem_inf, mem_levelH_iff, MonoidHom.mem_ker] at hy
    obtain ⟨hyq, hyℓ⟩ := hy
    have hyq' : ZMod.castHom (dvd_sq_mul q M') (ZMod q) (y : ZMod (q ^ 2 * M')) = 1 := by
      have := congrArg (fun u : (ZMod q)ˣ => (u : ZMod q)) hyq
      simpa [ZMod.unitsMap_def] using this
    have hyℓ' : ZMod.castHom (Dvd.dvd.mul_left hℓgM' (q ^ 2)) (ZMod ℓg) (y : ZMod (q ^ 2 * M')) = 1 := by
      have := congrArg (fun u : (ZMod ℓg)ˣ => (u : ZMod ℓg)) hyℓ
      simpa [ZMod.unitsMap_def] using this
    rcases Int.even_or_odd n with hn | hn
    ·
      rw [hn.neg_one_zpow, mul_one] at hyz
      apply hne
      have := hyℓ'
      rw [hyz, hval, map_intCast] at this
      exact this
    ·
      rw [hn.neg_one_zpow, mul_neg_one, neg_eq_iff_eq_neg] at hyz
      have := hyq'
      rw [hyz, Units.val_neg, map_neg, hval, map_intCast, h11] at this

      have h2 : ((2 : ℕ) : ZMod q) = 0 := by
        have e : (1 : ZMod q) + 1 = 0 := by
          calc (1 : ZMod q) + 1 = -1 + 1 := by rw [this]
            _ = 0 := by ring
        exact_mod_cast e
      rw [CharP.cast_eq_zero_iff (ZMod q) q 2] at h2
      exact hq2 ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).mp h2)

  have hMC : ((q ^ 2 * M' : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (NeZero.ne (q ^ 2 * M'))
  obtain ⟨k, f, g, f₁, g₁, pf, pg, pf₁, pg₁, c, hc, hf, hg, hf₁, hg₁, ef, eg, hg0, hg₁0, hneq⟩ :=
    ModularCurve.exists_intSeriesC_mul_ne_of_gamma0Units_not_mem ℂ (q ^ 2 * M') hMC H₁ γ' hγ'0 hnot

  have hgℚ : intSeriesC ℚ pg ≠ 0 := by
    intro h0
    apply hg0
    rw [← K2A.coeffMap_intSeriesC, h0, map_zero]
  let x : ↥(laurentBaseChange L (xHFunctionField (q ^ 2 * M') H₁)) :=
    ⟨coeffEmb L (intSeriesC ℚ pf / intSeriesC ℚ pg),
      coeffEmb_mem_laurentBaseChange L (div_mem_qExpFunctionFieldC f g hf hg hgℚ)⟩
  have key := hid k f g pf pg hf hg hgℚ x rfl ι hι
  rw [AlgEquiv.one_apply] at key

  have hx : coeffMap ι ((x : ↥(laurentBaseChange L (xHFunctionField (q ^ 2 * M') H₁))) : LaurentSeries L) =
      intSeriesC ℂ pf / intSeriesC ℂ pg := by
    show coeffMap ι (coeffEmb L (intSeriesC ℚ pf / intSeriesC ℚ pg)) = _
    rw [coeffEmb, coeffMap_coeffMap, coeffMap_congr (Subsingleton.elim _ (algebraMap ℚ ℂ)), map_div₀,
      K2A.coeffMap_intSeriesC, K2A.coeffMap_intSeriesC]

  have hper := K2A.one_mem_strictPeriods (q ^ 2 * M') H₁
  have ef' : ((⇑f : UpperHalfPlane → ℂ) ∣[k] conjElemN q γ) = c⁻¹ • (⇑f₁ : UpperHalfPlane → ℂ) := by
    rw [← hγ'GL, ef, smul_smul, inv_mul_cancel₀ hc, one_smul]
  have eg' : ((⇑g : UpperHalfPlane → ℂ) ∣[k] conjElemN q γ) = c⁻¹ • (⇑g₁ : UpperHalfPlane → ℂ) := by
    rw [← hγ'GL, eg, smul_smul, inv_mul_cancel₀ hc, one_smul]
  rw [hx, ef', eg', ModularForm.qExpansion_smul one_pos hper c⁻¹ f₁, ModularForm.qExpansion_smul one_pos hper c⁻¹ g₁,
    ← hf₁, ← hg₁, PowerSeries.smul_eq_C_mul, PowerSeries.smul_eq_C_mul, map_mul, map_mul,
    HahnSeries.ofPowerSeries_C] at key

  apply hneq
  have hC : (HahnSeries.C (c⁻¹) : LaurentSeries ℂ) ≠ 0 := HahnSeries.C_ne_zero (inv_ne_zero hc)
  have key2 : intSeriesC ℂ pf / intSeriesC ℂ pg * intSeriesC ℂ pg₁ = intSeriesC ℂ pf₁ := by
    have := key
    rw [mul_left_comm] at this
    exact mul_left_cancel₀ hC this
  rw [← key2]
  field_simp

end S_ModularCurve_FullLevel_intCast_apply_eq_one_of_isLevelAutAt_one_of_eq_levelH_inf_ker
end P2MW
export P2MW.S_ModularCurve_FullLevel_intCast_apply_eq_one_of_isLevelAutAt_one_of_eq_levelH_inf_ker (solution)
