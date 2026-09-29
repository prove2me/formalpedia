-- Prove2me | solution 1 for ModularCurve.FullLevel.qExpand_mem_and_apply_eq_of_isLevelAutAt_of_mem_Gamma
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/e6c6d76c-f251-522b-9888-062f04b6d2f2

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_ModularCurve_FullLevelLevelAutAt
import Definitions.Def_ModularForm_HeckeOperator
import Theorems.Thm_UpperHalfPlane_qCoeff_comp_heckeDiagMatrix_smul
import Theorems.Thm_ModularCurve_coeffEmb_qExpand
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_qExpand_mem_and_apply_eq_of_isLevelAutAt_of_mem_Gamma

open scoped MatrixGroups ModularForm
open Matrix ModularCurve ModularCurve.FullLevel CongruenceSubgroup
open scoped Pointwise

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace W1xLE
variable (m : ℕ) [NeZero m]

theorem mpos : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
theorem mne : (m : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne m
theorem mneZ : (m : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne m

abbrev Dr : GL (Fin 2) ℝ := ModularForm.heckeDiagMatrix m

@[scoped simp] theorem Dr_coe : ((Dr m : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = !![(m : ℝ), 0; 0, 1] :=
  ModularForm.val_heckeDiagMatrix (NeZero.ne m)

@[scoped simp] theorem conjElemN_coe (γ : SL(2, ℤ)) : ((conjElemN m γ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
    !![((γ 0 0 : ℤ) : ℝ), ((γ 0 1 : ℤ) : ℝ) / m; (m : ℝ) * ((γ 1 0 : ℤ) : ℝ), ((γ 1 1 : ℤ) : ℝ)] := rfl

theorem Dr_mul_conjElem (γ : SL(2, ℤ)) : Dr m * conjElemN m γ = (γ : GL (Fin 2) ℝ) * Dr m := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  simp only [Matrix.GeneralLinearGroup.coe_mul, Dr_coe, conjElemN_coe]
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, mul_div_assoc', mul_div_cancel_left₀ _ (mne m), mul_comm]

theorem conjElemN_eq (γ : SL(2, ℤ)) : conjElemN m γ = (Dr m)⁻¹ * (γ : GL (Fin 2) ℝ) * Dr m := by
  rw [mul_assoc, ← Dr_mul_conjElem, inv_mul_cancel_left]

theorem det_coeSL (γ : SL(2, ℤ)) : ((γ : GL (Fin 2) ℝ)).det = 1 := by
  ext
  simp

theorem det_conjElemN (γ : SL(2, ℤ)) : (conjElemN m γ).det = 1 := by
  rw [conjElemN_eq, map_mul, map_mul, map_inv, det_coeSL, mul_one, inv_mul_cancel]

theorem det_conjElemN_val (γ : SL(2, ℤ)) : ((conjElemN m γ).det : ℝ) = 1 := by
  rw [det_conjElemN]; rfl

theorem σ_conjElemN_apply (γ : SL(2, ℤ)) (z : ℂ) : UpperHalfPlane.σ (conjElemN m γ) z = z := by
  rw [UpperHalfPlane.σ, if_pos (by rw [det_conjElemN_val]; exact one_pos)]
  rfl

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

section GH
variable (m : ℕ) [NeZero m] (M' : ℕ)

abbrev GH : Subgroup SL(2, ℤ) := CohCarrier.GammaH (m ^ 2 * M') (levelH m M')

abbrev Γ : Subgroup (GL (Fin 2) ℝ) := ((GH m M' : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))

variable {m M'}

theorem mem_GH_iff (A : SL(2, ℤ)) :
    A ∈ GH m M' ↔ ((A 1 0 : ℤ) : ZMod (m ^ 2 * M')) = 0 ∧ ((A 1 1 : ℤ) : ZMod m) = 1 := by
  rw [GH, CohCarrier.mem_GammaH_iff]
  constructor
  · rintro ⟨hA, hH⟩
    refine ⟨Gamma0_mem.mp hA, ?_⟩
    rw [mem_levelH_iff] at hH
    have := congrArg (fun u : (ZMod m)ˣ => (u : ZMod m)) hH
    simpa [ZMod.unitsMap_def, CohCarrier.gamma0Units, Gamma0Map] using this
  · rintro ⟨h10, h11⟩
    refine ⟨Gamma0_mem.mpr h10, ?_⟩
    rw [mem_levelH_iff]
    ext
    simp [ZMod.unitsMap_def, CohCarrier.gamma0Units, Gamma0Map, h11]

scoped instance GH_finiteIndex (m M' : ℕ) [NeZero m] [NeZero M'] : (GH m M').FiniteIndex :=
  Subgroup.finiteIndex_of_le (Gamma1_le_GammaH _ _)

omit [NeZero m] in
theorem one_mem_strictPeriods : (1 : ℝ) ∈ (Γ m M').strictPeriods := by
  rw [Subgroup.strictPeriods_eq_zmultiples_one_of_T_mem (translation_mem_GammaH _ _)]
  exact AddSubgroup.mem_zmultiples _

end GH

section Pair

variable {q : ℕ} [NeZero q] {M' : ℕ} {ℓ : ℕ} [NeZero ℓ]

theorem Dr_mul_Dr : Dr (q * ℓ) = Dr q * Dr ℓ := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  simp only [Matrix.GeneralLinearGroup.coe_mul, Dr_coe]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem ell_dvd_of_mem {γ' : SL(2, ℤ)} (h : γ' ∈ GH (q * ℓ) M') : (ℓ : ℤ) ∣ γ' 1 0 := by
  obtain ⟨h10, _⟩ := (mem_GH_iff γ').mp h
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h10
  exact dvd_trans ⟨q * q * ℓ * M', by push_cast; ring⟩ h10

theorem upSL_mem {γ' : SL(2, ℤ)} (h : γ' ∈ GH (q * ℓ) M') : upSL (m := ℓ) γ' (ell_dvd_of_mem h) ∈ GH q M' := by
  obtain ⟨h10, h11⟩ := (mem_GH_iff γ').mp h
  rw [mem_GH_iff]
  constructor
  · show ((γ' 1 0 / ℓ : ℤ) : ZMod (q ^ 2 * M')) = 0
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h10 ⊢
    obtain ⟨c, hc⟩ := h10
    rw [hc]
    refine ⟨ℓ * c, ?_⟩
    push_cast
    rw [show ((q : ℤ) * ℓ) ^ 2 * M' * c = ℓ * ((q : ℤ) ^ 2 * M' * (ℓ * c)) by ring,
      Int.mul_ediv_cancel_left _ (mneZ ℓ)]
  · show ((γ' 1 1 : ℤ) : ZMod q) = 1
    have := congrArg (ZMod.castHom (dvd_mul_right q ℓ) (ZMod q)) h11
    rwa [map_intCast, map_one] at this

theorem le_conj_ell : Γ (q * ℓ) M' ≤ ConjAct.toConjAct (Dr ℓ)⁻¹ • Γ q M' := by
  rintro x ⟨γ', hγ', rfl⟩
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← ConjAct.toConjAct_inv, inv_inv,
    ConjAct.toConjAct_smul]
  refine ⟨upSL γ' (ell_dvd_of_mem hγ'), upSL_mem hγ', ?_⟩
  rw [eq_mul_inv_iff_mul_eq]
  exact upSL_coe γ' _

theorem q_dvd_01 {δ : SL(2, ℤ)} (hδ : δ ∈ Gamma q) : (q : ℤ) ∣ δ 0 1 :=
  (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (Gamma_mem.mp hδ).2.1

variable (hqM' : Nat.Coprime q M')
include hqM'

theorem downSL_mem {δ : SL(2, ℤ)} (hδ : δ ∈ Gamma q) (hδ0 : δ ∈ Gamma0 M') :
    downSL (m := q) δ (q_dvd_01 hδ) ∈ GH q M' := by
  obtain ⟨-, -, h10, h11⟩ := Gamma_mem.mp hδ
  rw [mem_GH_iff]
  refine ⟨?_, h11⟩
  show ((((q : ℤ) * δ 1 0 : ℤ)) : ZMod (q ^ 2 * M')) = 0
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
  have hq : (q : ℤ) ∣ δ 1 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h10
  have hM : (M' : ℤ) ∣ δ 1 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (Gamma0_mem.mp hδ0)
  have hcop : IsCoprime (q : ℤ) (M' : ℤ) := by
    rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd_natCast_natCast]
    exact hqM'
  obtain ⟨c, hc⟩ := hcop.mul_dvd hq hM
  exact ⟨c, by rw [hc]; push_cast; ring⟩

omit hqM' in
theorem conjElemN_eq_downSL {δ : SL(2, ℤ)} (hδ : δ ∈ Gamma q) :
    conjElemN q δ = ((downSL (m := q) δ (q_dvd_01 hδ) : SL(2, ℤ)) : GL (Fin 2) ℝ) := by
  rw [conjElemN_eq, mul_assoc, ← downSL_coe δ (q_dvd_01 hδ), inv_mul_cancel_left]

theorem slash_Dr_slash_conjElemN {k : ℤ} (f : ModularForm (Γ q M') k) {δ : SL(2, ℤ)}
    (hδ : δ ∈ Gamma q) (hδ0 : δ ∈ Gamma0 M') :
    ((⇑f : UpperHalfPlane → ℂ) ∣[k] Dr ℓ) ∣[k] conjElemN (q * ℓ) δ = (⇑f : UpperHalfPlane → ℂ) ∣[k] Dr ℓ := by
  have hgrp : Dr ℓ * conjElemN (q * ℓ) δ = conjElemN q δ * Dr ℓ := by
    rw [conjElemN_eq, conjElemN_eq, Dr_mul_Dr]; group
  rw [← SlashAction.slash_mul, hgrp, SlashAction.slash_mul, conjElemN_eq_downSL hδ]
  congr 1
  exact SlashInvariantFormClass.slash_action_eq f _ (Subgroup.mem_map_of_mem _ (downSL_mem hqM' hδ hδ0))

end Pair

section Stretch

open UpperHalfPlane Function

variable {Γ₁ Γ₂ : Subgroup SL(2, ℤ)} [Γ₁.FiniteIndex] {ℓ : ℕ} {k : ℤ}
variable (hle : (Γ₂ : Subgroup (GL (Fin 2) ℝ)) ≤
  ConjAct.toConjAct (ModularForm.heckeDiagMatrix ℓ)⁻¹ • (Γ₁ : Subgroup (GL (Fin 2) ℝ)))

def stretch (hℓ : ℓ ≠ 0) (f : ModularForm (Γ₁ : Subgroup (GL (Fin 2) ℝ)) k) :
    ModularForm (Γ₂ : Subgroup (GL (Fin 2) ℝ)) k :=
  ((ℓ : ℂ) ^ (k - 1))⁻¹ • restrictForm hle (ModularForm.translate f (ModularForm.heckeDiagMatrix ℓ))

theorem coe_stretch_eq_smul (hℓ : ℓ ≠ 0) (f : ModularForm (Γ₁ : Subgroup (GL (Fin 2) ℝ)) k) :
    (⇑(stretch hle hℓ f) : ℍ → ℂ) =
      ((ℓ : ℂ) ^ (k - 1))⁻¹ • ((⇑f : ℍ → ℂ) ∣[k] ModularForm.heckeDiagMatrix ℓ) := by
  rw [stretch, ModularForm.IsGLPos.coe_smul, coe_restrictForm, ModularForm.coe_translate]

theorem stretch_apply (hℓ : ℓ ≠ 0) (f : ModularForm (Γ₁ : Subgroup (GL (Fin 2) ℝ)) k) (τ : ℍ) :
    stretch hle hℓ f τ = f (ModularForm.heckeDiagMatrix ℓ • τ) := by
  have hpk : ((ℓ : ℂ) ^ (k - 1)) ≠ 0 := zpow_ne_zero _ (Nat.cast_ne_zero.mpr hℓ)
  have := congrFun (coe_stretch_eq_smul hle hℓ f) τ
  rw [this, Pi.smul_apply, ModularForm.slash_heckeDiagMatrix_apply k hℓ, smul_eq_mul, ← mul_assoc,
    inv_mul_cancel₀ hpk, one_mul]

theorem coe_stretch (hℓ : ℓ ≠ 0) (f : ModularForm (Γ₁ : Subgroup (GL (Fin 2) ℝ)) k) :
    (⇑(stretch hle hℓ f) : ℍ → ℂ) = fun τ => f (ModularForm.heckeDiagMatrix ℓ • τ) :=
  funext (stretch_apply hle hℓ f)

private theorem _root_.W1xLE.periodic_comp_ofComplex (hT : ModularGroup.T ∈ Γ₁)
    (f : ModularForm (Γ₁ : Subgroup (GL (Fin 2) ℝ)) k) :
    Periodic ((⇑f : ℍ → ℂ) ∘ ofComplex) 1 := by
  have h1 : (1 : ℝ) ∈ (Γ₁ : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
    rw [Subgroup.strictPeriods_eq_zmultiples_one_of_T_mem hT]
    exact AddSubgroup.mem_zmultiples 1
  exact SlashInvariantFormClass.periodic_comp_ofComplex f h1

p2m_export "W1xLE" "periodic_comp_ofComplex"

theorem qCoeff_stretch (hT : ModularGroup.T ∈ Γ₁) (hℓ : ℓ ≠ 0)
    (f : ModularForm (Γ₁ : Subgroup (GL (Fin 2) ℝ)) k) (n : ℕ) :
    ModularFormClass.qCoeff (⇑(stretch hle hℓ f)) n
      = if ℓ ∣ n then ModularFormClass.qCoeff (⇑f) (n / ℓ) else 0 := by
  rw [coe_stretch]
  exact UpperHalfPlane.qCoeff_comp_heckeDiagMatrix_smul (periodic_comp_ofComplex hT f) f.holo'
    (ModularFormClass.bdd_at_infty f) hℓ n

def expandPS (ℓ : ℕ) (p : PowerSeries ℤ) : PowerSeries ℤ :=
  PowerSeries.mk fun n => if ℓ ∣ n then PowerSeries.coeff (n / ℓ) p else 0

@[scoped simp] theorem coeff_expandPS (ℓ : ℕ) (p : PowerSeries ℤ) (n : ℕ) :
    PowerSeries.coeff n (expandPS ℓ p) = if ℓ ∣ n then PowerSeries.coeff (n / ℓ) p else 0 :=
  PowerSeries.coeff_mk _ _

theorem isIntegralQExp_stretch (hT : ModularGroup.T ∈ Γ₁) (hℓ : ℓ ≠ 0)
    (f : ModularForm (Γ₁ : Subgroup (GL (Fin 2) ℝ)) k) {p : PowerSeries ℤ}
    (hp : ModularCurve.IsIntegralQExp f p) :
    ModularCurve.IsIntegralQExp (stretch hle hℓ f) (expandPS ℓ p) := by
  rw [ModularCurve.isIntegralQExp_iff]
  intro n
  have h := qCoeff_stretch hle hT hℓ f n
  simp only [ModularFormClass.qCoeff] at h
  rw [h, coeff_expandPS]
  split_ifs with hdvd
  · exact hp.coeff (n / ℓ)
  · simp

theorem intSeriesC_expandPS (K : Type*) [Field K] (ℓ : ℕ) [NeZero ℓ] (p : PowerSeries ℤ) :
    ModularCurve.intSeriesC K (expandPS ℓ p)
      = ModularCurve.qExpand K ℓ (ModularCurve.intSeriesC K p) := by
  have hℓ : ℓ ≠ 0 := NeZero.ne ℓ
  ext m
  simp only [ModularCurve.intSeriesC]
  by_cases hdvd : (ℓ : ℤ) ∣ m
  · obtain ⟨m', rfl⟩ := hdvd
    rw [ModularCurve.qExpand_coeff_mul, PowerSeries.coeff_coe, PowerSeries.coeff_coe]
    by_cases hm' : m' < 0
    · have : (ℓ : ℤ) * m' < 0 :=
        mul_neg_of_pos_of_neg (by exact_mod_cast Nat.pos_of_ne_zero hℓ) hm'
      rw [if_pos this, if_pos hm']
    · have hm'0 : 0 ≤ m' := le_of_not_gt hm'
      have hprod : ¬ (ℓ : ℤ) * m' < 0 := not_lt.mpr (mul_nonneg (by positivity) hm'0)
      rw [if_neg hprod, if_neg hm', PowerSeries.coeff_map, PowerSeries.coeff_map, coeff_expandPS]
      have habs : ((ℓ : ℤ) * m').natAbs = ℓ * m'.natAbs := by
        rw [Int.natAbs_mul, Int.natAbs_natCast]
      rw [habs, if_pos (dvd_mul_right ℓ _), Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hℓ)]
  · rw [ModularCurve.qExpand_coeff_of_not_dvd ℓ _ hdvd, PowerSeries.coeff_coe]
    split_ifs with hm
    · rfl
    · rw [PowerSeries.coeff_map, coeff_expandPS]
      have : ¬ ℓ ∣ m.natAbs := by
        intro h
        apply hdvd
        have hm0 : 0 ≤ m := le_of_not_gt hm
        rw [← Int.natAbs_of_nonneg hm0]
        exact_mod_cast h
      rw [if_neg this, map_zero]

end Stretch

section Emb

open UpperHalfPlane HahnSeries

variable {L : Type} [Field L] [CharZero L]

def qC (F : ℍ → ℂ) : LaurentSeries ℂ := ofPowerSeries ℤ ℂ (qExpansion 1 F)

abbrev ιC : LaurentSeries ℚ →+* LaurentSeries ℂ := coeffMap (algebraMap ℚ ℂ)

variable (ι₀ : L →+* ℂ)

abbrev ιB : LaurentSeries L →+* LaurentSeries ℂ := coeffMap ι₀

theorem ιB_injective : Function.Injective (ιB ι₀) := fun x y h =>
  HahnSeries.ext (funext fun n => ι₀.injective (by
    have := congrArg (fun z : LaurentSeries ℂ => z.coeff n) h
    simpa using this))

theorem ιB_coeffEmb (x : LaurentSeries ℚ) : ιB ι₀ (coeffEmb L x) = ιC x := by
  rw [coeffEmb, coeffMap_coeffMap]
  exact coeffMap_congr (Subsingleton.elim _ _) x

theorem C_eq_algebraMap (c : L) : (HahnSeries.C c : LaurentSeries L) = algebraMap L (LaurentSeries L) c := by
  rw [algebraMap_laurentSeries_eq_single, HahnSeries.C_apply]

theorem ιC_intSeriesC {F : ℍ → ℂ} {p : PowerSeries ℤ} (h : IsIntegralQExp F p) :
    ιC (intSeriesC ℚ p) = qC F := by
  rw [qC, ← h]
  ext n
  simp only [intSeriesC, coeffMap_coeff, PowerSeries.coeff_coe]
  split_ifs
  · exact map_zero _
  · simp [PowerSeries.coeff_map]

abbrev eq (m : ℕ) : ℂ := Complex.exp (2 * Real.pi * Complex.I / m)

variable {m : ℕ} [NeZero m]

variable (L) in
theorem exists_emb [IsCyclotomicExtension {m} ℚ L] (ξ : L) (hξ : IsPrimitiveRoot ξ m) :
    ∃ ι₀ : L →+* ℂ, ι₀ ξ = eq m := by
  haveI : Module.Finite ℚ L := IsCyclotomicExtension.finite_of_singleton (n := m) ℚ L
  haveI : Algebra.IsAlgebraic ℚ L := Algebra.IsAlgebraic.of_finite ℚ L
  have hmin : minpoly ℚ ξ = Polynomial.cyclotomic m ℚ :=
    (Polynomial.cyclotomic_eq_minpoly_rat hξ (mpos m)).symm
  have hroot : eq m ∈ (minpoly ℚ ξ).rootSet ℂ := by
    rw [hmin, Polynomial.mem_rootSet]
    refine ⟨Polynomial.cyclotomic_ne_zero m ℚ, ?_⟩
    rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, Polynomial.map_cyclotomic]
    exact (Polynomial.isRoot_cyclotomic_iff.mpr (Complex.isPrimitiveRoot_exp m (NeZero.ne m))).eq_zero
  rw [← Algebra.IsAlgebraic.range_eval_eq_rootSet_minpoly ℂ ξ] at hroot
  obtain ⟨ψ, hψ⟩ := hroot
  exact ⟨ψ.toRingHom, hψ⟩

end Emb

section Main

open UpperHalfPlane IntermediateField HahnSeries
open scoped ModularForm

variable {q : ℕ} [NeZero q] {M' : ℕ} {ℓ : ℕ} [NeZero ℓ] (hqM' : Nat.Coprime q M')
  {L : Type} [Field L] [CharZero L] (ξ : L) (ι₀ : L →+* ℂ) (hι₀ : ι₀ ξ = eq (q * ℓ))

abbrev KL (L : Type) [Field L] [CharZero L] (q ℓ M' : ℕ) : IntermediateField L (LaurentSeries L) :=
  laurentBaseChange L (xHFunctionField ((q * ℓ) ^ 2 * M') (levelH (q * ℓ) M'))

variable (q M' ℓ) in

def P (x : LaurentSeries L) : Prop :=
  qExpand L ℓ x ∈ KL L q ℓ M' ∧
    ∀ w : KL L q ℓ M', (w : LaurentSeries L) = qExpand L ℓ x →
      ∀ γ : SL(2, ℤ), γ ∈ Gamma q → γ ∈ Gamma0 M' →
        ∀ τ : KL L q ℓ M' ≃ₐ[L] KL L q ℓ M',
          IsLevelAutAt L (q * ℓ) ξ (q * ℓ) ((q * ℓ) ^ 2 * M') (levelH (q * ℓ) M') γ⁻¹ (KL L q ℓ M') τ →
            τ w = w

variable {ξ}

theorem P.mk' {x : LaurentSeries L} (hmem : qExpand L ℓ x ∈ KL L q ℓ M')
    (hfix : ∀ γ : SL(2, ℤ), γ ∈ Gamma q → γ ∈ Gamma0 M' →
        ∀ τ : KL L q ℓ M' ≃ₐ[L] KL L q ℓ M',
          IsLevelAutAt L (q * ℓ) ξ (q * ℓ) ((q * ℓ) ^ 2 * M') (levelH (q * ℓ) M') γ⁻¹ (KL L q ℓ M') τ →
            τ ⟨qExpand L ℓ x, hmem⟩ = ⟨qExpand L ℓ x, hmem⟩) :
    P q M' ℓ ξ x := by
  refine ⟨hmem, fun w hw γ hγ hγ0 τ hτ => ?_⟩
  have e : w = ⟨qExpand L ℓ x, hmem⟩ := Subtype.ext hw
  rw [e]
  exact hfix γ hγ hγ0 τ hτ

theorem P.add {x y : LaurentSeries L} (hx : P q M' ℓ ξ x) (hy : P q M' ℓ ξ y) : P q M' ℓ ξ (x + y) := by
  have hmem : qExpand L ℓ (x + y) ∈ KL L q ℓ M' := by rw [map_add]; exact add_mem hx.1 hy.1
  refine P.mk' hmem fun γ hγ hγ0 τ hτ => ?_
  have e : (⟨qExpand L ℓ (x + y), hmem⟩ : KL L q ℓ M') = ⟨qExpand L ℓ x, hx.1⟩ + ⟨qExpand L ℓ y, hy.1⟩ :=
    Subtype.ext (by simp [map_add])
  rw [e, map_add, hx.2 _ rfl γ hγ hγ0 τ hτ, hy.2 _ rfl γ hγ hγ0 τ hτ]

theorem P.mul {x y : LaurentSeries L} (hx : P q M' ℓ ξ x) (hy : P q M' ℓ ξ y) : P q M' ℓ ξ (x * y) := by
  have hmem : qExpand L ℓ (x * y) ∈ KL L q ℓ M' := by rw [map_mul]; exact mul_mem hx.1 hy.1
  refine P.mk' hmem fun γ hγ hγ0 τ hτ => ?_
  have e : (⟨qExpand L ℓ (x * y), hmem⟩ : KL L q ℓ M') = ⟨qExpand L ℓ x, hx.1⟩ * ⟨qExpand L ℓ y, hy.1⟩ :=
    Subtype.ext (by simp [map_mul])
  rw [e, map_mul, hx.2 _ rfl γ hγ hγ0 τ hτ, hy.2 _ rfl γ hγ hγ0 τ hτ]

theorem P.neg {x : LaurentSeries L} (hx : P q M' ℓ ξ x) : P q M' ℓ ξ (-x) := by
  have hmem : qExpand L ℓ (-x) ∈ KL L q ℓ M' := by rw [map_neg]; exact neg_mem hx.1
  refine P.mk' hmem fun γ hγ hγ0 τ hτ => ?_
  have e : (⟨qExpand L ℓ (-x), hmem⟩ : KL L q ℓ M') = -⟨qExpand L ℓ x, hx.1⟩ :=
    Subtype.ext (by simp [map_neg])
  rw [e, map_neg, hx.2 _ rfl γ hγ hγ0 τ hτ]

theorem P.inv {x : LaurentSeries L} (hx : P q M' ℓ ξ x) : P q M' ℓ ξ x⁻¹ := by
  have hmem : qExpand L ℓ x⁻¹ ∈ KL L q ℓ M' := by rw [map_inv₀]; exact inv_mem hx.1
  refine P.mk' hmem fun γ hγ hγ0 τ hτ => ?_
  have e : (⟨qExpand L ℓ x⁻¹, hmem⟩ : KL L q ℓ M') = (⟨qExpand L ℓ x, hx.1⟩ : KL L q ℓ M')⁻¹ :=
    Subtype.ext (by simp [map_inv₀])
  rw [e, map_inv₀, hx.2 _ rfl γ hγ hγ0 τ hτ]

theorem P.one : P q M' ℓ ξ (1 : LaurentSeries L) := by
  have hmem : qExpand L ℓ (1 : LaurentSeries L) ∈ KL L q ℓ M' := by rw [map_one]; exact one_mem _
  refine P.mk' hmem fun γ hγ hγ0 τ hτ => ?_
  have e : (⟨qExpand L ℓ 1, hmem⟩ : KL L q ℓ M') = 1 := Subtype.ext (by simp)
  rw [e, map_one]

theorem P_algebraMap (c : L) : P q M' ℓ ξ (algebraMap L (LaurentSeries L) c) := by
  have hq : qExpand L ℓ (algebraMap L (LaurentSeries L) c) = algebraMap L (LaurentSeries L) c := by
    rw [← C_eq_algebraMap, qExpand_C]
  have hmem : qExpand L ℓ (algebraMap L (LaurentSeries L) c) ∈ KL L q ℓ M' := by
    rw [hq]; exact IntermediateField.algebraMap_mem _ _
  refine P.mk' hmem fun γ hγ hγ0 τ hτ => ?_
  have e : (⟨qExpand L ℓ (algebraMap L (LaurentSeries L) c), hmem⟩ : KL L q ℓ M') =
      algebraMap L (KL L q ℓ M') c :=
    Subtype.ext (by change qExpand L ℓ (algebraMap L (LaurentSeries L) c) = _; rw [hq]; rfl)
  rw [e, AlgEquiv.commutes]

section Gen

variable [NeZero M']
include hqM' hι₀

theorem P.gen {y : LaurentSeries ℚ} (hy : y ∈ intFormRatiosC ℚ (GH q M')) : P q M' ℓ ξ (coeffEmb L y) := by
  have hℓ : ℓ ≠ 0 := NeZero.ne ℓ
  obtain ⟨k, f, g, pf, pg, hf, hg, hg0, rfl⟩ := hy

  set f' : ModularForm (Γ (q * ℓ) M') k := stretch le_conj_ell hℓ f with hf'def
  set g' : ModularForm (Γ (q * ℓ) M') k := stretch le_conj_ell hℓ g with hg'def
  have hT : ModularGroup.T ∈ GH q M' := translation_mem_GammaH _ _
  have hf' : IsIntegralQExp f' (expandPS ℓ pf) := isIntegralQExp_stretch le_conj_ell hT hℓ f hf
  have hg' : IsIntegralQExp g' (expandPS ℓ pg) := isIntegralQExp_stretch le_conj_ell hT hℓ g hg
  have hg0' : intSeriesC ℚ (expandPS ℓ pg) ≠ 0 := by
    rw [intSeriesC_expandPS]
    exact fun h => hg0 (ModularCurve.qExpand_injective ℓ (by rw [h, map_zero]))
  have hser : qExpand L ℓ (coeffEmb L (intSeriesC ℚ pf / intSeriesC ℚ pg)) =
      coeffEmb L (intSeriesC ℚ (expandPS ℓ pf) / intSeriesC ℚ (expandPS ℓ pg)) := by
    rw [← ModularCurve.coeffEmb_qExpand, map_div₀, intSeriesC_expandPS, intSeriesC_expandPS]
  have hmem : qExpand L ℓ (coeffEmb L (intSeriesC ℚ pf / intSeriesC ℚ pg)) ∈ KL L q ℓ M' := by
    rw [hser]
    exact coeffEmb_mem_laurentBaseChange L (div_mem_qExpFunctionFieldC f' g' hf' hg' hg0')
  refine P.mk' hmem fun γ hγ hγ0 τ hτ => ?_
  set w : KL L q ℓ M' := ⟨qExpand L ℓ (coeffEmb L (intSeriesC ℚ pf / intSeriesC ℚ pg)), hmem⟩ with hwdef
  have hw : ((w : KL L q ℓ M') : LaurentSeries L) =
      coeffEmb L (intSeriesC ℚ (expandPS ℓ pf) / intSeriesC ℚ (expandPS ℓ pg)) := hser

  have key := hτ k f' g' (expandPS ℓ pf) (expandPS ℓ pg) hf' hg' hg0' w hw ι₀ hι₀

  have hinvf : ((⇑f' : ℍ → ℂ) ∣[k] conjElemN (q * ℓ) γ⁻¹) = ⇑f' := by
    rw [hf'def, coe_stretch_eq_smul, ModularForm.smul_slash, σ_conjElemN_apply,
      slash_Dr_slash_conjElemN hqM' f (inv_mem hγ) (inv_mem hγ0)]
  have hinvg : ((⇑g' : ℍ → ℂ) ∣[k] conjElemN (q * ℓ) γ⁻¹) = ⇑g' := by
    rw [hg'def, coe_stretch_eq_smul, ModularForm.smul_slash, σ_conjElemN_apply,
      slash_Dr_slash_conjElemN hqM' g (inv_mem hγ) (inv_mem hγ0)]
  rw [hinvf, hinvg] at key
  change coeffMap ι₀ ((τ w : KL L q ℓ M') : LaurentSeries L) * qC g' = qC f' at key

  have hw2 : coeffMap ι₀ ((w : KL L q ℓ M') : LaurentSeries L) * qC g' = qC f' := by
    rw [hw, ← ιB, ιB_coeffEmb, map_div₀, ιC_intSeriesC hf', ιC_intSeriesC hg']
    have hne : qC (⇑g') ≠ 0 := by
      rw [← ιC_intSeriesC hg']
      exact (map_ne_zero_iff _ (RingHom.injective _)).mpr hg0'
    rw [div_mul_cancel₀ _ hne]
  have hne : qC (⇑g') ≠ 0 := by
    rw [← ιC_intSeriesC hg']
    exact (map_ne_zero_iff _ (RingHom.injective _)).mpr hg0'
  have heq : coeffMap ι₀ ((τ w : KL L q ℓ M') : LaurentSeries L) = coeffMap ι₀ ((w : KL L q ℓ M') : LaurentSeries L) :=
    mul_right_cancel₀ hne (key.trans hw2.symm)
  exact Subtype.ext (ιB_injective ι₀ heq)

theorem P.of_mem_field {y : LaurentSeries ℚ} (hy : y ∈ xHFunctionField (q ^ 2 * M') (levelH q M')) :
    P q M' ℓ ξ (coeffEmb L y) := by
  change y ∈ Subfield.closure (Set.range (algebraMap ℚ (LaurentSeries ℚ)) ∪ intFormRatiosC ℚ (GH q M')) at hy
  induction hy using Subfield.closure_induction with
  | mem y hy =>
      rcases hy with ⟨r, rfl⟩ | hy
      · rw [algebraMap_laurentSeries_eq_single, coeffEmb, coeffMap_single, ← algebraMap_laurentSeries_eq_single]
        exact P_algebraMap _
      · exact P.gen hqM' ι₀ hι₀ hy
  | one => rw [map_one]; exact P.one
  | add x y _ _ hx hy => rw [map_add]; exact hx.add hy
  | neg x _ hx => rw [map_neg]; exact hx.neg
  | inv x _ hx => rw [map_inv₀]; exact hx.inv
  | mul x y _ _ hx hy => rw [map_mul]; exact hx.mul hy

theorem P.of_mem {x : LaurentSeries L}
    (hx : x ∈ laurentBaseChange L (xHFunctionField (q ^ 2 * M') (levelH q M'))) : P q M' ℓ ξ x := by
  rw [mem_laurentBaseChange_iff] at hx
  induction hx using Subfield.closure_induction with
  | mem y hy =>
      rcases hy with ⟨c, rfl⟩ | ⟨z, hz, rfl⟩
      · exact P_algebraMap c
      · exact P.of_mem_field hqM' ι₀ hι₀ hz
  | one => exact P.one
  | add x y _ _ hx hy => exact hx.add hy
  | neg x _ hx => exact hx.neg
  | inv x _ hx => exact hx.inv
  | mul x y _ _ hx hy => exact hx.mul hy

end Gen

end Main

end W1xLE
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_qExpand_mem_and_apply_eq_of_isLevelAutAt_of_mem_Gamma.W1xLE"

end
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_qExpand_mem_and_apply_eq_of_isLevelAutAt_of_mem_Gamma.W1xLE"

theorem solution
    (q : ℕ) [NeZero q] (M' : ℕ) [NeZero M'] (hqM' : Nat.Coprime q M') (ℓ : ℕ) [NeZero ℓ]
    (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {q * ℓ} ℚ L]
    (ξ : L) (hξ : IsPrimitiveRoot ξ (q * ℓ))
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L
      (ModularCurve.xHFunctionField ((q * ℓ) ^ 2 * M')
        (ModularCurve.FullLevel.levelH (q * ℓ) M'))) :
    (∀ x : LaurentSeries L,
      x ∈ ModularCurve.laurentBaseChange L
            (ModularCurve.xHFunctionField (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M')) →
        ModularCurve.qExpand L ℓ x ∈ K) ∧
    (∀ x : LaurentSeries L,
      x ∈ ModularCurve.laurentBaseChange L
            (ModularCurve.xHFunctionField (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M')) →
      ∀ w : ↥K, ((w : ↥K) : LaurentSeries L) = ModularCurve.qExpand L ℓ x →
        ∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma q → γ ∈ CongruenceSubgroup.Gamma0 M' →
          ∀ τ : ↥K ≃ₐ[L] ↥K, ModularCurve.FullLevel.IsLevelAutAt L (q * ℓ) ξ (q * ℓ) ((q * ℓ) ^ 2 * M')
              (ModularCurve.FullLevel.levelH (q * ℓ) M') γ⁻¹ K τ →
            τ w = w) := by
  subst hK
  obtain ⟨ι₀, hι₀⟩ := W1xLE.exists_emb (m := q * ℓ) L ξ hξ
  exact ⟨fun x hx => (W1xLE.P.of_mem hqM' ι₀ hι₀ hx).1,
    fun x hx w hw γ hγ hγ0 τ hτ => (W1xLE.P.of_mem hqM' ι₀ hι₀ hx).2 w hw γ hγ hγ0 τ hτ⟩

end S_ModularCurve_FullLevel_qExpand_mem_and_apply_eq_of_isLevelAutAt_of_mem_Gamma
end P2MW
export P2MW.S_ModularCurve_FullLevel_qExpand_mem_and_apply_eq_of_isLevelAutAt_of_mem_Gamma (solution)
