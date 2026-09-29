-- Prove2me | solution 1 for ModularCurve.FullLevel.AuxLevelOne.exists_isLevelAutAt_restrict_coeffMap_of_isLevelAutAt_of_isPrimitiveRoot_mul_of_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.339302+00:00
-- url     : https://prove2.me/submissions/d1f5505f-7365-501f-9144-89579ebde111

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_ModularCurve_FullLevelLevelAutAt
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_DrinfeldCurve_LocalChart
import Definitions.Def_ModularCurve_JqCoeff
import Theorems.Thm_ModularCurve_FullLevel_exists_isLevelAutAt_of_mem_gamma0_of_eq_levelH_inf_ker
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_AuxLevelOne_exists_isLevelAutAt_restrict_coeffMap_of_isLevelAutAt_of_isPrimitiveRoot_mul_of_dvd

open scoped MatrixGroups ModularForm
open Matrix ModularCurve ModularCurve.FullLevel CongruenceSubgroup
open scoped Pointwise

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace W1xLBCH
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

theorem det_coeSL (γ : SL(2, ℤ)) : ((γ : GL (Fin 2) ℝ)).det = 1 := by
  ext
  simp

theorem det_conjElemN (γ : SL(2, ℤ)) : (conjElemN m γ).det = 1 := by
  rw [conjElemN_eq, map_mul, map_mul, map_inv, det_coeSL, mul_one, inv_mul_cancel]

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
variable (m : ℕ) [NeZero m] (M' : ℕ) (H : Subgroup (ZMod (m ^ 2 * M'))ˣ)

abbrev GH : Subgroup SL(2, ℤ) := CohCarrier.GammaH (m ^ 2 * M') H

abbrev Γ : Subgroup (GL (Fin 2) ℝ) := ((GH m M' H : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))

variable {m M' H}

scoped instance GH_finiteIndex (m M' : ℕ) [NeZero m] [NeZero M'] (H : Subgroup (ZMod (m ^ 2 * M'))ˣ) :
    (GH m M' H).FiniteIndex :=
  Subgroup.finiteIndex_of_le (Gamma1_le_GammaH _ _)

omit [NeZero m] in
theorem one_mem_strictPeriods : (1 : ℝ) ∈ (Γ m M' H).strictPeriods := by
  rw [Subgroup.strictPeriods_eq_zmultiples_one_of_T_mem (translation_mem_GammaH _ _)]
  exact AddSubgroup.mem_zmultiples _

end GH

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

end Emb

section Normalise

variable {m : ℕ} [NeZero m] {M' : ℕ} {H : Subgroup (ZMod (m ^ 2 * M'))ˣ} {ℓg : ℕ}

abbrev SLq (m : ℕ) : SL(2, ℤ) →* SL(2, ZMod m) := Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod m))

theorem SLq_apply (A : SL(2, ℤ)) (i j : Fin 2) : (SLq m A) i j = ((A i j : ℤ) : ZMod m) := by
  simp

omit [NeZero m] in
theorem q_dvd_level : (m : ℤ) ∣ ((m ^ 2 * M' : ℕ) : ℤ) := ⟨m * M', by push_cast; ring⟩

theorem SLq_eq_one_iff (A : SL(2, ℤ)) : SLq m A = 1 ↔
    ((A 0 0 : ℤ) : ZMod m) = 1 ∧ ((A 0 1 : ℤ) : ZMod m) = 0 ∧ ((A 1 0 : ℤ) : ZMod m) = 0 ∧
      ((A 1 1 : ℤ) : ZMod m) = 1 := by
  constructor
  · intro h
    have e : ∀ i j, ((A i j : ℤ) : ZMod m) = (1 : SL(2, ZMod m)) i j := fun i j => by
      rw [← SLq_apply, h]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [e]
  · rintro ⟨h1, h2, h3, h4⟩
    ext i j
    rw [SLq_apply]
    fin_cases i <;> fin_cases j <;> simp [h1, h2, h3, h4]

variable
  (hmem : ∀ A : SL(2, ℤ), A ∈ GH m M' H ↔
    ((A 1 0 : ℤ) : ZMod (m ^ 2 * M')) = 0 ∧ ((A 1 1 : ℤ) : ZMod m) = 1 ∧ ((A 1 1 : ℤ) : ZMod ℓg) = 1)
  (hℓg : ℓg ∣ M')
include hmem hℓg

theorem upperLeft_of_mem_GH {δ : SL(2, ℤ)} (hδ : δ ∈ GH m M' H) : ((δ 0 0 : ℤ) : ZMod m) = 1 := by
  obtain ⟨h10, h11, h1ℓ⟩ := (hmem δ).mp hδ
  have hq10 : ((δ 1 0 : ℤ) : ZMod m) = 0 := by
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h10 ⊢
    exact dvd_trans q_dvd_level h10
  have hdet := Matrix.SpecialLinearGroup.det_coe δ
  rw [Matrix.det_fin_two] at hdet
  have := congrArg (fun z : ℤ => (z : ZMod m)) hdet
  simp only [Int.cast_sub, Int.cast_mul, Int.cast_one, hq10, h11, mul_one, mul_zero, sub_zero] at this
  exact this

theorem q_dvd_lowerLeft_of_mem_GH {δ : SL(2, ℤ)} (hδ : δ ∈ GH m M' H) : (m : ℤ) ∣ δ 1 0 := by
  obtain ⟨h10, _, _⟩ := (hmem δ).mp hδ
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h10
  exact dvd_trans q_dvd_level h10

theorem SLq_upSL_of_mem_GH {δ : SL(2, ℤ)} (hδ : δ ∈ GH m M' H) :
    SLq m (upSL δ (q_dvd_lowerLeft_of_mem_GH hmem hℓg hδ)) = 1 := by
  obtain ⟨h10, h11, h1ℓ⟩ := (hmem δ).mp hδ
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h10
  obtain ⟨c, hc⟩ := h10
  rw [SLq_eq_one_iff]
  refine ⟨?_, ?_, ?_, ?_⟩
  · show ((δ 0 0 : ℤ) : ZMod m) = 1
    exact upperLeft_of_mem_GH hmem hℓg hδ
  · show (((m : ℤ) * δ 0 1 : ℤ) : ZMod m) = 0
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]; exact Dvd.intro _ rfl
  · show ((δ 1 0 / m : ℤ) : ZMod m) = 0
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd, hc]
    refine ⟨M' * c, ?_⟩
    push_cast
    rw [show (m : ℤ) ^ 2 * M' * c = m * (m * (M' * c)) by ring, Int.mul_ediv_cancel_left _ (mneZ m)]
  · show ((δ 1 1 : ℤ) : ZMod m) = 1
    exact h11

theorem upSL_mem_Gamma0 {δ : SL(2, ℤ)} (hδ : δ ∈ GH m M' H) :
    upSL δ (q_dvd_lowerLeft_of_mem_GH hmem hℓg hδ) ∈ Gamma0 M' := by
  obtain ⟨h10, _, _⟩ := (hmem δ).mp hδ
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h10
  obtain ⟨c, hc⟩ := h10
  rw [Gamma0_mem]
  show ((δ 1 0 / m : ℤ) : ZMod M') = 0
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd, hc]
  refine ⟨m * c, ?_⟩
  push_cast
  rw [show (m : ℤ) ^ 2 * M' * c = m * (M' * (m * c)) by ring, Int.mul_ediv_cancel_left _ (mneZ m)]

variable (hmM' : Nat.Coprime m M')
include hmM'

theorem exists_conj_mem {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 M') {δ : SL(2, ℤ)} (hδ : δ ∈ GH m M' H) :
    ∃ δ' ∈ GH m M' H, ((δ' : SL(2, ℤ)) : GL (Fin 2) ℝ) = conjElemN m γ * (δ : GL (Fin 2) ℝ) * (conjElemN m γ)⁻¹ := by
  set u : SL(2, ℤ) := upSL δ (q_dvd_lowerLeft_of_mem_GH hmem hℓg hδ) with hu
  set ε : SL(2, ℤ) := γ * u * γ⁻¹ with hε
  have hεq : SLq m ε = 1 := by
    rw [hε, map_mul, map_mul, SLq_upSL_of_mem_GH hmem hℓg hδ, mul_one, map_inv, mul_inv_cancel]
  obtain ⟨e00, e01, e10, e11⟩ := (SLq_eq_one_iff ε).mp hεq
  have hε0 : ε ∈ Gamma0 M' := mul_mem (mul_mem hγ (upSL_mem_Gamma0 hmem hℓg hδ)) (inv_mem hγ)
  have h01 : (m : ℤ) ∣ ε 0 1 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp e01
  refine ⟨downSL ε h01, ?_, ?_⟩
  · rw [hmem]
    refine ⟨?_, e11, ?_⟩
    · show (((m : ℤ) * ε 1 0 : ℤ) : ZMod (m ^ 2 * M')) = 0
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
      have hq : (m : ℤ) ∣ ε 1 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp e10
      have hM : (M' : ℤ) ∣ ε 1 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (Gamma0_mem.mp hε0)
      have hcop : IsCoprime (m : ℤ) (M' : ℤ) := by
        rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd_natCast_natCast]
        exact hmM'
      obtain ⟨c, hc⟩ := hcop.mul_dvd hq hM
      refine ⟨c, ?_⟩
      rw [hc]; push_cast; ring
    ·
      show ((ε 1 1 : ℤ) : ZMod ℓg) = 1
      obtain ⟨h10, h11, h1ℓ⟩ := (hmem δ).mp hδ
      have hℓgZ : (ℓg : ℤ) ∣ (M' : ℤ) := Int.natCast_dvd_natCast.mpr hℓg
      have hG10 : ((γ 1 0 : ℤ) : ZMod ℓg) = 0 := by
        rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
        exact dvd_trans hℓgZ ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (Gamma0_mem.mp hγ))
      obtain ⟨c', hc'⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h10
      have hu10 : ((u 1 0 : ℤ) : ZMod ℓg) = 0 := by
        rw [hu]
        show ((δ 1 0 / m : ℤ) : ZMod ℓg) = 0
        rw [ZMod.intCast_zmod_eq_zero_iff_dvd, hc']
        obtain ⟨t, ht⟩ := hℓgZ
        refine ⟨m * t * c', ?_⟩
        push_cast
        rw [ht, show (m : ℤ) ^ 2 * (ℓg * t) * c' = m * (ℓg * (m * t * c')) by ring,
          Int.mul_ediv_cancel_left _ (mneZ m)]
      have hu11 : ((u 1 1 : ℤ) : ZMod ℓg) = 1 := by rw [hu]; exact h1ℓ
      have hu00 : ((u 0 0 : ℤ) : ZMod ℓg) = 1 := by
        have hdet := Matrix.SpecialLinearGroup.det_coe (u)
        rw [Matrix.det_fin_two] at hdet
        have := congrArg (fun z : ℤ => (z : ZMod ℓg)) hdet
        simp only [Int.cast_sub, Int.cast_mul, Int.cast_one, hu10, hu11, mul_one, mul_zero, sub_zero] at this
        exact this
      have hdetγ : ((γ 0 0 : ℤ) : ZMod ℓg) * ((γ 1 1 : ℤ) : ZMod ℓg) = 1 := by
        have hdet := Matrix.SpecialLinearGroup.det_coe γ
        rw [Matrix.det_fin_two] at hdet
        have := congrArg (fun z : ℤ => (z : ZMod ℓg)) hdet
        simp only [Int.cast_sub, Int.cast_mul, Int.cast_one, hG10, mul_zero, sub_zero] at this
        exact this
      have hε11 : (ε 1 1 : ℤ) =
          ((γ 1 0 : ℤ) * u 0 0 + (γ 1 1 : ℤ) * u 1 0) * (-(γ 0 1 : ℤ)) +
          ((γ 1 0 : ℤ) * u 0 1 + (γ 1 1 : ℤ) * u 1 1) * (γ 0 0 : ℤ) := by
        rw [hε]
        simp [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two,
          Matrix.mul_apply, Fin.sum_univ_two]
      rw [hε11]
      push_cast
      rw [hG10, hu10, hu11]
      simp only [zero_mul, mul_zero, zero_add, add_zero, mul_one]
      rw [mul_comm, hdetγ]
  · obtain ⟨c, hc⟩ := h01
    have hd := downSL_coe ε ⟨c, hc⟩
    have hup := upSL_coe δ (q_dvd_lowerLeft_of_mem_GH hmem hℓg hδ)
    rw [← hu] at hup
    have e1 : ((downSL ε ⟨c, hc⟩ : SL(2, ℤ)) : GL (Fin 2) ℝ) = (Dr m)⁻¹ * (ε : GL (Fin 2) ℝ) * Dr m := by
      rw [mul_assoc, ← hd, inv_mul_cancel_left]
    have e2 : (u : GL (Fin 2) ℝ) = Dr m * (δ : GL (Fin 2) ℝ) * (Dr m)⁻¹ := by
      rw [← hup, mul_inv_cancel_right]
    rw [e1, hε]
    simp only [map_mul, map_inv]
    rw [e2, conjElemN_eq]
    group

theorem le_conj {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 M') :
    Γ m M' H ≤ ConjAct.toConjAct (conjElemN m γ)⁻¹ • Γ m M' H := by
  rintro x ⟨δ, hδ, rfl⟩
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← ConjAct.toConjAct_inv, inv_inv,
    ConjAct.toConjAct_smul]
  obtain ⟨δ', hδ', e⟩ := exists_conj_mem hmem hℓg hmM' hγ hδ
  exact ⟨δ', hδ', e⟩

variable [NeZero M']

def sl {k : ℤ} (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M') (f : ModularForm (Γ m M' H) k) :
    ModularForm (Γ m M' H) k :=
  restrictForm (le_conj hmem hℓg hmM' hγ) (ModularForm.translate f (conjElemN m γ))

@[scoped simp]
theorem coe_sl {k : ℤ} (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M') (f : ModularForm (Γ m M' H) k) :
    ⇑(sl hmem hℓg hmM' γ hγ f) = ⇑f ∣[k] conjElemN m γ := rfl

theorem sl_inv_sl_apply {k : ℤ} (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M') (f : ModularForm (Γ m M' H) k) :
    ⇑(sl hmem hℓg hmM' γ⁻¹ (inv_mem hγ) (sl hmem hℓg hmM' γ hγ f)) = ⇑f := by
  rw [coe_sl, coe_sl, ← SlashAction.slash_mul, conjElemN_eq, conjElemN_eq]
  simp only [map_inv]
  rw [show (Dr m)⁻¹ * (γ : GL (Fin 2) ℝ) * Dr m * ((Dr m)⁻¹ * (γ : GL (Fin 2) ℝ)⁻¹ * Dr m) = 1 by group,
    SlashAction.slash_one]

theorem sl_ne_zero {k : ℤ} (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M') {f : ModularForm (Γ m M' H) k}
    (hf : f ≠ 0) : sl hmem hℓg hmM' γ hγ f ≠ 0 := by
  intro h
  apply hf
  have e := sl_inv_sl_apply hmem hℓg hmM' γ hγ f
  rw [h] at e
  apply DFunLike.ext
  intro τ
  have := congrFun e τ
  rw [coe_sl] at this
  rw [← this]
  simp

end Normalise

section QC

open UpperHalfPlane HahnSeries

variable {m : ℕ} [NeZero m] {M' : ℕ} {H : Subgroup (ZMod (m ^ 2 * M'))ˣ}

theorem qC_eq_zero_iff [NeZero M'] {k : ℤ} (f : ModularForm (Γ m M' H) k) : qC f = 0 ↔ f = 0 := by
  rw [qC, ← ModularForm.qExpansion_eq_zero_iff one_pos one_mem_strictPeriods f]
  exact map_eq_zero_iff _ HahnSeries.ofPowerSeries_injective

theorem ne_zero_of_intSeriesC_ne_zero' [NeZero M'] {k : ℤ} {g : ModularForm (Γ m M' H) k} {pg : PowerSeries ℤ}
    (hg : IsIntegralQExp (⇑g) pg) (hg0 : intSeriesC ℚ pg ≠ 0) : g ≠ 0 := by
  intro h
  apply hg0
  have h1 : ιC (intSeriesC ℚ pg) = 0 := by
    rw [ιC_intSeriesC hg, h]
    exact (qC_eq_zero_iff (0 : ModularForm (Γ m M' H) k)).2 rfl
  exact (map_eq_zero_iff _ (RingHom.injective _)).1 h1

end QC

section Main

open UpperHalfPlane IntermediateField HahnSeries
open scoped ModularForm

variable {N : ℕ} {H : Subgroup (ZMod N)ˣ}
  {L₀ : Type} [Field L₀] [CharZero L₀] {L : Type} [Field L] [CharZero L] (ι₀ : L₀ →+* L)

abbrev KL (L : Type) [Field L] [CharZero L] (N : ℕ) (H : Subgroup (ZMod N)ˣ) :
    IntermediateField L (LaurentSeries L) :=
  laurentBaseChange L (xHFunctionField N H)

theorem coeffMap_coeffEmb₀ (x : LaurentSeries ℚ) : coeffMap ι₀ (coeffEmb L₀ x) = coeffEmb L x := by
  rw [coeffEmb, coeffEmb, coeffMap_coeffMap]
  exact coeffMap_congr (Subsingleton.elim _ _) x

theorem coeffMap_algebraMap₀ (c : L₀) :
    coeffMap ι₀ (algebraMap L₀ (LaurentSeries L₀) c) = algebraMap L (LaurentSeries L) (ι₀ c) := by
  rw [algebraMap_laurentSeries_eq_single, algebraMap_laurentSeries_eq_single, coeffMap_single]

theorem coeffMap_mem_KL {x : LaurentSeries L₀} (hx : x ∈ KL L₀ N H) : coeffMap ι₀ x ∈ KL L N H := by
  rw [mem_laurentBaseChange_iff] at hx
  induction hx using Subfield.closure_induction with
  | mem y hy =>
      rcases hy with ⟨c, rfl⟩ | ⟨z, hz, rfl⟩
      · rw [coeffMap_algebraMap₀]
        exact IntermediateField.algebraMap_mem _ _
      · rw [coeffMap_coeffEmb₀]
        exact coeffEmb_mem_laurentBaseChange L hz
  | one => rw [map_one]; exact one_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | neg x _ hx => rw [map_neg]; exact neg_mem hx
  | inv x _ hx => rw [map_inv₀]; exact inv_mem hx
  | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy

variable (τ : KL L N H ≃ₐ[L] KL L N H) (τ₀ : KL L₀ N H ≃ₐ[L₀] KL L₀ N H)

def P (x : LaurentSeries L₀) : Prop :=
  x ∈ KL L₀ N H ∧ coeffMap ι₀ x ∈ KL L N H ∧
    ∀ (h₁ : x ∈ KL L₀ N H) (h₂ : coeffMap ι₀ x ∈ KL L N H),
      ((τ ⟨coeffMap ι₀ x, h₂⟩ : KL L N H) : LaurentSeries L) =
        coeffMap ι₀ ((τ₀ ⟨x, h₁⟩ : KL L₀ N H) : LaurentSeries L₀)

variable {ι₀ τ τ₀}

theorem P.mk' {x : LaurentSeries L₀} (h₁ : x ∈ KL L₀ N H)
    (h : ((τ ⟨coeffMap ι₀ x, coeffMap_mem_KL ι₀ h₁⟩ : KL L N H) : LaurentSeries L) =
      coeffMap ι₀ ((τ₀ ⟨x, h₁⟩ : KL L₀ N H) : LaurentSeries L₀)) :
    P ι₀ τ τ₀ x :=
  ⟨h₁, coeffMap_mem_KL ι₀ h₁, fun _ _ => h⟩

theorem P.mem₂ {x : LaurentSeries L₀} (hx : P ι₀ τ τ₀ x) : coeffMap ι₀ x ∈ KL L N H := hx.2.1

theorem P.out {x : LaurentSeries L₀} (hx : P ι₀ τ τ₀ x) :
    ((τ ⟨coeffMap ι₀ x, hx.mem₂⟩ : KL L N H) : LaurentSeries L) =
      coeffMap ι₀ ((τ₀ ⟨x, hx.1⟩ : KL L₀ N H) : LaurentSeries L₀) :=
  hx.2.2 hx.1 hx.2.1

theorem P.add {x y : LaurentSeries L₀} (hx : P ι₀ τ τ₀ x) (hy : P ι₀ τ τ₀ y) :
    P ι₀ τ τ₀ (x + y) := by
  have h₁ : x + y ∈ KL L₀ N H := add_mem hx.1 hy.1
  refine P.mk' h₁ ?_
  have e : (⟨coeffMap ι₀ (x + y), coeffMap_mem_KL ι₀ h₁⟩ : KL L N H) =
      ⟨coeffMap ι₀ x, hx.mem₂⟩ + ⟨coeffMap ι₀ y, hy.mem₂⟩ :=
    Subtype.ext (by simp [map_add])
  have e' : (⟨x + y, h₁⟩ : KL L₀ N H) = ⟨x, hx.1⟩ + ⟨y, hy.1⟩ := Subtype.ext rfl
  rw [e, e', map_add, map_add]
  push_cast
  rw [map_add, hx.out, hy.out]

theorem P.mul {x y : LaurentSeries L₀} (hx : P ι₀ τ τ₀ x) (hy : P ι₀ τ τ₀ y) :
    P ι₀ τ τ₀ (x * y) := by
  have h₁ : x * y ∈ KL L₀ N H := mul_mem hx.1 hy.1
  refine P.mk' h₁ ?_
  have e : (⟨coeffMap ι₀ (x * y), coeffMap_mem_KL ι₀ h₁⟩ : KL L N H) =
      ⟨coeffMap ι₀ x, hx.mem₂⟩ * ⟨coeffMap ι₀ y, hy.mem₂⟩ :=
    Subtype.ext (by simp [map_mul])
  have e' : (⟨x * y, h₁⟩ : KL L₀ N H) = ⟨x, hx.1⟩ * ⟨y, hy.1⟩ := Subtype.ext rfl
  rw [e, e', map_mul, map_mul]
  push_cast
  rw [map_mul, hx.out, hy.out]

theorem P.neg {x : LaurentSeries L₀} (hx : P ι₀ τ τ₀ x) : P ι₀ τ τ₀ (-x) := by
  have h₁ : -x ∈ KL L₀ N H := neg_mem hx.1
  refine P.mk' h₁ ?_
  have e : (⟨coeffMap ι₀ (-x), coeffMap_mem_KL ι₀ h₁⟩ : KL L N H) = -⟨coeffMap ι₀ x, hx.mem₂⟩ :=
    Subtype.ext (by simp [map_neg])
  have e' : (⟨-x, h₁⟩ : KL L₀ N H) = -⟨x, hx.1⟩ := Subtype.ext rfl
  rw [e, e', map_neg, map_neg]
  push_cast
  rw [map_neg, hx.out]

theorem P.inv {x : LaurentSeries L₀} (hx : P ι₀ τ τ₀ x) : P ι₀ τ τ₀ x⁻¹ := by
  have h₁ : x⁻¹ ∈ KL L₀ N H := inv_mem hx.1
  refine P.mk' h₁ ?_
  have e : (⟨coeffMap ι₀ x⁻¹, coeffMap_mem_KL ι₀ h₁⟩ : KL L N H) = (⟨coeffMap ι₀ x, hx.mem₂⟩ : KL L N H)⁻¹ :=
    Subtype.ext (by simp [map_inv₀])
  have e' : (⟨x⁻¹, h₁⟩ : KL L₀ N H) = (⟨x, hx.1⟩ : KL L₀ N H)⁻¹ := Subtype.ext rfl
  rw [e, e', map_inv₀, map_inv₀]
  push_cast
  rw [map_inv₀, hx.out]

theorem P.one : P ι₀ τ τ₀ (1 : LaurentSeries L₀) := by
  refine P.mk' (one_mem _) ?_
  have e : (⟨coeffMap ι₀ 1, coeffMap_mem_KL ι₀ (one_mem _)⟩ : KL L N H) = 1 := Subtype.ext (by simp)
  have e' : (⟨(1 : LaurentSeries L₀), one_mem _⟩ : KL L₀ N H) = 1 := Subtype.ext rfl
  rw [e, e', map_one, map_one]
  push_cast
  rw [map_one]

theorem P_algebraMap (c : L₀) : P ι₀ τ τ₀ (algebraMap L₀ (LaurentSeries L₀) c) := by
  have h₁ : algebraMap L₀ (LaurentSeries L₀) c ∈ KL L₀ N H := IntermediateField.algebraMap_mem _ _
  refine P.mk' h₁ ?_
  have e : (⟨coeffMap ι₀ (algebraMap L₀ (LaurentSeries L₀) c), coeffMap_mem_KL ι₀ h₁⟩ : KL L N H) =
      algebraMap L (KL L N H) (ι₀ c) :=
    Subtype.ext (by
      change coeffMap ι₀ (algebraMap L₀ (LaurentSeries L₀) c) = _
      rw [coeffMap_algebraMap₀]; rfl)
  have e' : (⟨algebraMap L₀ (LaurentSeries L₀) c, h₁⟩ : KL L₀ N H) = algebraMap L₀ (KL L₀ N H) c :=
    Subtype.ext rfl
  rw [e, e', AlgEquiv.commutes, AlgEquiv.commutes]
  change algebraMap L (LaurentSeries L) (ι₀ c) = coeffMap ι₀ (algebraMap L₀ (LaurentSeries L₀) c)
  rw [coeffMap_algebraMap₀]

end Main

section Gen

open UpperHalfPlane IntermediateField HahnSeries
open scoped ModularForm

variable {m : ℕ} [NeZero m] {M' : ℕ} [NeZero M'] {H : Subgroup (ZMod (m ^ 2 * M'))ˣ} {ℓg : ℕ}
  (hmem : ∀ A : SL(2, ℤ), A ∈ GH m M' H ↔
    ((A 1 0 : ℤ) : ZMod (m ^ 2 * M')) = 0 ∧ ((A 1 1 : ℤ) : ZMod m) = 1 ∧ ((A 1 1 : ℤ) : ZMod ℓg) = 1)
  (hℓg : ℓg ∣ M') (hqM' : Nat.Coprime m M')
  {L₀ : Type} [Field L₀] [CharZero L₀] {L : Type} [Field L] [CharZero L] {ι₀ : L₀ →+* L}
  {τ : KL L (m ^ 2 * M') H ≃ₐ[L] KL L (m ^ 2 * M') H} {τ₀ : KL L₀ (m ^ 2 * M') H ≃ₐ[L₀] KL L₀ (m ^ 2 * M') H}
  {n : ℕ}
include hmem hℓg hqM'

theorem P.gen {ξ₀ : L₀} (ι : L →+* ℂ) (hι : ι (ι₀ ξ₀) = eq n)
    (δ : SL(2, ℤ)) (hδ : δ ∈ Gamma0 M')
    (hτ : IsLevelAutAt L n (ι₀ ξ₀) m (m ^ 2 * M') H δ (KL L (m ^ 2 * M') H) τ)
    (hτ₀ : IsLevelAutAt L₀ n ξ₀ m (m ^ 2 * M') H δ (KL L₀ (m ^ 2 * M') H) τ₀)
    {y : LaurentSeries ℚ} (hy : y ∈ intFormRatiosC ℚ (GH m M' H)) : P ι₀ τ τ₀ (coeffEmb L₀ y) := by
  obtain ⟨k, f, g, pf, pg, hf, hg, hg0, rfl⟩ := hy
  have h₁ : coeffEmb L₀ (intSeriesC ℚ pf / intSeriesC ℚ pg) ∈ KL L₀ (m ^ 2 * M') H :=
    coeffEmb_mem_laurentBaseChange L₀ (div_mem_qExpFunctionFieldC f g hf hg hg0)
  refine P.mk' h₁ ?_
  set w : KL L (m ^ 2 * M') H := ⟨coeffMap ι₀ (coeffEmb L₀ (intSeriesC ℚ pf / intSeriesC ℚ pg)), coeffMap_mem_KL ι₀ h₁⟩
    with hwdef
  set x₀ : KL L₀ (m ^ 2 * M') H := ⟨coeffEmb L₀ (intSeriesC ℚ pf / intSeriesC ℚ pg), h₁⟩ with hx₀def
  have hw : ((w : KL L (m ^ 2 * M') H) : LaurentSeries L) = coeffEmb L (intSeriesC ℚ pf / intSeriesC ℚ pg) :=
    coeffMap_coeffEmb₀ ι₀ _

  set fδ : ModularForm (Γ m M' H) k := sl hmem hℓg hqM' δ hδ f with hfδdef
  set gδ : ModularForm (Γ m M' H) k := sl hmem hℓg hqM' δ hδ g with hgδdef

  have keyτ := hτ k f g pf pg hf hg hg0 w hw ι (by rw [hι])
  change coeffMap ι ((τ w : KL L (m ^ 2 * M') H) : LaurentSeries L) * qC (⇑gδ) = qC (⇑fδ) at keyτ

  have keyτ₀ := hτ₀ k f g pf pg hf hg hg0 x₀ rfl (ι.comp ι₀) (by rw [RingHom.comp_apply, hι])
  change coeffMap (ι.comp ι₀) ((τ₀ x₀ : KL L₀ (m ^ 2 * M') H) : LaurentSeries L₀) * qC (⇑gδ) = qC (⇑fδ) at keyτ₀

  have hne : qC (⇑gδ) ≠ 0 := by
    intro h
    rw [qC_eq_zero_iff] at h
    exact sl_ne_zero hmem hℓg hqM' δ hδ (ne_zero_of_intSeriesC_ne_zero' hg hg0) h
  have heq : coeffMap ι ((τ w : KL L (m ^ 2 * M') H) : LaurentSeries L) =
      coeffMap ι (coeffMap ι₀ ((τ₀ x₀ : KL L₀ (m ^ 2 * M') H) : LaurentSeries L₀)) := by
    rw [coeffMap_coeffMap]
    exact mul_right_cancel₀ hne (keyτ.trans keyτ₀.symm)
  exact ιB_injective ι heq

theorem P.of_mem_field {ξ₀ : L₀} (ι : L →+* ℂ) (hι : ι (ι₀ ξ₀) = eq n)
    (δ : SL(2, ℤ)) (hδ : δ ∈ Gamma0 M')
    (hτ : IsLevelAutAt L n (ι₀ ξ₀) m (m ^ 2 * M') H δ (KL L (m ^ 2 * M') H) τ)
    (hτ₀ : IsLevelAutAt L₀ n ξ₀ m (m ^ 2 * M') H δ (KL L₀ (m ^ 2 * M') H) τ₀)
    {y : LaurentSeries ℚ} (hy : y ∈ xHFunctionField (m ^ 2 * M') H) :
    P ι₀ τ τ₀ (coeffEmb L₀ y) := by
  change y ∈ Subfield.closure (Set.range (algebraMap ℚ (LaurentSeries ℚ)) ∪ intFormRatiosC ℚ (GH m M' H)) at hy
  induction hy using Subfield.closure_induction with
  | mem y hy =>
      rcases hy with ⟨r, rfl⟩ | hy
      · rw [algebraMap_laurentSeries_eq_single, coeffEmb, coeffMap_single, ← algebraMap_laurentSeries_eq_single]
        exact P_algebraMap _
      · exact P.gen hmem hℓg hqM' ι hι δ hδ hτ hτ₀ hy
  | one => rw [map_one]; exact P.one
  | add x y _ _ hx hy => rw [map_add]; exact hx.add hy
  | neg x _ hx => rw [map_neg]; exact hx.neg
  | inv x _ hx => rw [map_inv₀]; exact hx.inv
  | mul x y _ _ hx hy => rw [map_mul]; exact hx.mul hy

theorem P.of_mem {ξ₀ : L₀} (ι : L →+* ℂ) (hι : ι (ι₀ ξ₀) = eq n)
    (δ : SL(2, ℤ)) (hδ : δ ∈ Gamma0 M')
    (hτ : IsLevelAutAt L n (ι₀ ξ₀) m (m ^ 2 * M') H δ (KL L (m ^ 2 * M') H) τ)
    (hτ₀ : IsLevelAutAt L₀ n ξ₀ m (m ^ 2 * M') H δ (KL L₀ (m ^ 2 * M') H) τ₀)
    {x : LaurentSeries L₀} (hx : x ∈ KL L₀ (m ^ 2 * M') H) : P ι₀ τ τ₀ x := by
  rw [mem_laurentBaseChange_iff] at hx
  induction hx using Subfield.closure_induction with
  | mem y hy =>
      rcases hy with ⟨c, rfl⟩ | ⟨z, hz, rfl⟩
      · exact P_algebraMap c
      · exact P.of_mem_field hmem hℓg hqM' ι hι δ hδ hτ hτ₀ hz
  | one => exact P.one
  | add x y _ _ hx hy => exact hx.add hy
  | neg x _ hx => exact hx.neg
  | inv x _ hx => exact hx.inv
  | mul x y _ _ hx hy => exact hx.mul hy

end Gen

end W1xLBCH
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_AuxLevelOne_exists_isLevelAutAt_restrict_coeffMap_of_isLevelAutAt_of_isPrimitiveRoot_mul_of_dvd.W1xLBCH"

end
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_AuxLevelOne_exists_isLevelAutAt_restrict_coeffMap_of_isLevelAutAt_of_isPrimitiveRoot_mul_of_dvd.W1xLBCH"

theorem solution
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ12 : ℓ % 12 = 11) (hℓM' : ℓ ∣ M')
    (L₀ : Type) [Field L₀] [CharZero L₀] [IsCyclotomicExtension {q * ℓ} ℚ L₀]
    (ξ₀ : L₀) (hξ₀ : IsPrimitiveRoot ξ₀ (q * ℓ))
    (L : Type) [Field L] [CharZero L] (ι₀ : L₀ →+* L)
    (hι : ∃ ι : L →+* ℂ, ι (ι₀ ξ₀) = Complex.exp (2 * Real.pi * Complex.I / (q * ℓ)))
    (H₁ : Subgroup (ZMod (q ^ 2 * M'))ˣ)
    (hH₁ : H₁ = ModularCurve.FullLevel.levelH q M' ⊓ (ZMod.unitsMap (Dvd.dvd.mul_left hℓM' (q ^ 2))).ker)
    (K₀ : IntermediateField L₀ (LaurentSeries L₀))
    (hK₀ : K₀ = ModularCurve.laurentBaseChange L₀
      (ModularCurve.xHFunctionField (q ^ 2 * M') H₁))
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L
      (ModularCurve.xHFunctionField (q ^ 2 * M') H₁)) :

    (∀ x : ↥K₀, ModularCurve.coeffMap ι₀ ((x : ↥K₀) : LaurentSeries L₀) ∈ K) ∧

    (∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 M' →
      ∀ τ : ↥K ≃ₐ[L] ↥K, ModularCurve.FullLevel.IsLevelAutAt L q ((ι₀ ξ₀) ^ ℓ) q (q ^ 2 * M') H₁ γ⁻¹ K τ →
        ∃ τ₀ : ↥K₀ ≃ₐ[L₀] ↥K₀,
          ModularCurve.FullLevel.IsLevelAutAt L₀ q (ξ₀ ^ ℓ) q (q ^ 2 * M') H₁ γ⁻¹ K₀ τ₀ ∧
          ∀ (x : ↥K₀) (hx : ModularCurve.coeffMap ι₀ ((x : ↥K₀) : LaurentSeries L₀) ∈ K),
            ((τ ⟨_, hx⟩ : ↥K) : LaurentSeries L) = ModularCurve.coeffMap ι₀ ((τ₀ x : ↥K₀) : LaurentSeries L₀)) := by

  have hqp : q.Prime := Fact.out
  have hℓp : ℓ.Prime := Fact.out
  haveI : NeZero q := ⟨hqp.ne_zero⟩
  haveI : NeZero ℓ := ⟨hℓp.ne_zero⟩
  have hcop : Nat.Coprime q M' := (Nat.Prime.coprime_iff_not_dvd hqp).2 hqM'

  have hζ₀ : IsPrimitiveRoot (ξ₀ ^ ℓ) q :=
    hξ₀.pow (Nat.pos_of_ne_zero (mul_ne_zero hqp.ne_zero hℓp.ne_zero)) (mul_comm q ℓ)

  have hmem : ∀ A : SL(2, ℤ), A ∈ W1xLBCH.GH q M' H₁ ↔
      ((A 1 0 : ℤ) : ZMod (q ^ 2 * M')) = 0 ∧ ((A 1 1 : ℤ) : ZMod q) = 1 ∧ ((A 1 1 : ℤ) : ZMod ℓ) = 1 := by
    intro A
    rw [W1xLBCH.GH, CohCarrier.mem_GammaH_iff, hH₁]
    simp only [Subgroup.mem_inf, MonoidHom.mem_ker, ModularCurve.FullLevel.mem_levelH_iff]
    constructor
    · rintro ⟨hA, hH, hK⟩
      refine ⟨CongruenceSubgroup.Gamma0_mem.mp hA, ?_, ?_⟩
      · have := congrArg (fun u : (ZMod q)ˣ => (u : ZMod q)) hH
        simpa [ZMod.unitsMap_def, CohCarrier.gamma0Units, CongruenceSubgroup.Gamma0Map] using this
      · have := congrArg (fun u : (ZMod ℓ)ˣ => (u : ZMod ℓ)) hK
        simpa [ZMod.unitsMap_def, CohCarrier.gamma0Units, CongruenceSubgroup.Gamma0Map] using this
    · rintro ⟨h10, h11, h1ℓ⟩
      refine ⟨CongruenceSubgroup.Gamma0_mem.mpr h10, ?_, ?_⟩
      · ext
        simp [ZMod.unitsMap_def, CohCarrier.gamma0Units, CongruenceSubgroup.Gamma0Map, h11]
      · ext
        simp [ZMod.unitsMap_def, CohCarrier.gamma0Units, CongruenceSubgroup.Gamma0Map, h1ℓ]
  subst hK hK₀
  refine ⟨fun x => W1xLBCH.coeffMap_mem_KL ι₀ x.2, fun γ hγ τ hτ => ?_⟩

  obtain ⟨τ₀, hτ₀⟩ :=
    ModularCurve.FullLevel.exists_isLevelAutAt_of_mem_gamma0_of_eq_levelH_inf_ker q M' hqM' ℓ hℓM' L₀ (ξ₀ ^ ℓ) hζ₀
      H₁ hH₁ _ rfl γ hγ
  refine ⟨τ₀, hτ₀, fun x hx => ?_⟩
  obtain ⟨ι, hι⟩ := hι

  have hι₁ : ι (ι₀ (ξ₀ ^ ℓ)) = W1xLBCH.eq q := by
    have hℓC : (ℓ : ℂ) ≠ 0 := by exact_mod_cast hℓp.ne_zero
    have hqC : (q : ℂ) ≠ 0 := by exact_mod_cast hqp.ne_zero
    rw [map_pow, map_pow, hι, ← Complex.exp_nat_mul]
    congr 1
    field_simp
  rw [← map_pow] at hτ
  have hP := W1xLBCH.P.of_mem (τ := τ) (τ₀ := τ₀) hmem hℓM' hcop ι hι₁ γ⁻¹ (inv_mem hγ) hτ hτ₀ x.2
  exact hP.2.2 x.2 hx

end S_ModularCurve_FullLevel_AuxLevelOne_exists_isLevelAutAt_restrict_coeffMap_of_isLevelAutAt_of_isPrimitiveRoot_mul_of_dvd
end P2MW
export P2MW.S_ModularCurve_FullLevel_AuxLevelOne_exists_isLevelAutAt_restrict_coeffMap_of_isLevelAutAt_of_isPrimitiveRoot_mul_of_dvd (solution)
