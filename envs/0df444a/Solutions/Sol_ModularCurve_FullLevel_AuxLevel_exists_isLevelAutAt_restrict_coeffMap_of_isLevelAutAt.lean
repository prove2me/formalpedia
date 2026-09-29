-- Prove2me | solution 1 for ModularCurve.FullLevel.AuxLevel.exists_isLevelAutAt_restrict_coeffMap_of_isLevelAutAt
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.339302+00:00
-- url     : https://prove2.me/submissions/37965629-e578-5985-bd51-654ab51c48aa

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_ModularCurve_FullLevelLevelAutAt
import Theorems.Thm_ModularCurve_FullLevel_AuxLevel_exists_isLevelAutAt_of_mem_gamma0_of_exists_ringHom
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_AuxLevel_exists_isLevelAutAt_restrict_coeffMap_of_isLevelAutAt

open scoped MatrixGroups ModularForm
open Matrix ModularCurve ModularCurve.FullLevel CongruenceSubgroup
open scoped Pointwise

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace W1xLBC
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

variable {m : ℕ} [NeZero m] {M' : ℕ}

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

theorem upperLeft_of_mem_GH {δ : SL(2, ℤ)} (hδ : δ ∈ GH m M') : ((δ 0 0 : ℤ) : ZMod m) = 1 := by
  obtain ⟨h10, h11⟩ := (mem_GH_iff δ).mp hδ
  have hq10 : ((δ 1 0 : ℤ) : ZMod m) = 0 := by
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h10 ⊢
    exact dvd_trans q_dvd_level h10
  have hdet := Matrix.SpecialLinearGroup.det_coe δ
  rw [Matrix.det_fin_two] at hdet
  have := congrArg (fun z : ℤ => (z : ZMod m)) hdet
  simp only [Int.cast_sub, Int.cast_mul, Int.cast_one, hq10, h11, mul_one, mul_zero, sub_zero] at this
  exact this

theorem q_dvd_lowerLeft_of_mem_GH {δ : SL(2, ℤ)} (hδ : δ ∈ GH m M') : (m : ℤ) ∣ δ 1 0 := by
  obtain ⟨h10, _⟩ := (mem_GH_iff δ).mp hδ
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h10
  exact dvd_trans q_dvd_level h10

theorem SLq_upSL_of_mem_GH {δ : SL(2, ℤ)} (hδ : δ ∈ GH m M') :
    SLq m (upSL δ (q_dvd_lowerLeft_of_mem_GH hδ)) = 1 := by
  obtain ⟨h10, h11⟩ := (mem_GH_iff δ).mp hδ
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h10
  obtain ⟨c, hc⟩ := h10
  rw [SLq_eq_one_iff]
  refine ⟨?_, ?_, ?_, ?_⟩
  · show ((δ 0 0 : ℤ) : ZMod m) = 1
    exact upperLeft_of_mem_GH hδ
  · show (((m : ℤ) * δ 0 1 : ℤ) : ZMod m) = 0
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]; exact Dvd.intro _ rfl
  · show ((δ 1 0 / m : ℤ) : ZMod m) = 0
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd, hc]
    refine ⟨M' * c, ?_⟩
    push_cast
    rw [show (m : ℤ) ^ 2 * M' * c = m * (m * (M' * c)) by ring, Int.mul_ediv_cancel_left _ (mneZ m)]
  · show ((δ 1 1 : ℤ) : ZMod m) = 1
    exact h11

theorem upSL_mem_Gamma0 {δ : SL(2, ℤ)} (hδ : δ ∈ GH m M') :
    upSL δ (q_dvd_lowerLeft_of_mem_GH hδ) ∈ Gamma0 M' := by
  obtain ⟨h10, _⟩ := (mem_GH_iff δ).mp hδ
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

theorem exists_conj_mem {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 M') {δ : SL(2, ℤ)} (hδ : δ ∈ GH m M') :
    ∃ δ' ∈ GH m M', ((δ' : SL(2, ℤ)) : GL (Fin 2) ℝ) = conjElemN m γ * (δ : GL (Fin 2) ℝ) * (conjElemN m γ)⁻¹ := by
  set u : SL(2, ℤ) := upSL δ (q_dvd_lowerLeft_of_mem_GH hδ) with hu
  set ε : SL(2, ℤ) := γ * u * γ⁻¹ with hε
  have hεq : SLq m ε = 1 := by
    rw [hε, map_mul, map_mul, SLq_upSL_of_mem_GH hδ, mul_one, map_inv, mul_inv_cancel]
  obtain ⟨e00, e01, e10, e11⟩ := (SLq_eq_one_iff ε).mp hεq
  have hε0 : ε ∈ Gamma0 M' := mul_mem (mul_mem hγ (upSL_mem_Gamma0 hδ)) (inv_mem hγ)
  have h01 : (m : ℤ) ∣ ε 0 1 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp e01
  refine ⟨downSL ε h01, ?_, ?_⟩
  · rw [mem_GH_iff]
    refine ⟨?_, e11⟩
    show (((m : ℤ) * ε 1 0 : ℤ) : ZMod (m ^ 2 * M')) = 0
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    have hq : (m : ℤ) ∣ ε 1 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp e10
    have hM : (M' : ℤ) ∣ ε 1 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (Gamma0_mem.mp hε0)
    have hcop : IsCoprime (m : ℤ) (M' : ℤ) := by
      rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd_natCast_natCast]
      exact hmM'
    obtain ⟨c, hc⟩ := hcop.mul_dvd hq hM
    refine ⟨c, ?_⟩
    rw [hc]; push_cast; ring
  · obtain ⟨c, hc⟩ := h01
    have hd := downSL_coe ε ⟨c, hc⟩
    have hup := upSL_coe δ (q_dvd_lowerLeft_of_mem_GH hδ)
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
    Γ m M' ≤ ConjAct.toConjAct (conjElemN m γ)⁻¹ • Γ m M' := by
  rintro x ⟨δ, hδ, rfl⟩
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← ConjAct.toConjAct_inv, inv_inv,
    ConjAct.toConjAct_smul]
  obtain ⟨δ', hδ', e⟩ := exists_conj_mem hmM' hγ hδ
  exact ⟨δ', hδ', e⟩

variable [NeZero M']

def sl {k : ℤ} (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M') (f : ModularForm (Γ m M') k) :
    ModularForm (Γ m M') k :=
  restrictForm (le_conj hmM' hγ) (ModularForm.translate f (conjElemN m γ))

@[scoped simp]
theorem coe_sl {k : ℤ} (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M') (f : ModularForm (Γ m M') k) :
    ⇑(sl hmM' γ hγ f) = ⇑f ∣[k] conjElemN m γ := rfl

theorem sl_inv_sl_apply {k : ℤ} (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M') (f : ModularForm (Γ m M') k) :
    ⇑(sl hmM' γ⁻¹ (inv_mem hγ) (sl hmM' γ hγ f)) = ⇑f := by
  rw [coe_sl, coe_sl, ← SlashAction.slash_mul, conjElemN_eq, conjElemN_eq]
  simp only [map_inv]
  rw [show (Dr m)⁻¹ * (γ : GL (Fin 2) ℝ) * Dr m * ((Dr m)⁻¹ * (γ : GL (Fin 2) ℝ)⁻¹ * Dr m) = 1 by group,
    SlashAction.slash_one]

theorem sl_ne_zero {k : ℤ} (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M') {f : ModularForm (Γ m M') k}
    (hf : f ≠ 0) : sl hmM' γ hγ f ≠ 0 := by
  intro h
  apply hf
  have e := sl_inv_sl_apply hmM' γ hγ f
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

variable {m : ℕ} [NeZero m] {M' : ℕ}

theorem qC_eq_zero_iff [NeZero M'] {k : ℤ} (f : ModularForm (Γ m M') k) : qC f = 0 ↔ f = 0 := by
  rw [qC, ← ModularForm.qExpansion_eq_zero_iff one_pos one_mem_strictPeriods f]
  exact map_eq_zero_iff _ HahnSeries.ofPowerSeries_injective

theorem ne_zero_of_intSeriesC_ne_zero' [NeZero M'] {k : ℤ} {g : ModularForm (Γ m M') k} {pg : PowerSeries ℤ}
    (hg : IsIntegralQExp (⇑g) pg) (hg0 : intSeriesC ℚ pg ≠ 0) : g ≠ 0 := by
  intro h
  apply hg0
  have h1 : ιC (intSeriesC ℚ pg) = 0 := by
    rw [ιC_intSeriesC hg, h]
    exact (qC_eq_zero_iff (0 : ModularForm (Γ m M') k)).2 rfl
  exact (map_eq_zero_iff _ (RingHom.injective _)).1 h1

end QC

section Main

open UpperHalfPlane IntermediateField HahnSeries
open scoped ModularForm

variable {q : ℕ} [NeZero q] {M' : ℕ} [NeZero M'] {ℓ : ℕ} [NeZero ℓ]
  {L₀ : Type} [Field L₀] [CharZero L₀] {L : Type} [Field L] [CharZero L] (ι₀ : L₀ →+* L)

abbrev KL (L : Type) [Field L] [CharZero L] (q ℓ M' : ℕ) : IntermediateField L (LaurentSeries L) :=
  laurentBaseChange L (xHFunctionField ((q * ℓ) ^ 2 * M') (levelH (q * ℓ) M'))

omit [NeZero q] [NeZero M'] [NeZero ℓ] in

theorem coeffMap_coeffEmb₀ (x : LaurentSeries ℚ) : coeffMap ι₀ (coeffEmb L₀ x) = coeffEmb L x := by
  rw [coeffEmb, coeffEmb, coeffMap_coeffMap]
  exact coeffMap_congr (Subsingleton.elim _ _) x

omit [NeZero q] [NeZero M'] [NeZero ℓ] in

theorem coeffMap_algebraMap₀ (c : L₀) :
    coeffMap ι₀ (algebraMap L₀ (LaurentSeries L₀) c) = algebraMap L (LaurentSeries L) (ι₀ c) := by
  rw [algebraMap_laurentSeries_eq_single, algebraMap_laurentSeries_eq_single, coeffMap_single]

theorem coeffMap_mem_KL {x : LaurentSeries L₀} (hx : x ∈ KL L₀ q ℓ M') : coeffMap ι₀ x ∈ KL L q ℓ M' := by
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

variable (τ : KL L q ℓ M' ≃ₐ[L] KL L q ℓ M') (τ₀ : KL L₀ q ℓ M' ≃ₐ[L₀] KL L₀ q ℓ M')

variable (q M' ℓ) in

def P (x : LaurentSeries L₀) : Prop :=
  x ∈ KL L₀ q ℓ M' ∧ coeffMap ι₀ x ∈ KL L q ℓ M' ∧
    ∀ (h₁ : x ∈ KL L₀ q ℓ M') (h₂ : coeffMap ι₀ x ∈ KL L q ℓ M'),
      ((τ ⟨coeffMap ι₀ x, h₂⟩ : KL L q ℓ M') : LaurentSeries L) =
        coeffMap ι₀ ((τ₀ ⟨x, h₁⟩ : KL L₀ q ℓ M') : LaurentSeries L₀)

variable {ι₀ τ τ₀}

theorem P.mk' {x : LaurentSeries L₀} (h₁ : x ∈ KL L₀ q ℓ M')
    (h : ((τ ⟨coeffMap ι₀ x, coeffMap_mem_KL ι₀ h₁⟩ : KL L q ℓ M') : LaurentSeries L) =
      coeffMap ι₀ ((τ₀ ⟨x, h₁⟩ : KL L₀ q ℓ M') : LaurentSeries L₀)) :
    P q M' ℓ ι₀ τ τ₀ x :=
  ⟨h₁, coeffMap_mem_KL ι₀ h₁, fun _ _ => h⟩

theorem P.mem₂ {x : LaurentSeries L₀} (hx : P q M' ℓ ι₀ τ τ₀ x) : coeffMap ι₀ x ∈ KL L q ℓ M' := hx.2.1

theorem P.out {x : LaurentSeries L₀} (hx : P q M' ℓ ι₀ τ τ₀ x) :
    ((τ ⟨coeffMap ι₀ x, hx.mem₂⟩ : KL L q ℓ M') : LaurentSeries L) =
      coeffMap ι₀ ((τ₀ ⟨x, hx.1⟩ : KL L₀ q ℓ M') : LaurentSeries L₀) :=
  hx.2.2 hx.1 hx.2.1

theorem P.add {x y : LaurentSeries L₀} (hx : P q M' ℓ ι₀ τ τ₀ x) (hy : P q M' ℓ ι₀ τ τ₀ y) :
    P q M' ℓ ι₀ τ τ₀ (x + y) := by
  have h₁ : x + y ∈ KL L₀ q ℓ M' := add_mem hx.1 hy.1
  refine P.mk' h₁ ?_
  have e : (⟨coeffMap ι₀ (x + y), coeffMap_mem_KL ι₀ h₁⟩ : KL L q ℓ M') =
      ⟨coeffMap ι₀ x, hx.mem₂⟩ + ⟨coeffMap ι₀ y, hy.mem₂⟩ :=
    Subtype.ext (by simp [map_add])
  have e' : (⟨x + y, h₁⟩ : KL L₀ q ℓ M') = ⟨x, hx.1⟩ + ⟨y, hy.1⟩ := Subtype.ext rfl
  rw [e, e', map_add, map_add]
  push_cast
  rw [map_add, hx.out, hy.out]

theorem P.mul {x y : LaurentSeries L₀} (hx : P q M' ℓ ι₀ τ τ₀ x) (hy : P q M' ℓ ι₀ τ τ₀ y) :
    P q M' ℓ ι₀ τ τ₀ (x * y) := by
  have h₁ : x * y ∈ KL L₀ q ℓ M' := mul_mem hx.1 hy.1
  refine P.mk' h₁ ?_
  have e : (⟨coeffMap ι₀ (x * y), coeffMap_mem_KL ι₀ h₁⟩ : KL L q ℓ M') =
      ⟨coeffMap ι₀ x, hx.mem₂⟩ * ⟨coeffMap ι₀ y, hy.mem₂⟩ :=
    Subtype.ext (by simp [map_mul])
  have e' : (⟨x * y, h₁⟩ : KL L₀ q ℓ M') = ⟨x, hx.1⟩ * ⟨y, hy.1⟩ := Subtype.ext rfl
  rw [e, e', map_mul, map_mul]
  push_cast
  rw [map_mul, hx.out, hy.out]

theorem P.neg {x : LaurentSeries L₀} (hx : P q M' ℓ ι₀ τ τ₀ x) : P q M' ℓ ι₀ τ τ₀ (-x) := by
  have h₁ : -x ∈ KL L₀ q ℓ M' := neg_mem hx.1
  refine P.mk' h₁ ?_
  have e : (⟨coeffMap ι₀ (-x), coeffMap_mem_KL ι₀ h₁⟩ : KL L q ℓ M') = -⟨coeffMap ι₀ x, hx.mem₂⟩ :=
    Subtype.ext (by simp [map_neg])
  have e' : (⟨-x, h₁⟩ : KL L₀ q ℓ M') = -⟨x, hx.1⟩ := Subtype.ext rfl
  rw [e, e', map_neg, map_neg]
  push_cast
  rw [map_neg, hx.out]

theorem P.inv {x : LaurentSeries L₀} (hx : P q M' ℓ ι₀ τ τ₀ x) : P q M' ℓ ι₀ τ τ₀ x⁻¹ := by
  have h₁ : x⁻¹ ∈ KL L₀ q ℓ M' := inv_mem hx.1
  refine P.mk' h₁ ?_
  have e : (⟨coeffMap ι₀ x⁻¹, coeffMap_mem_KL ι₀ h₁⟩ : KL L q ℓ M') = (⟨coeffMap ι₀ x, hx.mem₂⟩ : KL L q ℓ M')⁻¹ :=
    Subtype.ext (by simp [map_inv₀])
  have e' : (⟨x⁻¹, h₁⟩ : KL L₀ q ℓ M') = (⟨x, hx.1⟩ : KL L₀ q ℓ M')⁻¹ := Subtype.ext rfl
  rw [e, e', map_inv₀, map_inv₀]
  push_cast
  rw [map_inv₀, hx.out]

theorem P.one : P q M' ℓ ι₀ τ τ₀ (1 : LaurentSeries L₀) := by
  refine P.mk' (one_mem _) ?_
  have e : (⟨coeffMap ι₀ 1, coeffMap_mem_KL ι₀ (one_mem _)⟩ : KL L q ℓ M') = 1 := Subtype.ext (by simp)
  have e' : (⟨(1 : LaurentSeries L₀), one_mem _⟩ : KL L₀ q ℓ M') = 1 := Subtype.ext rfl
  rw [e, e', map_one, map_one]
  push_cast
  rw [map_one]

theorem P_algebraMap (c : L₀) : P q M' ℓ ι₀ τ τ₀ (algebraMap L₀ (LaurentSeries L₀) c) := by
  have h₁ : algebraMap L₀ (LaurentSeries L₀) c ∈ KL L₀ q ℓ M' := IntermediateField.algebraMap_mem _ _
  refine P.mk' h₁ ?_
  have e : (⟨coeffMap ι₀ (algebraMap L₀ (LaurentSeries L₀) c), coeffMap_mem_KL ι₀ h₁⟩ : KL L q ℓ M') =
      algebraMap L (KL L q ℓ M') (ι₀ c) :=
    Subtype.ext (by
      change coeffMap ι₀ (algebraMap L₀ (LaurentSeries L₀) c) = _
      rw [coeffMap_algebraMap₀]; rfl)
  have e' : (⟨algebraMap L₀ (LaurentSeries L₀) c, h₁⟩ : KL L₀ q ℓ M') = algebraMap L₀ (KL L₀ q ℓ M') c :=
    Subtype.ext rfl
  rw [e, e', AlgEquiv.commutes, AlgEquiv.commutes]
  change algebraMap L (LaurentSeries L) (ι₀ c) = coeffMap ι₀ (algebraMap L₀ (LaurentSeries L₀) c)
  rw [coeffMap_algebraMap₀]

section Gen

variable (hqM' : Nat.Coprime (q * ℓ) M')
include hqM'

theorem P.gen {ξ₀ : L₀} (ι : L →+* ℂ) (hι : ι (ι₀ ξ₀) = eq (q * ℓ))
    (δ : SL(2, ℤ)) (hδ : δ ∈ Gamma0 M')
    (hτ : IsLevelAutAt L (q * ℓ) (ι₀ ξ₀) (q * ℓ) ((q * ℓ) ^ 2 * M') (levelH (q * ℓ) M') δ (KL L q ℓ M') τ)
    (hτ₀ : IsLevelAutAt L₀ (q * ℓ) ξ₀ (q * ℓ) ((q * ℓ) ^ 2 * M') (levelH (q * ℓ) M') δ (KL L₀ q ℓ M') τ₀)
    {y : LaurentSeries ℚ} (hy : y ∈ intFormRatiosC ℚ (GH (q * ℓ) M')) : P q M' ℓ ι₀ τ τ₀ (coeffEmb L₀ y) := by
  obtain ⟨k, f, g, pf, pg, hf, hg, hg0, rfl⟩ := hy
  have h₁ : coeffEmb L₀ (intSeriesC ℚ pf / intSeriesC ℚ pg) ∈ KL L₀ q ℓ M' :=
    coeffEmb_mem_laurentBaseChange L₀ (div_mem_qExpFunctionFieldC f g hf hg hg0)
  refine P.mk' h₁ ?_
  set w : KL L q ℓ M' := ⟨coeffMap ι₀ (coeffEmb L₀ (intSeriesC ℚ pf / intSeriesC ℚ pg)), coeffMap_mem_KL ι₀ h₁⟩
    with hwdef
  set x₀ : KL L₀ q ℓ M' := ⟨coeffEmb L₀ (intSeriesC ℚ pf / intSeriesC ℚ pg), h₁⟩ with hx₀def
  have hw : ((w : KL L q ℓ M') : LaurentSeries L) = coeffEmb L (intSeriesC ℚ pf / intSeriesC ℚ pg) :=
    coeffMap_coeffEmb₀ ι₀ _

  set fδ : ModularForm (Γ (q * ℓ) M') k := sl hqM' δ hδ f with hfδdef
  set gδ : ModularForm (Γ (q * ℓ) M') k := sl hqM' δ hδ g with hgδdef

  have keyτ := hτ k f g pf pg hf hg hg0 w hw ι (by rw [hι])
  change coeffMap ι ((τ w : KL L q ℓ M') : LaurentSeries L) * qC (⇑gδ) = qC (⇑fδ) at keyτ

  have keyτ₀ := hτ₀ k f g pf pg hf hg hg0 x₀ rfl (ι.comp ι₀) (by rw [RingHom.comp_apply, hι])
  change coeffMap (ι.comp ι₀) ((τ₀ x₀ : KL L₀ q ℓ M') : LaurentSeries L₀) * qC (⇑gδ) = qC (⇑fδ) at keyτ₀

  have hne : qC (⇑gδ) ≠ 0 := by
    intro h
    rw [qC_eq_zero_iff] at h
    exact sl_ne_zero hqM' δ hδ (ne_zero_of_intSeriesC_ne_zero' hg hg0) h
  have heq : coeffMap ι ((τ w : KL L q ℓ M') : LaurentSeries L) =
      coeffMap ι (coeffMap ι₀ ((τ₀ x₀ : KL L₀ q ℓ M') : LaurentSeries L₀)) := by
    rw [coeffMap_coeffMap]
    exact mul_right_cancel₀ hne (keyτ.trans keyτ₀.symm)
  exact ιB_injective ι heq

theorem P.of_mem_field {ξ₀ : L₀} (ι : L →+* ℂ) (hι : ι (ι₀ ξ₀) = eq (q * ℓ))
    (δ : SL(2, ℤ)) (hδ : δ ∈ Gamma0 M')
    (hτ : IsLevelAutAt L (q * ℓ) (ι₀ ξ₀) (q * ℓ) ((q * ℓ) ^ 2 * M') (levelH (q * ℓ) M') δ (KL L q ℓ M') τ)
    (hτ₀ : IsLevelAutAt L₀ (q * ℓ) ξ₀ (q * ℓ) ((q * ℓ) ^ 2 * M') (levelH (q * ℓ) M') δ (KL L₀ q ℓ M') τ₀)
    {y : LaurentSeries ℚ} (hy : y ∈ xHFunctionField ((q * ℓ) ^ 2 * M') (levelH (q * ℓ) M')) :
    P q M' ℓ ι₀ τ τ₀ (coeffEmb L₀ y) := by
  change y ∈ Subfield.closure (Set.range (algebraMap ℚ (LaurentSeries ℚ)) ∪ intFormRatiosC ℚ (GH (q * ℓ) M')) at hy
  induction hy using Subfield.closure_induction with
  | mem y hy =>
      rcases hy with ⟨r, rfl⟩ | hy
      · rw [algebraMap_laurentSeries_eq_single, coeffEmb, coeffMap_single, ← algebraMap_laurentSeries_eq_single]
        exact P_algebraMap _
      · exact P.gen hqM' ι hι δ hδ hτ hτ₀ hy
  | one => rw [map_one]; exact P.one
  | add x y _ _ hx hy => rw [map_add]; exact hx.add hy
  | neg x _ hx => rw [map_neg]; exact hx.neg
  | inv x _ hx => rw [map_inv₀]; exact hx.inv
  | mul x y _ _ hx hy => rw [map_mul]; exact hx.mul hy

theorem P.of_mem {ξ₀ : L₀} (ι : L →+* ℂ) (hι : ι (ι₀ ξ₀) = eq (q * ℓ))
    (δ : SL(2, ℤ)) (hδ : δ ∈ Gamma0 M')
    (hτ : IsLevelAutAt L (q * ℓ) (ι₀ ξ₀) (q * ℓ) ((q * ℓ) ^ 2 * M') (levelH (q * ℓ) M') δ (KL L q ℓ M') τ)
    (hτ₀ : IsLevelAutAt L₀ (q * ℓ) ξ₀ (q * ℓ) ((q * ℓ) ^ 2 * M') (levelH (q * ℓ) M') δ (KL L₀ q ℓ M') τ₀)
    {x : LaurentSeries L₀} (hx : x ∈ KL L₀ q ℓ M') : P q M' ℓ ι₀ τ τ₀ x := by
  rw [mem_laurentBaseChange_iff] at hx
  induction hx using Subfield.closure_induction with
  | mem y hy =>
      rcases hy with ⟨c, rfl⟩ | ⟨z, hz, rfl⟩
      · exact P_algebraMap c
      · exact P.of_mem_field hqM' ι hι δ hδ hτ hτ₀ hz
  | one => exact P.one
  | add x y _ _ hx hy => exact hx.add hy
  | neg x _ hx => exact hx.neg
  | inv x _ hx => exact hx.inv
  | mul x y _ _ hx hy => exact hx.mul hy

end Gen

end Main

end W1xLBC
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_AuxLevel_exists_isLevelAutAt_restrict_coeffMap_of_isLevelAutAt.W1xLBC"

end
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_AuxLevel_exists_isLevelAutAt_restrict_coeffMap_of_isLevelAutAt.W1xLBC"

theorem solution
    (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ3 : 3 ≤ ℓ) (hℓq : ℓ ≠ q) (hℓM' : ¬ ℓ ∣ M')
    (L₀ : Type) [Field L₀] [CharZero L₀] [IsCyclotomicExtension {q * ℓ} ℚ L₀]
    (ξ₀ : L₀) (hξ₀ : IsPrimitiveRoot ξ₀ (q * ℓ))
    (L : Type) [Field L] [CharZero L] (ι₀ : L₀ →+* L)
    (hι : ∃ ι : L →+* ℂ, ι (ι₀ ξ₀) = Complex.exp (2 * Real.pi * Complex.I / (q * ℓ)))
    (K₀ : IntermediateField L₀ (LaurentSeries L₀))
    (hK₀ : K₀ = ModularCurve.laurentBaseChange L₀
      (ModularCurve.xHFunctionField ((q * ℓ) ^ 2 * M') (ModularCurve.FullLevel.levelH (q * ℓ) M')))
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L
      (ModularCurve.xHFunctionField ((q * ℓ) ^ 2 * M') (ModularCurve.FullLevel.levelH (q * ℓ) M'))) :

    (∀ x : ↥K₀, ModularCurve.coeffMap ι₀ ((x : ↥K₀) : LaurentSeries L₀) ∈ K) ∧

    (∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 M' →
      ∀ τ : ↥K ≃ₐ[L] ↥K, ModularCurve.FullLevel.IsLevelAutAt L (q * ℓ) (ι₀ ξ₀) (q * ℓ) ((q * ℓ) ^ 2 * M')
          (ModularCurve.FullLevel.levelH (q * ℓ) M') γ⁻¹ K τ →
        ∃ τ₀ : ↥K₀ ≃ₐ[L₀] ↥K₀,
          ModularCurve.FullLevel.IsLevelAutAt L₀ (q * ℓ) ξ₀ (q * ℓ) ((q * ℓ) ^ 2 * M')
            (ModularCurve.FullLevel.levelH (q * ℓ) M') γ⁻¹ K₀ τ₀ ∧
          ∀ (x : ↥K₀) (hx : ModularCurve.coeffMap ι₀ ((x : ↥K₀) : LaurentSeries L₀) ∈ K),
            ((τ ⟨_, hx⟩ : ↥K) : LaurentSeries L) = ModularCurve.coeffMap ι₀ ((τ₀ x : ↥K₀) : LaurentSeries L₀)) := by
  have hqp : q.Prime := Fact.out
  have hℓp : ℓ.Prime := Fact.out
  haveI : NeZero q := ⟨hqp.ne_zero⟩
  haveI : NeZero ℓ := ⟨hℓp.ne_zero⟩
  have hcop : Nat.Coprime (q * ℓ) M' :=
    Nat.Coprime.mul_left ((Nat.Prime.coprime_iff_not_dvd hqp).2 hqM') ((Nat.Prime.coprime_iff_not_dvd hℓp).2 hℓM')

  have hι' : ∃ ι' : L₀ →+* ℂ, ι' ξ₀ = Complex.exp (2 * Real.pi * Complex.I / (q * ℓ)) := by
    obtain ⟨ι, hι⟩ := hι
    exact ⟨ι.comp ι₀, by rw [RingHom.comp_apply, hι]⟩
  subst hK hK₀
  refine ⟨fun x => W1xLBC.coeffMap_mem_KL ι₀ x.2, fun γ hγ τ hτ => ?_⟩

  obtain ⟨τ₀, hτ₀⟩ :=
    ModularCurve.FullLevel.AuxLevel.exists_isLevelAutAt_of_mem_gamma0_of_exists_ringHom q hq M' hqM' ℓ hℓ3 hℓq
      hℓM' L₀ ξ₀ hξ₀ hι' _ rfl γ hγ
  refine ⟨τ₀, hτ₀, fun x hx => ?_⟩
  obtain ⟨ι, hι⟩ := hι
  have hι₁ : ι (ι₀ ξ₀) = W1xLBC.eq (q * ℓ) := by
    rw [hι]
    change _ = Complex.exp (2 * Real.pi * Complex.I / ((q * ℓ : ℕ) : ℂ))
    push_cast
    rfl
  have hP := W1xLBC.P.of_mem (τ := τ) (τ₀ := τ₀) hcop ι hι₁ γ⁻¹ (inv_mem hγ) hτ hτ₀ x.2
  exact hP.2.2 x.2 hx

end S_ModularCurve_FullLevel_AuxLevel_exists_isLevelAutAt_restrict_coeffMap_of_isLevelAutAt
end P2MW
export P2MW.S_ModularCurve_FullLevel_AuxLevel_exists_isLevelAutAt_restrict_coeffMap_of_isLevelAutAt (solution)
