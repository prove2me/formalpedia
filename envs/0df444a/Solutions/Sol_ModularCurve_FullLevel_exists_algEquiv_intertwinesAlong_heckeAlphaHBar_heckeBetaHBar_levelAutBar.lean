-- Prove2me | solution 1 for ModularCurve.FullLevel.exists_algEquiv_intertwinesAlong_heckeAlphaHBar_heckeBetaHBar_levelAutBar
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.339302+00:00
-- url     : https://prove2.me/submissions/edd17ad2-be72-5585-89f9-0ce2547ab25b

import Mathlib
import Definitions.Def_ModularCurve_FullLevelJacobian
import Theorems.Thm_ModularCurve_FullLevel_levelAutInputs_of_not_dvd
import Theorems.Thm_UpperHalfPlane_qCoeff_comp_heckeDiagMatrix_smul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_exists_algEquiv_intertwinesAlong_heckeAlphaHBar_heckeBetaHBar_levelAutBar

open scoped MatrixGroups
open Matrix ModularCurve ModularCurve.FullLevel CongruenceSubgroup
open scoped Pointwise

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace W1LT
variable (q : ℕ) [Fact q.Prime]

theorem qpos : 0 < q := (Fact.out : q.Prime).pos
theorem qne : (q : ℝ) ≠ 0 := by exact_mod_cast (Fact.out : q.Prime).ne_zero
theorem qneZ : (q : ℤ) ≠ 0 := by exact_mod_cast (Fact.out : q.Prime).ne_zero

def Dr : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![(q : ℝ), 0; 0, 1]
    (by rw [Matrix.det_fin_two_of]; simp [qne q])

@[scoped simp] theorem Dr_coe : ((Dr q : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = !![(q : ℝ), 0; 0, 1] := rfl

@[scoped simp] theorem conjElem_coe (γ : SL(2, ℤ)) : ((conjElem q γ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
    !![((γ 0 0 : ℤ) : ℝ), ((γ 0 1 : ℤ) : ℝ) / q; (q : ℝ) * ((γ 1 0 : ℤ) : ℝ), ((γ 1 1 : ℤ) : ℝ)] := rfl

theorem Dr_mul_conjElem (γ : SL(2, ℤ)) : Dr q * conjElem q γ = (γ : GL (Fin 2) ℝ) * Dr q := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  simp only [Matrix.GeneralLinearGroup.coe_mul, Dr_coe, conjElem_coe]
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, mul_div_assoc', mul_div_cancel_left₀ _ (qne q), mul_comm]

theorem conjElem_eq (γ : SL(2, ℤ)) : conjElem q γ = (Dr q)⁻¹ * (γ : GL (Fin 2) ℝ) * Dr q := by
  rw [mul_assoc, ← Dr_mul_conjElem, inv_mul_cancel_left]

theorem conjElem_mul (γ δ : SL(2, ℤ)) : conjElem q (γ * δ) = conjElem q γ * conjElem q δ := by
  simp only [conjElem_eq, map_mul]; group

theorem conjElem_one : conjElem q 1 = 1 := by
  simp only [conjElem_eq, map_one]; group

theorem det_coeSL (γ : SL(2, ℤ)) : ((γ : GL (Fin 2) ℝ)).det = 1 := by
  ext
  simp

theorem det_conjElem (γ : SL(2, ℤ)) : (conjElem q γ).det = 1 := by
  rw [conjElem_eq, map_mul, map_mul, map_inv, det_coeSL, mul_one, inv_mul_cancel]

theorem det_conjElem_val (γ : SL(2, ℤ)) : ((conjElem q γ).det : ℝ) = 1 := by
  rw [det_conjElem]; rfl

variable {q}

def upMat (δ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ := !![δ 0 0, (q : ℤ) * δ 0 1; δ 1 0 / q, δ 1 1]

theorem det_upMat (δ : SL(2, ℤ)) (h : (q : ℤ) ∣ δ 1 0) : (upMat (q := q) δ).det = 1 := by
  obtain ⟨c, hc⟩ := h
  have hdet := Matrix.SpecialLinearGroup.det_coe δ
  rw [Matrix.det_fin_two] at hdet ⊢
  have h1 : (q : ℤ) * c / q = c := by rw [mul_comm]; exact Int.mul_ediv_cancel c (qneZ q)
  simp only [upMat, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, hc, h1] at hdet ⊢
  linear_combination hdet

def upSL (δ : SL(2, ℤ)) (h : (q : ℤ) ∣ δ 1 0) : SL(2, ℤ) := ⟨upMat (q := q) δ, det_upMat δ h⟩

def downMat (ε : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ := !![ε 0 0, ε 0 1 / q; (q : ℤ) * ε 1 0, ε 1 1]

theorem det_downMat (ε : SL(2, ℤ)) (h : (q : ℤ) ∣ ε 0 1) : (downMat (q := q) ε).det = 1 := by
  obtain ⟨b, hb⟩ := h
  have hdet := Matrix.SpecialLinearGroup.det_coe ε
  rw [Matrix.det_fin_two] at hdet ⊢
  have h1 : (q : ℤ) * b / q = b := by rw [mul_comm]; exact Int.mul_ediv_cancel b (qneZ q)
  simp only [downMat, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, hb, h1] at hdet ⊢
  linear_combination hdet

def downSL (ε : SL(2, ℤ)) (h : (q : ℤ) ∣ ε 0 1) : SL(2, ℤ) := ⟨downMat (q := q) ε, det_downMat ε h⟩

theorem upSL_coe (δ : SL(2, ℤ)) (h : (q : ℤ) ∣ δ 1 0) :
    ((upSL δ h : SL(2, ℤ)) : GL (Fin 2) ℝ) * Dr q = Dr q * (δ : GL (Fin 2) ℝ) := by
  obtain ⟨c, hc⟩ := h
  have h1 : (q : ℤ) * c / q = c := by rw [mul_comm]; exact Int.mul_ediv_cancel c (qneZ q)
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  simp only [Matrix.GeneralLinearGroup.coe_mul, Dr_coe]
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, upSL, upMat, hc, h1] <;> ring

theorem downSL_coe (ε : SL(2, ℤ)) (h : (q : ℤ) ∣ ε 0 1) :
    Dr q * ((downSL ε h : SL(2, ℤ)) : GL (Fin 2) ℝ) = (ε : GL (Fin 2) ℝ) * Dr q := by
  obtain ⟨b, hb⟩ := h
  have h1 : (q : ℤ) * b / q = b := by rw [mul_comm]; exact Int.mul_ediv_cancel b (qneZ q)
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  simp only [Matrix.GeneralLinearGroup.coe_mul, Dr_coe]
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, downSL, downMat, hb, h1] <;> ring

end W1LT
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_exists_algEquiv_intertwinesAlong_heckeAlphaHBar_heckeBetaHBar_levelAutBar.W1LT"

namespace W1LT
variable (q : ℕ) [Fact q.Prime] (M' : ℕ)

abbrev GH : Subgroup SL(2, ℤ) := CohCarrier.GammaH (q ^ 2 * M') (levelH q M')

abbrev Γ : Subgroup (GL (Fin 2) ℝ) := ((GH q M' : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))

variable {q M'}

theorem mem_GH_iff (A : SL(2, ℤ)) :
    A ∈ GH q M' ↔ ((A 1 0 : ℤ) : ZMod (q ^ 2 * M')) = 0 ∧ ((A 1 1 : ℤ) : ZMod q) = 1 := by
  rw [GH, CohCarrier.mem_GammaH_iff]
  constructor
  · rintro ⟨hA, hH⟩
    refine ⟨Gamma0_mem.mp hA, ?_⟩
    rw [mem_levelH_iff] at hH
    have := congrArg (fun u : (ZMod q)ˣ => (u : ZMod q)) hH
    simpa [ZMod.unitsMap_def, CohCarrier.gamma0Units, Gamma0Map] using this
  · rintro ⟨h10, h11⟩
    refine ⟨Gamma0_mem.mpr h10, ?_⟩
    rw [mem_levelH_iff]
    ext
    simp [ZMod.unitsMap_def, CohCarrier.gamma0Units, Gamma0Map, h11]

abbrev SLq (q : ℕ) : SL(2, ℤ) →* SL(2, ZMod q) := Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod q))

theorem SLq_apply (A : SL(2, ℤ)) (i j : Fin 2) : (SLq q A) i j = ((A i j : ℤ) : ZMod q) := by
  simp

omit [Fact q.Prime] in
theorem q_dvd_level : (q : ℤ) ∣ ((q ^ 2 * M' : ℕ) : ℤ) := ⟨q * M', by push_cast; ring⟩

theorem SLq_eq_one_iff (A : SL(2, ℤ)) : SLq q A = 1 ↔
    ((A 0 0 : ℤ) : ZMod q) = 1 ∧ ((A 0 1 : ℤ) : ZMod q) = 0 ∧ ((A 1 0 : ℤ) : ZMod q) = 0 ∧
      ((A 1 1 : ℤ) : ZMod q) = 1 := by
  constructor
  · intro h
    have e : ∀ i j, ((A i j : ℤ) : ZMod q) = (1 : SL(2, ZMod q)) i j := fun i j => by
      rw [← SLq_apply, h]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [e]
  · rintro ⟨h1, h2, h3, h4⟩
    ext i j
    rw [SLq_apply]
    fin_cases i <;> fin_cases j <;> simp [h1, h2, h3, h4]

theorem upperLeft_of_mem_GH {δ : SL(2, ℤ)} (hδ : δ ∈ GH q M') : ((δ 0 0 : ℤ) : ZMod q) = 1 := by
  obtain ⟨h10, h11⟩ := (mem_GH_iff δ).mp hδ
  have hq10 : ((δ 1 0 : ℤ) : ZMod q) = 0 := by
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h10 ⊢
    exact dvd_trans q_dvd_level h10
  have hdet := Matrix.SpecialLinearGroup.det_coe δ
  rw [Matrix.det_fin_two] at hdet
  have := congrArg (fun z : ℤ => (z : ZMod q)) hdet
  simp only [Int.cast_sub, Int.cast_mul, Int.cast_one, hq10, h11, mul_one, mul_zero, sub_zero] at this
  exact this

theorem q_dvd_lowerLeft_of_mem_GH {δ : SL(2, ℤ)} (hδ : δ ∈ GH q M') : (q : ℤ) ∣ δ 1 0 := by
  obtain ⟨h10, _⟩ := (mem_GH_iff δ).mp hδ
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h10
  exact dvd_trans q_dvd_level h10

theorem SLq_upSL_of_mem_GH {δ : SL(2, ℤ)} (hδ : δ ∈ GH q M') :
    SLq q (upSL δ (q_dvd_lowerLeft_of_mem_GH hδ)) = 1 := by
  obtain ⟨h10, h11⟩ := (mem_GH_iff δ).mp hδ
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h10
  obtain ⟨c, hc⟩ := h10
  rw [SLq_eq_one_iff]
  refine ⟨?_, ?_, ?_, ?_⟩
  · show ((δ 0 0 : ℤ) : ZMod q) = 1
    exact upperLeft_of_mem_GH hδ
  · show (((q : ℤ) * δ 0 1 : ℤ) : ZMod q) = 0
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]; exact Dvd.intro _ rfl
  · show ((δ 1 0 / q : ℤ) : ZMod q) = 0
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd, hc]
    refine ⟨M' * c, ?_⟩
    push_cast
    rw [show (q : ℤ) ^ 2 * M' * c = q * (q * (M' * c)) by ring, Int.mul_ediv_cancel_left _ (qneZ q)]
  · show ((δ 1 1 : ℤ) : ZMod q) = 1
    exact h11

theorem upSL_mem_Gamma0 {δ : SL(2, ℤ)} (hδ : δ ∈ GH q M') :
    upSL δ (q_dvd_lowerLeft_of_mem_GH hδ) ∈ Gamma0 M' := by
  obtain ⟨h10, _⟩ := (mem_GH_iff δ).mp hδ
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h10
  obtain ⟨c, hc⟩ := h10
  rw [Gamma0_mem]
  show ((δ 1 0 / q : ℤ) : ZMod M') = 0
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd, hc]
  refine ⟨q * c, ?_⟩
  push_cast
  rw [show (q : ℤ) ^ 2 * M' * c = q * (M' * (q * c)) by ring, Int.mul_ediv_cancel_left _ (qneZ q)]

variable (hqM' : ¬ q ∣ M')
include hqM'

theorem exists_conj_mem {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 M') {δ : SL(2, ℤ)} (hδ : δ ∈ GH q M') :
    ∃ δ' ∈ GH q M', ((δ' : SL(2, ℤ)) : GL (Fin 2) ℝ) = conjElem q γ * (δ : GL (Fin 2) ℝ) * (conjElem q γ)⁻¹ := by
  set u : SL(2, ℤ) := upSL δ (q_dvd_lowerLeft_of_mem_GH hδ) with hu
  set ε : SL(2, ℤ) := γ * u * γ⁻¹ with hε
  have hεq : SLq q ε = 1 := by
    rw [hε, map_mul, map_mul, SLq_upSL_of_mem_GH hδ, mul_one, map_inv, mul_inv_cancel]
  obtain ⟨e00, e01, e10, e11⟩ := (SLq_eq_one_iff ε).mp hεq
  have hε0 : ε ∈ Gamma0 M' := mul_mem (mul_mem hγ (upSL_mem_Gamma0 hδ)) (inv_mem hγ)
  have h01 : (q : ℤ) ∣ ε 0 1 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp e01
  refine ⟨downSL ε h01, ?_, ?_⟩
  · rw [mem_GH_iff]
    refine ⟨?_, e11⟩
    show (((q : ℤ) * ε 1 0 : ℤ) : ZMod (q ^ 2 * M')) = 0
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    have hq : (q : ℤ) ∣ ε 1 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp e10
    have hM : (M' : ℤ) ∣ ε 1 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (Gamma0_mem.mp hε0)
    have hcop : IsCoprime (q : ℤ) (M' : ℤ) := by
      rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd_natCast_natCast]
      exact (Nat.Prime.coprime_iff_not_dvd (Fact.out : q.Prime)).mpr hqM'
    obtain ⟨c, hc⟩ := hcop.mul_dvd hq hM
    refine ⟨c, ?_⟩
    rw [hc]; push_cast; ring
  · obtain ⟨c, hc⟩ := h01
    have hd := downSL_coe ε ⟨c, hc⟩
    have hup := upSL_coe δ (q_dvd_lowerLeft_of_mem_GH hδ)
    rw [← hu] at hup
    have e1 : ((downSL ε ⟨c, hc⟩ : SL(2, ℤ)) : GL (Fin 2) ℝ) = (Dr q)⁻¹ * (ε : GL (Fin 2) ℝ) * Dr q := by
      rw [mul_assoc, ← hd, inv_mul_cancel_left]
    have e2 : (u : GL (Fin 2) ℝ) = Dr q * (δ : GL (Fin 2) ℝ) * (Dr q)⁻¹ := by
      rw [← hup, mul_inv_cancel_right]
    rw [e1, hε]
    simp only [map_mul, map_inv]
    rw [e2, conjElem_eq]
    group

theorem le_conj {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 M') :
    Γ q M' ≤ ConjAct.toConjAct (conjElem q γ)⁻¹ • Γ q M' := by
  rintro x ⟨δ, hδ, rfl⟩
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← ConjAct.toConjAct_inv, inv_inv,
    ConjAct.toConjAct_smul]
  obtain ⟨δ', hδ', e⟩ := exists_conj_mem hqM' hγ hδ
  exact ⟨δ', hδ', e⟩

end W1LT
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_exists_algEquiv_intertwinesAlong_heckeAlphaHBar_heckeBetaHBar_levelAutBar.W1LT"

namespace W1LT

open UpperHalfPlane IntermediateField HahnSeries
open scoped ModularForm

variable {q : ℕ} [Fact q.Prime] {M' : ℕ}

omit [Fact q.Prime] in
theorem one_mem_strictPeriods : (1 : ℝ) ∈ (Γ q M').strictPeriods := by
  rw [Subgroup.strictPeriods_eq_zmultiples_one_of_T_mem (translation_mem_GammaH _ _)]
  exact AddSubgroup.mem_zmultiples _

section Slash

variable (hqM' : ¬ q ∣ M')
include hqM'

def sl {k : ℤ} (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M') (f : ModularForm (Γ q M') k) :
    ModularForm (Γ q M') k :=
  restrictForm (le_conj hqM' hγ) (ModularForm.translate f (conjElem q γ))

omit hqM' in
theorem σ_conjElem_apply (γ : SL(2, ℤ)) (z : ℂ) : UpperHalfPlane.σ (conjElem q γ) z = z := by
  rw [UpperHalfPlane.σ, if_pos (by rw [det_conjElem_val]; exact one_pos)]
  rfl

@[scoped simp]
theorem coe_sl {k : ℤ} (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M') (f : ModularForm (Γ q M') k) :
    ⇑(sl hqM' γ hγ f) = ⇑f ∣[k] conjElem q γ := rfl

theorem sl_sl {k : ℤ} (γ δ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M') (hδ : δ ∈ Gamma0 M')
    (f : ModularForm (Γ q M') k) :
    sl hqM' δ hδ (sl hqM' γ hγ f) = sl hqM' (γ * δ) (mul_mem hγ hδ) f := by
  ext τ
  simp only [coe_sl, conjElem_mul, SlashAction.slash_mul]

theorem sl_congr {k : ℤ} {γ γ' : SL(2, ℤ)} (h : γ = γ') (hγ : γ ∈ Gamma0 M') (hγ' : γ' ∈ Gamma0 M')
    (f : ModularForm (Γ q M') k) : sl hqM' γ hγ f = sl hqM' γ' hγ' f := by
  subst h; rfl

theorem sl_one {k : ℤ} (f : ModularForm (Γ q M') k) : sl hqM' 1 (one_mem _) f = f := by
  ext τ
  simp only [coe_sl, conjElem_one, SlashAction.slash_one]

theorem sl_inv_sl {k : ℤ} (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M') (f : ModularForm (Γ q M') k) :
    sl hqM' γ⁻¹ (inv_mem hγ) (sl hqM' γ hγ f) = f := by
  rw [sl_sl, sl_congr hqM' (mul_inv_cancel γ) _ (one_mem _), sl_one]

theorem sl_ne_zero {k : ℤ} (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M') {f : ModularForm (Γ q M') k}
    (hf : f ≠ 0) : sl hqM' γ hγ f ≠ 0 := by
  intro h
  apply hf
  rw [← sl_inv_sl hqM' γ hγ f, h]
  ext τ
  simp [coe_sl]

end Slash
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_exists_algEquiv_intertwinesAlong_heckeAlphaHBar_heckeBetaHBar_levelAutBar.W1LT"

section QExp

def qC (F : ℍ → ℂ) : LaurentSeries ℂ := ofPowerSeries ℤ ℂ (qExpansion 1 F)

theorem qC_eq_zero_iff {k : ℤ} (f : ModularForm (Γ q M') k) : qC f = 0 ↔ f = 0 := by
  rw [qC, ← ModularForm.qExpansion_eq_zero_iff one_pos one_mem_strictPeriods f]
  exact map_eq_zero_iff _ HahnSeries.ofPowerSeries_injective

theorem qC_sl_ne_zero (hqM' : ¬ q ∣ M') {k : ℤ} (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M')
    {g : ModularForm (Γ q M') k} (hg : g ≠ 0) : qC (sl hqM' γ hγ g) ≠ 0 := fun h =>
  sl_ne_zero hqM' γ hγ hg ((qC_eq_zero_iff _).mp h)

abbrev Qb : Type := AlgebraicClosure ℚ

abbrev ιC : LaurentSeries ℚ →+* LaurentSeries ℂ := coeffMap (algebraMap ℚ ℂ)

variable (ι₀ : Qb →+* ℂ)

abbrev ιB : LaurentSeries Qb →+* LaurentSeries ℂ := coeffMap ι₀

omit [Fact q.Prime] in
theorem ιB_injective : Function.Injective (ιB ι₀) := fun x y h =>
  HahnSeries.ext (funext fun n => ι₀.injective (by
    have := congrArg (fun z : LaurentSeries ℂ => z.coeff n) h
    simpa using this))

omit [Fact q.Prime] in
theorem ιB_coeffEmb (x : LaurentSeries ℚ) : ιB ι₀ (coeffEmb Qb x) = ιC x := by
  rw [coeffEmb, coeffMap_coeffMap]
  exact coeffMap_congr (Subsingleton.elim _ _) x

omit [Fact q.Prime] in
theorem ιC_intSeriesC {F : ℍ → ℂ} {p : PowerSeries ℤ} (h : IsIntegralQExp F p) :
    ιC (intSeriesC ℚ p) = qC F := by
  rw [qC, ← h]
  ext n
  simp only [intSeriesC, coeffMap_coeff, PowerSeries.coeff_coe]
  split_ifs
  · exact map_zero _
  · simp [PowerSeries.coeff_map]

theorem qC_ne_zero_of_intSeriesC {k : ℤ} {g : ModularForm (Γ q M') k} {pg : PowerSeries ℤ}
    (hg : IsIntegralQExp g pg) (hg0 : intSeriesC ℚ pg ≠ 0) : qC g ≠ 0 := by
  rw [← ιC_intSeriesC hg]
  exact (map_ne_zero_iff _ (RingHom.injective _)).mpr hg0

theorem ne_zero_of_intSeriesC_ne_zero {k : ℤ} {g : ModularForm (Γ q M') k} {pg : PowerSeries ℤ}
    (hg : IsIntegralQExp g pg) (hg0 : intSeriesC ℚ pg ≠ 0) : g ≠ 0 :=
  fun h => qC_ne_zero_of_intSeriesC hg hg0 ((qC_eq_zero_iff g).mpr h)

abbrev eq (q : ℕ) : ℂ := Complex.exp (2 * Real.pi * Complex.I / q)

theorem exists_emb (ζ : Idx q) : ∃ ι₀ : Qb →+* ℂ, ι₀ ζ.val = eq q := by
  haveI : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := AlgebraicClosure.isAlgebraic ℚ
  have hq0 : q ≠ 0 := (Fact.out : q.Prime).ne_zero
  have hζ := ζ.isPrimitiveRoot
  have hmin : minpoly ℚ ζ.val = Polynomial.cyclotomic q ℚ :=
    (Polynomial.cyclotomic_eq_minpoly_rat hζ (qpos q)).symm
  have hroot : eq q ∈ (minpoly ℚ ζ.val).rootSet ℂ := by
    rw [hmin, Polynomial.mem_rootSet]
    refine ⟨Polynomial.cyclotomic_ne_zero q ℚ, ?_⟩
    rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, Polynomial.map_cyclotomic]
    exact (Polynomial.isRoot_cyclotomic_iff.mpr (Complex.isPrimitiveRoot_exp q hq0)).eq_zero
  rw [← Algebra.IsAlgebraic.range_eval_eq_rootSet_minpoly ℂ ζ.val] at hroot
  obtain ⟨ψ, hψ⟩ := hroot
  exact ⟨ψ.toRingHom, hψ⟩

theorem coeffMap_qExpand {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (n : ℕ)
    [NeZero n] (x : LaurentSeries R) : coeffMap f (qExpand R n x) = qExpand S n (coeffMap f x) := by
  ext k
  by_cases hk : (n : ℤ) ∣ k
  · obtain ⟨m, rfl⟩ := hk
    rw [coeffMap_coeff, qExpand_coeff_mul, qExpand_coeff_mul, coeffMap_coeff]
  · rw [coeffMap_coeff, qExpand_coeff_of_not_dvd n _ hk, qExpand_coeff_of_not_dvd n _ hk,
      map_zero]

end QExp
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_exists_algEquiv_intertwinesAlong_heckeAlphaHBar_heckeBetaHBar_levelAutBar.W1LT"

end W1LT
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_exists_algEquiv_intertwinesAlong_heckeAlphaHBar_heckeBetaHBar_levelAutBar.W1LT"

namespace W1LT

open UpperHalfPlane IntermediateField HahnSeries
open scoped ModularForm

variable {q : ℕ} [Fact q.Prime] {M' : ℕ}

theorem GH_inf_Gamma0_eq (ℓ : ℕ) : GH q M' ⊓ Gamma0 (q ^ 2 * M' * ℓ) = GH q (M' * ℓ) := by
  ext A
  rw [Subgroup.mem_inf, mem_GH_iff, mem_GH_iff, Gamma0_mem, ZMod.intCast_zmod_eq_zero_iff_dvd,
    ZMod.intCast_zmod_eq_zero_iff_dvd, ZMod.intCast_zmod_eq_zero_iff_dvd]
  have e : ((q ^ 2 * M' * ℓ : ℕ) : ℤ) = ((q ^ 2 * (M' * ℓ) : ℕ) : ℤ) := by push_cast; ring
  constructor
  · rintro ⟨⟨_, h11⟩, h10⟩
    exact ⟨e ▸ h10, h11⟩
  · rintro ⟨h10, h11⟩
    have h10' : ((q ^ 2 * M' * ℓ : ℕ) : ℤ) ∣ A 1 0 := e.symm ▸ h10
    exact ⟨⟨dvd_trans ⟨ℓ, by push_cast; ring⟩ h10', h11⟩, h10'⟩

theorem GH_mul_le (ℓ : ℕ) : GH q (M' * ℓ) ≤ GH q M' := by
  rw [← GH_inf_Gamma0_eq]; exact inf_le_left

theorem Γ_mul_le (ℓ : ℕ) : Γ q (M' * ℓ) ≤ Γ q M' := Subgroup.map_mono (GH_mul_le ℓ)

theorem topField_eq (ℓ : ℕ) :
    xHTopFunctionFieldC ℚ (q ^ 2 * M') (levelH q M') (q ^ 2 * M' * ℓ) =
      xHFunctionField (q ^ 2 * (M' * ℓ)) (levelH q (M' * ℓ)) := by
  show qExpFunctionFieldC ℚ (GH q M' ⊓ Gamma0 (q ^ 2 * M' * ℓ)) = qExpFunctionFieldC ℚ (GH q (M' * ℓ))
  rw [GH_inf_Gamma0_eq]

theorem topBar_eq (ℓ : ℕ) :
    laurentBaseChange Qb (xHTopFunctionFieldC ℚ (q ^ 2 * M') (levelH q M') (q ^ 2 * M' * ℓ)) =
      fieldBar q (M' * ℓ) := by
  rw [topField_eq]

theorem GH_finiteIndex (hM : M' ≠ 0) : (GH q M').FiniteIndex := by
  haveI : NeZero (q ^ 2 * M') := ⟨Nat.mul_ne_zero (pow_ne_zero 2 (Fact.out : q.Prime).ne_zero) hM⟩
  have hle : Gamma (q ^ 2 * M') ≤ GH q M' := by
    intro A hA
    rw [Gamma_mem] at hA
    obtain ⟨_, _, h10, h11⟩ := hA
    rw [mem_GH_iff]
    refine ⟨h10, ?_⟩
    have := congrArg (ZMod.castHom (dvd_sq_mul q M') (ZMod q)) h11
    rwa [map_intCast, map_one] at this
  exact Subgroup.finiteIndex_of_le hle

theorem cocycle (ℓ : ℕ) (hℓ : ℓ ≠ 0) : ∀ γ ∈ GH q (M' * ℓ), ∃ γ₁ ∈ GH q M',
    γ₁ 0 0 = γ 0 0 ∧ γ₁ 0 1 = (ℓ : ℤ) * γ 0 1 ∧ (ℓ : ℤ) * γ₁ 1 0 = γ 1 0 ∧ γ₁ 1 1 = γ 1 1 := by
  intro γ hγ
  obtain ⟨h10, h11⟩ := (mem_GH_iff γ).mp hγ
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h10
  obtain ⟨c, hc⟩ := h10
  have hℓZ : (ℓ : ℤ) ≠ 0 := by exact_mod_cast hℓ
  have hdiv : γ 1 0 / ℓ = q ^ 2 * M' * c := by
    rw [hc]; push_cast
    rw [show (q : ℤ) ^ 2 * (M' * ℓ) * c = ℓ * (q ^ 2 * M' * c) by ring, Int.mul_ediv_cancel_left _ hℓZ]
  have hℓ10 : (ℓ : ℤ) ∣ γ 1 0 := ⟨q ^ 2 * M' * c, by rw [hc]; push_cast; ring⟩
  let γ₁ : SL(2, ℤ) := ⟨!![γ 0 0, (ℓ : ℤ) * γ 0 1; γ 1 0 / ℓ, γ 1 1], by
    have hdet := Matrix.SpecialLinearGroup.det_coe γ
    rw [Matrix.det_fin_two] at hdet
    obtain ⟨c', hc'⟩ := hℓ10
    have h1 : (ℓ : ℤ) * c' / ℓ = c' := by rw [mul_comm]; exact Int.mul_ediv_cancel c' hℓZ
    rw [Matrix.det_fin_two_of, hc', h1]
    rw [hc'] at hdet
    linear_combination hdet⟩
  refine ⟨γ₁, ?_, rfl, rfl, ?_, rfl⟩
  · rw [mem_GH_iff]
    refine ⟨?_, h11⟩
    show ((γ 1 0 / ℓ : ℤ) : ZMod (q ^ 2 * M')) = 0
    rw [hdiv, ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact ⟨c, by push_cast; ring⟩
  · show (ℓ : ℤ) * (γ 1 0 / ℓ) = γ 1 0
    exact Int.mul_ediv_cancel' hℓ10

end W1LT
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_exists_algEquiv_intertwinesAlong_heckeAlphaHBar_heckeBetaHBar_levelAutBar.W1LT"

namespace W1LT

open UpperHalfPlane ModularForm OnePoint HahnSeries
open scoped ModularForm Manifold

section Stretch

local notation "GL↑(" G ")" => ((G : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))

variable {G G' : Subgroup SL(2, ℤ)} [G.FiniteIndex] {ℓ : ℕ} {k : ℤ}

private theorem mapGL_coe_eq (s : SL(2, ℤ)) :
    ((Matrix.SpecialLinearGroup.mapGL ℝ s : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)
      = (s : Matrix (Fin 2) (Fin 2) ℤ).map (algebraMap ℤ ℝ) := rfl

theorem heckeDiagMatrix_mul_eq (hℓ : ℓ ≠ 0) {γ γ₁ : SL(2, ℤ)}
    (h00 : γ₁ 0 0 = γ 0 0) (h01 : γ₁ 0 1 = (ℓ : ℤ) * γ 0 1)
    (h10 : (ℓ : ℤ) * γ₁ 1 0 = γ 1 0) (h11 : γ₁ 1 1 = γ 1 1) :
    heckeDiagMatrix ℓ * Matrix.SpecialLinearGroup.mapGL ℝ γ
      = Matrix.SpecialLinearGroup.mapGL ℝ γ₁ * heckeDiagMatrix ℓ := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, mapGL_coe_eq, mapGL_coe_eq, val_heckeDiagMatrix hℓ]
  have e10 : ((γ 1 0 : ℤ) : ℝ) = (ℓ : ℝ) * ((γ₁ 1 0 : ℤ) : ℝ) := by
    rw [← h10]; push_cast; ring
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, h00, h01, h11, e10, mul_comm]

theorem isCusp_heckeDiagMatrix_smul (hℓ : ℓ ≠ 0) {c : OnePoint ℝ} (hc : IsCusp c 𝒮ℒ) :
    IsCusp (heckeDiagMatrix ℓ • c) 𝒮ℒ := by
  rw [isCusp_SL2Z_iff] at hc ⊢
  obtain ⟨c₀, rfl⟩ := hc
  let gQ : GL (Fin 2) ℚ := Matrix.GeneralLinearGroup.mkOfDetNeZero !![(ℓ : ℚ), 0; 0, 1]
    (by rw [Matrix.det_fin_two_of]; simp; exact_mod_cast hℓ)
  have hg : gQ.map (Rat.castHom ℝ) = heckeDiagMatrix ℓ := by
    apply Units.ext
    rw [val_heckeDiagMatrix hℓ]
    show (gQ : Matrix (Fin 2) (Fin 2) ℚ).map (Rat.castHom ℝ) = _
    ext i j; fin_cases i <;> fin_cases j <;> simp [gQ]
  refine ⟨gQ • c₀, ?_⟩
  rw [← hg, ← Rat.coe_castHom, OnePoint.map_smul]

variable (hG' : ∀ γ ∈ G', ∃ γ₁ ∈ G,
  γ₁ 0 0 = γ 0 0 ∧ γ₁ 0 1 = (ℓ : ℤ) * γ 0 1 ∧ (ℓ : ℤ) * γ₁ 1 0 = γ 1 0 ∧ γ₁ 1 1 = γ 1 1)

def stretchSlash (hℓ : ℓ ≠ 0) (f : ModularForm GL↑(G) k) : ModularForm GL↑(G') k where
  toFun := (⇑f : ℍ → ℂ) ∣[k] heckeDiagMatrix ℓ
  slash_action_eq' := by
    intro A hA
    obtain ⟨γ, hγ, rfl⟩ := hA
    obtain ⟨γ₁, hγ₁, h00, h01, h10, h11⟩ := hG' γ hγ
    rw [← SlashAction.slash_mul, heckeDiagMatrix_mul_eq hℓ h00 h01 h10 h11,
      SlashAction.slash_mul]
    congr 1
    exact SlashInvariantFormClass.slash_action_eq f _ (Subgroup.mem_map_of_mem _ hγ₁)
  holo' := f.holo'.slash k _
  bdd_at_cusps' := by
    intro c hc
    have hcSL : IsCusp c 𝒮ℒ := by
      refine hc.mono ?_
      rintro _ ⟨γ, -, rfl⟩
      exact ⟨γ, rfl⟩
    have hc' : IsCusp (heckeDiagMatrix ℓ • c) GL↑(G) := by
      rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z]
      exact isCusp_heckeDiagMatrix_smul hℓ hcSL
    exact IsBoundedAt.smul_iff.mp (f.bdd_at_cusps' hc')

@[scoped simp] theorem coe_stretchSlash (hℓ : ℓ ≠ 0) (f : ModularForm GL↑(G) k) :
    (⇑(stretchSlash hG' hℓ f) : ℍ → ℂ) = (⇑f : ℍ → ℂ) ∣[k] heckeDiagMatrix ℓ := rfl

def stretch (hℓ : ℓ ≠ 0) (f : ModularForm GL↑(G) k) : ModularForm GL↑(G') k :=
  ((ℓ : ℂ) ^ (k - 1))⁻¹ • stretchSlash hG' hℓ f

theorem coe_stretch_eq_smul (hℓ : ℓ ≠ 0) (f : ModularForm GL↑(G) k) :
    (⇑(stretch hG' hℓ f) : ℍ → ℂ) = ((ℓ : ℂ) ^ (k - 1))⁻¹ • ((⇑f : ℍ → ℂ) ∣[k] heckeDiagMatrix ℓ) := by
  rw [stretch, ModularForm.IsGLPos.coe_smul, coe_stretchSlash]

theorem stretch_apply (hℓ : ℓ ≠ 0) (f : ModularForm GL↑(G) k) (τ : ℍ) :
    stretch hG' hℓ f τ = f (heckeDiagMatrix ℓ • τ) := by
  have hpk : ((ℓ : ℂ) ^ (k - 1)) ≠ 0 := zpow_ne_zero _ (Nat.cast_ne_zero.mpr hℓ)
  rw [stretch, ModularForm.IsGLPos.smul_apply, coe_stretchSlash, slash_heckeDiagMatrix_apply k hℓ,
    smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hpk, one_mul]

theorem coe_stretch (hℓ : ℓ ≠ 0) (f : ModularForm GL↑(G) k) :
    (⇑(stretch hG' hℓ f) : ℍ → ℂ) = fun τ => f (heckeDiagMatrix ℓ • τ) :=
  funext (stretch_apply hG' hℓ f)

theorem qCoeff_stretch (hT : ModularGroup.T ∈ G) (hℓ : ℓ ≠ 0) (f : ModularForm GL↑(G) k) (n : ℕ) :
    ModularFormClass.qCoeff (⇑(stretch hG' hℓ f)) n
      = if ℓ ∣ n then ModularFormClass.qCoeff (⇑f) (n / ℓ) else 0 := by
  have h1 : (1 : ℝ) ∈ (GL↑(G)).strictPeriods := by
    rw [Subgroup.strictPeriods_eq_zmultiples_one_of_T_mem hT]
    exact AddSubgroup.mem_zmultiples 1
  rw [coe_stretch]
  exact UpperHalfPlane.qCoeff_comp_heckeDiagMatrix_smul
    (SlashInvariantFormClass.periodic_comp_ofComplex f h1) f.holo'
    (ModularFormClass.bdd_at_infty f) hℓ n

omit [G.FiniteIndex] in

theorem ofPowerSeries_eq_qExpand {R : Type*} [CommRing R] (ℓ : ℕ) [NeZero ℓ]
    (p r : PowerSeries R)
    (h : ∀ n : ℕ, PowerSeries.coeff n p = if ℓ ∣ n then PowerSeries.coeff (n / ℓ) r else 0) :
    HahnSeries.ofPowerSeries ℤ R p = qExpand R ℓ (HahnSeries.ofPowerSeries ℤ R r) := by
  have hℓ : ℓ ≠ 0 := NeZero.ne ℓ
  ext m
  by_cases hdvd : (ℓ : ℤ) ∣ m
  · obtain ⟨m', rfl⟩ := hdvd
    rw [qExpand_coeff_mul, PowerSeries.coeff_coe, PowerSeries.coeff_coe]
    by_cases hm' : m' < 0
    · have : (ℓ : ℤ) * m' < 0 :=
        mul_neg_of_pos_of_neg (by exact_mod_cast Nat.pos_of_ne_zero hℓ) hm'
      rw [if_pos this, if_pos hm']
    · have hm'0 : 0 ≤ m' := le_of_not_gt hm'
      have hprod : ¬ (ℓ : ℤ) * m' < 0 := not_lt.mpr (mul_nonneg (by positivity) hm'0)
      rw [if_neg hprod, if_neg hm', h]
      have habs : ((ℓ : ℤ) * m').natAbs = ℓ * m'.natAbs := by
        rw [Int.natAbs_mul, Int.natAbs_natCast]
      rw [habs, if_pos (dvd_mul_right ℓ _), Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hℓ)]
  · rw [qExpand_coeff_of_not_dvd ℓ _ hdvd, PowerSeries.coeff_coe]
    split_ifs with hm
    · rfl
    · rw [h]
      have : ¬ ℓ ∣ m.natAbs := by
        intro h'
        apply hdvd
        have hm0 : 0 ≤ m := le_of_not_gt hm
        rw [← Int.natAbs_of_nonneg hm0]
        exact_mod_cast h'
      rw [if_neg this]

theorem qC_stretch (hT : ModularGroup.T ∈ G) [NeZero ℓ] (f : ModularForm GL↑(G) k) :
    qC (⇑(stretch hG' (NeZero.ne ℓ) f)) = qExpand ℂ ℓ (qC ⇑f) := by
  refine ofPowerSeries_eq_qExpand ℓ _ _ (fun n => ?_)
  have h := qCoeff_stretch hG' hT (NeZero.ne ℓ) f n
  simp only [ModularFormClass.qCoeff] at h
  exact h

def expandPS (ℓ : ℕ) (p : PowerSeries ℤ) : PowerSeries ℤ :=
  PowerSeries.mk fun n => if ℓ ∣ n then PowerSeries.coeff (n / ℓ) p else 0

omit [G.FiniteIndex] in
@[scoped simp] theorem coeff_expandPS (ℓ : ℕ) (p : PowerSeries ℤ) (n : ℕ) :
    PowerSeries.coeff n (expandPS ℓ p) = if ℓ ∣ n then PowerSeries.coeff (n / ℓ) p else 0 :=
  PowerSeries.coeff_mk _ _

theorem isIntegralQExp_stretch (hT : ModularGroup.T ∈ G) (hℓ : ℓ ≠ 0) (f : ModularForm GL↑(G) k)
    {p : PowerSeries ℤ} (hp : IsIntegralQExp f p) :
    IsIntegralQExp (stretch hG' hℓ f) (expandPS ℓ p) := by
  rw [isIntegralQExp_iff]
  intro n
  have h := qCoeff_stretch hG' hT hℓ f n
  simp only [ModularFormClass.qCoeff] at h
  rw [h, coeff_expandPS]
  split_ifs with hdvd
  · exact hp.coeff (n / ℓ)
  · simp

omit [G.FiniteIndex] in

theorem intSeriesC_expandPS (K : Type*) [Field K] (ℓ : ℕ) [NeZero ℓ] (p : PowerSeries ℤ) :
    intSeriesC K (expandPS ℓ p) = qExpand K ℓ (intSeriesC K p) := by
  refine ofPowerSeries_eq_qExpand ℓ _ _ (fun n => ?_)
  rw [PowerSeries.coeff_map, PowerSeries.coeff_map, coeff_expandPS]
  split_ifs
  · rfl
  · exact map_zero _

end Stretch
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_exists_algEquiv_intertwinesAlong_heckeAlphaHBar_heckeBetaHBar_levelAutBar.W1LT"

end W1LT
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_exists_algEquiv_intertwinesAlong_heckeAlphaHBar_heckeBetaHBar_levelAutBar.W1LT"

namespace W1LT

open UpperHalfPlane IntermediateField HahnSeries AlgebraicCurve ModularForm
open scoped ModularForm

variable {q : ℕ} [Fact q.Prime] {M' : ℕ}

section Main

variable (hqM' : ¬ q ∣ M') {ℓ : ℕ} [NeZero ℓ] (hqℓ : ¬ q ∣ ℓ) (ζ : Idx q) {x x' : SL(2, ℤ)}
  (hx' : x' ∈ Gamma0 M')
  (h : !![(ℓ : ℤ), 0; 0, 1] * (x : Matrix (Fin 2) (Fin 2) ℤ) =
    (x' : Matrix (Fin 2) (Fin 2) ℤ) * !![(ℓ : ℤ), 0; 0, 1])

include h in

theorem entries :
    x' 0 0 = x 0 0 ∧ x' 0 1 = (ℓ : ℤ) * x 0 1 ∧ (ℓ : ℤ) * x' 1 0 = x 1 0 ∧ x' 1 1 = x 1 1 := by
  have hℓZ : (ℓ : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne ℓ
  have e := fun i j => congrFun (congrFun h i) j
  have e00 := e 0 0; have e01 := e 0 1; have e10 := e 1 0; have e11 := e 1 1
  simp [Matrix.mul_apply, Fin.sum_univ_two] at e00 e01 e10 e11
  refine ⟨?_, e01.symm, ?_, e11.symm⟩
  · have : (ℓ : ℤ) * x 0 0 = (ℓ : ℤ) * x' 0 0 := by rw [e00, mul_comm]
    exact (mul_left_cancel₀ hℓZ this).symm
  · rw [e10, mul_comm]

include hx' h in
theorem x_mem_Gamma0_mul : x ∈ Gamma0 (M' * ℓ) := by
  obtain ⟨_, _, e10, _⟩ := entries h
  rw [Gamma0_mem] at hx' ⊢
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at hx' ⊢
  obtain ⟨c, hc⟩ := hx'
  refine ⟨c, ?_⟩
  rw [← e10, hc]; push_cast; ring

include hx' h in
theorem x_mem_Gamma0 : x ∈ Gamma0 M' := by
  have := x_mem_Gamma0_mul (M' := M') hx' h
  rw [Gamma0_mem, ZMod.intCast_zmod_eq_zero_iff_dvd] at this ⊢
  exact dvd_trans ⟨ℓ, by push_cast; ring⟩ this

include hqM' hqℓ in
theorem not_dvd_mul : ¬ q ∣ M' * ℓ := by
  intro hd
  rcases (Nat.Prime.dvd_mul (Fact.out : q.Prime)).mp hd with h1 | h2
  · exact hqM' h1
  · exact hqℓ h2

include h in

theorem heckeDiagMatrix_mul_conjElem :
    heckeDiagMatrix ℓ * conjElem q x = conjElem q x' * heckeDiagMatrix ℓ := by
  have hℓ : ℓ ≠ 0 := NeZero.ne ℓ
  obtain ⟨e00, e01, e10, e11⟩ := entries h
  have r00 : ((x' 0 0 : ℤ) : ℝ) = ((x 0 0 : ℤ) : ℝ) := by rw [e00]
  have r01 : ((x' 0 1 : ℤ) : ℝ) = (ℓ : ℝ) * ((x 0 1 : ℤ) : ℝ) := by rw [e01]; push_cast; ring
  have r10 : ((x 1 0 : ℤ) : ℝ) = (ℓ : ℝ) * ((x' 1 0 : ℤ) : ℝ) := by rw [← e10]; push_cast; ring
  have r11 : ((x' 1 1 : ℤ) : ℝ) = ((x 1 1 : ℤ) : ℝ) := by rw [e11]
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  simp only [Matrix.GeneralLinearGroup.coe_mul, val_heckeDiagMatrix hℓ, conjElem_coe]
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, r00, r01, r10, r11] <;> ring

include hqM' hx' h in

theorem stretch_sl [Fact (M' ≠ 0)] {k : ℤ} (f : ModularForm (Γ q M') k) :
    haveI : (GH q M').FiniteIndex := GH_finiteIndex (Fact.out : M' ≠ 0)
    (⇑(stretch (cocycle ℓ (NeZero.ne ℓ)) (NeZero.ne ℓ) f) : ℍ → ℂ) ∣[k] conjElem q x =
      ⇑(stretch (cocycle ℓ (NeZero.ne ℓ)) (NeZero.ne ℓ) (sl hqM' x' hx' f)) := by
  haveI : (GH q M').FiniteIndex := GH_finiteIndex (Fact.out : M' ≠ 0)
  rw [coe_stretch_eq_smul, coe_stretch_eq_smul, ModularForm.smul_slash, σ_conjElem_apply,
    ← SlashAction.slash_mul, heckeDiagMatrix_mul_conjElem h, SlashAction.slash_mul, coe_sl]

def τ₂ (ζ : Idx q) (x : SL(2, ℤ)) : fieldBar q (M' * ℓ) ≃ₐ[Qb] fieldBar q (M' * ℓ) :=
  levelAutBar q (M' * ℓ) ζ x

include hqM' hqℓ hx' h in
theorem isLevelAutBar_τ₂ : IsLevelAutBar q (M' * ℓ) ζ x (τ₂ (M' := M') (ℓ := ℓ) ζ x) :=
  isLevelAutBar_levelAutBar
    (ModularCurve.FullLevel.levelAutInputs_of_not_dvd q (M' * ℓ) (not_dvd_mul hqM' hqℓ) ζ x
      (x_mem_Gamma0_mul hx' h))

include hqM' hx' h in
theorem isLevelAutBar_x : IsLevelAutBar q M' ζ x (levelAutBar q M' ζ x) :=
  isLevelAutBar_levelAutBar
    (ModularCurve.FullLevel.levelAutInputs_of_not_dvd q M' hqM' ζ x (x_mem_Gamma0 hx' h))

include hqM' hx' in
theorem isLevelAutBar_x' : IsLevelAutBar q M' ζ x' (levelAutBar q M' ζ x') :=
  isLevelAutBar_levelAutBar (ModularCurve.FullLevel.levelAutInputs_of_not_dvd q M' hqM' ζ x' hx')

def gen {k : ℤ} (f g : ModularForm (Γ q M') k) (pf pg : PowerSeries ℤ) (hf : IsIntegralQExp f pf)
    (hg : IsIntegralQExp g pg) (hg0 : intSeriesC ℚ pg ≠ 0) : fieldBar q M' :=
  ⟨coeffEmb Qb (intSeriesC ℚ pf / intSeriesC ℚ pg),
    coeffEmb_mem_laurentBaseChange Qb (div_mem_qExpFunctionFieldC f g hf hg hg0)⟩

def gen₂ {k : ℤ} (f g : ModularForm (Γ q M') k) (pf pg : PowerSeries ℤ) (hf : IsIntegralQExp f pf)
    (hg : IsIntegralQExp g pg) (hg0 : intSeriesC ℚ pg ≠ 0) : fieldBar q (M' * ℓ) :=
  ⟨coeffEmb Qb (intSeriesC ℚ pf / intSeriesC ℚ pg),
    coeffEmb_mem_laurentBaseChange Qb
      (div_mem_qExpFunctionFieldC (restrictForm (Γ_mul_le ℓ) f) (restrictForm (Γ_mul_le ℓ) g)
        (show IsIntegralQExp (⇑(restrictForm (Γ_mul_le ℓ) f)) pf by rw [coe_restrictForm]; exact hf)
        (show IsIntegralQExp (⇑(restrictForm (Γ_mul_le ℓ) g)) pg by rw [coe_restrictForm]; exact hg)
        hg0)⟩

omit [NeZero ℓ] in
theorem intSeriesC_expandPS_ne_zero {pg : PowerSeries ℤ} (hg0 : intSeriesC ℚ pg ≠ 0) [NeZero ℓ] :
    intSeriesC ℚ (expandPS ℓ pg) ≠ 0 := by
  rw [intSeriesC_expandPS]
  exact (map_ne_zero_iff _ (RingHom.injective _)).mpr hg0

def genβ [Fact (M' ≠ 0)] {k : ℤ} (f g : ModularForm (Γ q M') k) (pf pg : PowerSeries ℤ)
    (hf : IsIntegralQExp f pf) (hg : IsIntegralQExp g pg) (hg0 : intSeriesC ℚ pg ≠ 0) :
    fieldBar q (M' * ℓ) :=
  haveI : (GH q M').FiniteIndex := GH_finiteIndex (Fact.out : M' ≠ 0)
  ⟨coeffEmb Qb (intSeriesC ℚ (expandPS ℓ pf) / intSeriesC ℚ (expandPS ℓ pg)),
    coeffEmb_mem_laurentBaseChange Qb
      (div_mem_qExpFunctionFieldC (stretch (cocycle ℓ (NeZero.ne ℓ)) (NeZero.ne ℓ) f)
        (stretch (cocycle ℓ (NeZero.ne ℓ)) (NeZero.ne ℓ) g)
        (isIntegralQExp_stretch _ (translation_mem_GammaH _ _) _ f hf)
        (isIntegralQExp_stretch _ (translation_mem_GammaH _ _) _ g hg)
        (intSeriesC_expandPS_ne_zero hg0))⟩

theorem coe_genβ [Fact (M' ≠ 0)] {k : ℤ} (f g : ModularForm (Γ q M') k) (pf pg : PowerSeries ℤ)
    (hf : IsIntegralQExp f pf) (hg : IsIntegralQExp g pg) (hg0 : intSeriesC ℚ pg ≠ 0) :
    ((genβ (ℓ := ℓ) f g pf pg hf hg hg0 : fieldBar q (M' * ℓ)) : LaurentSeries Qb) =
      qExpand Qb ℓ (coeffEmb Qb (intSeriesC ℚ pf / intSeriesC ℚ pg)) := by
  show coeffEmb Qb (intSeriesC ℚ (expandPS ℓ pf) / intSeriesC ℚ (expandPS ℓ pg)) = _
  rw [intSeriesC_expandPS, intSeriesC_expandPS, ← map_div₀, coeffEmb, coeffMap_qExpand]

include hqM' hqℓ hx' h in

theorem τ₂_gen {k : ℤ} (f g : ModularForm (Γ q M') k) (pf pg : PowerSeries ℤ) (hf : IsIntegralQExp f pf)
    (hg : IsIntegralQExp g pg) (hg0 : intSeriesC ℚ pg ≠ 0) :
    ((τ₂ ζ x (gen₂ (ℓ := ℓ) f g pf pg hf hg hg0) : fieldBar q (M' * ℓ)) : LaurentSeries Qb) =
      ((levelAutBar q M' ζ x (gen f g pf pg hf hg hg0) : fieldBar q M') : LaurentSeries Qb) := by
  obtain ⟨ι₀, hι₀⟩ := exists_emb ζ
  have hx : x ∈ Gamma0 M' := x_mem_Gamma0 hx' h

  have e2 := isLevelAutBar_τ₂ hqM' hqℓ ζ hx' h k (restrictForm (Γ_mul_le ℓ) f) (restrictForm (Γ_mul_le ℓ) g)
    pf pg (show IsIntegralQExp (⇑(restrictForm (Γ_mul_le ℓ) f)) pf by rw [coe_restrictForm]; exact hf)
    (show IsIntegralQExp (⇑(restrictForm (Γ_mul_le ℓ) g)) pg by rw [coe_restrictForm]; exact hg) hg0 ι₀ hι₀

  have e1 := isLevelAutBar_x hqM' ζ hx' h k f g pf pg hf hg hg0 ι₀ hι₀
  change ιB ι₀ _ * qC (⇑(sl hqM' x hx g)) = qC (⇑(sl hqM' x hx f)) at e1
  change ιB ι₀ _ * qC (⇑(sl hqM' x hx g)) = qC (⇑(sl hqM' x hx f)) at e2
  have hne : qC (⇑(sl hqM' x hx g)) ≠ 0 := qC_sl_ne_zero hqM' x hx (ne_zero_of_intSeriesC_ne_zero hg hg0)
  have e3 := e2.trans e1.symm
  rw [mul_eq_mul_right_iff, or_iff_left hne] at e3
  exact ιB_injective ι₀ e3

include hqM' hqℓ hx' h in

theorem τ₂_genβ [Fact (M' ≠ 0)] {k : ℤ} (f g : ModularForm (Γ q M') k) (pf pg : PowerSeries ℤ)
    (hf : IsIntegralQExp f pf) (hg : IsIntegralQExp g pg) (hg0 : intSeriesC ℚ pg ≠ 0) :
    ((τ₂ ζ x (genβ (ℓ := ℓ) f g pf pg hf hg hg0) : fieldBar q (M' * ℓ)) : LaurentSeries Qb) =
      qExpand Qb ℓ ((levelAutBar q M' ζ x' (gen f g pf pg hf hg hg0) : fieldBar q M') : LaurentSeries Qb) := by
  haveI : (GH q M').FiniteIndex := GH_finiteIndex (Fact.out : M' ≠ 0)
  obtain ⟨ι₀, hι₀⟩ := exists_emb ζ

  have e2 := isLevelAutBar_τ₂ hqM' hqℓ ζ hx' h k (stretch (cocycle ℓ (NeZero.ne ℓ)) (NeZero.ne ℓ) f)
    (stretch (cocycle ℓ (NeZero.ne ℓ)) (NeZero.ne ℓ) g) (expandPS ℓ pf) (expandPS ℓ pg)
    (isIntegralQExp_stretch _ (translation_mem_GammaH _ _) _ f hf)
    (isIntegralQExp_stretch _ (translation_mem_GammaH _ _) _ g hg) (intSeriesC_expandPS_ne_zero hg0) ι₀ hι₀

  have e1 := isLevelAutBar_x' hqM' ζ hx' k f g pf pg hf hg hg0 ι₀ hι₀
  change ιB ι₀ _ * qC (⇑(stretch _ _ g) ∣[k] conjElem q x) = qC (⇑(stretch _ _ f) ∣[k] conjElem q x) at e2
  change ιB ι₀ _ * qC (⇑(sl hqM' x' hx' g)) = qC (⇑(sl hqM' x' hx' f)) at e1
  rw [stretch_sl hqM' hx' h, stretch_sl hqM' hx' h, qC_stretch _ (translation_mem_GammaH _ _),
    qC_stretch _ (translation_mem_GammaH _ _)] at e2
  have e1' := congrArg (qExpand ℂ ℓ) e1
  rw [map_mul] at e1'
  have hne : qExpand ℂ ℓ (qC (⇑(sl hqM' x' hx' g))) ≠ 0 :=
    (map_ne_zero_iff _ (RingHom.injective _)).mpr
      (qC_sl_ne_zero hqM' x' hx' (ne_zero_of_intSeriesC_ne_zero hg hg0))
  have e3 := e2.trans e1'.symm
  rw [mul_eq_mul_right_iff, or_iff_left hne, ← coeffMap_qExpand] at e3
  exact ιB_injective ι₀ e3

def inclQ : xHFunctionField (q ^ 2 * M') (levelH q M') →+* fieldBar q M' where
  toFun y := ⟨coeffEmb Qb (y : LaurentSeries ℚ), coeffEmb_mem_laurentBaseChange Qb y.2⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' _ _ := Subtype.ext (map_mul _ _ _)
  map_zero' := Subtype.ext (map_zero _)
  map_add' _ _ := Subtype.ext (map_add _ _ _)

omit [Fact q.Prime] in

theorem ringHom_ext_adjoin {S : Set (LaurentSeries ℚ)} {R : Type*} [DivisionRing R]
    (φ ψ : IntermediateField.adjoin ℚ S →+* R)
    (hφψ : ∀ (y : LaurentSeries ℚ) (hy : y ∈ S),
      φ ⟨y, IntermediateField.subset_adjoin ℚ S hy⟩ = ψ ⟨y, IntermediateField.subset_adjoin ℚ S hy⟩) :
    φ = ψ := by
  refine RingHom.ext fun y => ?_
  obtain ⟨y, hy⟩ := y
  induction hy using IntermediateField.adjoin_induction with
  | mem y hy => exact hφψ y hy
  | algebraMap c =>
      let j₁ : ℚ →+* IntermediateField.adjoin ℚ S := (algebraMap ℚ (LaurentSeries ℚ)).codRestrict
        (IntermediateField.adjoin ℚ S) (fun c => IntermediateField.algebraMap_mem _ c)
      exact RingHom.congr_fun (Subsingleton.elim (φ.comp j₁) (ψ.comp j₁)) c
  | add y z hy hz ihy ihz =>
      have : (⟨y + z, add_mem hy hz⟩ : IntermediateField.adjoin ℚ S) = ⟨y, hy⟩ + ⟨z, hz⟩ := rfl
      rw [this, map_add, map_add, ihy, ihz]
  | inv y hy ihy =>
      have : (⟨y⁻¹, inv_mem hy⟩ : IntermediateField.adjoin ℚ S) = ⟨y, hy⟩⁻¹ := rfl
      rw [this, map_inv₀, map_inv₀, ihy]
  | mul y z hy hz ihy ihz =>
      have : (⟨y * z, mul_mem hy hz⟩ : IntermediateField.adjoin ℚ S) = ⟨y, hy⟩ * ⟨z, hz⟩ := rfl
      rw [this, map_mul, map_mul, ihy, ihz]

theorem algHom_ext_gen {R : Type*} [Field R] [Algebra Qb R] (Φ₁ Φ₂ : fieldBar q M' →ₐ[Qb] R)
    (hgen : ∀ (k : ℤ) (f g : ModularForm (Γ q M') k) (pf pg : PowerSeries ℤ) (hf : IsIntegralQExp f pf)
      (hg : IsIntegralQExp g pg) (hg0 : intSeriesC ℚ pg ≠ 0),
      Φ₁ (gen f g pf pg hf hg hg0) = Φ₂ (gen f g pf pg hf hg hg0)) :
    Φ₁ = Φ₂ := by

  have h1 : Φ₁.toRingHom.comp inclQ = Φ₂.toRingHom.comp inclQ := by
    refine ringHom_ext_adjoin _ _ fun y hy => ?_
    obtain ⟨k, f, g, pf, pg, hf, hg, hg0, rfl⟩ := hy
    exact hgen k f g pf pg hf hg hg0

  refine IntermediateField.algHom_ext_of_eq_adjoin (F := Qb)
    (s := ⇑(coeffEmb Qb) '' ((xHFunctionField (q ^ 2 * M') (levelH q M')) : Set (LaurentSeries ℚ))) rfl ?_
  rintro _ ⟨y, hy, rfl⟩
  exact RingHom.congr_fun h1 ⟨y, hy⟩

def qExpandA : LaurentSeries Qb →ₐ[Qb] LaurentSeries Qb :=
  { qExpand Qb ℓ with
    commutes' := fun a => by
      show qExpand Qb ℓ (algebraMap Qb (LaurentSeries Qb) a) = algebraMap Qb (LaurentSeries Qb) a
      rw [algebraMap_laurentSeries_eq_single, qExpand_single, mul_zero] }

omit [Fact q.Prime] in
@[scoped simp] theorem qExpandA_apply (y : LaurentSeries Qb) : qExpandA (ℓ := ℓ) y = qExpand Qb ℓ y := rfl

abbrev Ftop (q : ℕ) [Fact q.Prime] (M' ℓ : ℕ) : IntermediateField Qb (LaurentSeries Qb) :=
  laurentBaseChange Qb (xHTopFunctionFieldC ℚ (q ^ 2 * M') (levelH q M') (q ^ 2 * M' * ℓ))

def eTop : Ftop q M' ℓ ≃ₐ[Qb] fieldBar q (M' * ℓ) :=
  AlgEquiv.ofAlgHom (IntermediateField.inclusion (topBar_eq (q := q) (M' := M') ℓ).le)
    (IntermediateField.inclusion (topBar_eq (q := q) (M' := M') ℓ).ge)
    (by ext z; rfl) (by ext z; rfl)

omit [NeZero ℓ] in
@[scoped simp] theorem coe_eTop (z : Ftop q M' ℓ) : ((eTop z : fieldBar q (M' * ℓ)) : LaurentSeries Qb) = z :=
  IntermediateField.coe_inclusion (topBar_eq (q := q) (M' := M') ℓ).le z

omit [NeZero ℓ] in
@[scoped simp] theorem coe_eTop_symm (z : fieldBar q (M' * ℓ)) :
    (((eTop (q := q) (M' := M') (ℓ := ℓ)).symm z : Ftop q M' ℓ) : LaurentSeries Qb) = z :=
  IntermediateField.coe_inclusion (topBar_eq (q := q) (M' := M') ℓ).ge z

def τTop (ζ : Idx q) (x : SL(2, ℤ)) : Ftop q M' ℓ ≃ₐ[Qb] Ftop q M' ℓ :=
  ((eTop (q := q) (M' := M') (ℓ := ℓ)).trans (τ₂ ζ x)).trans (eTop (q := q) (M' := M') (ℓ := ℓ)).symm

theorem coe_τTop (z : Ftop q M' ℓ) :
    ((τTop ζ x z : Ftop q M' ℓ) : LaurentSeries Qb) = τ₂ (M' := M') (ℓ := ℓ) ζ x (eTop z) := by
  show (((eTop (q := q) (M' := M') (ℓ := ℓ)).symm (τ₂ (M' := M') (ℓ := ℓ) ζ x (eTop z)) : Ftop q M' ℓ) :
      LaurentSeries Qb) = _
  rw [coe_eTop_symm]

include hqM' hqℓ hx' h in

theorem intertwines_alpha :
    SemilinearAut.IntertwinesAlong
      (heckeAlphaHBar Qb (q ^ 2 * M') (levelH q M') ℓ).toRingHom
      (SemilinearAut.ofAlgAut (levelAutBar q M' ζ x)) (SemilinearAut.ofAlgAut (τTop (ℓ := ℓ) ζ x)) := by

  let Φ₁ : fieldBar q M' →ₐ[Qb] LaurentSeries Qb :=
    ((fieldBar q (M' * ℓ)).val.comp (τ₂ (M' := M') (ℓ := ℓ) ζ x).toAlgHom).comp
      ((eTop (q := q) (M' := M') (ℓ := ℓ)).toAlgHom.comp (heckeAlphaHBar Qb (q ^ 2 * M') (levelH q M') ℓ))
  let Φ₂ : fieldBar q M' →ₐ[Qb] LaurentSeries Qb :=
    (fieldBar q M').val.comp (levelAutBar q M' ζ x).toAlgHom
  have hΦ : Φ₁ = Φ₂ := by
    refine algHom_ext_gen Φ₁ Φ₂ fun k f g pf pg hf hg hg0 => ?_
    have e1 : eTop (heckeAlphaHBar Qb (q ^ 2 * M') (levelH q M') ℓ (gen f g pf pg hf hg hg0)) =
        gen₂ (ℓ := ℓ) f g pf pg hf hg hg0 := Subtype.ext (by
      rw [coe_eTop, coe_heckeAlphaHBar]; rfl)
    show ((τ₂ ζ x (eTop (heckeAlphaHBar Qb (q ^ 2 * M') (levelH q M') ℓ (gen f g pf pg hf hg hg0))) :
        fieldBar q (M' * ℓ)) : LaurentSeries Qb) =
      ((levelAutBar q M' ζ x (gen f g pf pg hf hg hg0) : fieldBar q M') : LaurentSeries Qb)
    rw [e1]
    exact τ₂_gen hqM' hqℓ ζ hx' h f g pf pg hf hg hg0
  intro y
  apply Subtype.ext
  show ((τTop ζ x (heckeAlphaHBar Qb (q ^ 2 * M') (levelH q M') ℓ y) : Ftop q M' ℓ) : LaurentSeries Qb) =
    ((heckeAlphaHBar Qb (q ^ 2 * M') (levelH q M') ℓ (levelAutBar q M' ζ x y) : Ftop q M' ℓ) : LaurentSeries Qb)
  rw [coe_τTop, coe_heckeAlphaHBar]
  exact congrArg (fun φ : fieldBar q M' →ₐ[Qb] LaurentSeries Qb => φ y) hΦ

include hqM' hqℓ hx' h in

theorem intertwines_beta [Fact (M' ≠ 0)] (hβ : HeckeBetaHDefined (q ^ 2 * M') (levelH q M') ℓ) :
    SemilinearAut.IntertwinesAlong
      (heckeBetaHBar Qb (q ^ 2 * M') (levelH q M') ℓ).toRingHom
      (SemilinearAut.ofAlgAut (levelAutBar q M' ζ x')) (SemilinearAut.ofAlgAut (τTop (ℓ := ℓ) ζ x)) := by
  let Ψ₁ : fieldBar q M' →ₐ[Qb] LaurentSeries Qb :=
    ((fieldBar q (M' * ℓ)).val.comp (τ₂ (M' := M') (ℓ := ℓ) ζ x).toAlgHom).comp
      ((eTop (q := q) (M' := M') (ℓ := ℓ)).toAlgHom.comp (heckeBetaHBar Qb (q ^ 2 * M') (levelH q M') ℓ))
  let Ψ₂ : fieldBar q M' →ₐ[Qb] LaurentSeries Qb :=
    (qExpandA (ℓ := ℓ)).comp ((fieldBar q M').val.comp (levelAutBar q M' ζ x').toAlgHom)
  have hΨ : Ψ₁ = Ψ₂ := by
    refine algHom_ext_gen Ψ₁ Ψ₂ fun k f g pf pg hf hg hg0 => ?_
    have e1 : eTop (heckeBetaHBar Qb (q ^ 2 * M') (levelH q M') ℓ (gen f g pf pg hf hg hg0)) =
        genβ (ℓ := ℓ) f g pf pg hf hg hg0 := Subtype.ext (by
      rw [coe_eTop, coe_heckeBetaHBar _ _ _ hβ, coe_genβ]; rfl)
    show ((τ₂ ζ x (eTop (heckeBetaHBar Qb (q ^ 2 * M') (levelH q M') ℓ (gen f g pf pg hf hg hg0))) :
        fieldBar q (M' * ℓ)) : LaurentSeries Qb) =
      qExpand Qb ℓ ((levelAutBar q M' ζ x' (gen f g pf pg hf hg hg0) : fieldBar q M') : LaurentSeries Qb)
    rw [e1]
    exact τ₂_genβ hqM' hqℓ ζ hx' h f g pf pg hf hg hg0
  intro y
  apply Subtype.ext
  show ((τTop ζ x (heckeBetaHBar Qb (q ^ 2 * M') (levelH q M') ℓ y) : Ftop q M' ℓ) : LaurentSeries Qb) =
    ((heckeBetaHBar Qb (q ^ 2 * M') (levelH q M') ℓ (levelAutBar q M' ζ x' y) : Ftop q M' ℓ) : LaurentSeries Qb)
  rw [coe_τTop, coe_heckeBetaHBar _ _ _ hβ]
  exact congrArg (fun φ : fieldBar q M' →ₐ[Qb] LaurentSeries Qb => φ y) hΨ

end Main
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_exists_algEquiv_intertwinesAlong_heckeAlphaHBar_heckeBetaHBar_levelAutBar.W1LT"

theorem main (hqM' : ¬ q ∣ M') (ℓ : ℕ) [NeZero ℓ] (hqℓ : ¬ q ∣ ℓ)
    (hβ : HeckeBetaHDefined (q ^ 2 * M') (levelH q M') ℓ)
    (ζ : Idx q) (x x' : SL(2, ℤ)) (hx' : x' ∈ Gamma0 M')
    (h : !![(ℓ : ℤ), 0; 0, 1] * (x : Matrix (Fin 2) (Fin 2) ℤ) =
      (x' : Matrix (Fin 2) (Fin 2) ℤ) * !![(ℓ : ℤ), 0; 0, 1]) :
    ∃ τ : Ftop q M' ℓ ≃ₐ[Qb] Ftop q M' ℓ,
      SemilinearAut.IntertwinesAlong
          (heckeAlphaHBar Qb (q ^ 2 * M') (levelH q M') ℓ).toRingHom
          (SemilinearAut.ofAlgAut (levelAutBar q M' ζ x)) (SemilinearAut.ofAlgAut τ) ∧
        SemilinearAut.IntertwinesAlong
          (heckeBetaHBar Qb (q ^ 2 * M') (levelH q M') ℓ).toRingHom
          (SemilinearAut.ofAlgAut (levelAutBar q M' ζ x')) (SemilinearAut.ofAlgAut τ) := by
  haveI : Fact (M' ≠ 0) := ⟨by rintro rfl; exact hqM' (dvd_zero q)⟩
  exact ⟨τTop ζ x, intertwines_alpha hqM' hqℓ ζ hx' h, intertwines_beta hqM' hqℓ ζ hx' h hβ⟩

end W1LT
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_exists_algEquiv_intertwinesAlong_heckeAlphaHBar_heckeBetaHBar_levelAutBar.W1LT"

end
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_exists_algEquiv_intertwinesAlong_heckeAlphaHBar_heckeBetaHBar_levelAutBar.W1LT"

theorem solution
    (q : ℕ) [Fact q.Prime] (M' : ℕ) (hqM' : ¬ q ∣ M') (ℓ : ℕ) [NeZero ℓ] (hqℓ : ¬ q ∣ ℓ)
    (hβ : ModularCurve.HeckeBetaHDefined (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M') ℓ)
    (ζ : ModularCurve.FullLevel.Idx q) (x x' : SL(2, ℤ)) (hx' : x' ∈ CongruenceSubgroup.Gamma0 M')
    (h : !![(ℓ : ℤ), 0; 0, 1] * (x : Matrix (Fin 2) (Fin 2) ℤ) =
      (x' : Matrix (Fin 2) (Fin 2) ℤ) * !![(ℓ : ℤ), 0; 0, 1]) :
    ∃ τ : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ)
            (ModularCurve.xHTopFunctionFieldC ℚ (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M')
              (q ^ 2 * M' * ℓ))) ≃ₐ[AlgebraicClosure ℚ]
          ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ)
            (ModularCurve.xHTopFunctionFieldC ℚ (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M')
              (q ^ 2 * M' * ℓ))),
      AlgebraicCurve.SemilinearAut.IntertwinesAlong
          (ModularCurve.heckeAlphaHBar (AlgebraicClosure ℚ) (q ^ 2 * M')
            (ModularCurve.FullLevel.levelH q M') ℓ).toRingHom
          (AlgebraicCurve.SemilinearAut.ofAlgAut (ModularCurve.FullLevel.levelAutBar q M' ζ x))
          (AlgebraicCurve.SemilinearAut.ofAlgAut τ) ∧
        AlgebraicCurve.SemilinearAut.IntertwinesAlong
          (ModularCurve.heckeBetaHBar (AlgebraicClosure ℚ) (q ^ 2 * M')
            (ModularCurve.FullLevel.levelH q M') ℓ).toRingHom
          (AlgebraicCurve.SemilinearAut.ofAlgAut (ModularCurve.FullLevel.levelAutBar q M' ζ x'))
          (AlgebraicCurve.SemilinearAut.ofAlgAut τ) :=
  W1LT.main hqM' ℓ hqℓ hβ ζ x x' hx' h

end S_ModularCurve_FullLevel_exists_algEquiv_intertwinesAlong_heckeAlphaHBar_heckeBetaHBar_levelAutBar
end P2MW
export P2MW.S_ModularCurve_FullLevel_exists_algEquiv_intertwinesAlong_heckeAlphaHBar_heckeBetaHBar_levelAutBar (solution)
