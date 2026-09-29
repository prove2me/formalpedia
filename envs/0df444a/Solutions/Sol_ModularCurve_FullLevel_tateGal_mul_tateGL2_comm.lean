-- Prove2me | solution 1 for ModularCurve.FullLevel.tateGal_mul_tateGL2_comm
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/8b80b8b7-d6a0-5281-8e1e-fbb562534a46

import Mathlib
import Definitions.Def_ModularCurve_FullLevelJacobian
import Theorems.Thm_ModularCurve_FullLevel_levelAutInputs_of_not_dvd
import Theorems.Thm_ModularCurve_surjective_specialLinearGroup_map_zmod
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_tateGal_mul_tateGL2_comm

open scoped MatrixGroups
open Matrix ModularCurve ModularCurve.FullLevel CongruenceSubgroup
open scoped Pointwise

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace LawA_GLA
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

theorem conjElem_inv (γ : SL(2, ℤ)) : conjElem q γ⁻¹ = (conjElem q γ)⁻¹ := by
  simp only [conjElem_eq, map_inv]; group

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

end LawA_GLA
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_tateGal_mul_tateGL2_comm.LawA_GLA"

namespace LawA_GLA
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

end LawA_GLA
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_tateGal_mul_tateGL2_comm.LawA_GLA"

namespace LawA_GLA

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

theorem sl_mul_apply {k₁ k₂ : ℤ} (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M')
    (f : ModularForm (Γ q M') k₁) (g : ModularForm (Γ q M') k₂) :
    ⇑(sl hqM' γ hγ (f.mul g)) = ⇑(sl hqM' γ hγ f) * ⇑(sl hqM' γ hγ g) := by
  simp only [coe_sl, ModularForm.coe_mul, ModularForm.mul_slash, det_conjElem_val, abs_one, one_smul]

theorem sl_add {k : ℤ} (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M') (f g : ModularForm (Γ q M') k) :
    sl hqM' γ hγ (f + g) = sl hqM' γ hγ f + sl hqM' γ hγ g := by
  ext τ
  simp only [coe_sl, ModularForm.coe_add, SlashAction.add_slash, Pi.add_apply, ModularForm.add_apply]

theorem sl_smul {k : ℤ} (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M') (c : ℂ) (f : ModularForm (Γ q M') k) :
    ⇑(sl hqM' γ hγ (c • f)) = c • ⇑(sl hqM' γ hγ f) := by
  simp only [coe_sl, ModularForm.IsGLPos.coe_smul, ModularForm.smul_slash, σ_conjElem_apply]

theorem sl_neg {k : ℤ} (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M') (f : ModularForm (Γ q M') k) :
    ⇑(sl hqM' γ hγ (-f)) = -⇑(sl hqM' γ hγ f) := by
  simp only [coe_sl, ModularForm.coe_neg, SlashAction.neg_slash]

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

theorem sl_zero {k : ℤ} (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M') : sl hqM' γ hγ (0 : ModularForm (Γ q M') k) = 0 := by
  ext τ; simp [coe_sl]

theorem sl_const (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M') (c : ℂ) :
    sl hqM' γ hγ (ModularForm.const c : ModularForm (Γ q M') 0) = ModularForm.const c := by
  ext τ
  simp only [coe_sl, ModularForm.slash_def, ModularForm.coe_const, Function.const_apply, σ_conjElem_apply,
    det_conjElem_val, ModularForm.const_apply]
  simp

end Slash
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_tateGal_mul_tateGL2_comm.LawA_GLA"

section QExp

def qC (F : ℍ → ℂ) : LaurentSeries ℂ := ofPowerSeries ℤ ℂ (qExpansion 1 F)

theorem qC_mul {k₁ k₂ : ℤ} (f : ModularForm (Γ q M') k₁) (g : ModularForm (Γ q M') k₂) :
    qC (⇑f * ⇑g) = qC f * qC g := by
  rw [qC, qC, qC, ← map_mul, ← ModularForm.coe_mul,
    ModularForm.qExpansion_mul one_pos one_mem_strictPeriods]

theorem qC_add {k : ℤ} (f g : ModularForm (Γ q M') k) : qC (⇑f + ⇑g) = qC f + qC g := by
  rw [qC, qC, qC, ← map_add, ModularForm.qExpansion_add one_pos one_mem_strictPeriods f g]

theorem qC_smul {k : ℤ} (c : ℂ) (f : ModularForm (Γ q M') k) : qC (c • ⇑f) = HahnSeries.C c * qC f := by
  rw [qC, qC, ModularForm.qExpansion_smul one_pos one_mem_strictPeriods c f,
    ← HahnSeries.ofPowerSeries_C, ← map_mul, PowerSeries.smul_eq_C_mul]

theorem qC_neg {k : ℤ} (f : ModularForm (Γ q M') k) : qC (-⇑f) = -qC f := by
  rw [qC, qC, ModularForm.qExpansion_neg one_pos one_mem_strictPeriods f, map_neg]

theorem qC_eq_zero_iff {k : ℤ} (f : ModularForm (Γ q M') k) : qC f = 0 ↔ f = 0 := by
  rw [qC, ← ModularForm.qExpansion_eq_zero_iff one_pos one_mem_strictPeriods f]
  exact map_eq_zero_iff _ HahnSeries.ofPowerSeries_injective

theorem qC_zero : qC (0 : ℍ → ℂ) = 0 := by rw [qC, qExpansion_zero, map_zero]

theorem qC_one : qC (1 : ℍ → ℂ) = 1 := by rw [qC, qExpansion_one, map_one]

omit [Fact q.Prime] in
theorem coe_const_eq_smul_one (c : ℂ) :
    ((ModularForm.const c : ModularForm (Γ q M') 0) : ℍ → ℂ) =
      c • ((1 : ModularForm (Γ q M') 0) : ℍ → ℂ) := by
  funext z
  rw [Pi.smul_apply, ModularForm.const_apply, ModularForm.one_coe_eq_one, Pi.one_apply, smul_eq_mul,
    mul_one]

theorem qC_const (c : ℂ) : qC ((ModularForm.const c : ModularForm (Γ q M') 0) : ℍ → ℂ) = HahnSeries.C c := by
  rw [coe_const_eq_smul_one, qC_smul, ModularForm.one_coe_eq_one, qC_one, mul_one]

theorem qC_sum_smul {k : ℤ} (s : Finset ℕ) (c : ℕ → ℂ) (h : ℕ → ModularForm (Γ q M') k) :
    qC (∑ j ∈ s, c j • (⇑(h j) : ℍ → ℂ)) = ∑ j ∈ s, HahnSeries.C (c j) * qC (h j) := by
  classical
  have hcoe : ∀ t : Finset ℕ, (∑ j ∈ t, c j • (⇑(h j) : ℍ → ℂ)) = ⇑(∑ j ∈ t, c j • h j) := fun t => by
    induction t using Finset.induction_on with
    | empty => simp
    | insert a t ha ih =>
        rw [Finset.sum_insert ha, Finset.sum_insert ha, ModularForm.coe_add, ModularForm.IsGLPos.coe_smul, ih]
  induction s using Finset.induction_on with
  | empty => simp [qC_zero]
  | insert a t ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, hcoe t, ← ModularForm.IsGLPos.coe_smul, qC_add,
        ModularForm.IsGLPos.coe_smul, qC_smul, ← hcoe t, ih]

theorem mul_eq_mul_of_qC {k₁ k₂ k₃ k₄ : ℤ} (f₁ : ModularForm (Γ q M') k₁) (f₂ : ModularForm (Γ q M') k₂)
    (f₃ : ModularForm (Γ q M') k₃) (f₄ : ModularForm (Γ q M') k₄) (hk : k₃ + k₄ = k₁ + k₂)
    (h : qC f₁ * qC f₂ = qC f₃ * qC f₄) : (⇑f₁ * ⇑f₂ : ℍ → ℂ) = ⇑f₃ * ⇑f₄ := by
  set D : ModularForm (Γ q M') (k₁ + k₂) := f₁.mul f₂ - ModularForm.mcast hk (f₃.mul f₄) with hD
  have hcoe : (⇑D : ℍ → ℂ) = ⇑f₁ * ⇑f₂ - ⇑f₃ * ⇑f₄ := by
    rw [hD, ModularForm.coe_sub, ModularForm.coe_mul, ModularForm.coe_mcast, ModularForm.coe_mul]
  have hq : qC (⇑D) = 0 := by
    have hsub := ModularForm.qExpansion_sub one_pos one_mem_strictPeriods (f₁.mul f₂)
      (ModularForm.mcast hk (f₃.mul f₄))
    rw [ModularForm.coe_mul, ModularForm.coe_mcast, ModularForm.coe_mul] at hsub
    rw [hcoe, qC, hsub, map_sub]
    change qC (⇑f₁ * ⇑f₂) - qC (⇑f₃ * ⇑f₄) = 0
    rw [qC_mul, qC_mul, h, sub_self]
  have hD0 : D = 0 := (qC_eq_zero_iff D).mp hq
  have : (⇑D : ℍ → ℂ) = 0 := by rw [hD0, ModularForm.coe_zero]
  rw [hcoe] at this
  exact sub_eq_zero.mp this

variable (hqM' : ¬ q ∣ M')
include hqM'

theorem slash_mul_eq {k₁ k₂ k₃ k₄ : ℤ} (f₁ : ModularForm (Γ q M') k₁) (f₂ : ModularForm (Γ q M') k₂)
    (f₃ : ModularForm (Γ q M') k₃) (f₄ : ModularForm (Γ q M') k₄) (hk : k₃ + k₄ = k₁ + k₂)
    (h : (⇑f₁ * ⇑f₂ : ℍ → ℂ) = ⇑f₃ * ⇑f₄) (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M') :
    (⇑(sl hqM' γ hγ f₁) * ⇑(sl hqM' γ hγ f₂) : ℍ → ℂ) = ⇑(sl hqM' γ hγ f₃) * ⇑(sl hqM' γ hγ f₄) := by
  have h' := congrArg (fun F : ℍ → ℂ => F ∣[k₁ + k₂] conjElem q γ) h
  try simp only at h'
  rw [ModularForm.mul_slash] at h'
  conv at h' => rhs; rw [← hk, ModularForm.mul_slash]
  simpa only [coe_sl, det_conjElem_val, abs_one, one_smul] using h'

theorem qC_sl_ne_zero {k : ℤ} (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M') {g : ModularForm (Γ q M') k}
    (hg : g ≠ 0) : qC (sl hqM' γ hγ g) ≠ 0 := fun h =>
  sl_ne_zero hqM' γ hγ hg ((qC_eq_zero_iff _).mp h)

end QExp
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_tateGal_mul_tateGL2_comm.LawA_GLA"

section Img

variable (hqM' : ¬ q ∣ M') (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M')

def IsImgC (w w' : LaurentSeries ℂ) : Prop :=
  ∃ (k : ℤ) (f g : ModularForm (Γ q M') k), g ≠ 0 ∧ w = qC f / qC g ∧
    w' * qC (sl hqM' γ hγ g) = qC (sl hqM' γ hγ f)

variable {hqM' γ hγ}

theorem IsImgC.apply_rep {w w' : LaurentSeries ℂ} (h : IsImgC hqM' γ hγ w w') {k : ℤ}
    (f g : ModularForm (Γ q M') k) (hg : g ≠ 0) (hw : w = qC f / qC g) :
    w' * qC (sl hqM' γ hγ g) = qC (sl hqM' γ hγ f) := by
  obtain ⟨k₂, f₂, g₂, hg₂, hw₂, hy⟩ := h
  have hg' : qC g ≠ 0 := fun e => hg ((qC_eq_zero_iff g).mp e)
  have hg₂' : qC g₂ ≠ 0 := fun e => hg₂ ((qC_eq_zero_iff g₂).mp e)
  have hq : qC f * qC g₂ = qC f₂ * qC g := by
    rw [← div_eq_div_iff hg' hg₂', ← hw, ← hw₂]
  have hfun := mul_eq_mul_of_qC f g₂ f₂ g (add_comm k₂ k) hq
  have hsl := slash_mul_eq hqM' f g₂ f₂ g (add_comm k₂ k) hfun γ hγ
  have hqs : qC (sl hqM' γ hγ f) * qC (sl hqM' γ hγ g₂) =
      qC (sl hqM' γ hγ f₂) * qC (sl hqM' γ hγ g) := by
    rw [← qC_mul, ← qC_mul, hsl]
  have hne := qC_sl_ne_zero hqM' γ hγ hg₂
  apply mul_right_cancel₀ hne
  calc w' * qC (sl hqM' γ hγ g) * qC (sl hqM' γ hγ g₂)
      = w' * qC (sl hqM' γ hγ g₂) * qC (sl hqM' γ hγ g) := by ring
    _ = qC (sl hqM' γ hγ f₂) * qC (sl hqM' γ hγ g) := by rw [hy]
    _ = qC (sl hqM' γ hγ f) * qC (sl hqM' γ hγ g₂) := hqs.symm

theorem IsImgC.unique {w y y' : LaurentSeries ℂ} (h : IsImgC hqM' γ hγ w y) (h' : IsImgC hqM' γ hγ w y') :
    y = y' := by
  obtain ⟨k, f, g, hg, hw, hy'⟩ := h'
  have hy := h.apply_rep f g hg hw
  rw [← hy'] at hy
  exact mul_right_cancel₀ (qC_sl_ne_zero hqM' γ hγ hg) hy

theorem IsImgC.hasRep {w y : LaurentSeries ℂ} (h : IsImgC hqM' γ hγ w y) :
    ∃ (k : ℤ) (f g : ModularForm (Γ q M') k), g ≠ 0 ∧ w = qC f / qC g := by
  obtain ⟨k, f, g, hg, hw, _⟩ := h
  exact ⟨k, f, g, hg, hw⟩

theorem mul_ne_zero_form {k₁ k₂ : ℤ} {g₁ : ModularForm (Γ q M') k₁} {g₂ : ModularForm (Γ q M') k₂}
    (h₁ : g₁ ≠ 0) (h₂ : g₂ ≠ 0) : g₁.mul g₂ ≠ 0 := by
  intro h
  have : qC (⇑(g₁.mul g₂)) = 0 := by rw [h, ModularForm.coe_zero, qC_zero]
  rw [ModularForm.coe_mul, qC_mul] at this
  rcases mul_eq_zero.mp this with e | e
  · exact h₁ ((qC_eq_zero_iff _).mp e)
  · exact h₂ ((qC_eq_zero_iff _).mp e)

theorem IsImgC.mul {x₁ y₁ x₂ y₂ : LaurentSeries ℂ} (h₁ : IsImgC hqM' γ hγ x₁ y₁) (h₂ : IsImgC hqM' γ hγ x₂ y₂) :
    IsImgC hqM' γ hγ (x₁ * x₂) (y₁ * y₂) := by
  obtain ⟨k₁, f₁, g₁, hg₁, rfl, hy₁⟩ := h₁
  obtain ⟨k₂, f₂, g₂, hg₂, rfl, hy₂⟩ := h₂
  refine ⟨k₁ + k₂, f₁.mul f₂, g₁.mul g₂, mul_ne_zero_form hg₁ hg₂, ?_, ?_⟩
  · rw [ModularForm.coe_mul, ModularForm.coe_mul, qC_mul, qC_mul, div_mul_div_comm]
  · rw [sl_mul_apply, sl_mul_apply, qC_mul, qC_mul, ← hy₁, ← hy₂]
    ring

theorem IsImgC.add {x₁ y₁ x₂ y₂ : LaurentSeries ℂ} (h₁ : IsImgC hqM' γ hγ x₁ y₁) (h₂ : IsImgC hqM' γ hγ x₂ y₂) :
    IsImgC hqM' γ hγ (x₁ + x₂) (y₁ + y₂) := by
  obtain ⟨k₁, f₁, g₁, hg₁, rfl, hy₁⟩ := h₁
  obtain ⟨k₂, f₂, g₂, hg₂, rfl, hy₂⟩ := h₂
  have hg₁' : qC g₁ ≠ 0 := fun e => hg₁ ((qC_eq_zero_iff g₁).mp e)
  have hg₂' : qC g₂ ≠ 0 := fun e => hg₂ ((qC_eq_zero_iff g₂).mp e)
  refine ⟨k₁ + k₂, f₁.mul g₂ + (g₁.mul f₂), g₁.mul g₂, mul_ne_zero_form hg₁ hg₂, ?_, ?_⟩
  · rw [ModularForm.coe_add, qC_add, ModularForm.coe_mul, ModularForm.coe_mul, ModularForm.coe_mul, qC_mul,
      qC_mul, qC_mul, div_add_div _ _ hg₁' hg₂']
  · rw [sl_add, ModularForm.coe_add, qC_add, sl_mul_apply, sl_mul_apply,
      sl_mul_apply, qC_mul, qC_mul, qC_mul, ← hy₁, ← hy₂]
    ring

theorem IsImgC.neg {x y : LaurentSeries ℂ} (h : IsImgC hqM' γ hγ x y) : IsImgC hqM' γ hγ (-x) (-y) := by
  obtain ⟨k, f, g, hg, rfl, hy⟩ := h
  refine ⟨k, -f, g, hg, ?_, ?_⟩
  · rw [ModularForm.coe_neg, qC_neg]
    exact (neg_div (qC ⇑g) (qC ⇑f)).symm
  · rw [sl_neg, qC_neg, ← hy]
    ring

theorem one_ne_zero_form : (1 : ModularForm (Γ q M') 0) ≠ 0 := by
  intro h
  have := congrArg (fun F : ModularForm (Γ q M') 0 => qC (⇑F)) h
  simp only [ModularForm.one_coe_eq_one, qC_one, ModularForm.coe_zero, qC_zero] at this
  exact one_ne_zero this

theorem IsImgC.const (c : ℂ) : IsImgC hqM' γ hγ (HahnSeries.C c) (HahnSeries.C c) := by
  refine ⟨0, ModularForm.const c, 1, one_ne_zero_form, ?_, ?_⟩
  · rw [qC_const, ModularForm.one_coe_eq_one, qC_one, div_one]
  · have h1 : sl hqM' γ hγ (1 : ModularForm (Γ q M') 0) = 1 := by
      have := sl_const hqM' γ hγ (1 : ℂ)
      have e : (ModularForm.const 1 : ModularForm (Γ q M') 0) = 1 := by
        ext τ; simp
      rwa [e] at this
    rw [h1, sl_const, ModularForm.one_coe_eq_one, qC_one, mul_one, qC_const]

theorem IsImgC.one : IsImgC hqM' γ hγ 1 1 := by
  simpa using IsImgC.const (hqM' := hqM') (γ := γ) (hγ := hγ) 1

theorem IsImgC.zero : IsImgC hqM' γ hγ 0 0 := by
  simpa using IsImgC.const (hqM' := hqM') (γ := γ) (hγ := hγ) 0

theorem IsImgC.inv {x y : LaurentSeries ℂ} (h : IsImgC hqM' γ hγ x y) : IsImgC hqM' γ hγ x⁻¹ y⁻¹ := by
  obtain ⟨k, f, g, hg, rfl, hy⟩ := h
  by_cases hf : f = 0
  · have hy0 : y = 0 := by
      rw [hf, sl_zero, ModularForm.coe_zero, qC_zero] at hy
      exact (mul_eq_zero.mp hy).resolve_right (qC_sl_ne_zero hqM' γ hγ hg)
    rw [hf, ModularForm.coe_zero, qC_zero, zero_div, _root_.inv_zero, hy0, _root_.inv_zero]
    exact IsImgC.zero
  · refine ⟨k, g, f, hf, ?_, ?_⟩
    · rw [inv_div]
    · have hy' : y ≠ 0 := by
        intro e
        rw [e, zero_mul] at hy
        exact qC_sl_ne_zero hqM' γ hγ hf hy.symm
      rw [← hy, inv_mul_cancel_left₀ hy']

theorem IsImgC.symm {x y : LaurentSeries ℂ} (h : IsImgC hqM' γ hγ x y)
    (hyS : ∃ (k : ℤ) (P Q : ModularForm (Γ q M') k), Q ≠ 0 ∧ y = qC P / qC Q) :
    IsImgC hqM' γ⁻¹ (inv_mem hγ) y x := by
  obtain ⟨k, f, g, hg, hx, hy⟩ := h
  obtain ⟨kP, P, Q, hQ, rfl⟩ := hyS
  refine ⟨kP, P, Q, hQ, rfl, ?_⟩
  have hQ' : qC Q ≠ 0 := fun e => hQ ((qC_eq_zero_iff Q).mp e)
  have h1 : qC P * qC (sl hqM' γ hγ g) = qC (sl hqM' γ hγ f) * qC Q := by
    rw [← hy, div_mul_eq_mul_div, div_mul_cancel₀ _ hQ']
  have hfun := mul_eq_mul_of_qC P (sl hqM' γ hγ g) (sl hqM' γ hγ f) Q (add_comm k kP) h1
  have hsl := slash_mul_eq hqM' P (sl hqM' γ hγ g) (sl hqM' γ hγ f) Q (add_comm k kP) hfun γ⁻¹ (inv_mem hγ)
  rw [sl_inv_sl, sl_inv_sl] at hsl
  have hq : qC (sl hqM' γ⁻¹ (inv_mem hγ) P) * qC g = qC f * qC (sl hqM' γ⁻¹ (inv_mem hγ) Q) := by
    rw [← qC_mul, ← qC_mul, hsl]
  have hg' : qC g ≠ 0 := fun e => hg ((qC_eq_zero_iff g).mp e)
  rw [hx, div_mul_eq_mul_div, div_eq_iff hg']
  exact hq.symm

theorem IsImgC.congr_γ {γ' : SL(2, ℤ)} (e : γ = γ') {hγ' : γ' ∈ Gamma0 M'} {x y : LaurentSeries ℂ}
    (h : IsImgC hqM' γ hγ x y) : IsImgC hqM' γ' hγ' x y := by
  subst e; exact h

end Img
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_tateGal_mul_tateGL2_comm.LawA_GLA"

end LawA_GLA
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_tateGal_mul_tateGL2_comm.LawA_GLA"

namespace LawA_GLA

open UpperHalfPlane IntermediateField HahnSeries
open scoped ModularForm

variable {q : ℕ} [Fact q.Prime] {M' : ℕ}

section Emb

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
theorem ιB_C (c : Qb) : ιB ι₀ (HahnSeries.C c) = HahnSeries.C (ι₀ c) := by
  rw [HahnSeries.C_apply, HahnSeries.C_apply, coeffMap_single]

omit [Fact q.Prime] in
theorem C_eq_algebraMap (c : Qb) : (HahnSeries.C c : LaurentSeries Qb) = algebraMap Qb (LaurentSeries Qb) c := by
  rw [algebraMap_laurentSeries_eq_single, HahnSeries.C_apply]

omit [Fact q.Prime] in
theorem ιC_intSeriesC {F : ℍ → ℂ} {p : PowerSeries ℤ} (h : IsIntegralQExp F p) :
    ιC (intSeriesC ℚ p) = qC F := by
  rw [qC, ← h]
  ext n
  simp only [intSeriesC, coeffMap_coeff, PowerSeries.coeff_coe]
  split_ifs
  · exact map_zero _
  · simp [PowerSeries.coeff_map]

theorem qC_ne_zero_of_intSeriesC {k : ℤ} {g : ModularForm (Γ q M') k} {pg : PowerSeries ℤ} (hg : IsIntegralQExp g pg)
    (hg0 : intSeriesC ℚ pg ≠ 0) : qC g ≠ 0 := by
  rw [← ιC_intSeriesC hg]
  exact (map_ne_zero_iff _ (RingHom.injective _)).mpr hg0

theorem ne_zero_of_intSeriesC_ne_zero {k : ℤ} {g : ModularForm (Γ q M') k} {pg : PowerSeries ℤ}
    (hg : IsIntegralQExp g pg) (hg0 : intSeriesC ℚ pg ≠ 0) : g ≠ 0 :=
  fun h => qC_ne_zero_of_intSeriesC hg hg0 ((qC_eq_zero_iff g).mpr h)

end Emb
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_tateGal_mul_tateGL2_comm.LawA_GLA"

end LawA_GLA
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_tateGal_mul_tateGL2_comm.LawA_GLA"

namespace LawA_GLA

open UpperHalfPlane IntermediateField HahnSeries
open scoped ModularForm

variable {q : ℕ} [Fact q.Prime] {M' : ℕ}

section Emb0

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

end Emb0
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_tateGal_mul_tateGL2_comm.LawA_GLA"

section Aut

variable (hqM' : ¬ q ∣ M') (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M') (ι₀ : Qb →+* ℂ)

def IsImgAut (τ : fieldBar q M' ≃ₐ[Qb] fieldBar q M') : Prop :=
  ∀ X : fieldBar q M', IsImgC hqM' γ hγ (ιB ι₀ (X : LaurentSeries Qb)) (ιB ι₀ (τ X : LaurentSeries Qb))

variable {hqM' γ hγ ι₀}

theorem IsImgAut.unique {τ₁ τ₂ : fieldBar q M' ≃ₐ[Qb] fieldBar q M'} (h₁ : IsImgAut hqM' γ hγ ι₀ τ₁)
    (h₂ : IsImgAut hqM' γ hγ ι₀ τ₂) : τ₁ = τ₂ :=
  AlgEquiv.ext fun X => Subtype.ext (ιB_injective ι₀ ((h₁ X).unique (h₂ X)))

variable (hqM' γ hγ ι₀)

def Pulls (τ : fieldBar q M' ≃ₐ[Qb] fieldBar q M') (X : LaurentSeries Qb) : Prop :=
  ∃ hX : X ∈ fieldBar q M', IsImgC hqM' γ hγ (ιB ι₀ X) (ιB ι₀ (τ ⟨X, hX⟩ : LaurentSeries Qb))

variable {hqM' γ hγ ι₀} {τ : fieldBar q M' ≃ₐ[Qb] fieldBar q M'}

theorem Pulls.mul {X₁ X₂ : LaurentSeries Qb} (h₁ : Pulls hqM' γ hγ ι₀ τ X₁) (h₂ : Pulls hqM' γ hγ ι₀ τ X₂) :
    Pulls hqM' γ hγ ι₀ τ (X₁ * X₂) := by
  obtain ⟨hX₁, i₁⟩ := h₁
  obtain ⟨hX₂, i₂⟩ := h₂
  refine ⟨mul_mem hX₁ hX₂, ?_⟩
  have e : (τ ⟨X₁ * X₂, mul_mem hX₁ hX₂⟩ : LaurentSeries Qb) = τ ⟨X₁, hX₁⟩ * τ ⟨X₂, hX₂⟩ := by
    rw [← MulMemClass.coe_mul, ← map_mul]; rfl
  rw [map_mul, e, map_mul]
  exact i₁.mul i₂

theorem Pulls.add {X₁ X₂ : LaurentSeries Qb} (h₁ : Pulls hqM' γ hγ ι₀ τ X₁) (h₂ : Pulls hqM' γ hγ ι₀ τ X₂) :
    Pulls hqM' γ hγ ι₀ τ (X₁ + X₂) := by
  obtain ⟨hX₁, i₁⟩ := h₁
  obtain ⟨hX₂, i₂⟩ := h₂
  refine ⟨add_mem hX₁ hX₂, ?_⟩
  have e : (τ ⟨X₁ + X₂, add_mem hX₁ hX₂⟩ : LaurentSeries Qb) = τ ⟨X₁, hX₁⟩ + τ ⟨X₂, hX₂⟩ := by
    rw [← AddMemClass.coe_add, ← map_add]; rfl
  rw [map_add, e, map_add]
  exact i₁.add i₂

theorem Pulls.neg {X : LaurentSeries Qb} (h : Pulls hqM' γ hγ ι₀ τ X) : Pulls hqM' γ hγ ι₀ τ (-X) := by
  obtain ⟨hX, i⟩ := h
  refine ⟨neg_mem hX, ?_⟩
  have e : (τ ⟨-X, neg_mem hX⟩ : LaurentSeries Qb) = -τ ⟨X, hX⟩ := by
    rw [← NegMemClass.coe_neg, ← map_neg]; rfl
  rw [map_neg, e, map_neg]
  exact i.neg

theorem Pulls.inv {X : LaurentSeries Qb} (h : Pulls hqM' γ hγ ι₀ τ X) : Pulls hqM' γ hγ ι₀ τ X⁻¹ := by
  obtain ⟨hX, i⟩ := h
  refine ⟨inv_mem hX, ?_⟩
  have e : (τ ⟨X⁻¹, inv_mem hX⟩ : LaurentSeries Qb) = (τ ⟨X, hX⟩ : LaurentSeries Qb)⁻¹ := by
    have : (⟨X⁻¹, inv_mem hX⟩ : fieldBar q M') = ⟨X, hX⟩⁻¹ := rfl
    rw [this, map_inv₀]; rfl
  rw [map_inv₀, e, map_inv₀]
  exact i.inv

theorem Pulls.one : Pulls hqM' γ hγ ι₀ τ 1 := by
  refine ⟨one_mem _, ?_⟩
  have e : (τ ⟨1, one_mem _⟩ : LaurentSeries Qb) = 1 := by
    have : (⟨1, one_mem _⟩ : fieldBar q M') = 1 := rfl
    rw [this, map_one]; rfl
  rw [map_one, e, map_one]
  exact IsImgC.one

theorem pulls_algebraMap (c : Qb) : Pulls hqM' γ hγ ι₀ τ (algebraMap Qb (LaurentSeries Qb) c) := by
  refine ⟨IntermediateField.algebraMap_mem _ _, ?_⟩
  have e : (τ ⟨algebraMap Qb (LaurentSeries Qb) c, IntermediateField.algebraMap_mem _ _⟩ : LaurentSeries Qb) =
      algebraMap Qb (LaurentSeries Qb) c := by
    have : (⟨algebraMap Qb (LaurentSeries Qb) c, IntermediateField.algebraMap_mem _ _⟩ : fieldBar q M') =
        algebraMap Qb (fieldBar q M') c := rfl
    rw [this, AlgEquiv.commutes]; rfl
  rw [e, ← C_eq_algebraMap, ιB_C]
  exact IsImgC.const _

variable {ζ : Idx q}

theorem Pulls.gen (hι₀ : ι₀ ζ.val = eq q) (hτ : IsLevelAutBar q M' ζ γ τ) {x : LaurentSeries ℚ}
    (hx : x ∈ intFormRatiosC ℚ (GH q M')) : Pulls hqM' γ hγ ι₀ τ (coeffEmb Qb x) := by
  obtain ⟨k, f, g, pf, pg, hf, hg, hg0, rfl⟩ := hx
  refine ⟨coeffEmb_mem_laurentBaseChange Qb (div_mem_qExpFunctionFieldC f g hf hg hg0), k, f, g,
    ne_zero_of_intSeriesC_ne_zero hg hg0, ?_, ?_⟩
  · rw [ιB_coeffEmb, map_div₀, ιC_intSeriesC hf, ιC_intSeriesC hg]
  · exact hτ k f g pf pg hf hg hg0 ι₀ hι₀

theorem Pulls.of_mem_field (hι₀ : ι₀ ζ.val = eq q) (hτ : IsLevelAutBar q M' ζ γ τ) {x : LaurentSeries ℚ}
    (hx : x ∈ xHFunctionField (q ^ 2 * M') (levelH q M')) : Pulls hqM' γ hγ ι₀ τ (coeffEmb Qb x) := by
  change x ∈ Subfield.closure (Set.range (algebraMap ℚ (LaurentSeries ℚ)) ∪ intFormRatiosC ℚ (GH q M')) at hx
  induction hx using Subfield.closure_induction with
  | mem y hy =>
      rcases hy with ⟨r, rfl⟩ | hy
      · rw [algebraMap_laurentSeries_eq_single, coeffEmb, coeffMap_single, ← algebraMap_laurentSeries_eq_single]
        exact pulls_algebraMap _
      · exact Pulls.gen hι₀ hτ hy
  | one => rw [map_one]; exact Pulls.one
  | add x y _ _ hx hy => rw [map_add]; exact hx.add hy
  | neg x _ hx => rw [map_neg]; exact hx.neg
  | inv x _ hx => rw [map_inv₀]; exact hx.inv
  | mul x y _ _ hx hy => rw [map_mul]; exact hx.mul hy

theorem Pulls.of_mem (hι₀ : ι₀ ζ.val = eq q) (hτ : IsLevelAutBar q M' ζ γ τ) {X : LaurentSeries Qb}
    (hX : X ∈ fieldBar q M') : Pulls hqM' γ hγ ι₀ τ X := by
  rw [fieldBar, xHFunctionFieldBar, mem_laurentBaseChange_iff] at hX
  induction hX using Subfield.closure_induction with
  | mem y hy =>
      rcases hy with ⟨c, rfl⟩ | ⟨z, hz, rfl⟩
      · exact pulls_algebraMap c
      · exact Pulls.of_mem_field hι₀ hτ hz
  | one => exact Pulls.one
  | add x y _ _ hx hy => exact hx.add hy
  | neg x _ hx => exact hx.neg
  | inv x _ hx => exact hx.inv
  | mul x y _ _ hx hy => exact hx.mul hy

theorem isImgAut_of_isLevelAutBar (hι₀ : ι₀ ζ.val = eq q) (hτ : IsLevelAutBar q M' ζ γ τ) :
    IsImgAut hqM' γ hγ ι₀ τ := by
  intro X
  obtain ⟨_, h⟩ := Pulls.of_mem (hqM' := hqM') (hγ := hγ) hι₀ hτ X.2
  exact h

theorem isImgAut_levelAutBar (hι₀ : ι₀ ζ.val = eq q) : IsImgAut hqM' γ hγ ι₀ (levelAutBar q M' ζ γ) :=
  isImgAut_of_isLevelAutBar hι₀
    (isLevelAutBar_levelAutBar (ModularCurve.FullLevel.levelAutInputs_of_not_dvd q M' hqM' ζ γ hγ))

theorem isLevelAutBar_unique (hqM' : ¬ q ∣ M') {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 M')
    {τ₁ τ₂ : fieldBar q M' ≃ₐ[Qb] fieldBar q M'} (h₁ : IsLevelAutBar q M' ζ γ τ₁)
    (h₂ : IsLevelAutBar q M' ζ γ τ₂) : τ₁ = τ₂ := by
  obtain ⟨ι₀, hι₀⟩ := exists_emb ζ
  exact (isImgAut_of_isLevelAutBar (hqM' := hqM') (hγ := hγ) hι₀ h₁).unique
    (isImgAut_of_isLevelAutBar (hqM' := hqM') (hγ := hγ) hι₀ h₂)

end Aut
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_tateGal_mul_tateGL2_comm.LawA_GLA"

end LawA_GLA
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_tateGal_mul_tateGL2_comm.LawA_GLA"

namespace LawA_GL

variable {q : ℕ} [Fact q.Prime] {M' : ℕ}

section Reduction

abbrev SLq (n : ℕ) : SL(2, ℤ) →* SL(2, ZMod n) :=
  Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod n))

omit [Fact q.Prime] in
theorem SLq_apply (n : ℕ) (g : SL(2, ℤ)) (i j : Fin 2) : (SLq n g) i j = ((g i j : ℤ) : ZMod n) := rfl

omit [Fact q.Prime] in
theorem SLq_eq_iff (n : ℕ) (g g' : SL(2, ℤ)) :
    SLq n g = SLq n g' ↔ ∀ i j, (n : ℤ) ∣ g' i j - g i j := by
  constructor
  · intro h i j
    have hij : (SLq n g) i j = (SLq n g') i j := by rw [h]
    rw [SLq_apply, SLq_apply] at hij
    exact (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp hij
  · intro h
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    rw [SLq_apply, SLq_apply]
    exact (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mpr (h i j)

omit [Fact q.Prime] in
theorem SLq_eq_one_iff (n : ℕ) (g : SL(2, ℤ)) : SLq n g = 1 ↔ g ∈ Gamma n :=
  (Gamma_mem'.symm)

theorem redQ_eq (γ : SL(2, ℤ)) : redQ q γ = Matrix.SpecialLinearGroup.toGL (SLq q γ) := rfl

theorem map_cast_eq (γ : SL(2, ℤ)) :
    (γ : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ZMod q) =
      ((SLq q γ : SL(2, ZMod q)) : Matrix (Fin 2) (Fin 2) (ZMod q)) := by
  ext i j
  rw [SLq_apply]
  rfl

theorem coe_redQ (γ : SL(2, ℤ)) :
    ((redQ q γ : CuspidalType.GL2 q) : Matrix (Fin 2) (Fin 2) (ZMod q)) =
      (γ : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ZMod q) := by
  rw [map_cast_eq]
  rfl

omit [Fact q.Prime] in

theorem exists_crt {P M₁ : ℕ} [NeZero P] [NeZero M₁] (hcop : Nat.Coprime P M₁) (g : SL(2, ℤ)) :
    ∃ g₁ : SL(2, ℤ), SLq P g₁ = SLq P g ∧ SLq M₁ g₁ = 1 := by
  obtain ⟨x, y, hxy⟩ : IsCoprime (P : ℤ) (M₁ : ℤ) := Nat.isCoprime_iff_coprime.mpr hcop
  haveI : NeZero (P * M₁) := ⟨mul_ne_zero (NeZero.ne P) (NeZero.ne M₁)⟩
  set n : ℕ := P * M₁ with hn
  set e : ℤ := y * M₁ with he
  set f : ℤ := x * P with hf
  have hef : e + f = 1 := by rw [he, hf]; linear_combination hxy
  have hef' : (n : ℤ) ∣ e * f := ⟨x * y, by rw [hn, he, hf]; push_cast; ring⟩
  have hdet : (g 0 0 : ℤ) * g 1 1 - g 0 1 * g 1 0 = 1 := by
    have h := Matrix.SpecialLinearGroup.det_coe g
    rw [Matrix.det_fin_two] at h
    exact h
  have hE : ((e : ℤ) : ZMod n) + ((f : ℤ) : ZMod n) = 1 := by
    exact_mod_cast congrArg (Int.cast : ℤ → ZMod n) hef
  have hEF : ((e : ℤ) : ZMod n) * ((f : ℤ) : ZMod n) = 0 := by
    rw [← Int.cast_mul, ZMod.intCast_zmod_eq_zero_iff_dvd]; exact hef'
  have hD : ((g 0 0 : ℤ) : ZMod n) * ((g 1 1 : ℤ) : ZMod n)
      - ((g 0 1 : ℤ) : ZMod n) * ((g 1 0 : ℤ) : ZMod n) = 1 := by
    exact_mod_cast congrArg (Int.cast : ℤ → ZMod n) hdet
  let Y : SL(2, ZMod n) :=
    ⟨!![((e * g 0 0 + f : ℤ) : ZMod n), ((e * g 0 1 : ℤ) : ZMod n);
        ((e * g 1 0 : ℤ) : ZMod n), ((e * g 1 1 + f : ℤ) : ZMod n)], by
      rw [Matrix.det_fin_two_of]
      push_cast
      linear_combination ((e : ℤ) : ZMod n) ^ 2 * hD
        + (((g 0 0 : ℤ) : ZMod n) + ((g 1 1 : ℤ) : ZMod n) - 2) * hEF
        + (((e : ℤ) : ZMod n) + ((f : ℤ) : ZMod n) + 1) * hE⟩
  obtain ⟨g₁, hg₁⟩ := ModularCurve.surjective_specialLinearGroup_map_zmod n Y
  have hent : ∀ i j : Fin 2, (SLq n g₁) i j = Y i j := fun i j => by rw [← hg₁]
  have h00 : (n : ℤ) ∣ (e * g 0 0 + f) - g₁ 0 0 :=
    (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp (by simpa [SLq_apply, Y] using hent 0 0)
  have h01 : (n : ℤ) ∣ (e * g 0 1) - g₁ 0 1 :=
    (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp (by simpa [SLq_apply, Y] using hent 0 1)
  have h10 : (n : ℤ) ∣ (e * g 1 0) - g₁ 1 0 :=
    (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp (by simpa [SLq_apply, Y] using hent 1 0)
  have h11 : (n : ℤ) ∣ (e * g 1 1 + f) - g₁ 1 1 :=
    (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp (by simpa [SLq_apply, Y] using hent 1 1)
  have hPn : (P : ℤ) ∣ n := by rw [hn]; push_cast; exact dvd_mul_right _ _
  have hMn : (M₁ : ℤ) ∣ n := by rw [hn]; push_cast; exact dvd_mul_left _ _
  have hPe : (P : ℤ) ∣ e - 1 := ⟨-x, by rw [he]; linear_combination hxy⟩
  have hPf : (P : ℤ) ∣ f := ⟨x, by rw [hf]; ring⟩
  have hMe : (M₁ : ℤ) ∣ e := ⟨y, by rw [he]; ring⟩
  have hMf : (M₁ : ℤ) ∣ f - 1 := ⟨-y, by rw [hf]; linear_combination hxy⟩
  refine ⟨g₁, ?_, ?_⟩
  · rw [SLq_eq_iff]
    intro i j
    fin_cases i <;> fin_cases j
    · show (P : ℤ) ∣ g 0 0 - g₁ 0 0
      have : g 0 0 - g₁ 0 0 = ((e * g 0 0 + f) - g₁ 0 0) - (e - 1) * g 0 0 - f := by ring
      rw [this]
      exact dvd_sub (dvd_sub (dvd_trans hPn h00) (dvd_mul_of_dvd_left hPe _)) hPf
    · show (P : ℤ) ∣ g 0 1 - g₁ 0 1
      have : g 0 1 - g₁ 0 1 = ((e * g 0 1) - g₁ 0 1) - (e - 1) * g 0 1 := by ring
      rw [this]
      exact dvd_sub (dvd_trans hPn h01) (dvd_mul_of_dvd_left hPe _)
    · show (P : ℤ) ∣ g 1 0 - g₁ 1 0
      have : g 1 0 - g₁ 1 0 = ((e * g 1 0) - g₁ 1 0) - (e - 1) * g 1 0 := by ring
      rw [this]
      exact dvd_sub (dvd_trans hPn h10) (dvd_mul_of_dvd_left hPe _)
    · show (P : ℤ) ∣ g 1 1 - g₁ 1 1
      have : g 1 1 - g₁ 1 1 = ((e * g 1 1 + f) - g₁ 1 1) - (e - 1) * g 1 1 - f := by ring
      rw [this]
      exact dvd_sub (dvd_sub (dvd_trans hPn h11) (dvd_mul_of_dvd_left hPe _)) hPf
  · rw [← map_one (SLq M₁), SLq_eq_iff]
    intro i j
    fin_cases i <;> fin_cases j
    · show (M₁ : ℤ) ∣ (1 : SL(2, ℤ)) 0 0 - g₁ 0 0
      have : (1 : SL(2, ℤ)) 0 0 - g₁ 0 0 = ((e * g 0 0 + f) - g₁ 0 0) - e * g 0 0 - (f - 1) := by
        simp; ring
      rw [this]
      exact dvd_sub (dvd_sub (dvd_trans hMn h00) (dvd_mul_of_dvd_left hMe _)) hMf
    · show (M₁ : ℤ) ∣ (1 : SL(2, ℤ)) 0 1 - g₁ 0 1
      have : (1 : SL(2, ℤ)) 0 1 - g₁ 0 1 = ((e * g 0 1) - g₁ 0 1) - e * g 0 1 := by simp
      rw [this]
      exact dvd_sub (dvd_trans hMn h01) (dvd_mul_of_dvd_left hMe _)
    · show (M₁ : ℤ) ∣ (1 : SL(2, ℤ)) 1 0 - g₁ 1 0
      have : (1 : SL(2, ℤ)) 1 0 - g₁ 1 0 = ((e * g 1 0) - g₁ 1 0) - e * g 1 0 := by simp
      rw [this]
      exact dvd_sub (dvd_trans hMn h10) (dvd_mul_of_dvd_left hMe _)
    · show (M₁ : ℤ) ∣ (1 : SL(2, ℤ)) 1 1 - g₁ 1 1
      have : (1 : SL(2, ℤ)) 1 1 - g₁ 1 1 = ((e * g 1 1 + f) - g₁ 1 1) - e * g 1 1 - (f - 1) := by
        simp; ring
      rw [this]
      exact dvd_sub (dvd_sub (dvd_trans hMn h11) (dvd_mul_of_dvd_left hMe _)) hMf

theorem exists_mem_Gamma0_SLq_eq (hqM' : ¬ q ∣ M') (g : SL(2, ZMod q)) :
    ∃ γ : SL(2, ℤ), γ ∈ Gamma0 M' ∧ SLq q γ = g := by
  haveI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
  haveI : NeZero M' := ⟨by rintro rfl; exact hqM' (dvd_zero q)⟩
  obtain ⟨g₀, hg₀⟩ := ModularCurve.surjective_specialLinearGroup_map_zmod q g
  obtain ⟨g₁, hg₁q, hg₁M⟩ :=
    exists_crt ((Nat.Prime.coprime_iff_not_dvd (Fact.out : q.Prime)).mpr hqM') g₀
  refine ⟨g₁, ?_, ?_⟩
  · rw [SLq_eq_one_iff, Gamma_mem] at hg₁M
    rw [Gamma0_mem]
    exact hg₁M.2.2.1
  · rw [hg₁q]
    exact hg₀

end Reduction
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_tateGal_mul_tateGL2_comm.LawA_GLA"

section Decomp

theorem units_inv_mul_val (d : (ZMod q)ˣ) : ((d⁻¹ : (ZMod q)ˣ) : ZMod q) * (d : ZMod q) = 1 := by
  rw [← Units.val_mul, inv_mul_cancel, Units.val_one]

theorem units_mul_inv_val (d : (ZMod q)ˣ) : (d : ZMod q) * ((d⁻¹ : (ZMod q)ˣ) : ZMod q) = 1 := by
  rw [← Units.val_mul, mul_inv_cancel, Units.val_one]

theorem diag_inv_mul_diag (u : (ZMod q)ˣ) :
    !![(1 : ZMod q), 0; 0, ((u⁻¹ : (ZMod q)ˣ) : ZMod q)] * !![1, 0; 0, (u : ZMod q)] = 1 := by
  rw [Matrix.mul_fin_two, Matrix.one_fin_two]
  simp only [mul_one, mul_zero, add_zero, zero_add, zero_mul, units_inv_mul_val]

abbrev detU (g : CuspidalType.GL2 q) : (ZMod q)ˣ := Matrix.GeneralLinearGroup.det g

def slPart (g : CuspidalType.GL2 q) : SL(2, ZMod q) :=
  ⟨(g : Matrix (Fin 2) (Fin 2) (ZMod q)) * !![1, 0; 0, (((detU g)⁻¹ : (ZMod q)ˣ) : ZMod q)], by
    rw [Matrix.det_mul, Matrix.det_fin_two_of, ← Matrix.GeneralLinearGroup.val_det_apply, one_mul, mul_zero,
      sub_zero]
    exact units_mul_inv_val (detU g)⟩

theorem coe_slPart (g : CuspidalType.GL2 q) :
    ((slPart g : SL(2, ZMod q)) : Matrix (Fin 2) (Fin 2) (ZMod q)) =
      (g : Matrix (Fin 2) (Fin 2) (ZMod q)) * !![1, 0; 0, (((detU g)⁻¹ : (ZMod q)ˣ) : ZMod q)] :=
  rfl

theorem toGL_slPart_mul (g : CuspidalType.GL2 q) :
    Matrix.SpecialLinearGroup.toGL (slPart g) * diagOneElem q (detU g) = g := by
  apply Units.ext
  change ((slPart g : SL(2, ZMod q)) : Matrix (Fin 2) (Fin 2) (ZMod q)) * !![1, 0; 0, ((detU g : (ZMod q)ˣ) : ZMod q)] =
    (g : Matrix (Fin 2) (Fin 2) (ZMod q))
  rw [coe_slPart, Matrix.mul_assoc, diag_inv_mul_diag, Matrix.mul_one]

end Decomp
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_tateGal_mul_tateGL2_comm.LawA_GLA"

end LawA_GL
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_tateGal_mul_tateGL2_comm.LawA_GLA"

namespace LawA

open IntermediateField HahnSeries AlgebraicCurve ModularCurve ModularCurve.FullLevel CongruenceSubgroup
open scoped MatrixGroups ModularForm

variable {q : ℕ} [Fact q.Prime] {M' : ℕ}

local notation "Qb" => AlgebraicClosure ℚ
local notation "Gal" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

section Conj

variable (q M')

abbrev AG (σ : Gal) : SemilinearAut Qb (fieldBar q M') :=
  arithmeticGalois (xHFunctionField (q ^ 2 * M') (levelH q M')) σ

variable {q M'}

omit [Fact q.Prime] in
theorem AG_smul_algebraMap (g : SemilinearAut Qb (fieldBar q M')) (a : Qb) :
    SemilinearAut.toRingAut g (algebraMap Qb (fieldBar q M') a) =
      algebraMap Qb (fieldBar q M') (SemilinearAut.baseAut g a) :=
  SemilinearAut.commutes g a

def conj (σ : Gal) (τ : fieldBar q M' ≃ₐ[Qb] fieldBar q M') : fieldBar q M' ≃ₐ[Qb] fieldBar q M' :=
  AlgEquiv.ofRingEquiv
    (f := SemilinearAut.toRingAut (AG q M' σ * SemilinearAut.ofAlgAut τ * (AG q M' σ)⁻¹)) (by
      intro a
      change SemilinearAut.toRingAut (AG q M' σ) (τ
        (SemilinearAut.toRingAut (AG q M' σ)⁻¹ (algebraMap Qb (fieldBar q M') a))) = _
      rw [SemilinearAut.commutes, AlgEquiv.commutes, SemilinearAut.commutes, SemilinearAut.baseAut_inv,
        RingEquiv.apply_symm_apply])

omit [Fact q.Prime] in
theorem conj_apply (σ : Gal) (τ : fieldBar q M' ≃ₐ[Qb] fieldBar q M') (X : fieldBar q M') :
    conj σ τ X = SemilinearAut.toRingAut (AG q M' σ * SemilinearAut.ofAlgAut τ * (AG q M' σ)⁻¹) X :=
  rfl

omit [Fact q.Prime] in

theorem ofAlgAut_conj (σ : Gal) (τ : fieldBar q M' ≃ₐ[Qb] fieldBar q M') :
    SemilinearAut.ofAlgAut (conj σ τ) = AG q M' σ * SemilinearAut.ofAlgAut τ * (AG q M' σ)⁻¹ := by
  apply Subtype.ext
  apply Prod.ext
  · exact RingEquiv.ext fun _ => rfl
  · change SemilinearAut.baseAut (SemilinearAut.ofAlgAut (conj σ τ)) =
        SemilinearAut.baseAut (AG q M' σ * SemilinearAut.ofAlgAut τ * (AG q M' σ)⁻¹)
    rw [SemilinearAut.baseAut_ofAlgAut, SemilinearAut.baseAut_mul, SemilinearAut.baseAut_mul,
      SemilinearAut.baseAut_ofAlgAut, mul_one]
    exact (mul_inv_cancel (SemilinearAut.baseAut (AG q M' σ))).symm

omit [Fact q.Prime] in

theorem galois_smul_ofAlgAut_smul (σ : Gal) (τ : fieldBar q M' ≃ₐ[Qb] fieldBar q M') (y : jacComp q M') :
    σ • (SemilinearAut.ofAlgAut τ • y) = SemilinearAut.ofAlgAut (conj σ τ) • (σ • y) := by
  rw [galois_smul_pic0_def, galois_smul_pic0_def, ofAlgAut_conj, smul_smul, smul_smul,
    inv_mul_cancel_right]

omit [Fact q.Prime] in

theorem AG_inv_smul_coeffEmb (σ : Gal) (x : LaurentSeries ℚ) (hx : coeffEmb Qb x ∈ fieldBar q M') :
    SemilinearAut.toRingAut (AG q M' σ)⁻¹ (⟨coeffEmb Qb x, hx⟩ : fieldBar q M') = ⟨coeffEmb Qb x, hx⟩ :=
  Subtype.ext (by
    show coeffMap ((σ.symm : Gal) : Qb →+* Qb) (coeffEmb Qb x) = coeffEmb Qb x
    exact coeffMap_coeffEmb σ.symm x)

omit [Fact q.Prime] in

theorem coe_AG_toRingAut (σ : Gal) (X : fieldBar q M') :
    ((SemilinearAut.toRingAut (AG q M' σ) X : fieldBar q M') : LaurentSeries Qb) =
      coeffMap (σ : Qb →+* Qb) (X : LaurentSeries Qb) :=
  rfl

end Conj
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_tateGal_mul_tateGL2_comm.LawA_GLA"

section Covariance

theorem isLevelAutBar_conj (σ : Gal) {ζ : Idx q} {γ : SL(2, ℤ)}
    {τ : fieldBar q M' ≃ₐ[Qb] fieldBar q M'} (hτ : IsLevelAutBar q M' (σ⁻¹ • ζ) γ τ) :
    IsLevelAutBar q M' ζ γ (conj σ τ) := by
  intro k f g pf pg hf hg hg0 ι hι
  have hι' : (ι.comp (σ : Qb →+* Qb)) (σ⁻¹ • ζ).val = Complex.exp (2 * Real.pi * Complex.I / q) := by
    rw [RingHom.comp_apply, Idx.val_smul, RingHom.coe_coe, ← AlgEquiv.mul_apply, mul_inv_cancel,
      AlgEquiv.one_apply]
    exact hι
  have h := hτ k f g pf pg hf hg hg0 (ι.comp (σ : Qb →+* Qb)) hι'
  have key :
      coeffMap ι ((conj σ τ ⟨coeffEmb (AlgebraicClosure ℚ) (intSeriesC ℚ pf / intSeriesC ℚ pg),
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (div_mem_qExpFunctionFieldC f g hf hg hg0)⟩ : fieldBar q M') :
            LaurentSeries (AlgebraicClosure ℚ)) =
        coeffMap (ι.comp (σ : Qb →+* Qb))
          ((τ ⟨coeffEmb (AlgebraicClosure ℚ) (intSeriesC ℚ pf / intSeriesC ℚ pg),
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (div_mem_qExpFunctionFieldC f g hf hg hg0)⟩ : fieldBar q M') :
            LaurentSeries (AlgebraicClosure ℚ)) := by
    rw [← coeffMap_coeffMap, conj_apply]
    change coeffMap ι (coeffMap (σ : Qb →+* Qb) ((τ (SemilinearAut.toRingAut (AG q M' σ)⁻¹ _) :
      fieldBar q M') : LaurentSeries Qb)) = _
    rw [AG_inv_smul_coeffEmb]
  rw [key]
  exact h

theorem conj_levelAutBar (hqM' : ¬ q ∣ M') (σ : Gal) (ζ : Idx q) {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 M') :
    conj σ (levelAutBar q M' (σ⁻¹ • ζ) γ) = levelAutBar q M' ζ γ :=
  LawA_GLA.isLevelAutBar_unique hqM' hγ
    (isLevelAutBar_conj σ
      (isLevelAutBar_levelAutBar (ModularCurve.FullLevel.levelAutInputs_of_not_dvd q M' hqM' _ γ hγ)))
    (isLevelAutBar_levelAutBar (ModularCurve.FullLevel.levelAutInputs_of_not_dvd q M' hqM' ζ γ hγ))

theorem galois_smul_levelOp (hqM' : ¬ q ∣ M') (σ : Gal) (ζ : Idx q) {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 M')
    (y : jacComp q M') : σ • levelOp q M' (σ⁻¹ • ζ) γ y = levelOp q M' ζ γ (σ • y) := by
  rw [levelOp_apply, levelOp_apply, galois_smul_ofAlgAut_smul, conj_levelAutBar hqM' σ ζ hγ]

end Covariance
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_tateGal_mul_tateGL2_comm.LawA_GLA"

section Commute

abbrev slE (γ : SL(2, ℤ)) : AddMonoid.End (Jac q M') := slJac q M' γ

abbrev dgE (d : (ZMod q)ˣ) : AddMonoid.End (Jac q M') := diagJac q M' d

theorem galJac_mul_slE (hqM' : ¬ q ∣ M') (σ : Gal) {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 M') :
    galJac q M' σ * slE γ = slE γ * galJac q M' σ := by
  refine AddMonoidHom.ext fun x => Jac.ext fun ζ => ?_
  show (galJac q M' σ (slJac q M' γ x)).eval ζ = (slJac q M' γ (galJac q M' σ x)).eval ζ
  rw [galJac_eval, slJac_eval, slJac_eval, galJac_eval]
  exact galois_smul_levelOp hqM' σ ζ (inv_mem hγ) _

theorem smul_pow (σ : Gal) (ζ : Idx q) (d : (ZMod q)ˣ) : σ • (ζ.pow d) = (σ • ζ).pow d :=
  Idx.ext (by rw [Idx.val_smul, Idx.val_pow, Idx.val_pow, Idx.val_smul, map_pow])

theorem galJac_mul_dgE (σ : Gal) (d : (ZMod q)ˣ) :
    galJac q M' σ * dgE d = dgE d * galJac q M' σ := by
  refine AddMonoidHom.ext fun x => Jac.ext fun ζ => ?_
  show (galJac q M' σ (diagJac q M' d x)).eval ζ = (diagJac q M' d (galJac q M' σ x)).eval ζ
  rw [galJac_eval, diagJac_eval, diagJac_eval, galJac_eval, smul_pow]

theorem gl2Jac_eq (hqM' : ¬ q ∣ M') (hG : GL2Laws q M') (g : CuspidalType.GL2 q) :
    ∃ γ : SL(2, ℤ), γ ∈ Gamma0 M' ∧ gl2Jac q M' g = slE γ * dgE (LawA_GL.detU g) := by
  obtain ⟨γ, hγ, hγg⟩ := LawA_GL.exists_mem_Gamma0_SLq_eq (M' := M') hqM' (LawA_GL.slPart g)
  refine ⟨γ, hγ, ?_⟩
  conv_lhs => rw [← LawA_GL.toGL_slPart_mul g]
  rw [map_mul, ← hγg, ← LawA_GL.redQ_eq, gl2Jac_redQ hG γ hγ, gl2Jac_diagOneElem hG]

theorem galJac_mul_gl2Jac (hqM' : ¬ q ∣ M') (σ : Gal) (g : CuspidalType.GL2 q) :
    galJac q M' σ * gl2Jac q M' g = gl2Jac q M' g * galJac q M' σ := by
  by_cases hG : GL2Laws q M'
  · obtain ⟨γ, hγ, h⟩ := gl2Jac_eq hqM' hG g
    rw [h, ← mul_assoc, galJac_mul_slE hqM' σ hγ, mul_assoc, galJac_mul_dgE, mul_assoc]
  · rw [gl2Jac_of_not hG, MonoidHom.one_apply, mul_one, one_mul]

end Commute
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_tateGal_mul_tateGL2_comm.LawA_GLA"

theorem tateGal_mul_tateGL2_comm (hqM' : ¬ q ∣ M') (lam : ℕ) [Fact lam.Prime] (σ : Gal)
    (g : CuspidalType.GL2 q) :
    tateGal q M' lam σ * tateGL2 q M' lam g = tateGL2 q M' lam g * tateGal q M' lam σ := by
  show tateEnd q M' lam (galJac q M' σ) * tateEnd q M' lam (gl2Jac q M' g) =
    tateEnd q M' lam (gl2Jac q M' g) * tateEnd q M' lam (galJac q M' σ)
  rw [← map_mul, ← map_mul, galJac_mul_gl2Jac hqM']

end LawA
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_tateGal_mul_tateGL2_comm.LawA_GLA"

end
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_tateGal_mul_tateGL2_comm.LawA_GLA"

theorem solution
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M') (lam : ℕ) [Fact lam.Prime] :
    ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (x : CuspidalType.GL2 q),
      ModularCurve.FullLevel.tateGal q M' lam σ * ModularCurve.FullLevel.tateGL2 q M' lam x =
        ModularCurve.FullLevel.tateGL2 q M' lam x * ModularCurve.FullLevel.tateGal q M' lam σ :=
  fun σ x => LawA.tateGal_mul_tateGL2_comm hqM' lam σ x

end S_ModularCurve_FullLevel_tateGal_mul_tateGL2_comm
end P2MW
export P2MW.S_ModularCurve_FullLevel_tateGal_mul_tateGL2_comm (solution)
