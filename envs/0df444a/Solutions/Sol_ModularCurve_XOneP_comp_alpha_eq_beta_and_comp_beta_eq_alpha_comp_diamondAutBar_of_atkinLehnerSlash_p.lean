-- Prove2me | solution 1 for ModularCurve.XOneP.comp_alpha_eq_beta_and_comp_beta_eq_alpha_comp_diamondAutBar_of_atkinLehnerSlash_p
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/43d0c284-cfc2-56c0-86df-dc4947da91b4

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularForm_HeckeOperator
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_X1HeckeOperator
import Definitions.Def_ModularCurve_X1Diamond
import Definitions.Def_ModularCurve_AtkinLehnerPartial
import Theorems.Thm_ModularFormClass_qCoeff_comp_heckeDiagMatrix_smul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XOneP_comp_alpha_eq_beta_and_comp_beta_eq_alpha_comp_diamondAutBar_of_atkinLehnerSlash_p

set_option autoImplicit false

noncomputable section

open scoped MatrixGroups ModularForm Pointwise

namespace TOLD0b

open UpperHalfPlane CongruenceSubgroup ModularCurve Matrix IntermediateField HahnSeries

section Groups

abbrev Γ1 (N : ℕ) : Subgroup (GL (Fin 2) ℝ) :=
  ((Gamma1 N : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))

variable {N p : ℕ}

theorem T_mem_Gamma1 : ModularGroup.T ∈ Gamma1 N := by simp [ModularGroup.T]

theorem one_mem_sp1 : (1 : ℝ) ∈ (Γ1 N).strictPeriods := by
  rw [Subgroup.strictPeriods_eq_zmultiples_one_of_T_mem T_mem_Gamma1]
  exact AddSubgroup.mem_zmultiples _

theorem Γ1_mul_le : Γ1 (N * p) ≤ Γ1 N := Subgroup.map_mono (Gamma1_le_of_dvd (dvd_mul_right N p))

theorem conj_mem_Gamma1 {σ g : SL(2, ℤ)} (hσ : σ ∈ Gamma0 N) (hg : g ∈ Gamma1 N) :
    σ * g * σ⁻¹ ∈ Gamma1 N := by
  have hg0 : g ∈ Gamma0 N := Gamma1_in_Gamma0 N hg
  have hg1 : (⟨g, hg0⟩ : Gamma0 N) ∈ Gamma1' N := by
    rw [Gamma1_to_Gamma0_mem]; exact (Gamma1_mem N g).mp hg
  have hc : (⟨σ, hσ⟩ * ⟨g, hg0⟩ * (⟨σ, hσ⟩)⁻¹ : Gamma0 N) ∈ Gamma1' N :=
    (MonoidHom.normal_ker (Gamma0Map N)).conj_mem _ hg1 _
  rw [Gamma1_to_Gamma0_mem] at hc
  exact (Gamma1_mem N _).mpr hc

theorem Γ1_le_conj {σ : SL(2, ℤ)} (hσ : σ ∈ Gamma0 N) :
    Γ1 N ≤ ConjAct.toConjAct (Matrix.SpecialLinearGroup.mapGL ℝ σ)⁻¹ • Γ1 N := by
  rintro x ⟨g, hg, rfl⟩
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← ConjAct.toConjAct_inv, inv_inv,
    ConjAct.toConjAct_smul]
  refine ⟨_, conj_mem_Gamma1 hσ hg, ?_⟩
  rw [map_mul, map_mul, map_inv]

def conjMat (p : ℕ) (δ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ :=
  !![δ 0 0, (p : ℤ) * δ 0 1; δ 1 0 / p, δ 1 1]

theorem det_conjMat (δ : SL(2, ℤ)) (h : (p : ℤ) ∣ δ 1 0) : (conjMat p δ).det = 1 := by
  obtain ⟨c, hc⟩ := h
  have hdet := Matrix.SpecialLinearGroup.det_coe δ
  rw [Matrix.det_fin_two] at hdet ⊢
  rcases eq_or_ne (p : ℤ) 0 with h0 | h0
  · simp only [conjMat, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one, hc, h0, zero_mul, Int.zero_ediv,
      mul_zero, sub_zero] at hdet ⊢
    linear_combination hdet
  · have h1 : (p : ℤ) * c / p = c := by rw [mul_comm]; exact Int.mul_ediv_cancel c h0
    simp only [conjMat, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one, hc, h1] at hdet ⊢
    linear_combination hdet

def conjSL (δ : SL(2, ℤ)) (h : (p : ℤ) ∣ δ 1 0) : SL(2, ℤ) := ⟨conjMat p δ, det_conjMat δ h⟩

@[scoped simp] theorem conjSL_apply_00 (δ : SL(2, ℤ)) (h : (p : ℤ) ∣ δ 1 0) : conjSL δ h 0 0 = δ 0 0 := rfl
@[scoped simp] theorem conjSL_apply_01 (δ : SL(2, ℤ)) (h : (p : ℤ) ∣ δ 1 0) :
    conjSL δ h 0 1 = (p : ℤ) * δ 0 1 := rfl
@[scoped simp] theorem conjSL_apply_10 (δ : SL(2, ℤ)) (h : (p : ℤ) ∣ δ 1 0) :
    conjSL δ h 1 0 = δ 1 0 / p := rfl
@[scoped simp] theorem conjSL_apply_11 (δ : SL(2, ℤ)) (h : (p : ℤ) ∣ δ 1 0) : conjSL δ h 1 1 = δ 1 1 := rfl

theorem dvd_of_mem_Gamma0_mul {δ : SL(2, ℤ)} (hδ : δ ∈ Gamma0 (N * p)) : (p : ℤ) ∣ δ 1 0 := by
  rw [Gamma0_mem] at hδ
  have : ((N * p : ℕ) : ℤ) ∣ δ 1 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hδ
  exact (show (p : ℤ) ∣ ((N * p : ℕ) : ℤ) from ⟨N, by push_cast; ring⟩).trans this

theorem conjSL_mem_Gamma1 {δ : SL(2, ℤ)} (hδ1 : δ ∈ Gamma1 N) (hδ : δ ∈ Gamma0 (N * p))
    (hp : p ≠ 0) : conjSL δ (dvd_of_mem_Gamma0_mul hδ) ∈ Gamma1 N := by
  rw [Gamma1_mem] at hδ1 ⊢
  have hd : ((N * p : ℕ) : ℤ) ∣ δ 1 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (Gamma0_mem.mp hδ)
  obtain ⟨c, hc⟩ := hd
  have hp' : (p : ℤ) ≠ 0 := by exact_mod_cast hp
  have h10 : (conjSL δ (dvd_of_mem_Gamma0_mul hδ)) 1 0 = N * c := by
    show δ 1 0 / p = N * c
    rw [hc]; push_cast
    rw [show (N : ℤ) * p * c = p * (N * c) by ring]
    exact Int.mul_ediv_cancel_left _ hp'
  refine ⟨hδ1.1, hδ1.2.1, ?_⟩
  rw [h10]; push_cast
  simp

theorem heckeDiag_mul_mul_inv {δ : SL(2, ℤ)} (h : (p : ℤ) ∣ δ 1 0) (hp : p ≠ 0) :
    ModularForm.heckeDiagMatrix p * Matrix.SpecialLinearGroup.mapGL ℝ δ *
        (ModularForm.heckeDiagMatrix p)⁻¹ =
      Matrix.SpecialLinearGroup.mapGL ℝ (conjSL δ h) := by
  rw [mul_inv_eq_iff_eq_mul]
  ext i j
  obtain ⟨c, hc⟩ := h
  have hp' : (p : ℤ) ≠ 0 := by exact_mod_cast hp
  have h10 : (conjSL δ ⟨c, hc⟩ : SL(2, ℤ)) 1 0 = c := by
    show δ 1 0 / p = c
    rw [hc]; exact Int.mul_ediv_cancel_left _ hp'
  simp only [Matrix.GeneralLinearGroup.coe_mul, ModularForm.val_heckeDiagMatrix hp]
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, h10, hc] <;> ring

theorem raise_le_conj (hp : p ≠ 0) :
    Γ1 (N * p) ≤ ConjAct.toConjAct (ModularForm.heckeDiagMatrix p)⁻¹ • Γ1 N := by
  rintro x ⟨δ, hδ, rfl⟩
  have hδ1 : δ ∈ Gamma1 N := Gamma1_le_of_dvd (dvd_mul_right N p) hδ
  have hδ0 : δ ∈ Gamma0 (N * p) := Gamma1_in_Gamma0 _ hδ
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← ConjAct.toConjAct_inv, inv_inv,
    ConjAct.toConjAct_smul]
  exact ⟨_, conjSL_mem_Gamma1 hδ1 hδ0 hp, (heckeDiag_mul_mul_inv (dvd_of_mem_Gamma0_mul hδ0) hp).symm⟩

end Groups

section Forms

variable {N p : ℕ} {k : ℤ}

def levelRaise (p : ℕ) [NeZero p] (f : ModularForm (Γ1 N) k) : ModularForm (Γ1 (N * p)) k :=
  ((p : ℂ) ^ (k - 1))⁻¹ •
    restrictForm (raise_le_conj (NeZero.ne p)) (ModularForm.translate f (ModularForm.heckeDiagMatrix p))

theorem levelRaise_apply [NeZero p] (f : ModularForm (Γ1 N) k) (τ : ℍ) :
    levelRaise p f τ = f (ModularForm.heckeDiagMatrix p • τ) := by
  have hp : (p : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne p
  show ((p : ℂ) ^ (k - 1))⁻¹ • ((⇑f ∣[k] ModularForm.heckeDiagMatrix p) τ) = _
  rw [ModularForm.slash_heckeDiagMatrix_apply k (NeZero.ne p), smul_eq_mul, ← mul_assoc,
    inv_mul_cancel₀ (zpow_ne_zero _ hp), one_mul]

theorem coe_levelRaise [NeZero p] (f : ModularForm (Γ1 N) k) :
    ⇑(levelRaise p f) = fun τ => f (ModularForm.heckeDiagMatrix p • τ) :=
  funext (levelRaise_apply f)

theorem coe_levelRaise_eq_smul_slash [NeZero p] (f : ModularForm (Γ1 N) k) :
    ⇑(levelRaise p f) = ((p : ℂ) ^ (k - 1))⁻¹ • (⇑f ∣[k] ModularForm.heckeDiagMatrix p) := rfl

def dForm (σ : SL(2, ℤ)) (hσ : σ ∈ Gamma0 N) (f : ModularForm (Γ1 N) k) : ModularForm (Γ1 N) k :=
  restrictForm (Γ1_le_conj hσ) (ModularForm.translate f (Matrix.SpecialLinearGroup.mapGL ℝ σ))

@[scoped simp]
theorem coe_dForm (σ : SL(2, ℤ)) (hσ : σ ∈ Gamma0 N) (f : ModularForm (Γ1 N) k) :
    ⇑(dForm σ hσ f) = ⇑f ∣[k] σ := rfl

def res (p : ℕ) (f : ModularForm (Γ1 N) k) : ModularForm (Γ1 (N * p)) k :=
  restrictForm Γ1_mul_le f

@[scoped simp]
theorem coe_res (p : ℕ) (f : ModularForm (Γ1 N) k) : ⇑(res p f) = ⇑f := rfl

end Forms

section QExp

def qC (F : ℍ → ℂ) : LaurentSeries ℂ := ofPowerSeries ℤ ℂ (qExpansion 1 F)

variable {Γ : Subgroup SL(2, ℤ)}

local notation "GL⟮" Γ "⟯" => (((Γ : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)))

theorem qC_smul (hΓ : (1 : ℝ) ∈ (GL⟮Γ⟯).strictPeriods) {k : ℤ} (c : ℂ) (f : ModularForm GL⟮Γ⟯ k) :
    qC (c • ⇑f) = HahnSeries.C c * qC f := by
  rw [qC, qC, ModularForm.qExpansion_smul one_pos hΓ c f, ← HahnSeries.ofPowerSeries_C, ← map_mul,
    PowerSeries.smul_eq_C_mul]

theorem qC_eq_zero_iff (hΓ : (1 : ℝ) ∈ (GL⟮Γ⟯).strictPeriods) {k : ℤ} (f : ModularForm GL⟮Γ⟯ k) :
    qC f = 0 ↔ f = 0 := by
  rw [qC, ← ModularForm.qExpansion_eq_zero_iff one_pos hΓ f]
  exact map_eq_zero_iff _ HahnSeries.ofPowerSeries_injective

theorem qC_ne_zero_iff (hΓ : (1 : ℝ) ∈ (GL⟮Γ⟯).strictPeriods) {k : ℤ} (f : ModularForm GL⟮Γ⟯ k) :
    qC f ≠ 0 ↔ (⇑f : ℍ → ℂ) ≠ 0 := by
  rw [Ne, qC_eq_zero_iff hΓ, ← (ModularForm.coe_zero : ⇑(0 : ModularForm GL⟮Γ⟯ k) = 0)]
  exact ⟨fun h h' => h (DFunLike.ext' h'), fun h h' => h (by rw [h'])⟩

theorem qC_zero : qC (0 : ℍ → ℂ) = 0 := by rw [qC, qExpansion_zero, map_zero]

theorem qC_ne_zero_fun {F : ℍ → ℂ} (h : qC F ≠ 0) : F ≠ 0 := by
  rintro rfl; exact h qC_zero

theorem slash_ne_zero {k : ℤ} {F : ℍ → ℂ} (hF : F ≠ 0) (A : SL(2, ℤ)) : F ∣[k] A ≠ 0 := by
  intro h
  apply hF
  have : F ∣[k] (A * A⁻¹) = 0 := by rw [SlashAction.slash_mul, h, SlashAction.zero_slash]
  rwa [mul_inv_cancel, SlashAction.slash_one] at this

theorem C_ne_zero {c : ℂ} (hc : c ≠ 0) : (HahnSeries.C c : LaurentSeries ℂ) ≠ 0 :=
  (map_ne_zero_iff _ HahnSeries.C_injective).mpr hc

end QExp

section Expand

variable {N : ℕ} {k : ℤ}

theorem coeffMap_qExpand {R T : Type*} [CommRing R] [CommRing T] (φ : R →+* T) (n : ℕ) [NeZero n]
    (x : LaurentSeries R) : coeffMap φ (qExpand R n x) = qExpand T n (coeffMap φ x) := by
  ext m
  by_cases hk : (n : ℤ) ∣ m
  · obtain ⟨m, rfl⟩ := hk
    rw [coeffMap_coeff, qExpand_coeff_mul, qExpand_coeff_mul, coeffMap_coeff]
  · rw [coeffMap_coeff, qExpand_coeff_of_not_dvd n _ hk, qExpand_coeff_of_not_dvd n _ hk, map_zero]

def expandPS {R : Type*} [CommRing R] (n : ℕ) (P : PowerSeries R) : PowerSeries R :=
  PowerSeries.mk fun m => if n ∣ m then PowerSeries.coeff (m / n) P else 0

theorem coeff_expandPS {R : Type*} [CommRing R] (n : ℕ) (P : PowerSeries R) (m : ℕ) :
    PowerSeries.coeff m (expandPS n P) = if n ∣ m then PowerSeries.coeff (m / n) P else 0 := by
  rw [expandPS, PowerSeries.coeff_mk]

theorem ofPowerSeries_expandPS {R : Type*} [CommRing R] (n : ℕ) [NeZero n] (P : PowerSeries R) :
    ofPowerSeries ℤ R (expandPS n P) = qExpand R n (ofPowerSeries ℤ R P) := by
  ext m
  by_cases hdvd : (n : ℤ) ∣ m
  · obtain ⟨j, rfl⟩ := hdvd
    rw [qExpand_coeff_mul, PowerSeries.coeff_coe, PowerSeries.coeff_coe]
    have hn0 : (0 : ℤ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
    by_cases hj : j < 0
    · rw [if_pos hj, if_pos (mul_neg_of_pos_of_neg hn0 hj)]
    · rw [if_neg hj, if_neg (by push Not at hj ⊢; positivity)]
      simp only [coeff_expandPS]
      have h1 : ((n : ℤ) * j).natAbs = n * j.natAbs := by
        rw [Int.natAbs_mul, Int.natAbs_natCast]
      rw [h1, if_pos (Dvd.intro _ rfl), Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero (NeZero.ne n))]
  · rw [qExpand_coeff_of_not_dvd n _ hdvd, PowerSeries.coeff_coe]
    split_ifs with hm
    · rfl
    · rw [coeff_expandPS, if_neg]
      rintro ⟨c, hc⟩
      apply hdvd
      refine ⟨c, ?_⟩
      have : (m.natAbs : ℤ) = m := Int.natAbs_of_nonneg (le_of_not_gt hm)
      rw [← this, hc]; push_cast; ring

theorem qExpansion_comp_heckeDiag (p : ℕ) [NeZero p] (f : ModularForm (Γ1 N) k) :
    qExpansion 1 (fun τ => f (ModularForm.heckeDiagMatrix p • τ)) = expandPS p (qExpansion 1 f) := by
  ext n
  rw [coeff_expandPS]
  exact ModularFormClass.qCoeff_comp_heckeDiagMatrix_smul f one_mem_sp1 (NeZero.ne p) n

theorem qC_levelRaise (p : ℕ) [NeZero p] (f : ModularForm (Γ1 N) k) :
    qC (levelRaise p f) = qExpand ℂ p (qC f) := by
  rw [coe_levelRaise, qC, qExpansion_comp_heckeDiag, ofPowerSeries_expandPS, qC]

end Expand

section MatrixData

variable {M p : ℕ}

theorem entries {γ : SL(2, ℤ)} {a b c d : ℤ} (h : (γ : Matrix (Fin 2) (Fin 2) ℤ) = !![a, b; c, d]) :
    γ 0 0 = a ∧ γ 0 1 = b ∧ γ 1 0 = c ∧ γ 1 1 = d := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [h]

variable {y w₀ : ℤ} (hrel : (p : ℤ) * w₀ - (M : ℤ) * y = 1)
  {γ : SL(2, ℤ)} (hγ : (γ : Matrix (Fin 2) (Fin 2) ℤ) = !![1, y; (M : ℤ), (p : ℤ) * w₀])

include hrel hγ in

theorem gamma_mem_Gamma1 : γ ∈ Gamma1 M := by
  obtain ⟨g00, -, g10, g11⟩ := entries hγ
  rw [Gamma1_mem, g00, g10, g11]
  refine ⟨by simp, ?_, by simp⟩
  have : (p : ℤ) * w₀ = 1 + M * y := by linear_combination hrel
  rw [this]; push_cast; simp

def del (M p : ℕ) (y w₀ : ℤ) (hrel : (p : ℤ) * w₀ - (M : ℤ) * y = 1) : SL(2, ℤ) :=
  ⟨!![(p : ℤ), y; (M : ℤ), w₀], by rw [Matrix.det_fin_two_of]; linear_combination hrel⟩

@[scoped simp] theorem del_00 : del M p y w₀ hrel 0 0 = (p : ℤ) := rfl
@[scoped simp] theorem del_01 : del M p y w₀ hrel 0 1 = y := rfl
@[scoped simp] theorem del_10 : del M p y w₀ hrel 1 0 = (M : ℤ) := rfl
@[scoped simp] theorem del_11 : del M p y w₀ hrel 1 1 = w₀ := rfl

theorem del_mem_Gamma0 : del M p y w₀ hrel ∈ Gamma0 M := by
  rw [Gamma0_mem, del_10]
  push_cast
  exact ZMod.natCast_self M

theorem del_00_cast : (((del M p y w₀ hrel) 0 0 : ℤ) : ZMod M) = ((p : ℕ) : ZMod M) := by
  rw [del_00, Int.cast_natCast]

variable (hp : p ≠ 0)

def scal (p : ℕ) : GL (Fin 2) ℝ := ModularForm.heckeDiagMatrix p * ModularForm.heckeMatrix p 0

include hγ hp in

theorem heckeDiag_gamma_heckeDiag :
    ModularForm.heckeDiagMatrix p * Matrix.SpecialLinearGroup.mapGL ℝ γ * ModularForm.heckeDiagMatrix p =
      scal p * Matrix.SpecialLinearGroup.mapGL ℝ (del M p y w₀ hrel) := by
  obtain ⟨g00, g01, g10, g11⟩ := entries hγ
  apply Units.ext
  ext i j
  simp only [scal, Units.val_mul, ModularForm.val_heckeDiagMatrix hp, ModularForm.val_heckeMatrix hp]
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two, g00, g01, g10, g11]
  ring

end MatrixData

section SlashEval

variable {N p : ℕ} {k : ℤ}

theorem mapGL_eq_coe (γ : SL(2, ℤ)) : Matrix.SpecialLinearGroup.mapGL ℝ γ = (γ : GL (Fin 2) ℝ) := rfl

theorem slash_mapGL (F : ℍ → ℂ) (γ : SL(2, ℤ)) :
    F ∣[k] Matrix.SpecialLinearGroup.mapGL ℝ γ = F ∣[k] γ := rfl

theorem det_scal_pos (p : ℕ) : 0 < ((scal p).det : ℝ) := by
  rw [scal, map_mul, Units.val_mul]
  exact mul_pos (ModularForm.det_heckeDiagMatrix_pos p) (ModularForm.det_heckeMatrix_pos p 0)

theorem σ_scal (p : ℕ) : UpperHalfPlane.σ (scal p) = .refl ℝ ℂ := by
  rw [UpperHalfPlane.σ, if_pos (det_scal_pos p)]

theorem heckeDiag_smul_heckeMatrix_smul [NeZero p] (τ : ℍ) :
    ModularForm.heckeDiagMatrix p • (ModularForm.heckeMatrix p 0 • τ) = τ := by
  apply UpperHalfPlane.ext
  rw [ModularForm.coe_heckeDiagMatrix_smul (NeZero.ne p), ModularForm.coe_heckeMatrix_smul (NeZero.ne p) 0]
  have : (p : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne p
  field_simp
  push_cast
  ring

theorem slash_scal [NeZero p] (k : ℤ) (F : ℍ → ℂ) : F ∣[k] scal p = ((p : ℂ) ^ (k - 2)) • F := by
  have hp : (p : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne p
  funext τ
  rw [scal, SlashAction.slash_mul, ModularForm.slash_heckeMatrix_apply k (NeZero.ne p) 0,
    ModularForm.slash_heckeDiagMatrix_apply k (NeZero.ne p), heckeDiag_smul_heckeMatrix_smul,
    Pi.smul_apply, smul_eq_mul, show k - 2 = (k - 1) + (-1) by ring, zpow_add₀ hp, _root_.zpow_neg_one]
  ring

def Kk (p : ℕ) (k : ℤ) : ℂ :=
  (((p : ℂ)) ^ (k - 1))⁻¹ * ((((p : ℂ) ^ (k - 1))⁻¹ * (p : ℂ) ^ (k - 2)))

theorem Kk_ne_zero (hp : p ≠ 0) : Kk p k ≠ 0 := by
  have hp' : (p : ℂ) ≠ 0 := by exact_mod_cast hp
  unfold Kk
  exact mul_ne_zero (inv_ne_zero (zpow_ne_zero _ hp'))
    (mul_ne_zero (inv_ne_zero (zpow_ne_zero _ hp')) (zpow_ne_zero _ hp'))

theorem levelRaise_slash_apply [NeZero p] {γ δ₀ : SL(2, ℤ)}
    (hmat : ModularForm.heckeDiagMatrix p * Matrix.SpecialLinearGroup.mapGL ℝ γ *
        ModularForm.heckeDiagMatrix p =
      scal p * Matrix.SpecialLinearGroup.mapGL ℝ δ₀)
    (f : ModularForm (Γ1 N) k) (z : ℍ) :
    (⇑(levelRaise p f) ∣[k] γ) (ModularForm.heckeDiagMatrix p • z) = Kk p k * (⇑f ∣[k] δ₀) z := by
  have hp0 : p ≠ 0 := NeZero.ne p
  have hp' : (p : ℂ) ≠ 0 := by exact_mod_cast hp0
  have step1 : ∀ G : ℍ → ℂ, G (ModularForm.heckeDiagMatrix p • z) =
      (((p : ℂ)) ^ (k - 1))⁻¹ * (G ∣[k] ModularForm.heckeDiagMatrix p) z := by
    intro G
    rw [ModularForm.slash_heckeDiagMatrix_apply k hp0, ← mul_assoc, inv_mul_cancel₀ (zpow_ne_zero _ hp'),
      one_mul]
  have h3 : ((⇑f ∣[k] ModularForm.heckeDiagMatrix p) ∣[k] Matrix.SpecialLinearGroup.mapGL ℝ γ) ∣[k]
        ModularForm.heckeDiagMatrix p =
      ((p : ℂ) ^ (k - 2)) • (⇑f ∣[k] δ₀) := by
    rw [← SlashAction.slash_mul, ← SlashAction.slash_mul, ← mul_assoc, hmat, SlashAction.slash_mul,
      slash_scal, slash_mapGL, ModularForm.SL_smul_slash]
  have hfun : ((⇑(levelRaise p f) ∣[k] γ) ∣[k] ModularForm.heckeDiagMatrix p) =
      ((((p : ℂ) ^ (k - 1))⁻¹ * (p : ℂ) ^ (k - 2))) • (⇑f ∣[k] δ₀) := by
    rw [coe_levelRaise_eq_smul_slash, ModularForm.SL_smul_slash, ModularForm.smul_slash,
      ModularForm.σ_heckeDiagMatrix, ← slash_mapGL _ γ, h3, smul_smul]
    simp only [ContinuousAlgEquiv.refl_apply]
  rw [step1 (⇑(levelRaise p f) ∣[k] γ), hfun, Pi.smul_apply, smul_eq_mul, Kk]
  ring

end SlashEval

section Ext

local notation "L" => AlgebraicClosure ℚ

variable {N N' : ℕ}

theorem coeffEmb_algebraMap (c : ℚ) :
    coeffEmb L (algebraMap ℚ (LaurentSeries ℚ) c) = algebraMap L (LaurentSeries L) (algebraMap ℚ L c) := by
  rw [algebraMap_laurentSeries_eq_single, algebraMap_laurentSeries_eq_single, coeffEmb, coeffMap_single]

def IsGen (N : ℕ) (u : x1FunctionFieldBar N) : Prop :=
  ∃ (k : ℤ) (f g : ModularForm (Γ1 N) k) (pf pg : PowerSeries ℤ),
    IsIntegralQExp f pf ∧ IsIntegralQExp g pg ∧ intSeriesC ℚ pg ≠ 0 ∧
      (u : LaurentSeries L) = coeffEmb L (intSeriesC ℚ pf / intSeriesC ℚ pg)

variable (A B : x1FunctionFieldBar N →ₐ[L] x1FunctionFieldBar N')
  (hAB : ∀ u : x1FunctionFieldBar N, IsGen N u → A u = B u)

theorem algMap_eq (a : L) (ha : algebraMap L (LaurentSeries L) a ∈ x1FunctionFieldBar N) :
    A ⟨algebraMap L (LaurentSeries L) a, ha⟩ = B ⟨algebraMap L (LaurentSeries L) a, ha⟩ := by
  have hy : (⟨algebraMap L (LaurentSeries L) a, ha⟩ : x1FunctionFieldBar N) =
      algebraMap L (x1FunctionFieldBar N) a := Subtype.ext rfl
  rw [hy, AlgHom.commutes, AlgHom.commutes]

include hAB in

theorem eq_on_coeffEmb (z : LaurentSeries ℚ)
    (hz : z ∈ Subfield.closure (Set.range (algebraMap ℚ (LaurentSeries ℚ)) ∪ intFormRatiosC ℚ (Gamma1 N)))
    (hz' : coeffEmb L z ∈ x1FunctionFieldBar N) : A ⟨coeffEmb L z, hz'⟩ = B ⟨coeffEmb L z, hz'⟩ := by
  revert hz'
  induction hz using Subfield.closure_induction with
  | mem w hw =>
      intro hw'
      rcases hw with ⟨c, rfl⟩ | ⟨k, f, g, pf, pg, hf, hg, hg0, rfl⟩
      · have : (⟨coeffEmb L (algebraMap ℚ (LaurentSeries ℚ) c), hw'⟩ : x1FunctionFieldBar N) =
            ⟨algebraMap L (LaurentSeries L) (algebraMap ℚ L c), by
              rw [← coeffEmb_algebraMap]; exact hw'⟩ := Subtype.ext (coeffEmb_algebraMap c)
        rw [this]
        exact algMap_eq A B _ _
      · exact hAB _ ⟨k, f, g, pf, pg, hf, hg, hg0, rfl⟩
  | one =>
      intro h1
      have : (⟨coeffEmb L 1, h1⟩ : x1FunctionFieldBar N) = 1 := Subtype.ext (map_one _)
      rw [this, map_one, map_one]
  | add a b ha hb iha ihb =>
      intro hab
      have ha' : coeffEmb L a ∈ x1FunctionFieldBar N := coeffEmb_mem_laurentBaseChange L ha
      have hb' : coeffEmb L b ∈ x1FunctionFieldBar N := coeffEmb_mem_laurentBaseChange L hb
      have : (⟨coeffEmb L (a + b), hab⟩ : x1FunctionFieldBar N) = ⟨coeffEmb L a, ha'⟩ + ⟨coeffEmb L b, hb'⟩ :=
        Subtype.ext (map_add _ _ _)
      rw [this, map_add, map_add, iha ha', ihb hb']
  | neg a ha iha =>
      intro hna
      have ha' : coeffEmb L a ∈ x1FunctionFieldBar N := coeffEmb_mem_laurentBaseChange L ha
      have : (⟨coeffEmb L (-a), hna⟩ : x1FunctionFieldBar N) = -⟨coeffEmb L a, ha'⟩ :=
        Subtype.ext (map_neg _ _)
      rw [this, map_neg, map_neg, iha ha']
  | inv a ha iha =>
      intro hia
      have ha' : coeffEmb L a ∈ x1FunctionFieldBar N := coeffEmb_mem_laurentBaseChange L ha
      have : (⟨coeffEmb L a⁻¹, hia⟩ : x1FunctionFieldBar N) = (⟨coeffEmb L a, ha'⟩)⁻¹ :=
        Subtype.ext (map_inv₀ _ _)
      rw [this, map_inv₀, map_inv₀, iha ha']
  | mul a b ha hb iha ihb =>
      intro hab
      have ha' : coeffEmb L a ∈ x1FunctionFieldBar N := coeffEmb_mem_laurentBaseChange L ha
      have hb' : coeffEmb L b ∈ x1FunctionFieldBar N := coeffEmb_mem_laurentBaseChange L hb
      have : (⟨coeffEmb L (a * b), hab⟩ : x1FunctionFieldBar N) = ⟨coeffEmb L a, ha'⟩ * ⟨coeffEmb L b, hb'⟩ :=
        Subtype.ext (map_mul _ _ _)
      rw [this, map_mul, map_mul, iha ha', ihb hb']

include hAB in

theorem algHom_ext_of_isGen : A = B := by
  apply AlgHom.ext
  rintro ⟨x, hx⟩
  have hx' : x ∈ Subfield.closure (Set.range (algebraMap (AlgebraicClosure ℚ) _) ∪
      ⇑(coeffEmb (AlgebraicClosure ℚ)) '' (x1FunctionField N : Set (LaurentSeries ℚ))) := hx
  revert hx
  induction hx' using Subfield.closure_induction with
  | mem w hw =>
      intro hw'
      rcases hw with ⟨a, rfl⟩ | ⟨z, hz, rfl⟩
      · exact algMap_eq A B a _
      · exact eq_on_coeffEmb A B hAB z hz hw'
  | one =>
      intro h
      have e : (⟨1, h⟩ : x1FunctionFieldBar N) = 1 := Subtype.ext rfl
      rw [e, map_one, map_one]
  | add a b ha hb iha ihb =>
      intro hab
      have e : (⟨a + b, hab⟩ : x1FunctionFieldBar N) = ⟨a, ha⟩ + ⟨b, hb⟩ := Subtype.ext rfl
      rw [e, map_add, map_add, iha ha, ihb hb]
  | neg a ha iha =>
      intro hna
      have e : (⟨-a, hna⟩ : x1FunctionFieldBar N) = -⟨a, ha⟩ := Subtype.ext rfl
      rw [e, map_neg, map_neg, iha ha]
  | inv a ha iha =>
      intro hia
      have e : (⟨a⁻¹, hia⟩ : x1FunctionFieldBar N) = (⟨a, ha⟩)⁻¹ := Subtype.ext rfl
      rw [e, map_inv₀, map_inv₀, iha ha]
  | mul a b ha hb iha ihb =>
      intro hab
      have e : (⟨a * b, hab⟩ : x1FunctionFieldBar N) = ⟨a, ha⟩ * ⟨b, hb⟩ := Subtype.ext rfl
      rw [e, map_mul, map_mul, iha ha, ihb hb]

end Ext

section Laws

local notation "L" => AlgebraicClosure ℚ

abbrev ιC : LaurentSeries ℚ →+* LaurentSeries ℂ := coeffMap (algebraMap ℚ ℂ)

theorem ιC_injective : Function.Injective ιC := RingHom.injective _

theorem ιC_intSeriesC {F : ℍ → ℂ} {q : PowerSeries ℤ} (h : IsIntegralQExp F q) :
    ιC (intSeriesC ℚ q) = qC F := by
  rw [qC, ← h]
  ext n
  simp only [intSeriesC, coeffMap_coeff, PowerSeries.coeff_coe]
  split_ifs
  · exact map_zero _
  · simp [PowerSeries.coeff_map]

theorem coeffMap_ι_coeffEmb (ι : L →+* ℂ) (z : LaurentSeries ℚ) :
    coeffMap ι (coeffEmb L z) = ιC z := by
  rw [coeffEmb, coeffMap_coeffMap]
  exact coeffMap_congr (RingHom.ext_rat _ _) z

variable {M p : ℕ} [Fact p.Prime] [NeZero p]
  {y w₀ : ℤ} (hrel : (p : ℤ) * w₀ - (M : ℤ) * y = 1)
  {γ : SL(2, ℤ)} (hγ : (γ : Matrix (Fin 2) (Fin 2) ℤ) = !![1, y; (M : ℤ), (p : ℤ) * w₀])
  (ι : L →+* ℂ)
  (τ : x1FunctionFieldBar (M * p) ≃ₐ[L] x1FunctionFieldBar (M * p))
  (hτ : ∀ (x : x1FunctionFieldBar (M * p)) (k : ℤ) (f g φ ψ : ModularForm (Γ1 (M * p)) k) (D E : ℤ),
        D ≠ 0 → E ≠ 0 →
        (⇑φ : ℍ → ℂ) = (D : ℂ) • (fun z : ℍ => ((⇑f) ∣[k] γ) (ModularForm.heckeDiagMatrix p • z)) →
        (⇑ψ : ℍ → ℂ) = (E : ℂ) • (fun z : ℍ => ((⇑g) ∣[k] γ) (ModularForm.heckeDiagMatrix p • z)) →
        qC g ≠ 0 →
        coeffMap ι (x : LaurentSeries L) = qC f / qC g →
        coeffMap ι ((τ x : x1FunctionFieldBar (M * p)) : LaurentSeries L) =
          HahnSeries.C ((E : ℂ) / (D : ℂ)) * qC φ / qC ψ)
  (α₁ β₁ : x1FunctionFieldBar M →ₐ[L] x1FunctionFieldBar (M * p))
  (hα : ∀ u : x1FunctionFieldBar M,
    ((α₁ u : x1FunctionFieldBar (M * p)) : LaurentSeries L) = (u : LaurentSeries L))
  (hβ : haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
    ∀ u : x1FunctionFieldBar M,
      ((β₁ u : x1FunctionFieldBar (M * p)) : LaurentSeries L) = qExpand L p (u : LaurentSeries L))
  (hdia : IsDiamondAut M p (diamondAut M p))
  (hbc : IsBaseChangeAutOf L (diamondAut M p) (diamondAutBar M p))

theorem C_one_div_one : (HahnSeries.C ((((1 : ℤ) : ℂ)) / ((1 : ℤ) : ℂ)) : LaurentSeries ℂ) = 1 := by
  rw [Int.cast_one, div_one, map_one]

include hrel hγ hτ hα hβ in

theorem law1_gen (u : x1FunctionFieldBar M) (hu : IsGen M u) : τ (α₁ u) = β₁ u := by
  obtain ⟨k, f, g, pf, pg, hf, hg, hg0, hu⟩ := hu
  have hγ1 : γ ∈ Gamma1 M := gamma_mem_Gamma1 hrel hγ

  have hqg : qC g ≠ 0 := by
    rw [← ιC_intSeriesC hg]; exact (map_ne_zero_iff _ ιC_injective).mpr hg0
  have hcu : coeffMap ι (u : LaurentSeries L) = qC f / qC g := by
    rw [hu, coeffMap_ι_coeffEmb, map_div₀, ιC_intSeriesC hf, ιC_intSeriesC hg]
  have hx : coeffMap ι ((α₁ u : x1FunctionFieldBar (M * p)) : LaurentSeries L) = qC (res p f) / qC (res p g) := by
    rw [hα, coe_res, coe_res]; exact hcu

  have hfix : ∀ h : ModularForm (Γ1 M) k, (⇑h : ℍ → ℂ) ∣[k] γ = ⇑h := fun h =>
    SlashInvariantFormClass.slash_action_eq h _ (Subgroup.mem_map_of_mem _ hγ1)
  have hφ : (⇑(levelRaise p f) : ℍ → ℂ) =
      ((1 : ℤ) : ℂ) • (fun z : ℍ => ((⇑(res p f)) ∣[k] γ) (ModularForm.heckeDiagMatrix p • z)) := by
    rw [Int.cast_one, one_smul, coe_levelRaise, coe_res, hfix]
  have hψ : (⇑(levelRaise p g) : ℍ → ℂ) =
      ((1 : ℤ) : ℂ) • (fun z : ℍ => ((⇑(res p g)) ∣[k] γ) (ModularForm.heckeDiagMatrix p • z)) := by
    rw [Int.cast_one, one_smul, coe_levelRaise, coe_res, hfix]
  have hqg' : qC (res p g) ≠ 0 := by rw [coe_res]; exact hqg
  have hE1 := hτ (α₁ u) k (res p f) (res p g) (levelRaise p f) (levelRaise p g) 1 1 one_ne_zero one_ne_zero
    hφ hψ hqg' hx
  rw [C_one_div_one, one_mul, qC_levelRaise, qC_levelRaise, ← map_div₀ (qExpand ℂ p), ← hcu,
    ← coeffMap_qExpand] at hE1
  apply Subtype.ext
  apply RingHom.injective (coeffMap ι)
  rw [hE1, hβ]

include hrel hγ hτ hα hβ hdia hbc in

theorem law2_gen (u : x1FunctionFieldBar M) (hu : IsGen M u) : τ (β₁ u) = α₁ (diamondAutBar M p u) := by
  obtain ⟨k, f, g, pf, pg, hf, hg, hg0, hu⟩ := hu
  have hp : p ≠ 0 := NeZero.ne p

  set δ₀ : SL(2, ℤ) := del M p y w₀ hrel with hδ₀def
  have hδ₀ : δ₀ ∈ Gamma0 M := del_mem_Gamma0 hrel
  have hδ₀d : ((δ₀ 0 0 : ℤ) : ZMod M) = ((p : ℕ) : ZMod M) := del_00_cast hrel
  have hmat := heckeDiag_gamma_heckeDiag hrel hγ hp

  have hqg : qC g ≠ 0 := by
    rw [← ιC_intSeriesC hg]; exact (map_ne_zero_iff _ ιC_injective).mpr hg0
  have hcu : coeffMap ι (u : LaurentSeries L) = qC f / qC g := by
    rw [hu, coeffMap_ι_coeffEmb, map_div₀, ιC_intSeriesC hf, ιC_intSeriesC hg]
  have hlg : qC (levelRaise p g) ≠ 0 := by
    rw [qC_levelRaise]; exact fun h => hqg (qExpand_injective p (by rw [h, map_zero]))
  have hx : coeffMap ι ((β₁ u : x1FunctionFieldBar (M * p)) : LaurentSeries L) =
      qC (levelRaise p f) / qC (levelRaise p g) := by
    rw [hβ, coeffMap_qExpand, hcu, map_div₀, qC_levelRaise, qC_levelRaise]

  have hc : Kk p k ≠ 0 := Kk_ne_zero hp
  have hφ : (⇑(Kk p k • res p (dForm δ₀ hδ₀ f)) : ℍ → ℂ) =
      ((1 : ℤ) : ℂ) • (fun z : ℍ => ((⇑(levelRaise p f)) ∣[k] γ) (ModularForm.heckeDiagMatrix p • z)) := by
    rw [Int.cast_one, one_smul, ModularForm.IsGLPos.coe_smul, coe_res, coe_dForm]
    funext z
    rw [Pi.smul_apply, smul_eq_mul, levelRaise_slash_apply hmat f z]
  have hψ : (⇑(Kk p k • res p (dForm δ₀ hδ₀ g)) : ℍ → ℂ) =
      ((1 : ℤ) : ℂ) • (fun z : ℍ => ((⇑(levelRaise p g)) ∣[k] γ) (ModularForm.heckeDiagMatrix p • z)) := by
    rw [Int.cast_one, one_smul, ModularForm.IsGLPos.coe_smul, coe_res, coe_dForm]
    funext z
    rw [Pi.smul_apply, smul_eq_mul, levelRaise_slash_apply hmat g z]
  have hE1 := hτ (β₁ u) k (levelRaise p f) (levelRaise p g) (Kk p k • res p (dForm δ₀ hδ₀ f))
    (Kk p k • res p (dForm δ₀ hδ₀ g)) 1 1 one_ne_zero one_ne_zero hφ hψ hlg hx

  have hdg : qC (dForm δ₀ hδ₀ g) ≠ 0 := by
    rw [qC_ne_zero_iff one_mem_sp1] at hqg ⊢
    exact slash_ne_zero hqg δ₀
  have hres : ∀ h : ModularForm (Γ1 M) k,
      qC (⇑(Kk p k • res p (dForm δ₀ hδ₀ h))) = HahnSeries.C (Kk p k) * qC (dForm δ₀ hδ₀ h) := by
    intro h
    rw [ModularForm.IsGLPos.coe_smul, coe_res, qC_smul one_mem_sp1]
  rw [C_one_div_one, one_mul, hres, hres, mul_div_mul_left _ _ (C_ne_zero hc)] at hE1

  have hz : intSeriesC ℚ pf / intSeriesC ℚ pg ∈ x1FunctionField M := div_mem_qExpFunctionFieldC f g hf hg hg0
  have hueq : u = ⟨coeffEmb L (intSeriesC ℚ pf / intSeriesC ℚ pg), coeffEmb_mem_laurentBaseChange L hz⟩ :=
    Subtype.ext hu
  have h1 := hbc ⟨_, hz⟩
  have h2 := hdia.2 k f g pf pg hf hg hg0 δ₀ hδ₀ hδ₀d
  have hDm : coeffMap ι ((diamondAutBar M p u : x1FunctionFieldBar M) : LaurentSeries L) * qC (dForm δ₀ hδ₀ g) =
      qC (dForm δ₀ hδ₀ f) := by
    rw [hueq]
    change ((diamondAutBar M p ⟨coeffEmb L (intSeriesC ℚ pf / intSeriesC ℚ pg), _⟩ : x1FunctionFieldBar M) :
        LaurentSeries L) = _ at h1
    rw [h1, coeffMap_ι_coeffEmb]
    exact h2
  apply Subtype.ext
  apply RingHom.injective (coeffMap ι)
  rw [hE1, hα, (eq_div_iff hdg).mpr hDm]

end Laws

end TOLD0b
p2m_reactivate "P2MW.S_ModularCurve_XOneP_comp_alpha_eq_beta_and_comp_beta_eq_alpha_comp_diamondAutBar_of_atkinLehnerSlash_p.TOLD0b"

open ModularCurve TOLD0b in
theorem solution
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hpM : ¬ p ∣ M)

    (y w₀ : ℤ) (hrel : (p : ℤ) * w₀ - (M : ℤ) * y = 1)
    (γ γ' : SL(2, ℤ)) (hγ : (γ : Matrix (Fin 2) (Fin 2) ℤ) = !![1, y; (M : ℤ), (p : ℤ) * w₀])
    (hγ' : (γ' : Matrix (Fin 2) (Fin 2) ℤ) = !![w₀, -y; -(M : ℤ), (p : ℤ)])
    (ι : AlgebraicClosure ℚ →+* ℂ)
    (τ : ↥(ModularCurve.x1FunctionFieldBar (M * p)) ≃ₐ[(AlgebraicClosure ℚ)] ↥(ModularCurve.x1FunctionFieldBar (M * p)))
    (hτ :

      (∀ (x : ↥(ModularCurve.x1FunctionFieldBar (M * p))) (k : ℤ) (f g φ ψ : ModularForm (CongruenceSubgroup.Gamma1 (M * p) : Subgroup (GL (Fin 2) ℝ)) k) (D E : ℤ),
        D ≠ 0 → E ≠ 0 →
        (⇑φ : UpperHalfPlane → ℂ) = (D : ℂ) • (fun z : UpperHalfPlane => ((⇑f) ∣[k] γ) (ModularForm.heckeDiagMatrix p • z)) →
        (⇑ψ : UpperHalfPlane → ℂ) = (E : ℂ) • (fun z : UpperHalfPlane => ((⇑g) ∣[k] γ) (ModularForm.heckeDiagMatrix p • z)) →
        HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑g) ≠ 0 →
        ModularCurve.coeffMap ι ((x : ↥(ModularCurve.x1FunctionFieldBar (M * p))) : LaurentSeries (AlgebraicClosure ℚ)) = HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑f) / HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑g) →
        ModularCurve.coeffMap ι ((τ x : ↥(ModularCurve.x1FunctionFieldBar (M * p))) : LaurentSeries (AlgebraicClosure ℚ)) =
          HahnSeries.C ((E : ℂ) / (D : ℂ)) * HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑φ) / HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑ψ)))

    (α₁ β₁ : ↥(ModularCurve.x1FunctionFieldBar M) →ₐ[AlgebraicClosure ℚ] ↥(ModularCurve.x1FunctionFieldBar (M * p)))
    (hα : ∀ u : ↥(ModularCurve.x1FunctionFieldBar M), ((α₁ u : ↥(ModularCurve.x1FunctionFieldBar (M * p))) : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)))
    (hβ : haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
      ∀ u : ↥(ModularCurve.x1FunctionFieldBar M), ((β₁ u : ↥(ModularCurve.x1FunctionFieldBar (M * p))) : LaurentSeries (AlgebraicClosure ℚ)) = ModularCurve.qExpand (AlgebraicClosure ℚ) p (u : LaurentSeries (AlgebraicClosure ℚ)))

    (hdia : ModularCurve.IsDiamondAut M p (ModularCurve.diamondAut M p))
    (hbc : ModularCurve.IsBaseChangeAutOf (AlgebraicClosure ℚ) (ModularCurve.diamondAut M p) (ModularCurve.diamondAutBar M p)) :
    τ.toAlgHom.comp α₁ = β₁ ∧
    τ.toAlgHom.comp β₁ = α₁.comp (ModularCurve.diamondAutBar M p).toAlgHom := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  refine ⟨?_, ?_⟩
  · refine algHom_ext_of_isGen _ _ fun u hu => ?_
    show τ (α₁ u) = β₁ u
    exact law1_gen hrel hγ ι τ hτ α₁ β₁ hα hβ u hu
  · refine algHom_ext_of_isGen _ _ fun u hu => ?_
    show τ (β₁ u) = α₁ (diamondAutBar M p u)
    exact law2_gen hrel hγ ι τ hτ α₁ β₁ hα hβ hdia hbc u hu

end
end S_ModularCurve_XOneP_comp_alpha_eq_beta_and_comp_beta_eq_alpha_comp_diamondAutBar_of_atkinLehnerSlash_p
end P2MW
export P2MW.S_ModularCurve_XOneP_comp_alpha_eq_beta_and_comp_beta_eq_alpha_comp_diamondAutBar_of_atkinLehnerSlash_p (solution)
