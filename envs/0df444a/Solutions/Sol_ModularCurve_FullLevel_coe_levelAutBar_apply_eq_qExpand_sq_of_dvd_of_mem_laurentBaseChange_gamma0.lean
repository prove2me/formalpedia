-- Prove2me | solution 1 for ModularCurve.FullLevel.coe_levelAutBar_apply_eq_qExpand_sq_of_dvd_of_mem_laurentBaseChange_gamma0
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.339302+00:00
-- url     : https://prove2.me/submissions/deee9631-b345-5298-8d9f-956011317612

import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_ModularCurve_PhiGen
import Definitions.Def_ModularForm_HeckeOperator
import Theorems.Thm_ModularCurve_FullLevel_levelAutInputs_of_not_dvd
import Theorems.Thm_ModularForm_exists_degeneracy_Gamma0
import Theorems.Thm_ModularFormClass_qCoeff_comp_heckeDiagMatrix_smul
import Theorems.Thm_ModularCurve_FullLevel_laurentBaseChange_gamma0_le_fieldBar
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_coe_levelAutBar_apply_eq_qExpand_sq_of_dvd_of_mem_laurentBaseChange_gamma0

set_option autoImplicit false

p2m_open "AlgebraicCurve ModularCurve P2MW.S_ModularCurve_FullLevel_coe_levelAutBar_apply_eq_qExpand_sq_of_dvd_of_mem_laurentBaseChange_gamma0.ModularCurve ModularCurve.FullLevel P2MW.S_ModularCurve_FullLevel_coe_levelAutBar_apply_eq_qExpand_sq_of_dvd_of_mem_laurentBaseChange_gamma0.ModularCurve.FullLevel CongruenceSubgroup UpperHalfPlane"
open scoped MatrixGroups ModularForm

noncomputable section

namespace ModularCurve
p2m_export "ModularCurve" "IsIntegralQExp intSeriesC intFormRatiosC qExpFunctionFieldC div_mem_qExpFunctionFieldC qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd qExpand_C algebraMap_apply_eq_single ofPowerSeries_coeff_of_neg coeffMap coeffMap_coeff coeffMap_single coeffMap_coeffMap algebraMap_laurentSeries_eq_single coeffEmb laurentBaseChange coeffEmb_mem_laurentBaseChange FullLevel.levelAutInputs_of_not_dvd FullLevel.laurentBaseChange_gamma0_le_fieldBar"
namespace FullLevel
p2m_export "ModularCurve.FullLevel" "levelH fieldBar Idx conjElem IsLevelAutBar levelAutBar isLevelAutBar_levelAutBar levelAutInputs_of_not_dvd laurentBaseChange_gamma0_le_fieldBar"
namespace LawGen
p2m_open "ModularCurve.FullLevel ModularCurve"

section Slash

variable (q : ℕ) [Fact q.Prime]

private theorem val_conjElem (γ : SL(2, ℤ)) :
    ((conjElem q γ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
      !![((γ 0 0 : ℤ) : ℝ), ((γ 0 1 : ℤ) : ℝ) / q; (q : ℝ) * ((γ 1 0 : ℤ) : ℝ), ((γ 1 1 : ℤ) : ℝ)] := rfl

private theorem det_conjElem (γ : SL(2, ℤ)) : ((conjElem q γ).det : ℝ) = 1 := by
  have hq : (q : ℝ) ≠ 0 := by exact_mod_cast (Fact.out : q.Prime).ne_zero
  have hdet : ((γ 0 0 : ℤ) : ℝ) * ((γ 1 1 : ℤ) : ℝ) - ((γ 0 1 : ℤ) : ℝ) * ((γ 1 0 : ℤ) : ℝ) = 1 := by
    have h := Matrix.SpecialLinearGroup.det_coe γ
    rw [Matrix.det_fin_two] at h
    exact_mod_cast h
  rw [Matrix.GeneralLinearGroup.val_det_apply, val_conjElem, Matrix.det_fin_two_of]
  field_simp
  linear_combination hdet

private theorem det_conjElem_pos (γ : SL(2, ℤ)) : 0 < ((conjElem q γ).det : ℝ) := by
  rw [det_conjElem]; exact one_pos

private theorem σ_conjElem (γ : SL(2, ℤ)) : UpperHalfPlane.σ (conjElem q γ) = .refl ℝ ℂ := by
  rw [UpperHalfPlane.σ, if_pos (det_conjElem_pos q γ)]

private theorem denom_conjElem (γ : SL(2, ℤ)) (τ : ℍ) :
    denom (conjElem q γ) τ = (q : ℂ) * ((γ 1 0 : ℤ) : ℂ) * (τ : ℂ) + ((γ 1 1 : ℤ) : ℂ) := by
  simp [denom, val_conjElem]

private theorem num_conjElem (γ : SL(2, ℤ)) (τ : ℍ) :
    num (conjElem q γ) τ = ((γ 0 0 : ℤ) : ℂ) * (τ : ℂ) + ((γ 0 1 : ℤ) : ℂ) / (q : ℂ) := by
  simp [num, val_conjElem]

variable {q}

private def cofactor (δ : SL(2, ℤ)) (a' : ℤ) (ha : (δ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 = q * a') : SL(2, ℤ) :=
  ⟨!![a', δ 0 1; δ 1 0, q * δ 1 1], by
    have h := Matrix.SpecialLinearGroup.det_coe δ
    rw [Matrix.det_fin_two, ha] at h
    rw [Matrix.det_fin_two_of]
    linear_combination h⟩

private theorem cofactor_mem_gamma0 {M' : ℕ} (δ : SL(2, ℤ)) (hδ : δ ∈ Gamma0 M') (a' : ℤ)
    (ha : (δ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 = q * a') : cofactor δ a' ha ∈ Gamma0 M' := by
  rw [Gamma0_mem] at hδ ⊢
  exact hδ

private theorem mapGL_cofactor_mem {M' : ℕ} (δ : SL(2, ℤ)) (hδ : δ ∈ Gamma0 M') (a' : ℤ)
    (ha : (δ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 = q * a') :
    (Matrix.SpecialLinearGroup.mapGL ℝ (cofactor δ a' ha) : GL (Fin 2) ℝ) ∈
      ((Gamma0 M' : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) :=
  ⟨cofactor δ a' ha, cofactor_mem_gamma0 δ hδ a' ha, rfl⟩

private theorem val_mapGL (γ : SL(2, ℤ)) :
    ((Matrix.SpecialLinearGroup.mapGL ℝ γ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
      (γ : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ℝ) := rfl

private theorem det_mapGL_pos (γ : SL(2, ℤ)) : 0 < ((Matrix.SpecialLinearGroup.mapGL ℝ γ).det : ℝ) := by
  rw [Matrix.GeneralLinearGroup.val_det_apply, val_mapGL]
  have h := Matrix.SpecialLinearGroup.det_coe γ
  have : ((γ : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ℝ)).det = ((γ : Matrix (Fin 2) (Fin 2) ℤ).det : ℝ) := by
    rw [Int.cast_det]
  rw [this, h]; exact_mod_cast one_pos

private theorem conjElem_smul_eq (δ : SL(2, ℤ)) (a' : ℤ) (ha : (δ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 = q * a') (τ : ℍ) :
    conjElem q δ • τ =
      Matrix.SpecialLinearGroup.mapGL ℝ (cofactor δ a' ha) • (ModularForm.heckeDiagMatrix (q ^ 2) • τ) := by
  have hq0 : q ≠ 0 := (Fact.out : q.Prime).ne_zero
  have hq2 : q ^ 2 ≠ 0 := pow_ne_zero 2 hq0
  have hq : (q : ℂ) ≠ 0 := by exact_mod_cast hq0
  apply UpperHalfPlane.ext
  rw [coe_smul_of_det_pos (det_conjElem_pos q δ), coe_smul_of_det_pos (det_mapGL_pos _),
    num_conjElem, denom_conjElem]
  have hD : (q : ℂ) * ((δ 1 0 : ℤ) : ℂ) * (τ : ℂ) + ((δ 1 1 : ℤ) : ℂ) ≠ 0 := by
    rw [← denom_conjElem]; exact denom_ne_zero _ _
  simp only [num, denom, val_mapGL, Matrix.map_apply, cofactor, ModularForm.coe_heckeDiagMatrix_smul hq2]
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, Matrix.empty_val']
  have ha' : ((δ 0 0 : ℤ) : ℂ) = (q : ℂ) * (a' : ℂ) := by exact_mod_cast ha
  push_cast
  rw [ha']
  field_simp

private theorem slash_conjElem_of_gamma0 {M' : ℕ} {k : ℤ}
    (F : ModularForm ((Gamma0 M' : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) k)
    (δ : SL(2, ℤ)) (hδ : δ ∈ Gamma0 M') (ha : (q : ℤ) ∣ (δ : Matrix (Fin 2) (Fin 2) ℤ) 0 0) :
    (⇑F : ℍ → ℂ) ∣[k] conjElem q δ = fun τ => (q : ℂ) ^ k * F (ModularForm.heckeDiagMatrix (q ^ 2) • τ) := by
  obtain ⟨a', ha'⟩ := ha
  have hq0 : q ≠ 0 := (Fact.out : q.Prime).ne_zero
  have hq2 : q ^ 2 ≠ 0 := pow_ne_zero 2 hq0
  funext τ
  rw [ModularForm.slash_apply, σ_conjElem, det_conjElem, conjElem_smul_eq δ a' ha' τ,
    SlashInvariantForm.slash_action_eqn'' F (mapGL_cofactor_mem δ hδ a' ha')]
  have hD : denom (conjElem q δ) τ ≠ 0 := denom_ne_zero _ _
  have hden : denom (Matrix.SpecialLinearGroup.mapGL ℝ (cofactor δ a' ha') : GL (Fin 2) ℝ)
      ((ModularForm.heckeDiagMatrix (q ^ 2) • τ : ℍ) : ℂ) = (q : ℂ) * denom (conjElem q δ) τ := by
    rw [denom_conjElem]
    simp only [denom, val_mapGL, Matrix.map_apply, cofactor, ModularForm.coe_heckeDiagMatrix_smul hq2]
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one, Matrix.empty_val']
    push_cast
    ring
  rw [hden]
  have hDk : denom (conjElem q δ) τ ^ k ≠ 0 := zpow_ne_zero k hD
  simp only [ContinuousAlgEquiv.refl_apply, abs_one, Complex.ofReal_one, one_zpow, mul_zpow, zpow_neg]
  field_simp

end Slash

section Forms

private def restrictLE {Γ Γ' : Subgroup SL(2, ℤ)} (h : Γ' ≤ Γ) {k : ℤ}
    (F : ModularForm ((Γ : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) k) :
    ModularForm ((Γ' : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) k where
  toFun := ⇑F
  slash_action_eq' A hA := SlashInvariantFormClass.slash_action_eq F A (Subgroup.map_mono h hA)
  holo' := ModularFormClass.holo F
  bdd_at_cusps' hc := ModularFormClass.bdd_at_cusps F (hc.mono (Subgroup.map_mono h))

@[scoped simp] private theorem coe_restrictLE {Γ Γ' : Subgroup SL(2, ℤ)} (h : Γ' ≤ Γ) {k : ℤ}
    (F : ModularForm ((Γ : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) k) :
    (⇑(restrictLE h F) : ℍ → ℂ) = ⇑F := rfl

private theorem one_mem_strictPeriods_gamma0 (N : ℕ) :
    (1 : ℝ) ∈ ((Gamma0 N : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
  rw [CongruenceSubgroup.strictPeriods_Gamma0]; exact AddSubgroup.mem_zmultiples _

private theorem ofPowerSeries_qExpansion_comp_heckeDiagMatrix {M' : ℕ} {k : ℤ}
    (F : ModularForm ((Gamma0 M' : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) k) (n : ℕ) [NeZero n] :
    HahnSeries.ofPowerSeries ℤ ℂ (qExpansion 1 (fun τ => F (ModularForm.heckeDiagMatrix n • τ))) =
      qExpand ℂ n (HahnSeries.ofPowerSeries ℤ ℂ (qExpansion 1 ⇑F)) := by
  ext m
  by_cases hm : 0 ≤ m
  · lift m to ℕ using hm
    rw [HahnSeries.ofPowerSeries_apply_coeff]
    have h := ModularFormClass.qCoeff_comp_heckeDiagMatrix_smul F (one_mem_strictPeriods_gamma0 M') (NeZero.ne n) m
    simp only [ModularFormClass.qCoeff] at h
    rw [h]
    by_cases hd : n ∣ m
    · obtain ⟨m', rfl⟩ := hd
      rw [if_pos (dvd_mul_right n m'), Nat.mul_div_cancel_left _ (NeZero.pos n), Nat.cast_mul,
        qExpand_coeff_mul, HahnSeries.ofPowerSeries_apply_coeff]
    · rw [if_neg hd, qExpand_coeff_of_not_dvd]
      exact_mod_cast hd
  · have hm' : m < 0 := not_le.mp hm
    rw [ofPowerSeries_coeff_of_neg _ hm']
    by_cases hd : (n : ℤ) ∣ m
    · obtain ⟨m', rfl⟩ := hd
      rw [qExpand_coeff_mul, ofPowerSeries_coeff_of_neg]
      have hn : (0 : ℤ) < n := by exact_mod_cast NeZero.pos n
      nlinarith
    · rw [qExpand_coeff_of_not_dvd _ _ hd]

private theorem coeffMap_qExpand {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (n : ℕ) [NeZero n]
    (x : LaurentSeries R) : coeffMap f (qExpand R n x) = qExpand S n (coeffMap f x) := by
  ext k
  by_cases h : (n : ℤ) ∣ k
  · obtain ⟨m, rfl⟩ := h
    rw [coeffMap_coeff, qExpand_coeff_mul, qExpand_coeff_mul, coeffMap_coeff]
  · rw [coeffMap_coeff, qExpand_coeff_of_not_dvd _ _ h, qExpand_coeff_of_not_dvd _ _ h, map_zero]

private theorem coeffMap_injective {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (hf : Function.Injective f) : Function.Injective (coeffMap f : LaurentSeries R → LaurentSeries S) := by
  intro x y h
  ext k
  apply hf
  have := congrArg (fun s : LaurentSeries S => s.coeff k) h
  simpa only [coeffMap_coeff] using this

private theorem coeffMap_intSeriesC {R S : Type*} [Field R] [Field S] (f : R →+* S) (p : PowerSeries ℤ) :
    coeffMap f (intSeriesC R p) = intSeriesC S p := by
  ext n
  rw [coeffMap_coeff, intSeriesC, intSeriesC]
  by_cases hn : 0 ≤ n
  · lift n to ℕ using hn
    rw [HahnSeries.ofPowerSeries_apply_coeff, HahnSeries.ofPowerSeries_apply_coeff, PowerSeries.coeff_map,
      PowerSeries.coeff_map, eq_intCast, eq_intCast, map_intCast]
  · rw [ofPowerSeries_coeff_of_neg _ (not_le.mp hn), ofPowerSeries_coeff_of_neg _ (not_le.mp hn), map_zero]

private theorem ofPowerSeries_qExpansion_eq_intSeriesC {f : ℍ → ℂ} {p : PowerSeries ℤ} (h : IsIntegralQExp f p) :
    HahnSeries.ofPowerSeries ℤ ℂ (qExpansion 1 f) = intSeriesC ℂ p := by
  rw [intSeriesC, ← h]

private theorem exists_emb {q : ℕ} [Fact q.Prime] (ζ : Idx q) :
    ∃ ι₀ : AlgebraicClosure ℚ →+* ℂ, ι₀ ζ.val = Complex.exp (2 * Real.pi * Complex.I / q) := by
  haveI : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := AlgebraicClosure.isAlgebraic ℚ
  have hq0 : q ≠ 0 := (Fact.out : q.Prime).ne_zero
  have hζ := ζ.isPrimitiveRoot
  have hmin : minpoly ℚ ζ.val = Polynomial.cyclotomic q ℚ :=
    (Polynomial.cyclotomic_eq_minpoly_rat hζ (Nat.pos_of_ne_zero hq0)).symm
  have hroot : Complex.exp (2 * Real.pi * Complex.I / q) ∈ (minpoly ℚ ζ.val).rootSet ℂ := by
    rw [hmin, Polynomial.mem_rootSet]
    refine ⟨Polynomial.cyclotomic_ne_zero q ℚ, ?_⟩
    rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, Polynomial.map_cyclotomic]
    exact (Polynomial.isRoot_cyclotomic_iff.mpr (Complex.isPrimitiveRoot_exp q hq0)).eq_zero
  rw [← Algebra.IsAlgebraic.range_eval_eq_rootSet_minpoly ℂ ζ.val] at hroot
  obtain ⟨ψ, hψ⟩ := hroot
  exact ⟨ψ.toRingHom, hψ⟩

end Forms

section Generators

variable (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M') (ζ : Idx q)
  (δ : SL(2, ℤ)) (hδ : δ ∈ Gamma0 M') (ha : (q : ℤ) ∣ (δ : Matrix (Fin 2) (Fin 2) ℤ) 0 0)

private theorem gammaH_le_gamma0 : CohCarrier.GammaH (q ^ 2 * M') (levelH q M') ≤ Gamma0 M' := by
  refine (CohCarrier.GammaH_le_Gamma0 _).trans ?_
  intro γ hγ
  rw [Gamma0_mem] at hγ ⊢
  have h1 := congrArg (ZMod.castHom (show M' ∣ q ^ 2 * M' from ⟨q ^ 2, by ring⟩) (ZMod M')) hγ
  rwa [map_intCast, map_zero] at h1

include hqM' hδ ha in

private theorem coe_levelAutBar_ratio {k : ℤ}
    (F G : ModularForm ((Gamma0 M' : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) k)
    (P Q : PowerSeries ℤ) (hF : IsIntegralQExp F P) (hG : IsIntegralQExp G Q) (hQ0 : intSeriesC ℚ Q ≠ 0)
    (x : fieldBar q M')
    (hx : (x : LaurentSeries (AlgebraicClosure ℚ)) = coeffEmb (AlgebraicClosure ℚ) (intSeriesC ℚ P / intSeriesC ℚ Q)) :
    ((levelAutBar q M' ζ δ x : fieldBar q M') : LaurentSeries (AlgebraicClosure ℚ)) =
      qExpand (AlgebraicClosure ℚ) (q ^ 2) (x : LaurentSeries (AlgebraicClosure ℚ)) := by
  classical
  have hτ : IsLevelAutBar q M' ζ δ (levelAutBar q M' ζ δ) :=
    isLevelAutBar_levelAutBar (ModularCurve.FullLevel.levelAutInputs_of_not_dvd q M' hqM' ζ δ hδ)
  obtain ⟨ι, hι⟩ := exists_emb ζ
  have hιinj : Function.Injective ι := ι.injective
  let f := restrictLE (gammaH_le_gamma0 q M') F
  let g := restrictLE (gammaH_le_gamma0 q M') G
  have hf : IsIntegralQExp f P := hF
  have hg : IsIntegralQExp g Q := hG
  have hyx : (⟨coeffEmb (AlgebraicClosure ℚ) (intSeriesC ℚ P / intSeriesC ℚ Q),
      coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (div_mem_qExpFunctionFieldC f g hf hg hQ0)⟩ :
        fieldBar q M') = x := Subtype.ext hx.symm
  have hc := hτ k f g P Q hf hg hQ0 ι hι
  rw [hyx] at hc

  have hfs : (⇑f : ℍ → ℂ) ∣[k] conjElem q δ = fun τ => (q : ℂ) ^ k * F (ModularForm.heckeDiagMatrix (q ^ 2) • τ) :=
    slash_conjElem_of_gamma0 F δ hδ ha
  have hgs : (⇑g : ℍ → ℂ) ∣[k] conjElem q δ = fun τ => (q : ℂ) ^ k * G (ModularForm.heckeDiagMatrix (q ^ 2) • τ) :=
    slash_conjElem_of_gamma0 G δ hδ ha

  haveI : NeZero (q ^ 2 * M') := ⟨mul_ne_zero (pow_ne_zero _ (Fact.out : q.Prime).ne_zero) (NeZero.ne M')⟩
  obtain ⟨Fn, hFn⟩ := ModularForm.exists_degeneracy_Gamma0 (k := k) (M := M') (N := q ^ 2 * M') (d := q ^ 2)
    dvd_rfl F
  obtain ⟨Gn, hGn⟩ := ModularForm.exists_degeneracy_Gamma0 (k := k) (M := M') (N := q ^ 2 * M') (d := q ^ 2)
    dvd_rfl G
  have h1n := one_mem_strictPeriods_gamma0 (q ^ 2 * M')
  have hEW : (fun τ : ℍ => (q : ℂ) ^ k * F (ModularForm.heckeDiagMatrix (q ^ 2) • τ)) = ((q : ℂ) ^ k) • (⇑Fn : ℍ → ℂ) := by
    rw [hFn]; rfl
  have hDW : (fun τ : ℍ => (q : ℂ) ^ k * G (ModularForm.heckeDiagMatrix (q ^ 2) • τ)) = ((q : ℂ) ^ k) • (⇑Gn : ℍ → ℂ) := by
    rw [hGn]; rfl
  haveI : NeZero (q ^ 2) := ⟨pow_ne_zero _ (Fact.out : q.Prime).ne_zero⟩
  rw [hfs, hgs, hEW, hDW, ModularForm.qExpansion_smul one_pos h1n _ Fn,
    ModularForm.qExpansion_smul one_pos h1n _ Gn, hFn, hGn, PowerSeries.smul_eq_C_mul, PowerSeries.smul_eq_C_mul,
    map_mul, map_mul, HahnSeries.ofPowerSeries_C, ofPowerSeries_qExpansion_comp_heckeDiagMatrix F (q ^ 2),
    ofPowerSeries_qExpansion_comp_heckeDiagMatrix G (q ^ 2), ofPowerSeries_qExpansion_eq_intSeriesC hF,
    ofPowerSeries_qExpansion_eq_intSeriesC hG] at hc

  have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast (Fact.out : q.Prime).ne_zero
  have hC0 : (HahnSeries.C ((q : ℂ) ^ k) : LaurentSeries ℂ) ≠ 0 := HahnSeries.C_ne_zero (zpow_ne_zero _ hq0)
  have hQC0 : intSeriesC ℂ Q ≠ 0 := by
    intro h; apply hQ0
    apply coeffMap_injective (algebraMap ℚ ℂ) (algebraMap ℚ ℂ).injective
    rw [coeffMap_intSeriesC, h, map_zero]
  have hqQ0 : qExpand ℂ (q ^ 2) (intSeriesC ℂ Q) ≠ 0 := by
    intro h; apply hQC0
    exact (qExpand ℂ (q ^ 2)).injective (by rw [h, map_zero])
  have hxC : coeffMap ι (x : LaurentSeries (AlgebraicClosure ℚ)) = intSeriesC ℂ P / intSeriesC ℂ Q := by
    rw [hx, coeffEmb, coeffMap_coeffMap, map_div₀, coeffMap_intSeriesC, coeffMap_intSeriesC]
  have hkey : coeffMap ι ((levelAutBar q M' ζ δ x : fieldBar q M') : LaurentSeries (AlgebraicClosure ℚ)) =
      qExpand ℂ (q ^ 2) (intSeriesC ℂ P) / qExpand ℂ (q ^ 2) (intSeriesC ℂ Q) := by
    rw [eq_div_iff hqQ0]
    apply mul_left_cancel₀ hC0
    calc HahnSeries.C ((q : ℂ) ^ k) * (coeffMap ι ↑(levelAutBar q M' ζ δ x) * qExpand ℂ (q ^ 2) (intSeriesC ℂ Q))
        = coeffMap ι ↑(levelAutBar q M' ζ δ x) * (HahnSeries.C ((q : ℂ) ^ k) * qExpand ℂ (q ^ 2) (intSeriesC ℂ Q)) := by
          ring
      _ = _ := hc
  apply coeffMap_injective ι hιinj
  rw [hkey, coeffMap_qExpand, hxC, map_div₀]

end Generators

end ModularCurve.FullLevel.LawGen
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_coe_levelAutBar_apply_eq_qExpand_sq_of_dvd_of_mem_laurentBaseChange_gamma0.ModularCurve P2MW.S_ModularCurve_FullLevel_coe_levelAutBar_apply_eq_qExpand_sq_of_dvd_of_mem_laurentBaseChange_gamma0.ModularCurve.FullLevel P2MW.S_ModularCurve_FullLevel_coe_levelAutBar_apply_eq_qExpand_sq_of_dvd_of_mem_laurentBaseChange_gamma0.ModularCurve.FullLevel.LawGen"
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_coe_levelAutBar_apply_eq_qExpand_sq_of_dvd_of_mem_laurentBaseChange_gamma0.ModularCurve P2MW.S_ModularCurve_FullLevel_coe_levelAutBar_apply_eq_qExpand_sq_of_dvd_of_mem_laurentBaseChange_gamma0.ModularCurve.FullLevel"
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_coe_levelAutBar_apply_eq_qExpand_sq_of_dvd_of_mem_laurentBaseChange_gamma0.ModularCurve"

namespace ModularCurve
p2m_export "ModularCurve" "IsIntegralQExp intSeriesC intFormRatiosC qExpFunctionFieldC div_mem_qExpFunctionFieldC qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd qExpand_C algebraMap_apply_eq_single ofPowerSeries_coeff_of_neg coeffMap coeffMap_coeff coeffMap_single coeffMap_coeffMap algebraMap_laurentSeries_eq_single coeffEmb laurentBaseChange coeffEmb_mem_laurentBaseChange FullLevel.levelAutInputs_of_not_dvd FullLevel.laurentBaseChange_gamma0_le_fieldBar"
namespace FullLevel
p2m_export "ModularCurve.FullLevel" "levelH fieldBar Idx conjElem IsLevelAutBar levelAutBar isLevelAutBar_levelAutBar levelAutInputs_of_not_dvd laurentBaseChange_gamma0_le_fieldBar"
namespace LawGen
p2m_open "ModularCurve.FullLevel ModularCurve"

section Closure

variable (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M') (ζ : Idx q)
  (δ : SL(2, ℤ)) (hδ : δ ∈ Gamma0 M') (ha : (q : ℤ) ∣ (δ : Matrix (Fin 2) (Fin 2) ℤ) 0 0)

private theorem qExpand_algebraMap (n : ℕ) [NeZero n] (c : AlgebraicClosure ℚ) :
    qExpand (AlgebraicClosure ℚ) n (algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) c) =
      algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) c := by
  rw [algebraMap_laurentSeries_eq_single, ← HahnSeries.C_apply, qExpand_C]

private def fixedSet : IntermediateField (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) where
  carrier := {g | ∃ hg : g ∈ fieldBar q M',
    ((levelAutBar q M' ζ δ ⟨g, hg⟩ : fieldBar q M') : LaurentSeries (AlgebraicClosure ℚ)) =
      qExpand (AlgebraicClosure ℚ) (q ^ 2) g}
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨mul_mem ha hb, ?_⟩
    have : (⟨a * b, mul_mem ha hb⟩ : fieldBar q M') = ⟨a, ha⟩ * ⟨b, hb⟩ := rfl
    rw [this, map_mul, map_mul]
    show ((levelAutBar q M' ζ δ ⟨a, ha⟩ : fieldBar q M') : LaurentSeries (AlgebraicClosure ℚ)) *
      ((levelAutBar q M' ζ δ ⟨b, hb⟩ : fieldBar q M') : LaurentSeries (AlgebraicClosure ℚ)) = _
    rw [ha', hb']
  one_mem' := by
    refine ⟨one_mem _, ?_⟩
    have : (⟨1, one_mem _⟩ : fieldBar q M') = 1 := rfl
    rw [this, map_one, map_one]; rfl
  add_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨add_mem ha hb, ?_⟩
    have : (⟨a + b, add_mem ha hb⟩ : fieldBar q M') = ⟨a, ha⟩ + ⟨b, hb⟩ := rfl
    rw [this, map_add, map_add]
    show ((levelAutBar q M' ζ δ ⟨a, ha⟩ : fieldBar q M') : LaurentSeries (AlgebraicClosure ℚ)) +
      ((levelAutBar q M' ζ δ ⟨b, hb⟩ : fieldBar q M') : LaurentSeries (AlgebraicClosure ℚ)) = _
    rw [ha', hb']
  zero_mem' := by
    refine ⟨zero_mem _, ?_⟩
    have : (⟨0, zero_mem _⟩ : fieldBar q M') = 0 := rfl
    rw [this, map_zero, map_zero]; rfl
  algebraMap_mem' := by
    intro c
    refine ⟨IntermediateField.algebraMap_mem _ c, ?_⟩
    have : (⟨algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) c,
        IntermediateField.algebraMap_mem _ c⟩ : fieldBar q M') = algebraMap (AlgebraicClosure ℚ) (fieldBar q M') c := rfl
    rw [this, AlgEquiv.commutes, qExpand_algebraMap]
    rfl
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    refine ⟨inv_mem ha, ?_⟩
    have : (⟨a⁻¹, inv_mem ha⟩ : fieldBar q M') = (⟨a, ha⟩ : fieldBar q M')⁻¹ := rfl
    rw [this, map_inv₀, map_inv₀]
    show (((levelAutBar q M' ζ δ ⟨a, ha⟩ : fieldBar q M') : LaurentSeries (AlgebraicClosure ℚ)))⁻¹ = _
    rw [ha']

private theorem mem_fixedSet_iff (g : LaurentSeries (AlgebraicClosure ℚ)) :
    g ∈ fixedSet q M' ζ δ ↔ ∃ hg : g ∈ fieldBar q M',
      ((levelAutBar q M' ζ δ ⟨g, hg⟩ : fieldBar q M') : LaurentSeries (AlgebraicClosure ℚ)) =
        qExpand (AlgebraicClosure ℚ) (q ^ 2) g := Iff.rfl

include hqM' hδ ha in
private theorem coeffEmb_ratio_mem_fixedSet (r : LaurentSeries ℚ) (hr : r ∈ intFormRatiosC ℚ (Gamma0 M')) :
    coeffEmb (AlgebraicClosure ℚ) r ∈ fixedSet q M' ζ δ := by
  obtain ⟨k, F, G, P, Q, hF, hG, hQ0, rfl⟩ := hr
  have hmem : coeffEmb (AlgebraicClosure ℚ) (intSeriesC ℚ P / intSeriesC ℚ Q) ∈ fieldBar q M' :=
    ModularCurve.FullLevel.laurentBaseChange_gamma0_le_fieldBar q M'
      (coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (div_mem_qExpFunctionFieldC F G hF hG hQ0))
  exact ⟨hmem, coe_levelAutBar_ratio q M' hqM' ζ δ hδ ha F G P Q hF hG hQ0 ⟨_, hmem⟩ rfl⟩

include hqM' hδ ha in

private theorem laurentBaseChange_gamma0_le_fixedSet :
    laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (Gamma0 M')) ≤ fixedSet q M' ζ δ := by
  change IntermediateField.adjoin _ _ ≤ _
  rw [IntermediateField.adjoin_le_iff]
  rintro _ ⟨z, hz, rfl⟩
  have hz' : z ∈ Subfield.closure (Set.range (algebraMap ℚ (LaurentSeries ℚ)) ∪ intFormRatiosC ℚ (Gamma0 M')) := hz
  have hmap : coeffEmb (AlgebraicClosure ℚ) z ∈ (Subfield.closure
      (Set.range (algebraMap ℚ (LaurentSeries ℚ)) ∪ intFormRatiosC ℚ (Gamma0 M'))).map
        (coeffEmb (AlgebraicClosure ℚ)) := ⟨z, hz', rfl⟩
  suffices hsub : (Subfield.closure
      (Set.range (algebraMap ℚ (LaurentSeries ℚ)) ∪ intFormRatiosC ℚ (Gamma0 M'))).map
        (coeffEmb (AlgebraicClosure ℚ)) ≤ (fixedSet q M' ζ δ).toSubfield from hsub hmap
  rw [RingHom.map_field_closure]
  refine Subfield.closure_le.mpr ?_
  rintro _ ⟨w, hw | hw, rfl⟩
  · obtain ⟨c, rfl⟩ := hw
    rw [algebraMap_apply_eq_single]
    show coeffMap (algebraMap ℚ (AlgebraicClosure ℚ)) (HahnSeries.single 0 c) ∈ fixedSet q M' ζ δ
    rw [coeffMap_single, ← algebraMap_laurentSeries_eq_single]
    exact (fixedSet q M' ζ δ).algebraMap_mem _
  · show coeffEmb (AlgebraicClosure ℚ) w ∈ fixedSet q M' ζ δ
    exact coeffEmb_ratio_mem_fixedSet q M' hqM' ζ δ hδ ha w hw

end Closure
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_coe_levelAutBar_apply_eq_qExpand_sq_of_dvd_of_mem_laurentBaseChange_gamma0.ModularCurve P2MW.S_ModularCurve_FullLevel_coe_levelAutBar_apply_eq_qExpand_sq_of_dvd_of_mem_laurentBaseChange_gamma0.ModularCurve.FullLevel P2MW.S_ModularCurve_FullLevel_coe_levelAutBar_apply_eq_qExpand_sq_of_dvd_of_mem_laurentBaseChange_gamma0.ModularCurve.FullLevel.LawGen"

end ModularCurve.FullLevel.LawGen
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_coe_levelAutBar_apply_eq_qExpand_sq_of_dvd_of_mem_laurentBaseChange_gamma0.ModularCurve P2MW.S_ModularCurve_FullLevel_coe_levelAutBar_apply_eq_qExpand_sq_of_dvd_of_mem_laurentBaseChange_gamma0.ModularCurve.FullLevel P2MW.S_ModularCurve_FullLevel_coe_levelAutBar_apply_eq_qExpand_sq_of_dvd_of_mem_laurentBaseChange_gamma0.ModularCurve.FullLevel.LawGen"
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_coe_levelAutBar_apply_eq_qExpand_sq_of_dvd_of_mem_laurentBaseChange_gamma0.ModularCurve P2MW.S_ModularCurve_FullLevel_coe_levelAutBar_apply_eq_qExpand_sq_of_dvd_of_mem_laurentBaseChange_gamma0.ModularCurve.FullLevel P2MW.S_ModularCurve_FullLevel_coe_levelAutBar_apply_eq_qExpand_sq_of_dvd_of_mem_laurentBaseChange_gamma0.ModularCurve.FullLevel.LawGen"
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_coe_levelAutBar_apply_eq_qExpand_sq_of_dvd_of_mem_laurentBaseChange_gamma0.ModularCurve P2MW.S_ModularCurve_FullLevel_coe_levelAutBar_apply_eq_qExpand_sq_of_dvd_of_mem_laurentBaseChange_gamma0.ModularCurve.FullLevel P2MW.S_ModularCurve_FullLevel_coe_levelAutBar_apply_eq_qExpand_sq_of_dvd_of_mem_laurentBaseChange_gamma0.ModularCurve.FullLevel.LawGen"

open ModularCurve.FullLevel.LawGen in

theorem solution
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M') (ζ : Idx q)
    (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M') (ha : (q : ℤ) ∣ (γ : Matrix (Fin 2) (Fin 2) ℤ) 0 0)
    (g : LaurentSeries (AlgebraicClosure ℚ))
    (hg : g ∈ laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (Gamma0 M')))
    (x : fieldBar q M') (hx : (x : LaurentSeries (AlgebraicClosure ℚ)) = g) :
    ((levelAutBar q M' ζ γ x : fieldBar q M') : LaurentSeries (AlgebraicClosure ℚ)) =
      qExpand (AlgebraicClosure ℚ) (q ^ 2) g := by
  obtain ⟨hg', h⟩ := (mem_fixedSet_iff q M' ζ γ g).mp
    (laurentBaseChange_gamma0_le_fixedSet q M' hqM' ζ γ hγ ha hg)
  have hxg : x = ⟨g, hg'⟩ := Subtype.ext hx
  rw [hxg]
  exact h

end
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_coe_levelAutBar_apply_eq_qExpand_sq_of_dvd_of_mem_laurentBaseChange_gamma0.ModularCurve P2MW.S_ModularCurve_FullLevel_coe_levelAutBar_apply_eq_qExpand_sq_of_dvd_of_mem_laurentBaseChange_gamma0.ModularCurve.FullLevel P2MW.S_ModularCurve_FullLevel_coe_levelAutBar_apply_eq_qExpand_sq_of_dvd_of_mem_laurentBaseChange_gamma0.ModularCurve.FullLevel.LawGen"

end S_ModularCurve_FullLevel_coe_levelAutBar_apply_eq_qExpand_sq_of_dvd_of_mem_laurentBaseChange_gamma0
end P2MW
export P2MW.S_ModularCurve_FullLevel_coe_levelAutBar_apply_eq_qExpand_sq_of_dvd_of_mem_laurentBaseChange_gamma0 (solution)
