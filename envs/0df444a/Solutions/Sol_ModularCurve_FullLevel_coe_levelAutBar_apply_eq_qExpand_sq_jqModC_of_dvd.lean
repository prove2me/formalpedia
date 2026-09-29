-- Prove2me | solution 1 for ModularCurve.FullLevel.coe_levelAutBar_apply_eq_qExpand_sq_jqModC_of_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.339302+00:00
-- url     : https://prove2.me/submissions/51201ca5-811f-5c86-ab0b-bdd2559368a8

import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularForm_HeckeOperator
import Theorems.Thm_ModularCurve_FullLevel_levelAutInputs_of_not_dvd
import Theorems.Thm_ModularForm_exists_degeneracy_Gamma0
import Theorems.Thm_ModularFormClass_qCoeff_comp_heckeDiagMatrix_smul
import Theorems.Thm_ModularCurve_qExpansion_discriminant_eq_map_X_mul_dedekindEtaUnit
import Theorems.Thm_ModularCurve_jqModC_eq_qExpansion_E4_cube_div_discriminant
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_coe_levelAutBar_apply_eq_qExpand_sq_jqModC_of_dvd

set_option autoImplicit false

p2m_open "AlgebraicCurve ModularCurve P2MW.S_ModularCurve_FullLevel_coe_levelAutBar_apply_eq_qExpand_sq_jqModC_of_dvd.ModularCurve ModularCurve.FullLevel P2MW.S_ModularCurve_FullLevel_coe_levelAutBar_apply_eq_qExpand_sq_jqModC_of_dvd.ModularCurve.FullLevel CongruenceSubgroup UpperHalfPlane"
open scoped MatrixGroups ModularForm

noncomputable section

namespace ModularCurve
p2m_export "ModularCurve" "FullLevel.conjElem IsIntegralQExp isIntegralQExp_iff intSeriesC div_mem_qExpFunctionFieldC qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd eisenstein4 dedekindEtaUnit constantCoeff_dedekindEtaUnit dedekindEtaUnitInv dedekindEtaUnit_mul_inv jNum ofPowerSeries_coeff_of_neg coeffMap coeffMap_coeff coeffEmb coeffEmb_mem_laurentBaseChange jqModC map_jqModC FullLevel.levelAutInputs_of_not_dvd qExpansion_discriminant_eq_map_X_mul_dedekindEtaUnit jqModC_eq_qExpansion_E4_cube_div_discriminant"
namespace FullLevel
p2m_export "ModularCurve.FullLevel" "levelH fieldBar Idx conjElem IsLevelAutBar levelAutBar isLevelAutBar_levelAutBar levelAutInputs_of_not_dvd"
namespace ConjElemSlash
p2m_open "ModularCurve.FullLevel ModularCurve"

variable (q : ℕ) [Fact q.Prime]

private theorem val_conjElem (γ : SL(2, ℤ)) :
    ((conjElem q γ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
      !![((γ 0 0 : ℤ) : ℝ), ((γ 0 1 : ℤ) : ℝ) / q; (q : ℝ) * ((γ 1 0 : ℤ) : ℝ), ((γ 1 1 : ℤ) : ℝ)] := by
  rfl

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

private theorem mapGL_mem_SL (γ : SL(2, ℤ)) :
    (Matrix.SpecialLinearGroup.mapGL ℝ γ : GL (Fin 2) ℝ) ∈ 𝒮ℒ := ⟨γ, rfl⟩

private theorem val_mapGL (γ : SL(2, ℤ)) :
    ((Matrix.SpecialLinearGroup.mapGL ℝ γ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
      (γ : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ℝ) := by
  rfl

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

private theorem slash_conjElem_of_levelOne {k : ℤ} (F : ModularForm 𝒮ℒ k)
    (q : ℕ) [Fact q.Prime] (δ : SL(2, ℤ)) (ha : (q : ℤ) ∣ (δ : Matrix (Fin 2) (Fin 2) ℤ) 0 0) :
    (⇑F : ℍ → ℂ) ∣[k] ModularCurve.FullLevel.conjElem q δ =
      fun τ => (q : ℂ) ^ k * F (ModularForm.heckeDiagMatrix (q ^ 2) • τ) := by
  obtain ⟨a', ha'⟩ := ha
  have hq0 : q ≠ 0 := (Fact.out : q.Prime).ne_zero
  have hq2 : q ^ 2 ≠ 0 := pow_ne_zero 2 hq0
  have hq : (q : ℂ) ≠ 0 := by exact_mod_cast hq0
  funext τ
  rw [ModularForm.slash_apply, σ_conjElem, det_conjElem, conjElem_smul_eq δ a' ha' τ,
    SlashInvariantForm.slash_action_eqn'' F (mapGL_mem_SL (cofactor δ a' ha'))]
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

end ModularCurve.FullLevel.ConjElemSlash

namespace ModularCurve
p2m_export "ModularCurve" "FullLevel.conjElem IsIntegralQExp isIntegralQExp_iff intSeriesC div_mem_qExpFunctionFieldC qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd eisenstein4 dedekindEtaUnit constantCoeff_dedekindEtaUnit dedekindEtaUnitInv dedekindEtaUnit_mul_inv jNum ofPowerSeries_coeff_of_neg coeffMap coeffMap_coeff coeffEmb coeffEmb_mem_laurentBaseChange jqModC map_jqModC FullLevel.levelAutInputs_of_not_dvd qExpansion_discriminant_eq_map_X_mul_dedekindEtaUnit jqModC_eq_qExpansion_E4_cube_div_discriminant"
namespace FullLevel
p2m_export "ModularCurve.FullLevel" "levelH fieldBar Idx conjElem IsLevelAutBar levelAutBar isLevelAutBar_levelAutBar levelAutInputs_of_not_dvd"
namespace LevelAutJ
p2m_open "ModularCurve.FullLevel ModularCurve"

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

@[scoped simp] private theorem coe_ofCuspSL {k : ℤ} (F : CuspForm 𝒮ℒ k) : (⇑(ofCuspSL F) : ℍ → ℂ) = ⇑F := rfl

private theorem ofPowerSeries_qExpansion_comp_heckeDiagMatrix {k : ℤ} (F : ModularForm 𝒮ℒ k) (n : ℕ) [NeZero n] :
    HahnSeries.ofPowerSeries ℤ ℂ (qExpansion 1 (fun τ => F (ModularForm.heckeDiagMatrix n • τ))) =
      qExpand ℂ n (HahnSeries.ofPowerSeries ℤ ℂ (qExpansion 1 ⇑F)) := by
  ext m
  by_cases hm : 0 ≤ m
  · lift m to ℕ using hm
    rw [HahnSeries.ofPowerSeries_apply_coeff]
    have h := ModularFormClass.qCoeff_comp_heckeDiagMatrix_smul F one_mem_strictPeriods_SL (NeZero.ne n) m
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

private theorem isIntegralQExp_E4 : IsIntegralQExp (ModularForm.E₄ : ℍ → ℂ) eisenstein4 := by
  rw [isIntegralQExp_iff]
  intro n
  rw [EisensteinSeries.E_qExpansion_coeff (by norm_num) (by decide) n, eisenstein4, PowerSeries.coeff_mk]
  split_ifs with h
  · simp
  · rw [show _root_.bernoulli 4 = -1 / 30 by decide +kernel, ArithmeticFunction.sigma_apply]
    push_cast
    ring

private theorem intSeriesC_delta_ne_zero (K : Type*) [Field K] :
    intSeriesC K (PowerSeries.X * dedekindEtaUnit) ≠ 0 := by
  intro h
  have h1 := congrArg (fun z : LaurentSeries K => z.coeff 1) h
  simp only [intSeriesC, HahnSeries.coeff_zero] at h1
  have h2 : (HahnSeries.ofPowerSeries ℤ K
      ((PowerSeries.X * dedekindEtaUnit).map (Int.castRingHom K))).coeff ((1 : ℕ) : ℤ) = 1 := by
    rw [HahnSeries.ofPowerSeries_apply_coeff, PowerSeries.coeff_map,
      show (1 : ℕ) = 0 + 1 from rfl, PowerSeries.coeff_succ_X_mul,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, constantCoeff_dedekindEtaUnit, map_one]
  rw [show ((1 : ℕ) : ℤ) = 1 from rfl] at h2
  rw [h2] at h1
  exact one_ne_zero h1

private theorem jqModC_mul_delta (K : Type*) [Field K] :
    jqModC K * intSeriesC K (PowerSeries.X * dedekindEtaUnit) = intSeriesC K (eisenstein4 ^ 3) := by
  rw [jqModC, intSeriesC, intSeriesC, jNum, mul_assoc, ← map_mul, ← map_mul,
    show eisenstein4 ^ 3 * dedekindEtaUnitInv * (PowerSeries.X * dedekindEtaUnit) =
      PowerSeries.X * eisenstein4 ^ 3 by
        rw [mul_comm PowerSeries.X dedekindEtaUnit, ← mul_assoc, mul_assoc (eisenstein4 ^ 3),
          mul_comm dedekindEtaUnitInv, dedekindEtaUnit_mul_inv, mul_one, mul_comm],
    map_mul, PowerSeries.map_X, map_mul, HahnSeries.ofPowerSeries_X, ← mul_assoc,
    HahnSeries.single_mul_single]
  simp

private theorem jqModC_eq_div (K : Type*) [Field K] :
    jqModC K = intSeriesC K (eisenstein4 ^ 3) / intSeriesC K (PowerSeries.X * dedekindEtaUnit) := by
  rw [eq_div_iff (intSeriesC_delta_ne_zero K), jqModC_mul_delta]

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

end ModularCurve.FullLevel.LevelAutJ
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_coe_levelAutBar_apply_eq_qExpand_sq_jqModC_of_dvd.ModularCurve P2MW.S_ModularCurve_FullLevel_coe_levelAutBar_apply_eq_qExpand_sq_jqModC_of_dvd.ModularCurve.FullLevel P2MW.S_ModularCurve_FullLevel_coe_levelAutBar_apply_eq_qExpand_sq_jqModC_of_dvd.ModularCurve.FullLevel.LevelAutJ"
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_coe_levelAutBar_apply_eq_qExpand_sq_jqModC_of_dvd.ModularCurve P2MW.S_ModularCurve_FullLevel_coe_levelAutBar_apply_eq_qExpand_sq_jqModC_of_dvd.ModularCurve.FullLevel"
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_coe_levelAutBar_apply_eq_qExpand_sq_jqModC_of_dvd.ModularCurve"

end
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_coe_levelAutBar_apply_eq_qExpand_sq_jqModC_of_dvd.ModularCurve P2MW.S_ModularCurve_FullLevel_coe_levelAutBar_apply_eq_qExpand_sq_jqModC_of_dvd.ModularCurve.FullLevel P2MW.S_ModularCurve_FullLevel_coe_levelAutBar_apply_eq_qExpand_sq_jqModC_of_dvd.ModularCurve.FullLevel.LevelAutJ"

p2m_open "AlgebraicCurve ModularCurve P2MW.S_ModularCurve_FullLevel_coe_levelAutBar_apply_eq_qExpand_sq_jqModC_of_dvd.ModularCurve ModularCurve.FullLevel P2MW.S_ModularCurve_FullLevel_coe_levelAutBar_apply_eq_qExpand_sq_jqModC_of_dvd.ModularCurve.FullLevel IsLocalRing CongruenceSubgroup"
open scoped MatrixGroups

open ModularCurve.FullLevel.LevelAutJ UpperHalfPlane in

theorem solution
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M') (ζ : Idx q)
    (δ : SL(2, ℤ)) (hδ : δ ∈ Gamma0 M') (ha : (q : ℤ) ∣ (δ : Matrix (Fin 2) (Fin 2) ℤ) 0 0)
    (x : fieldBar q M') (hx : (x : LaurentSeries (AlgebraicClosure ℚ)) = jqModC (AlgebraicClosure ℚ)) :
    ((levelAutBar q M' ζ δ x : fieldBar q M') : LaurentSeries (AlgebraicClosure ℚ)) =
      qExpand (AlgebraicClosure ℚ) (q ^ 2) (jqModC (AlgebraicClosure ℚ)) := by
  classical

  have hτ : IsLevelAutBar q M' ζ δ (levelAutBar q M' ζ δ) :=
    isLevelAutBar_levelAutBar (ModularCurve.FullLevel.levelAutInputs_of_not_dvd q M' hqM' ζ δ hδ)
  obtain ⟨ι, hι⟩ := exists_emb ζ
  have hιinj : Function.Injective ι := ι.injective

  set Γ : Subgroup SL(2, ℤ) := CohCarrier.GammaH (q ^ 2 * M') (levelH q M') with hΓ
  let E3 : ModularForm 𝒮ℒ 12 := (ModularForm.E₄.mul (ModularForm.E₄.mul ModularForm.E₄)).mcast (by norm_num)
  have hE3 : (⇑E3 : ℍ → ℂ) = fun τ => ModularForm.E₄ τ ^ 3 := by
    funext τ
    show ModularForm.E₄ τ * (ModularForm.E₄ τ * ModularForm.E₄ τ) = _
    ring
  let Dl : ModularForm 𝒮ℒ 12 := ofCuspSL CuspForm.discriminant
  have hDl : (⇑Dl : ℍ → ℂ) = ModularForm.discriminant := by
    show ⇑(CuspForm.discriminant) = _
    exact CuspForm.coe_discriminant
  have hqE3 : qExpansion 1 (⇑E3 : ℍ → ℂ) = (qExpansion 1 (⇑ModularForm.E₄ : ℍ → ℂ)) ^ 3 := by
    show qExpansion 1 (⇑(ModularForm.E₄.mul (ModularForm.E₄.mul ModularForm.E₄)) : ℍ → ℂ) = _
    rw [ModularForm.qExpansion_mul one_pos one_mem_strictPeriods_SL,
      ModularForm.qExpansion_mul one_pos one_mem_strictPeriods_SL]
    ring
  let f : ModularForm (CohCarrier.GammaH (q ^ 2 * M') (levelH q M') : Subgroup (GL (Fin 2) ℝ)) 12 :=
    restrictSL E3 Γ
  let g : ModularForm (CohCarrier.GammaH (q ^ 2 * M') (levelH q M') : Subgroup (GL (Fin 2) ℝ)) 12 :=
    restrictSL Dl Γ

  have hf : IsIntegralQExp f (eisenstein4 ^ 3) := by
    rw [IsIntegralQExp, map_pow, isIntegralQExp_E4]
    show _ = qExpansion 1 (⇑E3 : ℍ → ℂ)
    rw [hqE3]
  have hg : IsIntegralQExp g (PowerSeries.X * dedekindEtaUnit) := by
    rw [IsIntegralQExp]
    show _ = qExpansion 1 (⇑Dl : ℍ → ℂ)
    rw [hDl]
    exact ModularCurve.qExpansion_discriminant_eq_map_X_mul_dedekindEtaUnit.symm
  have hg0 : intSeriesC ℚ (PowerSeries.X * dedekindEtaUnit) ≠ 0 := intSeriesC_delta_ne_zero ℚ

  have hyx : (⟨coeffEmb (AlgebraicClosure ℚ)
        (intSeriesC ℚ (eisenstein4 ^ 3) / intSeriesC ℚ (PowerSeries.X * dedekindEtaUnit)),
      coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (div_mem_qExpFunctionFieldC f g hf hg hg0)⟩ :
        fieldBar q M') = x := by
    apply Subtype.ext
    show coeffEmb (AlgebraicClosure ℚ) _ = (x : LaurentSeries (AlgebraicClosure ℚ))
    rw [← jqModC_eq_div ℚ, hx]
    exact map_jqModC _

  have hc := hτ 12 f g (eisenstein4 ^ 3) (PowerSeries.X * dedekindEtaUnit) hf hg hg0 ι hι
  rw [hyx] at hc

  have hfs : (⇑f : ℍ → ℂ) ∣[(12 : ℤ)] conjElem q δ =
      fun τ => (q : ℂ) ^ (12 : ℤ) * E3 (ModularForm.heckeDiagMatrix (q ^ 2) • τ) :=
    ConjElemSlash.slash_conjElem_of_levelOne E3 q δ ha
  have hgs : (⇑g : ℍ → ℂ) ∣[(12 : ℤ)] conjElem q δ =
      fun τ => (q : ℂ) ^ (12 : ℤ) * Dl (ModularForm.heckeDiagMatrix (q ^ 2) • τ) :=
    ConjElemSlash.slash_conjElem_of_levelOne Dl q δ ha

  haveI : NeZero (q ^ 2) := ⟨pow_ne_zero _ (Fact.out : q.Prime).ne_zero⟩
  obtain ⟨En, hEn⟩ := ModularForm.exists_degeneracy_Gamma0 (k := (12 : ℤ)) (M := 1) (N := q ^ 2) (d := q ^ 2)
    (by simp) (restrictSL E3 (CongruenceSubgroup.Gamma0 1))
  obtain ⟨Dn, hDn⟩ := ModularForm.exists_degeneracy_Gamma0 (k := (12 : ℤ)) (M := 1) (N := q ^ 2) (d := q ^ 2)
    (by simp) (restrictSL Dl (CongruenceSubgroup.Gamma0 1))
  rw [coe_restrictSL] at hEn hDn
  have h1n : (1 : ℝ) ∈ ((CongruenceSubgroup.Gamma0 (q ^ 2) : Subgroup SL(2, ℤ)) :
      Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
    rw [CongruenceSubgroup.strictPeriods_Gamma0]; exact AddSubgroup.mem_zmultiples _
  have hEW : (fun τ : ℍ => (q : ℂ) ^ (12 : ℤ) * E3 (ModularForm.heckeDiagMatrix (q ^ 2) • τ)) =
      ((q : ℂ) ^ (12 : ℤ)) • (⇑En : ℍ → ℂ) := by
    rw [hEn]; rfl
  have hDW : (fun τ : ℍ => (q : ℂ) ^ (12 : ℤ) * Dl (ModularForm.heckeDiagMatrix (q ^ 2) • τ)) =
      ((q : ℂ) ^ (12 : ℤ)) • (⇑Dn : ℍ → ℂ) := by
    rw [hDn]; rfl

  have hΔ0 : HahnSeries.ofPowerSeries ℤ ℂ (qExpansion 1 ModularForm.discriminant) ≠ 0 := by
    intro h
    have := congrArg (fun s : LaurentSeries ℂ => s.coeff ((1 : ℕ) : ℤ)) h
    simp only [HahnSeries.ofPowerSeries_apply_coeff, ModularForm.discriminant_qExpansion_coeff_one] at this
    simp at this
  have hjΔ : jqModC ℂ * HahnSeries.ofPowerSeries ℤ ℂ (qExpansion 1 ModularForm.discriminant) =
      HahnSeries.ofPowerSeries ℤ ℂ (qExpansion 1 (⇑E3 : ℍ → ℂ)) := by
    rw [ModularCurve.jqModC_eq_qExpansion_E4_cube_div_discriminant, div_mul_cancel₀ _ hΔ0, hqE3, map_pow]
  rw [hfs, hgs, hEW, hDW, ModularForm.qExpansion_smul one_pos h1n _ En,
    ModularForm.qExpansion_smul one_pos h1n _ Dn, hEn, hDn, PowerSeries.smul_eq_C_mul, PowerSeries.smul_eq_C_mul,
    map_mul, map_mul, HahnSeries.ofPowerSeries_C, ofPowerSeries_qExpansion_comp_heckeDiagMatrix E3 (q ^ 2),
    ofPowerSeries_qExpansion_comp_heckeDiagMatrix Dl (q ^ 2), hDl, ← hjΔ, map_mul] at hc

  have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast (Fact.out : q.Prime).ne_zero
  have hC0 : (HahnSeries.C ((q : ℂ) ^ (12 : ℤ)) : LaurentSeries ℂ) ≠ 0 :=
    HahnSeries.C_ne_zero (zpow_ne_zero _ hq0)
  have hqΔ0 : qExpand ℂ (q ^ 2) (HahnSeries.ofPowerSeries ℤ ℂ (qExpansion 1 ModularForm.discriminant)) ≠ 0 := by
    intro h
    apply hΔ0
    ext m
    have := congrArg (fun s : LaurentSeries ℂ => s.coeff ((q ^ 2 : ℕ) * m)) h
    simpa only [qExpand_coeff_mul, HahnSeries.coeff_zero] using this
  have hjC : coeffMap ι (jqModC (AlgebraicClosure ℚ)) = jqModC ℂ := by
    ext m
    rw [coeffMap_coeff, ← map_jqModC ι, HahnSeries.map_coeff]
  have hkey : coeffMap ι ((levelAutBar q M' ζ δ x : fieldBar q M') : LaurentSeries (AlgebraicClosure ℚ)) =
      qExpand ℂ (q ^ 2) (jqModC ℂ) := by
    apply mul_right_cancel₀ hqΔ0
    apply mul_left_cancel₀ hC0
    calc HahnSeries.C ((q : ℂ) ^ (12 : ℤ)) * (coeffMap ι ↑(levelAutBar q M' ζ δ x) *
            qExpand ℂ (q ^ 2) (HahnSeries.ofPowerSeries ℤ ℂ (qExpansion 1 ModularForm.discriminant)))
          = coeffMap ι ↑(levelAutBar q M' ζ δ x) * (HahnSeries.C ((q : ℂ) ^ (12 : ℤ)) *
            qExpand ℂ (q ^ 2) (HahnSeries.ofPowerSeries ℤ ℂ (qExpansion 1 ModularForm.discriminant))) := by
            ring
      _ = _ := hc
      _ = _ := by ring

  apply coeffMap_injective ι hιinj
  rw [hkey, coeffMap_qExpand, hjC]

end S_ModularCurve_FullLevel_coe_levelAutBar_apply_eq_qExpand_sq_jqModC_of_dvd
end P2MW
export P2MW.S_ModularCurve_FullLevel_coe_levelAutBar_apply_eq_qExpand_sq_jqModC_of_dvd (solution)
