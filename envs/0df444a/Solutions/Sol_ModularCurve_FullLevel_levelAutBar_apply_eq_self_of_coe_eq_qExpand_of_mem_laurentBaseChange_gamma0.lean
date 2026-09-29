-- Prove2me | solution 1 for ModularCurve.FullLevel.levelAutBar_apply_eq_self_of_coe_eq_qExpand_of_mem_laurentBaseChange_gamma0
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/f357402d-3c52-5a1f-b454-a641abd2d561

import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_ModularForm_HeckeOperator
import Theorems.Thm_ModularCurve_FullLevel_levelAutInputs_of_not_dvd
import Theorems.Thm_ModularForm_exists_degeneracy_Gamma0
import Theorems.Thm_ModularFormClass_qCoeff_comp_heckeDiagMatrix_smul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_levelAutBar_apply_eq_self_of_coe_eq_qExpand_of_mem_laurentBaseChange_gamma0

set_option autoImplicit false

p2m_open "ModularCurve P2MW.S_ModularCurve_FullLevel_levelAutBar_apply_eq_self_of_coe_eq_qExpand_of_mem_laurentBaseChange_gamma0.ModularCurve ModularCurve.FullLevel P2MW.S_ModularCurve_FullLevel_levelAutBar_apply_eq_self_of_coe_eq_qExpand_of_mem_laurentBaseChange_gamma0.ModularCurve.FullLevel CongruenceSubgroup UpperHalfPlane"
open scoped MatrixGroups ModularForm

noncomputable section

namespace ModularCurve
p2m_export "ModularCurve" "restrictForm coe_restrictForm IsIntegralQExp intSeriesC qExpFunctionFieldC div_mem_qExpFunctionFieldC qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd qExpand_single qExpand_injective algebraMap_apply_eq_single ofPowerSeries_coeff_of_neg coeffMap coeffMap_coeff coeffMap_single coeffMap_coeffMap coeffMap_congr algebraMap_laurentSeries_eq_single coeffEmb coeffMap_coeffEmb laurentBaseChange coeffEmb_mem_laurentBaseChange FullLevel.levelAutInputs_of_not_dvd"
namespace FullLevel
p2m_export "ModularCurve.FullLevel" "levelH fieldBar Idx conjElem IsLevelAutBar levelAutBar isLevelAutBar_levelAutBar levelAutInputs_of_not_dvd"
namespace LevelAutFix
p2m_open "ModularCurve.FullLevel ModularCurve"

private theorem gammaH_le_Gamma0 (N : ℕ) (H : Subgroup (ZMod N)ˣ) : CohCarrier.GammaH N H ≤ Gamma0 N := by
  unfold CohCarrier.GammaH
  exact Subgroup.map_subtype_le _

private theorem gammaH_le_Gamma0_GL (N : ℕ) (H : Subgroup (ZMod N)ˣ) :
    ((CohCarrier.GammaH N H : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) ≤
      ((Gamma0 N : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) :=
  Subgroup.map_mono (gammaH_le_Gamma0 N H)

private theorem exists_degeneracy_gammaH (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] {k : ℤ}
    (F : ModularForm (Gamma0 M' : Subgroup (GL (Fin 2) ℝ)) k) :
    ∃ F' : ModularForm (CohCarrier.GammaH (q ^ 2 * M') (levelH q M') : Subgroup (GL (Fin 2) ℝ)) k,
      (⇑F' : ℍ → ℂ) = fun τ => F (ModularForm.heckeDiagMatrix q • τ) := by
  haveI : NeZero (q ^ 2 * M') := ⟨mul_ne_zero (pow_ne_zero _ (Fact.out : q.Prime).ne_zero) (NeZero.ne M')⟩
  obtain ⟨En, hEn⟩ := ModularForm.exists_degeneracy_Gamma0 (k := k) (M := M') (N := q ^ 2 * M') (d := q)
    ⟨q, by ring⟩ F
  exact ⟨ModularCurve.restrictForm (gammaH_le_Gamma0_GL _ _) En, by rw [ModularCurve.coe_restrictForm, hEn]⟩

private def expandSeries (q : ℕ) (p : PowerSeries ℤ) : PowerSeries ℤ :=
  PowerSeries.mk fun n => if q ∣ n then PowerSeries.coeff (n / q) p else 0

private theorem coeff_expandSeries (q : ℕ) (p : PowerSeries ℤ) (n : ℕ) :
    PowerSeries.coeff n (expandSeries q p) = if q ∣ n then PowerSeries.coeff (n / q) p else 0 := by
  rw [expandSeries, PowerSeries.coeff_mk]

private theorem one_mem_strictPeriods_Gamma0 (N : ℕ) :
    (1 : ℝ) ∈ ((Gamma0 N : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
  rw [CongruenceSubgroup.strictPeriods_Gamma0]; exact AddSubgroup.mem_zmultiples _

private theorem isIntegralQExp_degeneracy (q : ℕ) [Fact q.Prime] (N : ℕ) {k : ℤ}
    (F : ModularForm (Gamma0 N : Subgroup (GL (Fin 2) ℝ)) k) (pF : PowerSeries ℤ) (hF : IsIntegralQExp F pF)
    {F' : ℍ → ℂ} (hF' : F' = fun τ => F (ModularForm.heckeDiagMatrix q • τ)) :
    IsIntegralQExp F' (expandSeries q pF) := by
  rw [IsIntegralQExp] at hF ⊢
  ext n
  have h := ModularFormClass.qCoeff_comp_heckeDiagMatrix_smul F (one_mem_strictPeriods_Gamma0 N)
    (Fact.out : q.Prime).ne_zero n
  simp only [ModularFormClass.qCoeff] at h
  rw [hF', h, PowerSeries.coeff_map, coeff_expandSeries, ← hF]
  split_ifs with hd
  · rw [PowerSeries.coeff_map]
  · rw [map_zero]

private theorem intSeriesC_expandSeries (K : Type*) [Field K] (q : ℕ) [NeZero q] (p : PowerSeries ℤ) :
    intSeriesC K (expandSeries q p) = qExpand K q (intSeriesC K p) := by
  ext m
  simp only [intSeriesC]
  by_cases hm : 0 ≤ m
  · lift m to ℕ using hm
    rw [HahnSeries.ofPowerSeries_apply_coeff, PowerSeries.coeff_map, coeff_expandSeries]
    by_cases hd : q ∣ m
    · obtain ⟨m', rfl⟩ := hd
      rw [if_pos (dvd_mul_right q m'), Nat.mul_div_cancel_left _ (NeZero.pos q), Nat.cast_mul,
        qExpand_coeff_mul, HahnSeries.ofPowerSeries_apply_coeff, PowerSeries.coeff_map]
    · rw [if_neg hd, map_zero, qExpand_coeff_of_not_dvd]
      exact_mod_cast hd
  · have hm' : m < 0 := not_le.mp hm
    rw [ofPowerSeries_coeff_of_neg _ hm']
    by_cases hd : (q : ℤ) ∣ m
    · obtain ⟨m', rfl⟩ := hd
      rw [qExpand_coeff_mul, ofPowerSeries_coeff_of_neg]
      have hn : (0 : ℤ) < q := by exact_mod_cast NeZero.pos q
      nlinarith
    · rw [qExpand_coeff_of_not_dvd _ _ hd]

private theorem coeffMap_qExpand {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (n : ℕ) [NeZero n]
    (x : LaurentSeries R) : coeffMap f (qExpand R n x) = qExpand S n (coeffMap f x) := by
  ext k
  by_cases h : (n : ℤ) ∣ k
  · obtain ⟨m, rfl⟩ := h
    rw [coeffMap_coeff, qExpand_coeff_mul, qExpand_coeff_mul, coeffMap_coeff]
  · rw [coeffMap_coeff, qExpand_coeff_of_not_dvd _ _ h, qExpand_coeff_of_not_dvd _ _ h, map_zero]

private theorem coeffEmb_qExpand (L : Type*) [Field L] [Algebra ℚ L] (n : ℕ) [NeZero n] (x : LaurentSeries ℚ) :
    coeffEmb L (qExpand ℚ n x) = qExpand L n (coeffEmb L x) :=
  coeffMap_qExpand _ _ _

private theorem coeffMap_injective {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (hf : Function.Injective f) : Function.Injective (coeffMap f : LaurentSeries R → LaurentSeries S) := by
  intro x y h
  ext k
  apply hf
  have := congrArg (fun s : LaurentSeries S => s.coeff k) h
  simpa only [coeffMap_coeff] using this

private theorem coeffMap_coeffEmb (ι : AlgebraicClosure ℚ →+* ℂ) (x : LaurentSeries ℚ) :
    coeffMap ι (coeffEmb (AlgebraicClosure ℚ) x) = coeffMap (algebraMap ℚ ℂ) x := by
  rw [coeffEmb, coeffMap_coeffMap]
  exact coeffMap_congr (Subsingleton.elim _ _) x

private theorem coeffMap_intSeriesC {F : ℍ → ℂ} {p : PowerSeries ℤ} (h : IsIntegralQExp F p) :
    coeffMap (algebraMap ℚ ℂ) (intSeriesC ℚ p) = HahnSeries.ofPowerSeries ℤ ℂ (qExpansion 1 F) := by
  rw [← h]
  ext n
  simp only [intSeriesC, coeffMap_coeff, PowerSeries.coeff_coe]
  split_ifs
  · exact map_zero _
  · simp [PowerSeries.coeff_map]

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

private theorem heckeDiagMatrix_mul_conjElem (q : ℕ) [Fact q.Prime] (δ : SL(2, ℤ)) :
    ModularForm.heckeDiagMatrix q * conjElem q δ =
      (Matrix.SpecialLinearGroup.mapGL ℝ δ : GL (Fin 2) ℝ) * ModularForm.heckeDiagMatrix q := by
  have hq0 : q ≠ 0 := (Fact.out : q.Prime).ne_zero
  have hq : (q : ℝ) ≠ 0 := by exact_mod_cast hq0
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, ModularForm.val_heckeDiagMatrix hq0]
  have hc : ((conjElem q δ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
      !![((δ 0 0 : ℤ) : ℝ), ((δ 0 1 : ℤ) : ℝ) / q; (q : ℝ) * ((δ 1 0 : ℤ) : ℝ), ((δ 1 1 : ℤ) : ℝ)] := rfl
  have hm : ((Matrix.SpecialLinearGroup.mapGL ℝ δ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
      (δ : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ℝ) := rfl
  rw [hc, hm]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.map_apply] <;> field_simp

private theorem det_conjElem (q : ℕ) [Fact q.Prime] (γ : SL(2, ℤ)) : ((conjElem q γ).det : ℝ) = 1 := by
  have hq : (q : ℝ) ≠ 0 := by exact_mod_cast (Fact.out : q.Prime).ne_zero
  have hdet : ((γ 0 0 : ℤ) : ℝ) * ((γ 1 1 : ℤ) : ℝ) - ((γ 0 1 : ℤ) : ℝ) * ((γ 1 0 : ℤ) : ℝ) = 1 := by
    have h := Matrix.SpecialLinearGroup.det_coe γ
    rw [Matrix.det_fin_two] at h
    exact_mod_cast h
  have hc : ((conjElem q γ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
      !![((γ 0 0 : ℤ) : ℝ), ((γ 0 1 : ℤ) : ℝ) / q; (q : ℝ) * ((γ 1 0 : ℤ) : ℝ), ((γ 1 1 : ℤ) : ℝ)] := rfl
  rw [Matrix.GeneralLinearGroup.val_det_apply, hc, Matrix.det_fin_two_of]
  field_simp
  linear_combination hdet

private theorem σ_conjElem (q : ℕ) [Fact q.Prime] (γ : SL(2, ℤ)) : UpperHalfPlane.σ (conjElem q γ) = .refl ℝ ℂ := by
  rw [UpperHalfPlane.σ, if_pos (by rw [det_conjElem]; exact one_pos)]

private theorem degeneracy_slash_conjElem (q : ℕ) [Fact q.Prime] (M' : ℕ) {k : ℤ}
    (F : ModularForm (Gamma0 M' : Subgroup (GL (Fin 2) ℝ)) k)
    (δ : SL(2, ℤ)) (hδq : δ ∈ Gamma0 M')
    {F' : ℍ → ℂ} (hF' : F' = fun τ => F (ModularForm.heckeDiagMatrix q • τ)) :
    F' ∣[k] conjElem q δ = F' := by
  have hq0 : q ≠ 0 := (Fact.out : q.Prime).ne_zero
  have hq : (q : ℂ) ≠ 0 := by exact_mod_cast hq0
  have hck : ((q : ℂ) ^ (k - 1)) ≠ 0 := zpow_ne_zero _ hq

  have hFD : F' = ((q : ℂ) ^ (k - 1))⁻¹ • ((⇑F : ℍ → ℂ) ∣[k] ModularForm.heckeDiagMatrix q) := by
    funext τ
    simp only [hF', Pi.smul_apply, smul_eq_mul]
    rw [ModularForm.slash_heckeDiagMatrix_apply k hq0, inv_mul_cancel_left₀ hck]
  have hinv : (⇑F : ℍ → ℂ) ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ δ : GL (Fin 2) ℝ) = ⇑F :=
    SlashInvariantFormClass.slash_action_eq F _ ⟨δ, hδq, rfl⟩
  rw [hFD, ModularForm.smul_slash, σ_conjElem, ContinuousAlgEquiv.refl_apply, ← SlashAction.slash_mul,
    heckeDiagMatrix_mul_conjElem, SlashAction.slash_mul, hinv]

private theorem qExpand_coeffEmb_div_mem_fieldBar
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M']
    {k : ℤ} (F G : ModularForm (Gamma0 M' : Subgroup (GL (Fin 2) ℝ)) k) (pF pG : PowerSeries ℤ)
    (hF : IsIntegralQExp F pF) (hG : IsIntegralQExp G pG) (hG0 : intSeriesC ℚ pG ≠ 0) :
    qExpand (AlgebraicClosure ℚ) q
        (coeffEmb (AlgebraicClosure ℚ) (intSeriesC ℚ pF / intSeriesC ℚ pG)) ∈ fieldBar q M' := by
  obtain ⟨F', hF'⟩ := exists_degeneracy_gammaH q M' F
  obtain ⟨G', hG'⟩ := exists_degeneracy_gammaH q M' G
  have hIF := isIntegralQExp_degeneracy q M' F pF hF hF'
  have hIG := isIntegralQExp_degeneracy q M' G pG hG hG'
  have hG0' : intSeriesC ℚ (expandSeries q pG) ≠ 0 := by
    rw [intSeriesC_expandSeries]
    exact (map_ne_zero_iff _ (qExpand_injective q)).mpr hG0
  have h := coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (div_mem_qExpFunctionFieldC F' G' hIF hIG hG0')
  rw [intSeriesC_expandSeries, intSeriesC_expandSeries, ← map_div₀, coeffEmb_qExpand] at h
  exact h

private theorem levelAutBar_apply_eq_self_of_generator
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M') (ζ : Idx q)
    (δ : SL(2, ℤ)) (hδ : δ ∈ Gamma0 M')
    {k : ℤ} (F G : ModularForm (Gamma0 M' : Subgroup (GL (Fin 2) ℝ)) k) (pF pG : PowerSeries ℤ)
    (hF : IsIntegralQExp F pF) (hG : IsIntegralQExp G pG) (hG0 : intSeriesC ℚ pG ≠ 0)
    (x : fieldBar q M')
    (hx : (x : LaurentSeries (AlgebraicClosure ℚ)) =
      qExpand (AlgebraicClosure ℚ) q (coeffEmb (AlgebraicClosure ℚ) (intSeriesC ℚ pF / intSeriesC ℚ pG))) :
    levelAutBar q M' ζ δ x = x := by
  classical
  have hτ : IsLevelAutBar q M' ζ δ (levelAutBar q M' ζ δ) :=
    isLevelAutBar_levelAutBar (ModularCurve.FullLevel.levelAutInputs_of_not_dvd q M' hqM' ζ δ hδ)
  obtain ⟨ι, hι⟩ := exists_emb ζ
  have hιinj : Function.Injective ι := ι.injective

  obtain ⟨F', hF'⟩ := exists_degeneracy_gammaH q M' F
  obtain ⟨G', hG'⟩ := exists_degeneracy_gammaH q M' G
  have hIF := isIntegralQExp_degeneracy q M' F pF hF hF'
  have hIG := isIntegralQExp_degeneracy q M' G pG hG hG'
  have hG0' : intSeriesC ℚ (expandSeries q pG) ≠ 0 := by
    rw [intSeriesC_expandSeries]
    exact (map_ne_zero_iff _ (qExpand_injective q)).mpr hG0

  have hyx : (⟨coeffEmb (AlgebraicClosure ℚ)
        (intSeriesC ℚ (expandSeries q pF) / intSeriesC ℚ (expandSeries q pG)),
      coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (div_mem_qExpFunctionFieldC F' G' hIF hIG hG0')⟩ :
        fieldBar q M') = x := by
    apply Subtype.ext
    show coeffEmb (AlgebraicClosure ℚ) _ = (x : LaurentSeries (AlgebraicClosure ℚ))
    rw [hx, intSeriesC_expandSeries, intSeriesC_expandSeries, ← map_div₀, coeffEmb_qExpand]

  have hcq := hτ k F' G' (expandSeries q pF) (expandSeries q pG) hIF hIG hG0' ι hι
  rw [hyx] at hcq

  rw [degeneracy_slash_conjElem q M' F δ hδ hF', degeneracy_slash_conjElem q M' G δ hδ hG'] at hcq

  have hxC : coeffMap ι (x : LaurentSeries (AlgebraicClosure ℚ)) *
      HahnSeries.ofPowerSeries ℤ ℂ (qExpansion 1 (⇑G' : ℍ → ℂ)) =
      HahnSeries.ofPowerSeries ℤ ℂ (qExpansion 1 (⇑F' : ℍ → ℂ)) := by
    rw [← hyx]
    show coeffMap ι (coeffEmb (AlgebraicClosure ℚ) _) * _ = _
    rw [coeffMap_coeffEmb, map_div₀, coeffMap_intSeriesC hIF, coeffMap_intSeriesC hIG,
      div_mul_cancel₀]
    rw [← coeffMap_intSeriesC hIG]
    exact (map_ne_zero_iff _ (coeffMap_injective _ (algebraMap ℚ ℂ).injective)).mpr hG0'
  have hGC0 : HahnSeries.ofPowerSeries ℤ ℂ (qExpansion 1 (⇑G' : ℍ → ℂ)) ≠ 0 := by
    rw [← coeffMap_intSeriesC hIG]
    exact (map_ne_zero_iff _ (coeffMap_injective _ (algebraMap ℚ ℂ).injective)).mpr hG0'

  have hkey : coeffMap ι ((levelAutBar q M' ζ δ x : fieldBar q M') : LaurentSeries (AlgebraicClosure ℚ)) =
      coeffMap ι (x : LaurentSeries (AlgebraicClosure ℚ)) :=
    mul_right_cancel₀ hGC0 (hcq.trans hxC.symm)
  exact Subtype.ext (coeffMap_injective ι hιinj hkey)

end ModularCurve.FullLevel.LevelAutFix

end

noncomputable section

namespace ModularCurve
p2m_export "ModularCurve" "restrictForm coe_restrictForm IsIntegralQExp intSeriesC qExpFunctionFieldC div_mem_qExpFunctionFieldC qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd qExpand_single qExpand_injective algebraMap_apply_eq_single ofPowerSeries_coeff_of_neg coeffMap coeffMap_coeff coeffMap_single coeffMap_coeffMap coeffMap_congr algebraMap_laurentSeries_eq_single coeffEmb coeffMap_coeffEmb laurentBaseChange coeffEmb_mem_laurentBaseChange FullLevel.levelAutInputs_of_not_dvd"
p2m_open "ModularCurve"

section closure

variable (L : Type*) [Field L] [Algebra ℚ L] (N : ℕ) [NeZero N]

omit [Algebra ℚ L] in
private theorem qExpand_algebraMap (a : L) :
    qExpand L N (algebraMap L (LaurentSeries L) a) = algebraMap L (LaurentSeries L) a := by
  rw [algebraMap_laurentSeries_eq_single, qExpand_single, mul_zero]

private theorem coeffEmb_algebraMap (r : ℚ) :
    coeffEmb L (algebraMap ℚ (LaurentSeries ℚ) r) = algebraMap L (LaurentSeries L) (algebraMap ℚ L r) := by
  rw [algebraMap_apply_eq_single, coeffEmb, coeffMap_single, algebraMap_laurentSeries_eq_single]

private theorem qExpand_mem_of_mem_laurentBaseChange (Γ : Subgroup SL(2, ℤ))
    (E : IntermediateField L (LaurentSeries L))
    (hgen : ∀ (k : ℤ) (F G : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k) (pF pG : PowerSeries ℤ),
      IsIntegralQExp F pF → IsIntegralQExp G pG → intSeriesC ℚ pG ≠ 0 →
        qExpand L N (coeffEmb L (intSeriesC ℚ pF / intSeriesC ℚ pG)) ∈ E)
    {g : LaurentSeries L} (hg : g ∈ laurentBaseChange L (qExpFunctionFieldC ℚ Γ)) :
    qExpand L N g ∈ E := by

  have inner : ∀ r ∈ qExpFunctionFieldC ℚ Γ, qExpand L N (coeffEmb L r) ∈ E := by
    intro r hr
    induction hr using IntermediateField.adjoin_induction with
    | mem x hx =>
      obtain ⟨k, F, G, pF, pG, hF, hG, hG0, rfl⟩ := hx
      exact hgen k F G pF pG hF hG hG0
    | algebraMap x =>
      rw [coeffEmb_algebraMap, qExpand_algebraMap]
      exact E.algebraMap_mem _
    | add x y _ _ hx hy => rw [map_add, map_add]; exact add_mem hx hy
    | inv x _ hx => rw [map_inv₀, map_inv₀]; exact inv_mem hx
    | mul x y _ _ hx hy => rw [map_mul, map_mul]; exact mul_mem hx hy

  induction hg using IntermediateField.adjoin_induction with
  | mem x hx =>
    obtain ⟨r, hr, rfl⟩ := hx
    exact inner r hr
  | algebraMap x =>
    rw [qExpand_algebraMap]
    exact E.algebraMap_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | inv x _ hx => rw [map_inv₀]; exact inv_mem hx
  | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy

end closure

namespace FullLevel
p2m_export "ModularCurve.FullLevel" "levelH fieldBar Idx conjElem IsLevelAutBar levelAutBar isLevelAutBar_levelAutBar levelAutInputs_of_not_dvd"
p2m_open "ModularCurve.FullLevel"

private def fixedBy {K E : Type*} [Field K] [Field E] [Algebra K E] (τ : E ≃ₐ[K] E) : IntermediateField K E :=
  (AlgHom.equalizer (τ : E →ₐ[K] E) (AlgHom.id K E)).toIntermediateField fun x hx => by
    rw [AlgHom.mem_equalizer] at hx ⊢
    simp only [AlgHom.coe_id, id_eq, map_inv₀] at hx ⊢
    rw [hx]

private theorem mem_fixedBy_iff {K E : Type*} [Field K] [Field E] [Algebra K E] (τ : E ≃ₐ[K] E) (x : E) :
    x ∈ fixedBy τ ↔ τ x = x := by
  show x ∈ AlgHom.equalizer (τ : E →ₐ[K] E) (AlgHom.id K E) ↔ _
  rw [AlgHom.mem_equalizer]
  rfl

private theorem qExpand_coe_mem_fieldBar_of_mem_gamma0
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M']
    (g : LaurentSeries (AlgebraicClosure ℚ))
    (hg : g ∈ laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (Gamma0 M'))) :
    qExpand (AlgebraicClosure ℚ) q g ∈ fieldBar q M' :=
  qExpand_mem_of_mem_laurentBaseChange (AlgebraicClosure ℚ) q (Gamma0 M') (fieldBar q M')
    (fun _ F G pF pG hF hG hG0 => LevelAutFix.qExpand_coeffEmb_div_mem_fieldBar q M' F G pF pG hF hG hG0) hg

private theorem levelAutBar_apply_eq_self_of_coe_eq_qExpand_gamma0
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M') (ζ : Idx q)
    (δ : SL(2, ℤ)) (hδ : δ ∈ CongruenceSubgroup.Gamma0 M')
    (g : LaurentSeries (AlgebraicClosure ℚ))
    (hg : g ∈ laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (Gamma0 M')))
    (x : fieldBar q M') (hx : (x : LaurentSeries (AlgebraicClosure ℚ)) = qExpand (AlgebraicClosure ℚ) q g) :
    levelAutBar q M' ζ δ x = x := by

  set E : IntermediateField (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) :=
    (fixedBy (levelAutBar q M' ζ δ)).map (fieldBar q M').val with hE
  have hgen : ∀ (k : ℤ) (F G : ModularForm (Gamma0 M' : Subgroup (GL (Fin 2) ℝ)) k) (pF pG : PowerSeries ℤ),
      IsIntegralQExp F pF → IsIntegralQExp G pG → intSeriesC ℚ pG ≠ 0 →
        qExpand (AlgebraicClosure ℚ) q
          (coeffEmb (AlgebraicClosure ℚ) (intSeriesC ℚ pF / intSeriesC ℚ pG)) ∈ E := by
    intro k F G pF pG hF hG hG0
    refine (IntermediateField.mem_map _).2
      ⟨⟨_, LevelAutFix.qExpand_coeffEmb_div_mem_fieldBar q M' F G pF pG hF hG hG0⟩, ?_, rfl⟩
    exact (mem_fixedBy_iff _ _).2
      (LevelAutFix.levelAutBar_apply_eq_self_of_generator q M' hqM' ζ δ hδ F G pF pG hF hG hG0 _ rfl)
  have hxE : (x : LaurentSeries (AlgebraicClosure ℚ)) ∈ E :=
    hx ▸ qExpand_mem_of_mem_laurentBaseChange (AlgebraicClosure ℚ) q (Gamma0 M') E hgen hg
  obtain ⟨y, hy, hyx⟩ := (IntermediateField.mem_map _).1 hxE
  have : y = x := Subtype.ext hyx
  subst this
  exact (mem_fixedBy_iff _ _).1 hy

end FullLevel

end ModularCurve

end

theorem solution
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M') (ζ : Idx q)
    (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M')
    (g : LaurentSeries (AlgebraicClosure ℚ))
    (hg : g ∈ laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (Gamma0 M')))
    (x : fieldBar q M') (hx : (x : LaurentSeries (AlgebraicClosure ℚ)) = qExpand (AlgebraicClosure ℚ) q g) :
    levelAutBar q M' ζ γ x = x :=
  ModularCurve.FullLevel.levelAutBar_apply_eq_self_of_coe_eq_qExpand_gamma0 q M' hqM' ζ γ hγ g hg x hx

end S_ModularCurve_FullLevel_levelAutBar_apply_eq_self_of_coe_eq_qExpand_of_mem_laurentBaseChange_gamma0
end P2MW
export P2MW.S_ModularCurve_FullLevel_levelAutBar_apply_eq_self_of_coe_eq_qExpand_of_mem_laurentBaseChange_gamma0 (solution)
