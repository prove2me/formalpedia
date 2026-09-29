-- Prove2me | solution 1 for ModularCurve.FullLevel.exists_injective_linearMap_tateModule_jac_comp_tateGal_eq_and_comp_tateGL2_eq_of_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.339302+00:00
-- url     : https://prove2.me/submissions/4ee30c69-310b-5386-91ab-7d9d1d6ca944

import Mathlib
import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_AlgebraicCurve_Correspondence
import Theorems.Thm_ModularCurve_FullLevel_coe_levelAutBar_apply_eq_coe_levelAutBar_apply_of_dvd_of_coe_eq
import Theorems.Thm_ModularCurve_surjective_specialLinearGroup_map_zmod
import Theorems.Thm_ModularCurve_hasPrincipalDivisors_xHFunctionFieldBar
import Theorems.Thm_ModularCurve_JOneES_exists_transcendental_finiteDimensional_laurentBaseChange
import Theorems.Thm_AlgebraicCurve_finiteDimensional_adjoin_of_transcendental
import Theorems.Thm_AlgebraicCurve_separableAlong_of_charZero
import Theorems.Thm_AlgebraicCurve_fundamentalIdentityAlong
import Theorems.Thm_AlgebraicCurve_normFormulaAlong
import Theorems.Thm_AlgebraicCurve_sumRamificationInertia_of_fundamentalIdentity
import Theorems.Thm_AlgebraicCurve_Place_deg_ne_zero_of_finiteDimensional_adjoin
import Theorems.Thm_AlgebraicCurve_Pic0_pushforwardHom_pullbackHom
import Theorems.Thm_AlgebraicCurve_SemilinearAut_pullbackAlong_smul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_exists_injective_linearMap_tateModule_jac_comp_tateGal_eq_and_comp_tateGL2_eq_of_dvd
p2m_attr_erase "instance" "AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint"
p2m_attr_erase "simp" "AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one"

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open scoped MatrixGroups
open Matrix ModularCurve ModularCurve.FullLevel CongruenceSubgroup AlgebraicCurve IntermediateField

namespace R1aDegeneracy

section Reduction

variable {q : ℕ} [Fact q.Prime]

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

theorem exists_mem_Gamma0_SLq_eq {M : ℕ} (hqM : ¬ q ∣ M) (g : SL(2, ZMod q)) :
    ∃ γ : SL(2, ℤ), γ ∈ Gamma0 M ∧ SLq q γ = g := by
  haveI : NeZero M := ⟨by rintro rfl; exact hqM (dvd_zero q)⟩
  obtain ⟨g₀, hg₀⟩ := ModularCurve.surjective_specialLinearGroup_map_zmod q g
  obtain ⟨g₁, hg₁q, hg₁M⟩ :=
    exists_crt ((Nat.Prime.coprime_iff_not_dvd (Fact.out : q.Prime)).mpr hqM) g₀
  refine ⟨g₁, ?_, ?_⟩
  · rw [SLq_eq_one_iff, Gamma_mem] at hg₁M
    rw [Gamma0_mem]
    exact hg₁M.2.2.1
  · rw [hg₁q]
    exact hg₀

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
  change ((slPart g : SL(2, ZMod q)) : Matrix (Fin 2) (Fin 2) (ZMod q)) *
      !![1, 0; 0, ((detU g : (ZMod q)ˣ) : ZMod q)] = (g : Matrix (Fin 2) (Fin 2) (ZMod q))
  rw [coe_slPart, Matrix.mul_assoc, diag_inv_mul_diag, Matrix.mul_one]

theorem exists_mem_Gamma0_eq_redQ_mul_diagOneElem {M : ℕ} (hqM : ¬ q ∣ M) (g : CuspidalType.GL2 q) :
    ∃ γ : SL(2, ℤ), γ ∈ Gamma0 M ∧ g = redQ q γ * diagOneElem q (detU g) := by
  obtain ⟨γ, hγ, hγred⟩ := exists_mem_Gamma0_SLq_eq hqM (slPart g)
  exact ⟨γ, hγ, by rw [redQ_eq, hγred, toGL_slPart_mul]⟩

end Reduction

section Levels

variable (q : ℕ) [Fact q.Prime]

theorem mem_gammaH_levelH_iff (M : ℕ) (A : SL(2, ℤ)) :
    A ∈ CohCarrier.GammaH (q ^ 2 * M) (levelH q M) ↔
      A ∈ Gamma0 (q ^ 2 * M) ∧ ((A 1 1 : ℤ) : ZMod q) = 1 := by
  rw [CohCarrier.mem_GammaH_iff]
  constructor
  · rintro ⟨hA, hH⟩
    refine ⟨hA, ?_⟩
    rw [mem_levelH_iff] at hH
    have h := congrArg (fun u : (ZMod q)ˣ => (u : ZMod q)) hH
    simpa [ZMod.unitsMap_def, Units.coe_map, CohCarrier.gamma0Units, Gamma0Map] using h
  · rintro ⟨hA, h1⟩
    refine ⟨hA, ?_⟩
    rw [mem_levelH_iff]
    ext
    simpa [ZMod.unitsMap_def, Units.coe_map, CohCarrier.gamma0Units, Gamma0Map] using h1

omit [Fact q.Prime] in
theorem gamma0_le_of_dvd {N N' : ℕ} (h : N ∣ N') : Gamma0 N' ≤ Gamma0 N := by
  intro A hA
  rw [Gamma0_mem] at hA ⊢
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at hA ⊢
  exact (Int.natCast_dvd_natCast.mpr h).trans hA

variable {M' M'' : ℕ} (hM : M' ∣ M'')
include hM

theorem gammaH_le :
    CohCarrier.GammaH (q ^ 2 * M'') (levelH q M'') ≤ CohCarrier.GammaH (q ^ 2 * M') (levelH q M') := by
  intro A hA
  rw [mem_gammaH_levelH_iff] at hA ⊢
  exact ⟨gamma0_le_of_dvd (mul_dvd_mul_left (q ^ 2) hM) hA.1, hA.2⟩

theorem xHFunctionField_le :
    xHFunctionField (q ^ 2 * M') (levelH q M') ≤ xHFunctionField (q ^ 2 * M'') (levelH q M'') :=
  qExpFunctionFieldC_mono ℚ (gammaH_le q hM)

theorem fieldBar_le : fieldBar q M' ≤ fieldBar q M'' := by
  show laurentBaseChange (AlgebraicClosure ℚ) _ ≤ laurentBaseChange (AlgebraicClosure ℚ) _
  rw [laurentBaseChange, IntermediateField.adjoin_le_iff]
  rintro _ ⟨y, hy, rfl⟩
  exact coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (xHFunctionField_le q hM hy)

def incl : fieldBar q M' →ₐ[AlgebraicClosure ℚ] fieldBar q M'' :=
  IntermediateField.inclusion (fieldBar_le q hM)

@[scoped simp] theorem coe_incl (u : fieldBar q M') :
    ((incl q hM u : fieldBar q M'') : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)) :=
  IntermediateField.coe_inclusion _ u

end Levels

section Along

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']

theorem transcendental_map (φ : F →ₐ[K] F') {x : F} (hx : Transcendental K x) :
    Transcendental K (φ x) := by
  rintro ⟨p, hp0, hp⟩
  refine hx ⟨p, hp0, ?_⟩
  rw [Polynomial.aeval_algHom_apply] at hp
  exact (map_eq_zero_iff φ (RingHom.injective (φ : F →+* F'))).mp hp

theorem finiteAlong_of_finiteDimensional_adjoin (φ : F →ₐ[K] F') (x : F)
    [h : FiniteDimensional (IntermediateField.adjoin K ({φ x} : Set F')) F'] : FiniteAlong K φ := by
  letI := algebraAlong φ
  show Module.Finite F F'
  set E := IntermediateField.adjoin K ({φ x} : Set F')
  have hE : E ≤ φ.fieldRange := by
    rw [IntermediateField.adjoin_le_iff, Set.singleton_subset_iff]
    exact ⟨x, rfl⟩
  obtain ⟨s, hs⟩ := Module.finite_def.mp h
  refine Module.finite_def.mpr ⟨s, ?_⟩
  rw [eq_top_iff]
  rintro y -
  have hy : y ∈ Submodule.span E (s : Set F') := by rw [hs]; trivial
  induction hy using Submodule.span_induction with
  | mem z hz => exact Submodule.subset_span hz
  | zero => exact zero_mem _
  | add a b _ _ ha hb => exact add_mem ha hb
  | smul c a _ ha =>
      obtain ⟨b, hb⟩ := AlgHom.mem_fieldRange.mp (hE c.2)
      have : (c • a : F') = b • a := by
        show (c : F') * a = φ.toRingHom b * a
        rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, hb]
      rw [this]
      exact Submodule.smul_mem _ b ha

theorem isIntegral_of_finiteAlong (φ : F →ₐ[K] F') (h : FiniteAlong K φ) : φ.toRingHom.IsIntegral := by
  letI := algebraAlong φ
  haveI : Module.Finite F F' := h
  intro y
  exact Algebra.IsIntegral.isIntegral (R := F) y

theorem finiteAlong_of_exists
    (hT : ∃ x : F', Transcendental K x ∧ FiniteDimensional (IntermediateField.adjoin K ({x} : Set F')) F')
    (hB : ∃ x : F, Transcendental K x) (φ : F →ₐ[K] F') : FiniteAlong K φ := by
  obtain ⟨xT, hxT, hfdT⟩ := hT
  obtain ⟨xB, hxB⟩ := hB
  haveI := hfdT
  have htr : Transcendental K (φ xB) := transcendental_map φ hxB
  haveI := AlgebraicCurve.finiteDimensional_adjoin_of_transcendental xT htr
  exact finiteAlong_of_finiteDimensional_adjoin φ xB

theorem exists_pullback_package [CharZero F] [HasPrincipalDivisors K F']
    (hT : ∃ x : F', Transcendental K x ∧ FiniteDimensional (IntermediateField.adjoin K ({x} : Set F')) F')
    (hB : ∃ x : F, Transcendental K x ∧ FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    (φ : F →ₐ[K] F') :
    ∃ (δ₀ : Pic0 K F →+ Pic0 K F') (N₀ : Pic0 K F' →+ Pic0 K F) (d : ℕ), 0 < d ∧
      (∀ x, N₀ (δ₀ x) = (d : ℤ) • x) ∧
      (∀ (g : SemilinearAut K F) (g' : SemilinearAut K F'),
        SemilinearAut.IntertwinesAlong φ.toRingHom g g' → ∀ x, δ₀ (g • x) = g' • δ₀ x) := by
  have hfin : FiniteAlong K φ := finiteAlong_of_exists hT (hB.imp fun _ h => h.1) φ
  have hφ : φ.toRingHom.IsIntegral := isIntegral_of_finiteAlong φ hfin
  have hsep : SeparableAlong K φ := AlgebraicCurve.separableAlong_of_charZero φ hφ
  have hFI : FundamentalIdentityAlong K φ hφ := AlgebraicCurve.fundamentalIdentityAlong φ hφ hfin hsep
  have hN : NormFormulaAlong K φ hfin := AlgebraicCurve.normFormulaAlong φ hfin hsep
  letI := algebraAlong φ
  haveI := isScalarTower_along φ
  haveI := isIntegral_along φ hφ
  haveI : Module.Finite F F' := hfin
  haveI : FundamentalIdentity K F F' := hFI
  have hN' : Divisor.PushforwardNormFormula K F F' := hN
  have hdeg : ∀ v : Place K F, v.deg ≠ 0 := by
    obtain ⟨x, hx, hfd⟩ := hB
    haveI := hfd
    exact AlgebraicCurve.Place.deg_ne_zero_of_finiteDimensional_adjoin x hx
  haveI : SumRamificationInertia K F F' := AlgebraicCurve.sumRamificationInertia_of_fundamentalIdentity hdeg
  refine ⟨Pic0.pullbackHom F', Pic0.pushforwardHom K F F' hN', Module.finrank F F', Module.finrank_pos,
    fun x => AlgebraicCurve.Pic0.pushforwardHom_pullbackHom hN' x, ?_⟩
  intro g g' hgg' x
  obtain ⟨D, rfl⟩ := Pic0.mk_surjective x
  rw [SemilinearAut.pic0_smul_mk, Pic0.pullbackHom_mk, Pic0.pullbackHom_mk, SemilinearAut.pic0_smul_mk]
  refine congrArg Pic0.mk (Subtype.ext ?_)
  simp only [Pic0.coe_pullbackDegZeroHom, SemilinearAut.coe_degZeroSMulHom]
  exact AlgebraicCurve.SemilinearAut.pullbackAlong_smul φ hφ hgg' (D : Divisor K F)

end Along

section Component

variable (q : ℕ) [Fact q.Prime] {M' M'' : ℕ} [NeZero M'] [NeZero M''] (hM : M' ∣ M'')

local notation "Qb" => AlgebraicClosure ℚ
local notation "Gal" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

scoped instance gammaH_finiteIndex (M : ℕ) [NeZero M] : (CohCarrier.GammaH (q ^ 2 * M) (levelH q M)).FiniteIndex :=
  Subgroup.finiteIndex_of_le (Gamma1_le_GammaH _ _)

theorem exists_transcendental (M : ℕ) [NeZero M] :
    ∃ x : fieldBar q M, Transcendental Qb x ∧
      FiniteDimensional (IntermediateField.adjoin Qb ({x} : Set (fieldBar q M))) (fieldBar q M) :=
  ModularCurve.JOneES.exists_transcendental_finiteDimensional_laurentBaseChange Qb
    (CohCarrier.GammaH (q ^ 2 * M) (levelH q M)) (translation_mem_GammaH _ _)

theorem charZero_fieldBar (M : ℕ) : CharZero (fieldBar q M) :=
  charZero_of_injective_algebraMap (algebraMap Qb (fieldBar q M)).injective

include hM in

theorem exists_component_package :
    ∃ (δ₀ : jacComp q M' →+ jacComp q M'') (N₀ : jacComp q M'' →+ jacComp q M') (d : ℕ), 0 < d ∧
      (∀ x, N₀ (δ₀ x) = (d : ℤ) • x) ∧
      (∀ (σ : Gal) (x : jacComp q M'), δ₀ (σ • x) = σ • δ₀ x) ∧
      (∀ (τ' : fieldBar q M' ≃ₐ[Qb] fieldBar q M') (τ'' : fieldBar q M'' ≃ₐ[Qb] fieldBar q M''),
        (∀ u : fieldBar q M', ((τ'' (incl q hM u) : fieldBar q M'') : LaurentSeries Qb) =
            ((τ' u : fieldBar q M') : LaurentSeries Qb)) →
        ∀ x : jacComp q M', δ₀ (SemilinearAut.ofAlgAut τ' • x) = SemilinearAut.ofAlgAut τ'' • δ₀ x) := by
  haveI := charZero_fieldBar q M'
  haveI : HasPrincipalDivisors Qb (fieldBar q M'') :=
    ModularCurve.hasPrincipalDivisors_xHFunctionFieldBar (q ^ 2 * M'') (levelH q M'')
  obtain ⟨δ₀, N₀, d, hd, hNδ, hequiv⟩ :=
    exists_pullback_package (K := Qb) (exists_transcendental q M'') (exists_transcendental q M') (incl q hM)
  refine ⟨δ₀, N₀, d, hd, hNδ, ?_, ?_⟩
  · intro σ x
    rw [galois_smul_pic0_def, galois_smul_pic0_def]
    refine hequiv _ _ ?_ x
    intro u
    apply Subtype.ext
    show ((arithmeticGalois _ σ • incl q hM u : fieldBar q M'') : LaurentSeries Qb) =
      ((incl q hM (arithmeticGalois _ σ • u) : fieldBar q M'') : LaurentSeries Qb)
    rw [coe_arithmeticGalois_smul, coe_incl, coe_incl, coe_arithmeticGalois_smul]
  · intro τ' τ'' hτ x
    refine hequiv _ _ ?_ x
    intro u
    show SemilinearAut.ofAlgAut τ'' • (incl q hM u) = incl q hM (SemilinearAut.ofAlgAut τ' • u)
    rw [SemilinearAut.ofAlgAut_smul, SemilinearAut.ofAlgAut_smul]
    apply Subtype.ext
    exact (hτ u).trans (coe_incl q hM (τ' u)).symm

end Component

section JacLevel

variable (q : ℕ) [Fact q.Prime] {M' M'' : ℕ} [NeZero M'] [NeZero M''] (hM : M' ∣ M'') (hqM'' : ¬ q ∣ M'')
  (hLA : LevelAutInputs q M') (hGL : GL2Laws q M') (hLA'' : LevelAutInputs q M'') (hGL'' : GL2Laws q M'')

local notation "Qb" => AlgebraicClosure ℚ
local notation "Gal" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

def jacMap {M₁ M₂ : ℕ} (f : jacComp q M₁ →+ jacComp q M₂) : Jac q M₁ →+ Jac q M₂ where
  toFun x := Jac.mk fun ζ => f (x.eval ζ)
  map_zero' := Jac.ext fun ζ => by simp only [Jac.eval_mk, Jac.eval_zero, map_zero]
  map_add' x y := Jac.ext fun ζ => by simp only [Jac.eval_mk, Jac.eval_add, map_add]

@[scoped simp] theorem jacMap_eval {M₁ M₂ : ℕ} (f : jacComp q M₁ →+ jacComp q M₂) (x : Jac q M₁) (ζ : Idx q) :
    (jacMap q f x).eval ζ = f (x.eval ζ) := rfl

include hM hqM'' hLA hGL hLA'' hGL'' in

theorem exists_jac_package :
    ∃ (δJ : Jac q M' →+ Jac q M'') (NJ : Jac q M'' →+ Jac q M') (d : ℕ), 0 < d ∧
      (∀ x, NJ (δJ x) = (d : ℤ) • x) ∧
      (∀ (σ : Gal) (x : Jac q M'), δJ (galJac q M' σ x) = galJac q M'' σ (δJ x)) ∧
      (∀ (g : CuspidalType.GL2 q) (x : Jac q M'), δJ (gl2Jac q M' g x) = gl2Jac q M'' g (δJ x)) := by
  obtain ⟨δ₀, N₀, d, hd, hNδ, hgal, hlev⟩ := exists_component_package q hM
  have hqM' : ¬ q ∣ M' := fun h => hqM'' (h.trans hM)
  refine ⟨jacMap q δ₀, jacMap q N₀, d, hd, ?_, ?_, ?_⟩
  · intro x
    exact Jac.ext fun ζ => by rw [jacMap_eval, jacMap_eval, hNδ, Jac.eval_zsmul]
  · intro σ x
    exact Jac.ext fun ζ => by rw [jacMap_eval, galJac_eval, galJac_eval, jacMap_eval, hgal]
  ·
    have hsl : ∀ (γ : SL(2, ℤ)), γ ∈ Gamma0 M'' → ∀ x : Jac q M',
        jacMap q δ₀ (slJac q M' γ x) = slJac q M'' γ (jacMap q δ₀ x) := by
      intro γ hγ x
      refine Jac.ext fun ζ => ?_
      rw [jacMap_eval, slJac_eval, slJac_eval, jacMap_eval, levelOp_apply, levelOp_apply]
      refine hlev _ _ ?_ _
      intro u
      exact ModularCurve.FullLevel.coe_levelAutBar_apply_eq_coe_levelAutBar_apply_of_dvd_of_coe_eq q M' M'' hM
        hqM'' hLA hLA'' ζ γ⁻¹ (inv_mem hγ) u (incl q hM u) (coe_incl q hM u)
    have hdiag : ∀ (dd : (ZMod q)ˣ) (x : Jac q M'),
        jacMap q δ₀ (diagJac q M' dd x) = diagJac q M'' dd (jacMap q δ₀ x) := by
      intro dd x
      exact Jac.ext fun ζ => by rw [jacMap_eval, diagJac_eval, diagJac_eval, jacMap_eval]
    intro g x
    obtain ⟨γ, hγ, hg⟩ := exists_mem_Gamma0_eq_redQ_mul_diagOneElem (q := q) hqM'' g
    have hγ' : γ ∈ Gamma0 M' := gamma0_le_of_dvd hM hγ
    rw [hg, map_mul, map_mul, gl2Jac_redQ hGL γ hγ', gl2Jac_redQ hGL'' γ hγ, gl2Jac_diagOneElem hGL,
      gl2Jac_diagOneElem hGL'']
    show jacMap q δ₀ (slJac q M' γ (diagJac q M' (detU g) x)) =
      slJac q M'' γ (diagJac q M'' (detU g) (jacMap q δ₀ x))
    rw [hsl γ hγ, hdiag]

end JacLevel

section Tate

variable (lam : ℕ) [Fact lam.Prime] {A B : Type} [AddCommGroup A] [AddCommGroup B]

def tmap (f : A →+ B) : TateModule lam A →ₗ[ℤ_[lam]] TateModule lam B where
  toFun x := ⟨fun n => f ((x : ℕ → A) n), fun n =>
    ⟨by rw [← map_zsmul, TateModule.torsion, map_zero],
     by rw [← map_zsmul, TateModule.compat]⟩⟩
  map_add' x y := Subtype.ext (funext fun n => by
    show f (((x + y : TateModule lam A) : ℕ → A) n) = f ((x : ℕ → A) n) + f ((y : ℕ → A) n)
    rw [AddSubgroup.coe_add, Pi.add_apply, map_add])
  map_smul' a x := Subtype.ext (funext fun n => by
    show f (((a • x : TateModule lam A) : ℕ → A) n) = ((a.appr n : ℕ) : ℤ) • f ((x : ℕ → A) n)
    rw [TateModule.smul_apply, map_zsmul])

@[scoped simp] theorem tmap_apply_coe (f : A →+ B) (x : TateModule lam A) (n : ℕ) :
    ((tmap lam f x : TateModule lam B) : ℕ → B) n = f ((x : ℕ → A) n) := rfl

theorem eq_zero_of_smul_eq_zero {d : ℕ} (hd : 0 < d) (x : TateModule lam A)
    (hx : ∀ n, (d : ℤ) • (x : ℕ → A) n = 0) : x = 0 := by
  have hp : Nat.Prime lam := Fact.out

  obtain ⟨a, u, hu, hdu⟩ := Nat.exists_eq_pow_mul_and_not_dvd hd.ne' lam hp.ne_one
  refine Subtype.ext (funext fun n => ?_)
  show (x : ℕ → A) n = 0

  have h1 : (u : ℤ) • (x : ℕ → A) n = 0 := by
    have := hx (n + a)
    rw [hdu, Nat.cast_mul, mul_comm, mul_smul, Nat.cast_pow] at this
    rwa [← Nat.cast_pow, TateModule.compat_pow] at this

  have h2 : ((lam ^ n : ℕ) : ℤ) • (x : ℕ → A) n = 0 := TateModule.torsion x n

  have hcop : Nat.Coprime u (lam ^ n) :=
    (Nat.Coprime.pow_right n ((Nat.Prime.coprime_iff_not_dvd hp).mpr hu).symm)
  obtain ⟨s, t, hst⟩ : IsCoprime (u : ℤ) ((lam ^ n : ℕ) : ℤ) := Nat.isCoprime_iff_coprime.mpr hcop
  calc (x : ℕ → A) n = (1 : ℤ) • (x : ℕ → A) n := (one_smul ℤ _).symm
    _ = (s * u + t * (lam ^ n : ℕ)) • (x : ℕ → A) n := by rw [hst]
    _ = 0 := by rw [add_smul, mul_smul, mul_smul, h1, h2, smul_zero, smul_zero, add_zero]

theorem tmap_comp_rep_apply {G : Type} [Monoid G] [DistribMulAction G A] {G' : Type} [Monoid G']
    [DistribMulAction G' B] (f : A →+ B) (g : G) (g' : G') (h : ∀ a : A, f (g • a) = g' • f a)
    (x : TateModule lam A) :
    tmap lam f (TateModule.rep lam A G g x) = TateModule.rep lam B G' g' (tmap lam f x) :=
  Subtype.ext (funext fun n => by
    show f (g • (x : ℕ → A) n) = g' • f ((x : ℕ → A) n)
    exact h _)

end Tate

section Assembly

variable (q : ℕ) [Fact q.Prime] {M' M'' : ℕ} [NeZero M'] [NeZero M''] (hM : M' ∣ M'') (hqM'' : ¬ q ∣ M'')
  (hLA : LevelAutInputs q M') (hGL : GL2Laws q M') (hLA'' : LevelAutInputs q M'') (hGL'' : GL2Laws q M'')
  (lam : ℕ) [Fact lam.Prime]

include hM hqM'' hLA hGL hLA'' hGL'' in
theorem main :
    ∃ δ : TateModule lam (Jac q M') →ₗ[ℤ_[lam]] TateModule lam (Jac q M''),
      Function.Injective δ ∧
      (∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
        δ ∘ₗ tateGal q M' lam σ = tateGal q M'' lam σ ∘ₗ δ) ∧
      (∀ g : CuspidalType.GL2 q, δ ∘ₗ tateGL2 q M' lam g = tateGL2 q M'' lam g ∘ₗ δ) := by
  obtain ⟨δJ, NJ, d, hd, hNδ, hgal, hgl⟩ := exists_jac_package q hM hqM'' hLA hGL hLA'' hGL''
  refine ⟨tmap lam δJ, ?_, ?_, ?_⟩
  · intro x y hxy
    rw [← sub_eq_zero] at hxy ⊢
    rw [← map_sub] at hxy
    refine eq_zero_of_smul_eq_zero lam hd (x - y) fun n => ?_
    have h := congrArg (fun z : TateModule lam (Jac q M'') => NJ ((z : ℕ → Jac q M'') n)) hxy
    simp only [tmap_apply_coe, hNδ] at h
    rw [h]
    show NJ (((0 : TateModule lam (Jac q M'')) : ℕ → Jac q M'') n) = 0
    rw [AddSubgroup.coe_zero, Pi.zero_apply, map_zero]
  · intro σ
    refine LinearMap.ext fun x => ?_
    rw [LinearMap.comp_apply, LinearMap.comp_apply]
    exact tmap_comp_rep_apply lam δJ (galJac q M' σ) (galJac q M'' σ) (fun a => hgal σ a) x
  · intro g
    refine LinearMap.ext fun x => ?_
    rw [LinearMap.comp_apply, LinearMap.comp_apply]
    exact tmap_comp_rep_apply lam δJ (gl2Jac q M' g) (gl2Jac q M'' g) (fun a => hgl g a) x

end Assembly

end R1aDegeneracy
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_exists_injective_linearMap_tateModule_jac_comp_tateGal_eq_and_comp_tateGL2_eq_of_dvd.R1aDegeneracy"

end
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_exists_injective_linearMap_tateModule_jac_comp_tateGal_eq_and_comp_tateGL2_eq_of_dvd.R1aDegeneracy"

theorem solution
    (q : ℕ) [Fact q.Prime] (M' M'' : ℕ) [NeZero M'] [NeZero M''] (hM : M' ∣ M'') (hqM'' : ¬ q ∣ M'')
    (hLA : ModularCurve.FullLevel.LevelAutInputs q M') (hGL : ModularCurve.FullLevel.GL2Laws q M')
    (hLA'' : ModularCurve.FullLevel.LevelAutInputs q M'') (hGL'' : ModularCurve.FullLevel.GL2Laws q M'')
    (lam : ℕ) [Fact lam.Prime] :
    ∃ δ : TateModule lam (ModularCurve.FullLevel.Jac q M') →ₗ[ℤ_[lam]]
        TateModule lam (ModularCurve.FullLevel.Jac q M''),
      Function.Injective δ ∧
      (∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
        δ ∘ₗ ModularCurve.FullLevel.tateGal q M' lam σ = ModularCurve.FullLevel.tateGal q M'' lam σ ∘ₗ δ) ∧
      (∀ g : CuspidalType.GL2 q,
        δ ∘ₗ ModularCurve.FullLevel.tateGL2 q M' lam g = ModularCurve.FullLevel.tateGL2 q M'' lam g ∘ₗ δ) :=
  R1aDegeneracy.main q hM hqM'' hLA hGL hLA'' hGL'' lam

end S_ModularCurve_FullLevel_exists_injective_linearMap_tateModule_jac_comp_tateGal_eq_and_comp_tateGL2_eq_of_dvd
end P2MW
export P2MW.S_ModularCurve_FullLevel_exists_injective_linearMap_tateModule_jac_comp_tateGal_eq_and_comp_tateGL2_eq_of_dvd (solution)
