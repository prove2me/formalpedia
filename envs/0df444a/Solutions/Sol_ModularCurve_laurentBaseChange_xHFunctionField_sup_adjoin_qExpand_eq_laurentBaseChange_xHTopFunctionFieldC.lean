-- Prove2me | solution 1 for ModularCurve.laurentBaseChange_xHFunctionField_sup_adjoin_qExpand_eq_laurentBaseChange_xHTopFunctionFieldC
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/b257a90c-5a19-5778-b15c-082337e82cf6

import Mathlib
import Definitions.Def_ModularCurve_X1HeckeOperator
import Definitions.Def_ModularCurve_XH
import Definitions.Def_ModularCurve_X0ModL
import Theorems.Thm_ModularCurve_relrank_adjoin_qExpansion_div_le_relIndex
import Theorems.Thm_ModularCurve_relIndex_gamma0_le_relrank_adjoin_insert_jqNModC
import Theorems.Thm_ModularCurve_qExpansion_div_mem_laurentBaseChange_xHFunctionField
import Theorems.Thm_ModularCurve_relfinrank_laurentBaseChange
import Theorems.Thm_ModularCurve_laurentBaseChange_adjoin
import Theorems.Thm_ModularCurve_JOneES_exists_transcendental_finiteDimensional_qExpFunctionFieldC
import Theorems.Thm_AlgebraicCurve_finiteDimensional_adjoin_of_transcendental
import Theorems.Thm_ModularCurve_modularFunctionFieldFullC_le_qExpFunctionFieldC_gamma0
import Theorems.Thm_ModularCurve_map_jqNModC
import Theorems.Thm_ModularCurve_qExpand_image_intFormRatiosC_subset
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_laurentBaseChange_xHFunctionField_sup_adjoin_qExpand_eq_laurentBaseChange_xHTopFunctionFieldC
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe"
p2m_attr_erase "simp" "ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ"

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open scoped MatrixGroups

namespace Gen0Sol

open ModularCurve CongruenceSubgroup IntermediateField AlgebraicCurve HahnSeries UpperHalfPlane

section Groups

variable (M : ℕ) (H' : Subgroup (ZMod M)ˣ) (q : ℕ)

abbrev Gam : Subgroup SL(2, ℤ) := CohCarrier.GammaH M H'

abbrev Gam' : Subgroup SL(2, ℤ) := CohCarrier.GammaH M H' ⊓ Gamma0 (M * q)

theorem Gam'_le : Gam' M H' q ≤ Gam M H' := inf_le_left

scoped instance [NeZero M] : (Gam M H').FiniteIndex := Subgroup.finiteIndex_of_le (Gamma1_le_GammaH M H')

scoped instance [NeZero M] [NeZero q] : (Gam' M H' q).FiniteIndex := by
  haveI : NeZero (M * q) := NeZero.mul
  refine Subgroup.finiteIndex_of_le (H := Gamma1 (M * q)) (le_inf ?_ (Gamma1_in_Gamma0 _))
  exact (Gamma1_le_of_dvd (dvd_mul_right M q)).trans (Gamma1_le_GammaH M H')

theorem T_mem_Gam' : ModularGroup.T ∈ Gam' M H' q := by
  refine Subgroup.mem_inf.mpr ⟨translation_mem_GammaH M H', ?_⟩
  rw [Gamma0_mem]
  simp [ModularGroup.T]

theorem relIndex_Gam'_ne_zero [NeZero M] [NeZero q] : (Gam' M H' q).relIndex (Gam M H') ≠ 0 := by
  intro h0
  have hdvd := Subgroup.relIndex_dvd_index_of_le (Gam'_le M H' q)
  rw [h0, zero_dvd_iff] at hdvd
  exact Subgroup.FiniteIndex.index_ne_zero hdvd

end Groups

section RatFields

variable (M : ℕ) (H' : Subgroup (ZMod M)ˣ) (q : ℕ)

abbrev FF : IntermediateField ℚ (LaurentSeries ℚ) := qExpFunctionFieldC ℚ (Gam M H')

abbrev FF' : IntermediateField ℚ (LaurentSeries ℚ) := qExpFunctionFieldC ℚ (Gam' M H' q)

theorem FF_le : FF M H' ≤ FF' M H' q := qExpFunctionFieldC_mono ℚ (Gam'_le M H' q)

theorem relfinrank_adjoin_eq_finrank {K E : Type*} [Field K] [Field E] [Algebra K E]
    (B : IntermediateField K E) (x : B) :
    relfinrank (adjoin K ({(x : E)} : Set E)) B = Module.finrank (adjoin K ({x} : Set B)) B := by
  have hc : (adjoin K ({(x : E)} : Set E)).comap B.val = adjoin K ({x} : Set B) := by
    apply le_antisymm
    · intro y hy
      change B.val y ∈ adjoin K ({(x : E)} : Set E) at hy
      have h' : (y : E) ∈ lift (adjoin K ({x} : Set B)) := by
        rw [lift_adjoin_simple]; exact hy
      exact (IntermediateField.mem_lift y).mp h'
    · rw [adjoin_le_iff, Set.singleton_subset_iff, SetLike.mem_coe]
      change B.val x ∈ adjoin K ({(x : E)} : Set E)
      exact mem_adjoin_simple_self K (x : E)
  have h := IntermediateField.finrank_comap B.val (A := adjoin K ({(x : E)} : Set E))
  rw [fieldRange_val] at h
  rw [← h]
  exact congrArg (fun C : IntermediateField K B => Module.finrank C B) hc

theorem relfinrank_adjoin_ne_zero {K E : Type*} [Field K] [Field E] [Algebra K E]
    (B : IntermediateField K E) (x : B) (h : FiniteDimensional (adjoin K ({x} : Set B)) B) :
    relfinrank (adjoin K ({(x : E)} : Set E)) B ≠ 0 := by
  rw [relfinrank_adjoin_eq_finrank]
  exact Module.finrank_pos.ne'

theorem transcendental_of_subsingleton_ratAlgebra {F : Type*} [Field F] {i₁ : Algebra ℚ F}
    (i₂ : Algebra ℚ F) {x : F} (h : @Transcendental ℚ F _ _ i₁ x) : @Transcendental ℚ F _ _ i₂ x := by
  have := Subsingleton.elim i₁ i₂; subst this; exact h

theorem isAlgebraic_of_subsingleton_ratAlgebra {F : Type*} [Field F] {i₁ : Algebra ℚ F}
    (i₂ : Algebra ℚ F) {x : F} (h : @IsAlgebraic ℚ F _ _ i₁ x) : @IsAlgebraic ℚ F _ _ i₂ x := by
  have := Subsingleton.elim i₁ i₂; subst this; exact h

theorem finiteDimensional_adjoin_of_subsingleton_ratAlgebra {F : Type*} [Field F] {i₁ : Algebra ℚ F}
    (i₂ : Algebra ℚ F) {x : F}
    (h : letI := i₁; FiniteDimensional (adjoin ℚ ({x} : Set F)) F) :
    letI := i₂; FiniteDimensional (adjoin ℚ ({x} : Set F)) F := by
  have := Subsingleton.elim i₁ i₂; subst this; exact h

variable [NeZero M] [NeZero q]

theorem exists_good_x :
    ∃ x : LaurentSeries ℚ, x ∈ FF M H' ∧ Transcendental ℚ x ∧
      relfinrank (adjoin ℚ ({x} : Set (LaurentSeries ℚ))) (FF M H') ≠ 0 ∧
      relfinrank (adjoin ℚ ({x} : Set (LaurentSeries ℚ))) (FF' M H' q) ≠ 0 := by
  obtain ⟨x, hxt, hfd⟩ :=
    ModularCurve.JOneES.exists_transcendental_finiteDimensional_qExpFunctionFieldC (Gam M H')
      (translation_mem_GammaH M H')
  obtain ⟨x', hxt', hfd'⟩ :=
    ModularCurve.JOneES.exists_transcendental_finiteDimensional_qExpFunctionFieldC (Gam' M H' q)
      (T_mem_Gam' M H' q)
  let y : FF' M H' q := ⟨(x : LaurentSeries ℚ), FF_le M H' q x.2⟩
  have hxE : Transcendental ℚ (x : LaurentSeries ℚ) := fun h =>
    transcendental_of_subsingleton_ratAlgebra _ hxt
      ((IntermediateField.isAlgebraic_iff (K := ℚ) (S := FF M H') (x := x)).mpr h)
  have hyt : Transcendental ℚ y := fun h =>
    hxE ((IntermediateField.isAlgebraic_iff (K := ℚ) (S := FF' M H' q) (x := y)).mp
      (isAlgebraic_of_subsingleton_ratAlgebra _ h))
  haveI := hfd'
  have hfdy : FiniteDimensional (adjoin ℚ ({y} : Set (FF' M H' q))) (FF' M H' q) :=
    AlgebraicCurve.finiteDimensional_adjoin_of_transcendental x' hyt
  refine ⟨_, x.2, hxE,
    relfinrank_adjoin_ne_zero (FF M H') x (finiteDimensional_adjoin_of_subsingleton_ratAlgebra _ hfd),
    relfinrank_adjoin_ne_zero (FF' M H' q) y
      (finiteDimensional_adjoin_of_subsingleton_ratAlgebra _ hfdy)⟩

theorem relfinrank_laurentBaseChange_eq (L : Type*) [Field L] [Algebra ℚ L]
    {F₀ F₁ : IntermediateField ℚ (LaurentSeries ℚ)} (hle : F₀ ≤ F₁) {x : LaurentSeries ℚ}
    (hxF : x ∈ F₀) (hxt : Transcendental ℚ x)
    (hF : relfinrank (adjoin ℚ ({x} : Set (LaurentSeries ℚ))) F₀ ≠ 0) :
    relfinrank (laurentBaseChange L F₀) (laurentBaseChange L F₁) = relfinrank F₀ F₁ := by
  have h1 := ModularCurve.relfinrank_laurentBaseChange L F₀ x hxF hxt
  have h2 := ModularCurve.relfinrank_laurentBaseChange L F₁ x (hle hxF) hxt
  have hxle : adjoin ℚ ({x} : Set (LaurentSeries ℚ)) ≤ F₀ := by
    rw [adjoin_le_iff, Set.singleton_subset_iff]; exact hxF
  have hmono : laurentBaseChange L F₀ ≤ laurentBaseChange L F₁ := by
    rw [laurentBaseChange, IntermediateField.adjoin_le_iff]
    rintro _ ⟨y, hy, rfl⟩
    exact coeffEmb_mem_laurentBaseChange L (hle hy)
  have hxLle : adjoin L ({coeffEmb L x} : Set (LaurentSeries L)) ≤ laurentBaseChange L F₀ := by
    rw [adjoin_le_iff, Set.singleton_subset_iff]; exact coeffEmb_mem_laurentBaseChange L hxF
  have tQ := relfinrank_mul_relfinrank hxle hle
  have tL := relfinrank_mul_relfinrank hxLle hmono
  rw [h1, h2, ← tQ] at tL
  exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hF) tL

end RatFields

section BaseChange

variable (L : Type*) [Field L] [Algebra ℚ L]

theorem laurentBaseChange_mono' {F₀ F₁ : IntermediateField ℚ (LaurentSeries ℚ)} (h : F₀ ≤ F₁) :
    laurentBaseChange L F₀ ≤ laurentBaseChange L F₁ := by
  rw [laurentBaseChange, IntermediateField.adjoin_le_iff]
  rintro _ ⟨y, hy, rfl⟩
  exact coeffEmb_mem_laurentBaseChange L (h hy)

theorem laurentBaseChange_sup (F₀ F₁ : IntermediateField ℚ (LaurentSeries ℚ)) :
    laurentBaseChange L (F₀ ⊔ F₁) = laurentBaseChange L F₀ ⊔ laurentBaseChange L F₁ := by
  apply le_antisymm
  · have hsup : F₀ ⊔ F₁ = adjoin ℚ ((F₀ : Set (LaurentSeries ℚ)) ∪ (F₁ : Set (LaurentSeries ℚ))) := by
      rw [adjoin_union, adjoin_self, adjoin_self]
    rw [hsup, ModularCurve.laurentBaseChange_adjoin, Set.image_union, adjoin_union]
    rfl
  · exact sup_le (laurentBaseChange_mono' L le_sup_left) (laurentBaseChange_mono' L le_sup_right)

end BaseChange

section ComplexSide

variable (M : ℕ) (H' : Subgroup (ZMod M)ˣ) (q : ℕ)

def anSet (Δ : Subgroup SL(2, ℤ)) : Set (LaurentSeries ℂ) :=
  {x : LaurentSeries ℂ | ∃ (k : ℤ) (f g : ModularForm (Δ : Subgroup (GL (Fin 2) ℝ)) k),
      qExpansion 1 (⇑g) ≠ 0 ∧
        x = ofPowerSeries ℤ ℂ (qExpansion 1 ⇑f) / ofPowerSeries ℤ ℂ (qExpansion 1 ⇑g)}

abbrev An (Δ : Subgroup SL(2, ℤ)) : IntermediateField ℂ (LaurentSeries ℂ) := adjoin ℂ (anSet Δ)

theorem coeffEmb_intSeriesC {F : UpperHalfPlane → ℂ} {p : PowerSeries ℤ} (h : IsIntegralQExp F p) :
    coeffEmb ℂ (intSeriesC ℚ p) = ofPowerSeries ℤ ℂ (qExpansion 1 F) := by
  rw [← h]
  ext n
  simp only [coeffEmb, intSeriesC, coeffMap_coeff, PowerSeries.coeff_coe]
  split_ifs
  · exact map_zero _
  · simp [PowerSeries.coeff_map]

theorem coeffEmb_image_subset (Δ : Subgroup SL(2, ℤ)) :
    coeffEmb ℂ '' intFormRatiosC ℚ Δ ⊆ anSet Δ := by
  rintro _ ⟨x, ⟨k, f, g, pf, pg, hf, hg, hg0, rfl⟩, rfl⟩
  refine ⟨k, f, g, ?_, ?_⟩
  · intro h0
    apply hg0
    have := coeffEmb_intSeriesC hg
    rw [h0, map_zero] at this
    exact (map_eq_zero_iff _ (RingHom.injective _)).mp this
  · rw [map_div₀, coeffEmb_intSeriesC hf, coeffEmb_intSeriesC hg]

theorem laurentBaseChange_le_An (Δ : Subgroup SL(2, ℤ)) :
    laurentBaseChange ℂ (qExpFunctionFieldC ℚ Δ) ≤ An Δ := by
  rw [qExpFunctionFieldC, ModularCurve.laurentBaseChange_adjoin]
  exact adjoin.mono ℂ _ _ (coeffEmb_image_subset Δ)

theorem An_Gam_le [NeZero M] : An (Gam M H') ≤ laurentBaseChange ℂ (FF M H') := by
  rw [adjoin_le_iff]
  rintro _ ⟨k, f, g, hg, rfl⟩
  have hg' : g ≠ 0 := by
    rintro rfl
    exact hg (by rw [ModularForm.coe_zero, qExpansion_zero])
  exact ModularCurve.qExpansion_div_mem_laurentBaseChange_xHFunctionField M H' f g hg'

theorem laurentBaseChange_FF_eq_An [NeZero M] : laurentBaseChange ℂ (FF M H') = An (Gam M H') :=
  le_antisymm (laurentBaseChange_le_An (Gam M H')) (An_Gam_le M H')

theorem relrank_mono_right {K E : Type*} [Field K] [Field E] [Algebra K E]
    {A B C : IntermediateField K E} (hAB : A ≤ B) (hBC : B ≤ C) : relrank A B ≤ relrank A C := by
  rw [← relrank_mul_relrank hAB hBC]
  have h0 : relrank B C ≠ 0 := by
    rw [relrank_eq_rank_of_le hBC]
    exact rank_pos.ne'
  exact Cardinal.le_mul_right h0

variable [NeZero M] [NeZero q]

abbrev KC : IntermediateField ℂ (LaurentSeries ℂ) := laurentBaseChange ℂ (FF M H')
abbrev EC : IntermediateField ℂ (LaurentSeries ℂ) := laurentBaseChange ℂ (FF' M H' q)

theorem KC_le_EC : KC M H' ≤ EC M H' q := laurentBaseChange_mono' ℂ (FF_le M H' q)

theorem relrank_KC_EC_le :
    relrank (KC M H') (EC M H' q) ≤ ((Gam' M H' q).relIndex (Gam M H') : Cardinal) := by
  have hC2 := ModularCurve.relrank_adjoin_qExpansion_div_le_relIndex (Gam M H') (Gam' M H' q)
    (Gam'_le M H' q) (T_mem_Gam' M H' q) (relIndex_Gam'_ne_zero M H' q)
  change relrank (An (Gam M H')) (An (Gam' M H' q)) ≤ _ at hC2
  calc relrank (KC M H') (EC M H' q)
        ≤ relrank (KC M H') (An (Gam' M H' q)) :=
          relrank_mono_right (KC_le_EC M H' q) (laurentBaseChange_le_An (Gam' M H' q))
    _ = relrank (An (Gam M H')) (An (Gam' M H' q)) := by rw [show KC M H' = An (Gam M H') from laurentBaseChange_FF_eq_An M H']
    _ ≤ ((Gam' M H' q).relIndex (Gam M H') : Cardinal) := hC2

theorem mem_Gam_of_entries_eq {A B : SL(2, ℤ)} (hB : B ∈ Gam M H')
    (h10 : ((A 1 0 : ℤ) : ZMod M) = B 1 0) (h11 : ((A 1 1 : ℤ) : ZMod M) = B 1 1) : A ∈ Gam M H' := by
  obtain ⟨hB0, hBH⟩ := CohCarrier.mem_GammaH_iff.mp hB
  have hA0 : A ∈ Gamma0 M := by
    rw [Gamma0_mem] at hB0 ⊢
    rw [h10]; exact hB0
  refine CohCarrier.mem_GammaH_iff.mpr ⟨hA0, ?_⟩
  have heq : CohCarrier.gamma0Units M ⟨A, hA0⟩ = CohCarrier.gamma0Units M ⟨B, hB0⟩ := by
    apply Units.ext
    rw [CohCarrier.val_gamma0Units, CohCarrier.val_gamma0Units]
    show ((A 1 1 : ℤ) : ZMod M) = ((B 1 1 : ℤ) : ZMod M)
    exact h11
  rw [heq]; exact hBH

theorem cocycle' : ∀ γ ∈ Gam' M H' q, ∃ γ₁ ∈ Gam M H',
    γ₁ 0 0 = γ 0 0 ∧ γ₁ 0 1 = (q : ℤ) * γ 0 1 ∧ (q : ℤ) * γ₁ 1 0 = γ 1 0 ∧ γ₁ 1 1 = γ 1 1 := by
  intro γ hγ
  obtain ⟨hγH, hγ0⟩ := Subgroup.mem_inf.mp hγ
  have hdet : (γ 0 0 : ℤ) * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    have := γ.det_coe; rwa [Matrix.det_fin_two] at this
  have hMℓc : ((M * q : ℕ) : ℤ) ∣ γ 1 0 := by
    have := Gamma0_mem.mp hγ0; rwa [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  obtain ⟨c', hc'⟩ := hMℓc
  rw [Nat.cast_mul] at hc'
  have hdet' : Matrix.det !![(γ 0 0 : ℤ), (q : ℤ) * γ 0 1; (M : ℤ) * c', γ 1 1] = 1 := by
    rw [Matrix.det_fin_two_of]; linear_combination hdet + (γ 0 1 : ℤ) * hc'
  refine ⟨⟨_, hdet'⟩, ?_, rfl, rfl, ?_, rfl⟩
  · refine mem_Gam_of_entries_eq M H' hγH ?_ rfl
    show (((M : ℤ) * c' : ℤ) : ZMod M) = ((γ 1 0 : ℤ) : ZMod M)
    have h0 : ((γ 1 0 : ℤ) : ZMod M) = 0 := Gamma0_mem.mp (CohCarrier.GammaH_le_Gamma0 H' hγH)
    rw [h0]; push_cast; rw [ZMod.natCast_self, zero_mul]
  · show (q : ℤ) * ((M : ℤ) * c') = γ 1 0
    linear_combination -hc'

theorem qExpand_mem_FF' (y : LaurentSeries ℚ) (hy : y ∈ FF M H') : qExpand ℚ q y ∈ FF' M H' q := by
  have hsub := ModularCurve.qExpand_image_intFormRatiosC_subset ℚ
    (Γ := Gam M H') (translation_mem_GammaH M H') q (cocycle' M H' q)
  have hy' : y ∈ IntermediateField.adjoin ℚ (intFormRatiosC ℚ (Gam M H')) := hy
  have hmap : (IntermediateField.adjoin ℚ (intFormRatiosC ℚ (Gam M H'))).map (qExpandₐ q)
      ≤ IntermediateField.adjoin ℚ (intFormRatiosC ℚ (Gam' M H' q)) := by
    rw [IntermediateField.adjoin_map]
    exact IntermediateField.adjoin.mono ℚ _ _ hsub
  exact hmap ⟨y, hy', rfl⟩

abbrev GG : IntermediateField ℚ (LaurentSeries ℚ) := adjoin ℚ (qExpand ℚ q '' (FF M H' : Set (LaurentSeries ℚ)))

theorem GG_le_FF' : GG M H' q ≤ FF' M H' q := by
  rw [adjoin_le_iff]
  rintro _ ⟨y, hy, rfl⟩
  exact qExpand_mem_FF' M H' q y hy

theorem jqNModC_mem_GG : jqNModC ℂ (M * q) ∈ laurentBaseChange ℂ (GG M H' q) := by
  haveI : NeZero (M * q) := NeZero.mul
  have hM : jqNModC ℚ M ∈ FF M H' := by
    have hfull : jqNModC ℚ M ∈ modularFunctionFieldFullC ℚ M := jqModCd_mem_full ℚ M dvd_rfl
    have h0 : jqNModC ℚ M ∈ qExpFunctionFieldC ℚ (Gamma0 M) :=
      ModularCurve.modularFunctionFieldFullC_le_qExpFunctionFieldC_gamma0 ℚ M hfull
    exact qExpFunctionFieldC_mono ℚ (CohCarrier.GammaH_le_Gamma0 H' : Gam M H' ≤ Gamma0 M) h0
  have h1 : jqNModC ℚ (M * q) ∈ GG M H' q := by
    have e : jqNModC ℚ (M * q) = qExpand ℚ q (jqNModC ℚ M) := by
      rw [jqNModC, jqNModC, qExpand_qExpand]
      exact qExpand_congr (Nat.mul_comm M q) _
    rw [e]
    exact subset_adjoin ℚ _ ⟨_, hM, rfl⟩
  have h2 : coeffEmb ℂ (jqNModC ℚ (M * q)) = jqNModC ℂ (M * q) := ModularCurve.map_jqNModC (algebraMap ℚ ℂ) (M * q)
  rw [← h2]
  exact coeffEmb_mem_laurentBaseChange ℂ h1

abbrev BC : IntermediateField ℂ (LaurentSeries ℂ) := KC M H' ⊔ laurentBaseChange ℂ (GG M H' q)

theorem BC_le_EC : BC M H' q ≤ EC M H' q :=
  sup_le (KC_le_EC M H' q) (laurentBaseChange_mono' ℂ (GG_le_FF' M H' q))

theorem le_relrank_KC_BC :
    ((Gam' M H' q).relIndex (Gam M H') : Cardinal) ≤ relrank (KC M H') (BC M H' q) := by
  haveI : NeZero (M * q) := NeZero.mul
  have h23 := ModularCurve.relIndex_gamma0_le_relrank_adjoin_insert_jqNModC (Gam M H')
    (translation_mem_GammaH M H') (M * q)
  rw [← Subgroup.inf_relIndex_left (Gam M H') (Gamma0 (M * q))] at h23
  change ((((Gam' M H' q).relIndex (Gam M H') : ℕ)) : Cardinal) ≤
    relrank (An (Gam M H')) (adjoin ℂ (insert (jqNModC ℂ (M * q)) (anSet (Gam M H')))) at h23
  have hins : adjoin ℂ (insert (jqNModC ℂ (M * q)) (anSet (Gam M H'))) ≤ BC M H' q := by
    rw [adjoin_le_iff, Set.insert_subset_iff]
    refine ⟨(le_sup_right : laurentBaseChange ℂ (GG M H' q) ≤ BC M H' q) (jqNModC_mem_GG M H' q), ?_⟩
    intro x hx
    exact le_sup_left (b := laurentBaseChange ℂ (GG M H' q)) (An_Gam_le M H' (subset_adjoin ℂ _ hx))
  have hsub : An (Gam M H') ≤ adjoin ℂ (insert (jqNModC ℂ (M * q)) (anSet (Gam M H'))) :=
    adjoin.mono ℂ _ _ (Set.subset_insert _ _)
  calc (((Gam' M H' q).relIndex (Gam M H') : ℕ) : Cardinal)
        ≤ relrank (An (Gam M H')) (adjoin ℂ (insert (jqNModC ℂ (M * q)) (anSet (Gam M H')))) := h23
    _ ≤ relrank (An (Gam M H')) (BC M H' q) := relrank_mono_right hsub hins
    _ = relrank (KC M H') (BC M H' q) := by rw [show KC M H' = An (Gam M H') from laurentBaseChange_FF_eq_An M H']

theorem BC_eq_EC : BC M H' q = EC M H' q := by
  have hKB : KC M H' ≤ BC M H' q := le_sup_left
  have hBE : BC M H' q ≤ EC M H' q := BC_le_EC M H' q
  have hup := relrank_KC_EC_le M H' q
  have hlo := le_relrank_KC_BC M H' q
  have hKBE : relrank (KC M H') (BC M H' q) ≤ relrank (KC M H') (EC M H' q) := relrank_mono_right hKB hBE
  have hKE : relrank (KC M H') (EC M H' q) = ((Gam' M H' q).relIndex (Gam M H') : Cardinal) :=
    le_antisymm hup (hlo.trans hKBE)
  have hKBeq : relrank (KC M H') (BC M H' q) = ((Gam' M H' q).relIndex (Gam M H') : Cardinal) :=
    le_antisymm (hKBE.trans hup) hlo
  have hmul := relrank_mul_relrank hKB hBE
  rw [hKE, hKBeq] at hmul
  have hI0 : (((Gam' M H' q).relIndex (Gam M H') : ℕ) : Cardinal) ≠ 0 := by
    exact_mod_cast relIndex_Gam'_ne_zero M H' q
  have hIfin : (((Gam' M H' q).relIndex (Gam M H') : ℕ) : Cardinal) < Cardinal.aleph0 :=
    Cardinal.natCast_lt_aleph0
  have hBE1 : relrank (BC M H' q) (EC M H' q) = 1 := by
    have h := hmul
    have hr : relrank (BC M H' q) (EC M H' q) < Cardinal.aleph0 := by
      by_contra hinf
      have hge : Cardinal.aleph0 ≤ relrank (BC M H' q) (EC M H' q) := le_of_not_gt hinf
      have : Cardinal.aleph0 ≤ (((Gam' M H' q).relIndex (Gam M H') : ℕ) : Cardinal) := by
        calc Cardinal.aleph0 ≤ relrank (BC M H' q) (EC M H' q) := hge
          _ ≤ (((Gam' M H' q).relIndex (Gam M H') : ℕ) : Cardinal) * relrank (BC M H' q) (EC M H' q) :=
              Cardinal.le_mul_left hI0
          _ = _ := h
      exact absurd this (not_le.mpr hIfin)
    obtain ⟨n, hn⟩ := Cardinal.lt_aleph0.mp hr
    rw [hn] at h ⊢
    have h' : ((Gam' M H' q).relIndex (Gam M H')) * n = (Gam' M H' q).relIndex (Gam M H') := by
      have := h; norm_cast at this
    have hn1 : n = 1 := by
      have hpos := Nat.pos_of_ne_zero (relIndex_Gam'_ne_zero M H' q)
      exact Nat.eq_of_mul_eq_mul_left hpos (h'.trans (mul_one _).symm)
    rw [hn1]; norm_cast
  exact le_antisymm hBE ((relrank_eq_one_iff).mp hBE1)

end ComplexSide

section Transport

variable (M : ℕ) (H' : Subgroup (ZMod M)ˣ) (q : ℕ) [NeZero M] [NeZero q]

theorem sup_eq (L : Type*) [Field L] [Algebra ℚ L] :
    laurentBaseChange L (FF M H') ⊔ laurentBaseChange L (GG M H' q) = laurentBaseChange L (FF' M H' q) := by
  obtain ⟨x, hxF, hxt, hF, hF'⟩ := exists_good_x M H' q
  have hle0 : FF M H' ≤ FF M H' ⊔ GG M H' q := le_sup_left
  have hle1 : FF M H' ⊔ GG M H' q ≤ FF' M H' q := sup_le (FF_le M H' q) (GG_le_FF' M H' q)
  have hxle : adjoin ℚ ({x} : Set (LaurentSeries ℚ)) ≤ FF M H' := by
    rw [adjoin_le_iff, Set.singleton_subset_iff]; exact hxF
  have hB : relfinrank (adjoin ℚ ({x} : Set (LaurentSeries ℚ))) (FF M H' ⊔ GG M H' q) ≠ 0 := by
    intro h0
    have t := relfinrank_mul_relfinrank (hxle.trans hle0) hle1
    rw [h0, zero_mul] at t
    exact hF' t.symm

  have hC : relfinrank (laurentBaseChange ℂ (FF M H' ⊔ GG M H' q)) (laurentBaseChange ℂ (FF' M H' q)) = 1 := by
    rw [laurentBaseChange_sup, show laurentBaseChange ℂ (FF M H') ⊔ laurentBaseChange ℂ (GG M H' q) = BC M H' q from rfl,
      BC_eq_EC M H' q]
    exact relfinrank_self _
  have hQ : relfinrank (FF M H' ⊔ GG M H' q) (FF' M H' q) = 1 := by
    rw [← relfinrank_laurentBaseChange_eq ℂ hle1 (hle0 hxF) hxt hB, hC]
  have hL : relfinrank (laurentBaseChange L (FF M H' ⊔ GG M H' q)) (laurentBaseChange L (FF' M H' q)) = 1 := by
    rw [relfinrank_laurentBaseChange_eq L hle1 (hle0 hxF) hxt hB]; exact hQ
  have hmono : laurentBaseChange L (FF M H' ⊔ GG M H' q) ≤ laurentBaseChange L (FF' M H' q) :=
    laurentBaseChange_mono' L hle1
  have hfin : relrank (laurentBaseChange L (FF M H' ⊔ GG M H' q)) (laurentBaseChange L (FF' M H' q)) < Cardinal.aleph0 := by
    by_contra hinf
    rw [relfinrank_eq_toNat_relrank, Cardinal.toNat_apply_of_aleph0_le (le_of_not_gt hinf)] at hL
    exact zero_ne_one hL
  have h1 : relrank (laurentBaseChange L (FF M H' ⊔ GG M H' q)) (laurentBaseChange L (FF' M H' q)) = 1 := by
    rw [relfinrank_eq_toNat_relrank] at hL
    have := Cardinal.cast_toNat_of_lt_aleph0 hfin
    rw [hL, Nat.cast_one] at this
    exact this.symm
  rw [← laurentBaseChange_sup]
  exact le_antisymm hmono ((relrank_eq_one_iff).mp h1)

theorem laurentBaseChange_GG (L : Type*) [Field L] [Algebra ℚ L] :
    laurentBaseChange L (GG M H' q)
      = adjoin L (qExpand L q '' (laurentBaseChange L (FF M H') : Set (LaurentSeries L))) := by

  let φ : LaurentSeries L →ₐ[L] LaurentSeries L :=
    { qExpand L q with
      commutes' := fun a => by
        show qExpand L q (algebraMap L (LaurentSeries L) a) = algebraMap L (LaurentSeries L) a
        rw [algebraMap_laurentSeries_eq_single, qExpand_single, mul_zero] }
  have hφ : ∀ z, φ z = qExpand L q z := fun _ => rfl
  have hcomm : ∀ y : LaurentSeries ℚ, coeffEmb L (qExpand ℚ q y) = qExpand L q (coeffEmb L y) := by
    intro y
    ext n
    by_cases hn : (q : ℤ) ∣ n
    · obtain ⟨m, rfl⟩ := hn
      rw [coeffEmb_coeff, qExpand_coeff_mul, qExpand_coeff_mul, coeffEmb_coeff]
    · rw [coeffEmb_coeff, qExpand_coeff_of_not_dvd q _ hn, qExpand_coeff_of_not_dvd q _ hn, map_zero]

  rw [show GG M H' q = adjoin ℚ (qExpand ℚ q '' (FF M H' : Set (LaurentSeries ℚ))) from rfl,
    ModularCurve.laurentBaseChange_adjoin]
  have himg : coeffEmb L '' (qExpand ℚ q '' (FF M H' : Set (LaurentSeries ℚ)))
      = φ '' (coeffEmb L '' (FF M H' : Set (LaurentSeries ℚ))) := by
    ext z
    constructor
    · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
      exact ⟨coeffEmb L y, ⟨y, hy, rfl⟩, by rw [hφ, hcomm]⟩
    · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
      exact ⟨qExpand ℚ q y, ⟨y, hy, rfl⟩, by rw [hcomm, ← hφ]⟩
  rw [himg]

  have hR : (qExpand L q '' (laurentBaseChange L (FF M H') : Set (LaurentSeries L)))
      = ((adjoin L (coeffEmb L '' (FF M H' : Set (LaurentSeries ℚ)))).map φ : Set (LaurentSeries L)) := by
    rw [laurentBaseChange, IntermediateField.coe_map]
    rfl
  rw [hR, IntermediateField.adjoin_map, adjoin_self]

end Transport

end Gen0Sol
p2m_reactivate "P2MW.S_ModularCurve_laurentBaseChange_xHFunctionField_sup_adjoin_qExpand_eq_laurentBaseChange_xHTopFunctionFieldC.Gen0Sol"

theorem solution
    (L : Type*) [Field L] [Algebra ℚ L] (N q : ℕ) [NeZero N] [NeZero q] (H' : Subgroup (ZMod N)ˣ) :
    ModularCurve.laurentBaseChange L (ModularCurve.xHFunctionField N H') ⊔
        IntermediateField.adjoin L (⇑(ModularCurve.qExpand L q) '' (ModularCurve.laurentBaseChange L (ModularCurve.xHFunctionField N H') : Set (LaurentSeries L))) =
      ModularCurve.laurentBaseChange L (ModularCurve.xHTopFunctionFieldC ℚ N H' (N * q)) := by
  have h := Gen0Sol.sup_eq N H' q L
  rw [Gen0Sol.laurentBaseChange_GG] at h
  exact h

end
p2m_reactivate "P2MW.S_ModularCurve_laurentBaseChange_xHFunctionField_sup_adjoin_qExpand_eq_laurentBaseChange_xHTopFunctionFieldC.Gen0Sol"

end S_ModularCurve_laurentBaseChange_xHFunctionField_sup_adjoin_qExpand_eq_laurentBaseChange_xHTopFunctionFieldC
end P2MW
export P2MW.S_ModularCurve_laurentBaseChange_xHFunctionField_sup_adjoin_qExpand_eq_laurentBaseChange_xHTopFunctionFieldC (solution)
