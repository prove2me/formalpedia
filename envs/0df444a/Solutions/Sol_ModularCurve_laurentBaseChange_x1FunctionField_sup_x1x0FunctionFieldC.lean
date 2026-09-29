-- Prove2me | solution 1 for ModularCurve.laurentBaseChange_x1FunctionField_sup_x1x0FunctionFieldC
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/ca8459df-cda0-5f15-9dfa-333aa2e840b3

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
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_laurentBaseChange_x1FunctionField_sup_x1x0FunctionFieldC
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation"
p2m_attr_erase "simp" "ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver"
p2m_attr_erase "simp" "AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven"
p2m_attr_erase "simp" "ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ"

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open scoped MatrixGroups

namespace Gen1Sol

open ModularCurve CongruenceSubgroup IntermediateField AlgebraicCurve HahnSeries UpperHalfPlane

section Groups

variable (M q : ℕ)

abbrev Gam : Subgroup SL(2, ℤ) := CohCarrier.GammaH M ⊥

abbrev Gam' : Subgroup SL(2, ℤ) := CohCarrier.GammaH M ⊥ ⊓ Gamma0 (M * q)

theorem Gam'_le : Gam' M q ≤ Gam M := inf_le_left

scoped instance [NeZero M] : (Gam M).FiniteIndex := Subgroup.finiteIndex_of_le (Gamma1_le_GammaH M ⊥)

scoped instance [NeZero M] [NeZero q] : (Gam' M q).FiniteIndex := by
  haveI : NeZero (M * q) := NeZero.mul
  refine Subgroup.finiteIndex_of_le (H := Gamma1 (M * q)) (le_inf ?_ (Gamma1_in_Gamma0 _))
  exact (Gamma1_le_of_dvd (dvd_mul_right M q)).trans (Gamma1_le_GammaH M ⊥)

theorem T_mem_Gam' : ModularGroup.T ∈ Gam' M q := by
  refine Subgroup.mem_inf.mpr ⟨translation_mem_GammaH M ⊥, ?_⟩
  rw [Gamma0_mem]
  simp [ModularGroup.T]

theorem Gam_eq : Gam M = Gamma1 M := GammaH_bot M

theorem Gam_inf_Gamma0_eq {N t : ℕ} (htq : Nat.Coprime t q) (hM : M = N * t) :
    Gam M ⊓ Gamma0 (N * q) = Gam' M q := by
  ext A
  simp only [Subgroup.mem_inf, Gamma0_mem]
  constructor
  · rintro ⟨hA, h0⟩
    refine ⟨hA, ?_⟩
    have hMdvd : ((M : ℕ) : ℤ) ∣ A 1 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (Gamma0_mem.mp (CohCarrier.GammaH_le_Gamma0 ⊥ hA))
    have hNq : ((N * q : ℕ) : ℤ) ∣ A 1 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h0
    obtain ⟨c, hc⟩ : ((N : ℕ) : ℤ) ∣ A 1 0 := (show ((N:ℕ):ℤ) ∣ ((M:ℕ):ℤ) from ⟨t, by rw [hM]; push_cast; ring⟩).trans hMdvd
    have ht : (t : ℤ) ∣ c ∨ N = 0 := by
      rcases Nat.eq_zero_or_pos N with hN | hN
      · exact Or.inr hN
      · left
        have : ((N:ℕ):ℤ) * t ∣ ((N:ℕ):ℤ) * c := by
          have := hMdvd; rw [hM, hc] at this; push_cast at this; exact this
        exact (mul_dvd_mul_iff_left (by exact_mod_cast hN.ne')).mp this
    have hq' : (q : ℤ) ∣ c ∨ N = 0 := by
      rcases Nat.eq_zero_or_pos N with hN | hN
      · exact Or.inr hN
      · left
        have : ((N:ℕ):ℤ) * q ∣ ((N:ℕ):ℤ) * c := by
          have := hNq; rw [hc] at this; push_cast at this; exact this
        exact (mul_dvd_mul_iff_left (by exact_mod_cast hN.ne')).mp this
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr
    rcases Nat.eq_zero_or_pos N with hN | hN
    · subst hN
      simp only [zero_mul] at hM
      subst hM
      simp only [zero_mul, Nat.cast_zero]
      have : A 1 0 = 0 := by simpa using hNq
      rw [this]
    · have htc : (t : ℤ) ∣ c := ht.resolve_right hN.ne'
      have hqc : (q : ℤ) ∣ c := hq'.resolve_right hN.ne'
      have hcop : IsCoprime (t : ℤ) (q : ℤ) := Nat.isCoprime_iff_coprime.mpr htq
      have htq' : (t : ℤ) * q ∣ c := hcop.mul_dvd htc hqc
      rw [hM, hc]
      push_cast
      rw [mul_assoc]
      exact mul_dvd_mul_left _ htq'
  · rintro ⟨hA, h0⟩
    refine ⟨hA, ?_⟩
    have hMq : ((M * q : ℕ) : ℤ) ∣ A 1 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h0
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr
    refine dvd_trans ?_ hMq
    rw [hM]; push_cast
    exact ⟨t, by ring⟩

theorem relIndex_Gamma0_eq {N t : ℕ} (htq : Nat.Coprime t q) (hM : M = N * t) :
    (Gamma0 (N * q)).relIndex (Gam M) = (Gam' M q).relIndex (Gam M) := by
  rw [← Subgroup.inf_relIndex_left (Gam M) (Gamma0 (N * q)), Gam_inf_Gamma0_eq M q htq hM]

theorem relIndex_Gam'_ne_zero [NeZero M] [NeZero q] : (Gam' M q).relIndex (Gam M) ≠ 0 := by
  intro h0
  have hdvd := Subgroup.relIndex_dvd_index_of_le (Gam'_le M q)
  rw [h0, zero_dvd_iff] at hdvd
  exact Subgroup.FiniteIndex.index_ne_zero hdvd

end Groups

section RatFields

variable (M q : ℕ)

abbrev FF : IntermediateField ℚ (LaurentSeries ℚ) := qExpFunctionFieldC ℚ (Gam M)

abbrev FF' : IntermediateField ℚ (LaurentSeries ℚ) := qExpFunctionFieldC ℚ (Gam' M q)

theorem FF_le : FF M ≤ FF' M q := qExpFunctionFieldC_mono ℚ (Gam'_le M q)

theorem FF_eq_x1 : FF M = x1FunctionField M := by
  show qExpFunctionFieldC ℚ (CohCarrier.GammaH M ⊥) = qExpFunctionFieldC ℚ (Gamma1 M)
  rw [GammaH_bot]

theorem FF'_eq_x1x0 : FF' M q = x1x0FunctionFieldC ℚ M (M * q) := by
  show qExpFunctionFieldC ℚ (CohCarrier.GammaH M ⊥ ⊓ Gamma0 (M * q)) =
    qExpFunctionFieldC ℚ (Gamma1 M ⊓ Gamma0 (M * q))
  rw [GammaH_bot]

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
    ∃ x : LaurentSeries ℚ, x ∈ FF M ∧ Transcendental ℚ x ∧
      relfinrank (adjoin ℚ ({x} : Set (LaurentSeries ℚ))) (FF M) ≠ 0 ∧
      relfinrank (adjoin ℚ ({x} : Set (LaurentSeries ℚ))) (FF' M q) ≠ 0 := by
  obtain ⟨x, hxt, hfd⟩ :=
    ModularCurve.JOneES.exists_transcendental_finiteDimensional_qExpFunctionFieldC (Gam M)
      (translation_mem_GammaH M ⊥)
  obtain ⟨x', hxt', hfd'⟩ :=
    ModularCurve.JOneES.exists_transcendental_finiteDimensional_qExpFunctionFieldC (Gam' M q)
      (T_mem_Gam' M q)
  let y : FF' M q := ⟨(x : LaurentSeries ℚ), FF_le M q x.2⟩
  have hxE : Transcendental ℚ (x : LaurentSeries ℚ) := fun h =>
    transcendental_of_subsingleton_ratAlgebra _ hxt
      ((IntermediateField.isAlgebraic_iff (K := ℚ) (S := FF M) (x := x)).mpr h)
  have hyt : Transcendental ℚ y := fun h =>
    hxE ((IntermediateField.isAlgebraic_iff (K := ℚ) (S := FF' M q) (x := y)).mp
      (isAlgebraic_of_subsingleton_ratAlgebra _ h))
  haveI := hfd'
  have hfdy : FiniteDimensional (adjoin ℚ ({y} : Set (FF' M q))) (FF' M q) :=
    AlgebraicCurve.finiteDimensional_adjoin_of_transcendental x' hyt
  refine ⟨_, x.2, hxE,
    relfinrank_adjoin_ne_zero (FF M) x (finiteDimensional_adjoin_of_subsingleton_ratAlgebra _ hfd),
    relfinrank_adjoin_ne_zero (FF' M q) y
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

variable (M q : ℕ)

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

theorem An_Gam_le [NeZero M] : An (Gam M) ≤ laurentBaseChange ℂ (FF M) := by
  rw [adjoin_le_iff]
  rintro _ ⟨k, f, g, hg, rfl⟩
  have hg' : g ≠ 0 := by
    rintro rfl
    exact hg (by rw [ModularForm.coe_zero, qExpansion_zero])
  exact ModularCurve.qExpansion_div_mem_laurentBaseChange_xHFunctionField M ⊥ f g hg'

theorem laurentBaseChange_FF_eq_An [NeZero M] : laurentBaseChange ℂ (FF M) = An (Gam M) :=
  le_antisymm (laurentBaseChange_le_An (Gam M)) (An_Gam_le M)

theorem relrank_mono_right {K E : Type*} [Field K] [Field E] [Algebra K E]
    {A B C : IntermediateField K E} (hAB : A ≤ B) (hBC : B ≤ C) : relrank A B ≤ relrank A C := by
  rw [← relrank_mul_relrank hAB hBC]
  have h0 : relrank B C ≠ 0 := by
    rw [relrank_eq_rank_of_le hBC]
    exact rank_pos.ne'
  exact Cardinal.le_mul_right h0

variable [NeZero M] [NeZero q]

abbrev KC : IntermediateField ℂ (LaurentSeries ℂ) := laurentBaseChange ℂ (FF M)
abbrev EC : IntermediateField ℂ (LaurentSeries ℂ) := laurentBaseChange ℂ (FF' M q)

theorem KC_le_EC : KC M ≤ EC M q := laurentBaseChange_mono' ℂ (FF_le M q)

theorem relrank_KC_EC_le :
    relrank (KC M) (EC M q) ≤ ((Gam' M q).relIndex (Gam M) : Cardinal) := by
  have hC2 := ModularCurve.relrank_adjoin_qExpansion_div_le_relIndex (Gam M) (Gam' M q)
    (Gam'_le M q) (T_mem_Gam' M q) (relIndex_Gam'_ne_zero M q)
  change relrank (An (Gam M)) (An (Gam' M q)) ≤ _ at hC2
  calc relrank (KC M) (EC M q)
        ≤ relrank (KC M) (An (Gam' M q)) :=
          relrank_mono_right (KC_le_EC M q) (laurentBaseChange_le_An (Gam' M q))
    _ = relrank (An (Gam M)) (An (Gam' M q)) := by rw [show KC M = An (Gam M) from laurentBaseChange_FF_eq_An M]
    _ ≤ ((Gam' M q).relIndex (Gam M) : Cardinal) := hC2

variable {N t : ℕ} [NeZero N] (htq : Nat.Coprime t q) (hM : M = N * t)

abbrev RR (N q : ℕ) : IntermediateField ℚ (LaurentSeries ℚ) := x1x0FunctionFieldC ℚ N (N * q)

include hM in

theorem RR_le_FF' : RR N q ≤ FF' M q := by
  have hNM : N ∣ M := ⟨t, hM⟩
  refine qExpFunctionFieldC_mono ℚ ?_
  show CohCarrier.GammaH M ⊥ ⊓ Gamma0 (M * q) ≤ Gamma1 N ⊓ Gamma0 (N * q)
  rw [GammaH_bot]
  refine inf_le_inf (Gamma1_le_of_dvd hNM) ?_
  intro A hA
  rw [Gamma0_mem] at hA ⊢
  have := congrArg (ZMod.castHom (mul_dvd_mul_right hNM q) (ZMod (N * q))) hA
  rwa [map_intCast, map_zero] at this

theorem jqNModC_mem_RR : jqNModC ℂ (N * q) ∈ laurentBaseChange ℂ (RR N q) := by
  haveI : NeZero (N * q) := NeZero.mul
  have h1 : jqNModC ℚ (N * q) ∈ RR N q := by
    have hfull : jqNModC ℚ (N * q) ∈ modularFunctionFieldFullC ℚ (N * q) :=
      jqModCd_mem_full ℚ (N * q) dvd_rfl
    have h0 : jqNModC ℚ (N * q) ∈ qExpFunctionFieldC ℚ (Gamma0 (N * q)) :=
      ModularCurve.modularFunctionFieldFullC_le_qExpFunctionFieldC_gamma0 ℚ (N * q) hfull
    exact qExpFunctionFieldC_mono ℚ (inf_le_right : Gamma1 N ⊓ Gamma0 (N * q) ≤ Gamma0 (N * q)) h0
  have h2 : coeffEmb ℂ (jqNModC ℚ (N * q)) = jqNModC ℂ (N * q) := ModularCurve.map_jqNModC (algebraMap ℚ ℂ) (N * q)
  rw [← h2]
  exact coeffEmb_mem_laurentBaseChange ℂ h1

abbrev BC (N q : ℕ) (M : ℕ) : IntermediateField ℂ (LaurentSeries ℂ) := KC M ⊔ laurentBaseChange ℂ (RR N q)

include hM in
theorem BC_le_EC : BC N q M ≤ EC M q :=
  sup_le (KC_le_EC M q) (laurentBaseChange_mono' ℂ (RR_le_FF' M q hM))

include htq hM in

theorem le_relrank_KC_BC :
    ((Gam' M q).relIndex (Gam M) : Cardinal) ≤ relrank (KC M) (BC N q M) := by
  haveI : NeZero (N * q) := NeZero.mul
  have h23 := ModularCurve.relIndex_gamma0_le_relrank_adjoin_insert_jqNModC (Gam M)
    (translation_mem_GammaH M ⊥) (N * q)
  rw [relIndex_Gamma0_eq M q htq hM] at h23
  change ((((Gam' M q).relIndex (Gam M) : ℕ)) : Cardinal) ≤
    relrank (An (Gam M)) (adjoin ℂ (insert (jqNModC ℂ (N * q)) (anSet (Gam M)))) at h23
  have hins : adjoin ℂ (insert (jqNModC ℂ (N * q)) (anSet (Gam M))) ≤ BC N q M := by
    rw [adjoin_le_iff, Set.insert_subset_iff]
    refine ⟨(le_sup_right : laurentBaseChange ℂ (RR N q) ≤ BC N q M) (jqNModC_mem_RR (N := N) q), ?_⟩
    intro x hx
    exact le_sup_left (b := laurentBaseChange ℂ (RR N q)) (An_Gam_le M (subset_adjoin ℂ _ hx))
  have hsub : An (Gam M) ≤ adjoin ℂ (insert (jqNModC ℂ (N * q)) (anSet (Gam M))) :=
    adjoin.mono ℂ _ _ (Set.subset_insert _ _)
  calc (((Gam' M q).relIndex (Gam M) : ℕ) : Cardinal)
        ≤ relrank (An (Gam M)) (adjoin ℂ (insert (jqNModC ℂ (N * q)) (anSet (Gam M)))) := h23
    _ ≤ relrank (An (Gam M)) (BC N q M) := relrank_mono_right hsub hins
    _ = relrank (KC M) (BC N q M) := by rw [show KC M = An (Gam M) from laurentBaseChange_FF_eq_An M]

include htq hM in

theorem BC_eq_EC : BC N q M = EC M q := by
  have hKB : KC M ≤ BC N q M := le_sup_left
  have hBE : BC N q M ≤ EC M q := BC_le_EC M q hM
  have hup := relrank_KC_EC_le M q
  have hlo := le_relrank_KC_BC M q htq hM

  have hKBE : relrank (KC M) (BC N q M) ≤ relrank (KC M) (EC M q) := relrank_mono_right hKB hBE
  have hKE : relrank (KC M) (EC M q) = ((Gam' M q).relIndex (Gam M) : Cardinal) :=
    le_antisymm hup (hlo.trans hKBE)
  have hKBeq : relrank (KC M) (BC N q M) = ((Gam' M q).relIndex (Gam M) : Cardinal) :=
    le_antisymm (hKBE.trans hup) hlo

  have hmul := relrank_mul_relrank hKB hBE
  rw [hKE, hKBeq] at hmul
  have hI0 : (((Gam' M q).relIndex (Gam M) : ℕ) : Cardinal) ≠ 0 := by
    exact_mod_cast relIndex_Gam'_ne_zero M q
  have hIfin : (((Gam' M q).relIndex (Gam M) : ℕ) : Cardinal) < Cardinal.aleph0 :=
    Cardinal.natCast_lt_aleph0
  have hBE1 : relrank (BC N q M) (EC M q) = 1 := by
    have h := hmul

    have hr : relrank (BC N q M) (EC M q) < Cardinal.aleph0 := by
      by_contra hinf
      have hge : Cardinal.aleph0 ≤ relrank (BC N q M) (EC M q) := le_of_not_gt hinf
      have : Cardinal.aleph0 ≤ (((Gam' M q).relIndex (Gam M) : ℕ) : Cardinal) := by
        calc Cardinal.aleph0 ≤ relrank (BC N q M) (EC M q) := hge
          _ ≤ (((Gam' M q).relIndex (Gam M) : ℕ) : Cardinal) * relrank (BC N q M) (EC M q) :=
              Cardinal.le_mul_left hI0
          _ = _ := h
      exact absurd this (not_le.mpr hIfin)
    obtain ⟨n, hn⟩ := Cardinal.lt_aleph0.mp hr
    rw [hn] at h ⊢
    have h' : ((Gam' M q).relIndex (Gam M)) * n = (Gam' M q).relIndex (Gam M) := by
      have := h; norm_cast at this
    have hn1 : n = 1 := by
      have hpos := Nat.pos_of_ne_zero (relIndex_Gam'_ne_zero M q)
      exact Nat.eq_of_mul_eq_mul_left hpos (h'.trans (mul_one _).symm)
    rw [hn1]; norm_cast
  exact le_antisymm hBE ((relrank_eq_one_iff).mp hBE1)

end ComplexSide

section Transport

variable (M q : ℕ) [NeZero M] [NeZero q] {N t : ℕ} [NeZero N] (htq : Nat.Coprime t q) (hM : M = N * t)

include htq hM in

theorem relfinrank_sup_FF'_eq_one : relfinrank (FF M ⊔ RR N q) (FF' M q) = 1 := by
  obtain ⟨x, hxF, hxt, hF, hF'⟩ := exists_good_x M q
  have hle0 : FF M ≤ FF M ⊔ RR N q := le_sup_left
  have hle1 : FF M ⊔ RR N q ≤ FF' M q := sup_le (FF_le M q) (RR_le_FF' M q hM)

  have hxle : adjoin ℚ ({x} : Set (LaurentSeries ℚ)) ≤ FF M := by
    rw [adjoin_le_iff, Set.singleton_subset_iff]; exact hxF
  have hB : relfinrank (adjoin ℚ ({x} : Set (LaurentSeries ℚ))) (FF M ⊔ RR N q) ≠ 0 := by
    intro h0
    have t := relfinrank_mul_relfinrank (hxle.trans hle0) hle1
    rw [h0, zero_mul] at t
    exact hF' t.symm

  have hC : relfinrank (laurentBaseChange ℂ (FF M ⊔ RR N q)) (laurentBaseChange ℂ (FF' M q)) = 1 := by
    rw [laurentBaseChange_sup, show laurentBaseChange ℂ (FF M) ⊔ laurentBaseChange ℂ (RR N q) = BC N q M from rfl,
      BC_eq_EC M q htq hM]
    exact relfinrank_self _
  rw [← relfinrank_laurentBaseChange_eq ℂ hle1 (hle0 hxF) hxt hB, hC]

include htq hM in

theorem sup_eq (L : Type*) [Field L] [Algebra ℚ L] :
    laurentBaseChange L (FF M) ⊔ laurentBaseChange L (RR N q) = laurentBaseChange L (FF' M q) := by
  obtain ⟨x, hxF, hxt, hF, hF'⟩ := exists_good_x M q
  have hle0 : FF M ≤ FF M ⊔ RR N q := le_sup_left
  have hle1 : FF M ⊔ RR N q ≤ FF' M q := sup_le (FF_le M q) (RR_le_FF' M q hM)
  have hxle : adjoin ℚ ({x} : Set (LaurentSeries ℚ)) ≤ FF M := by
    rw [adjoin_le_iff, Set.singleton_subset_iff]; exact hxF
  have hB : relfinrank (adjoin ℚ ({x} : Set (LaurentSeries ℚ))) (FF M ⊔ RR N q) ≠ 0 := by
    intro h0
    have t := relfinrank_mul_relfinrank (hxle.trans hle0) hle1
    rw [h0, zero_mul] at t
    exact hF' t.symm
  have hL : relfinrank (laurentBaseChange L (FF M ⊔ RR N q)) (laurentBaseChange L (FF' M q)) = 1 := by
    rw [relfinrank_laurentBaseChange_eq L hle1 (hle0 hxF) hxt hB]
    exact relfinrank_sup_FF'_eq_one M q htq hM
  have hmono : laurentBaseChange L (FF M ⊔ RR N q) ≤ laurentBaseChange L (FF' M q) :=
    laurentBaseChange_mono' L hle1

  have hfin : relrank (laurentBaseChange L (FF M ⊔ RR N q)) (laurentBaseChange L (FF' M q)) < Cardinal.aleph0 := by
    by_contra hinf
    rw [relfinrank_eq_toNat_relrank, Cardinal.toNat_apply_of_aleph0_le (le_of_not_gt hinf)] at hL
    exact zero_ne_one hL
  have h1 : relrank (laurentBaseChange L (FF M ⊔ RR N q)) (laurentBaseChange L (FF' M q)) = 1 := by
    rw [relfinrank_eq_toNat_relrank] at hL
    have := Cardinal.cast_toNat_of_lt_aleph0 hfin
    rw [hL, Nat.cast_one] at this
    exact this.symm
  rw [← laurentBaseChange_sup]
  exact le_antisymm hmono ((relrank_eq_one_iff).mp h1)

end Transport

end Gen1Sol
p2m_reactivate "P2MW.S_ModularCurve_laurentBaseChange_x1FunctionField_sup_x1x0FunctionFieldC.Gen1Sol"

theorem solution
    (L : Type*) [Field L] [Algebra ℚ L] (N t q : ℕ) [NeZero N] [NeZero t] [NeZero q]
    (htq : Nat.Coprime t q) (N' : ℕ) (hN' : N' = N * t) :
    ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField N') ⊔
        ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ N (N * q))
      = ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ N' (N' * q)) := by
  haveI : NeZero N' := ⟨by rw [hN']; exact mul_ne_zero (NeZero.ne N) (NeZero.ne t)⟩
  have h := Gen1Sol.sup_eq N' q htq hN' L
  rw [Gen1Sol.FF_eq_x1, Gen1Sol.FF'_eq_x1x0] at h
  exact h

end
p2m_reactivate "P2MW.S_ModularCurve_laurentBaseChange_x1FunctionField_sup_x1x0FunctionFieldC.Gen1Sol"

end S_ModularCurve_laurentBaseChange_x1FunctionField_sup_x1x0FunctionFieldC
end P2MW
export P2MW.S_ModularCurve_laurentBaseChange_x1FunctionField_sup_x1x0FunctionFieldC (solution)
