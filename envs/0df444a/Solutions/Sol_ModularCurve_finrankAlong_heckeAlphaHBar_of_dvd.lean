-- Prove2me | solution 1 for ModularCurve.finrankAlong_heckeAlphaHBar_of_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/baba1e99-2709-5e1c-9426-1ce02d0d8aa4

import Mathlib
import Definitions.Def_ModularCurve_XHHeckeOperator
import Theorems.Thm_ModularCurve_relrank_adjoin_qExpansion_div_le_relIndex
import Theorems.Thm_ModularCurve_qExpansion_div_mem_laurentBaseChange_xHFunctionField
import Theorems.Thm_ModularCurve_relfinrank_laurentBaseChange
import Theorems.Thm_ModularCurve_laurentBaseChange_adjoin
import Theorems.Thm_AlgebraicCurve_finrankAlong_eq_relfinrank_fieldRange
import Theorems.Thm_ModularCurve_JOneES_exists_transcendental_finiteDimensional_qExpFunctionFieldC
import Theorems.Thm_AlgebraicCurve_finiteDimensional_adjoin_of_transcendental
import Theorems.Thm_ModularCurve_Gamma0_index
import Theorems.Thm_CongruenceSubgroup_relIndex_gamma1_inf_gamma0_mul_of_dvd
import Theorems.Thm_ModularCurve_relIndex_gamma0_le_relrank_adjoin_insert_jqNModC
import Theorems.Thm_ModularCurve_dedekindPsi_mul_prime
import Theorems.Thm_ModularCurve_modularFunctionFieldFullC_le_qExpFunctionFieldC_gamma0
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_finrankAlong_heckeAlphaHBar_of_dvd
p2m_attr_erase "instance" "ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid"
p2m_attr_erase "simp" "ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal"
p2m_attr_erase "simp" "AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven"
p2m_attr_erase "simp" "ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar ModularCurve.ProjectiveLine.map_mk"

noncomputable section

open scoped MatrixGroups

namespace FinrankAlphaHDvdSol

open ModularCurve CongruenceSubgroup IntermediateField AlgebraicCurve HahnSeries UpperHalfPlane

variable (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (ℓ : ℕ)

section Groups

abbrev Gam : Subgroup SL(2, ℤ) := CohCarrier.GammaH M H

abbrev Gam' : Subgroup SL(2, ℤ) := CohCarrier.GammaH M H ⊓ Gamma0 (M * ℓ)

omit [NeZero M] in
theorem Gam'_le : Gam' M H ℓ ≤ Gam M H := inf_le_left

scoped instance : (Gam M H).FiniteIndex := Subgroup.finiteIndex_of_le (Gamma1_le_GammaH M H)

scoped instance [NeZero ℓ] : (Gam' M H ℓ).FiniteIndex := by
  haveI : NeZero (M * ℓ) := NeZero.mul
  refine Subgroup.finiteIndex_of_le (H := Gamma1 (M * ℓ)) (le_inf ?_ (Gamma1_in_Gamma0 _))
  exact (Gamma1_le_of_dvd (dvd_mul_right M ℓ)).trans (Gamma1_le_GammaH M H)

omit [NeZero M] in
theorem T_mem_Gam' : ModularGroup.T ∈ Gam' M H ℓ := by
  refine Subgroup.mem_inf.mpr ⟨translation_mem_GammaH M H, ?_⟩
  rw [Gamma0_mem]
  simp [ModularGroup.T]

omit [NeZero M] in

theorem Gamma0_mul_le : Gamma0 (M * ℓ) ≤ Gamma0 M := by
  intro A hA
  rw [Gamma0_mem] at hA ⊢
  have h : ((M * ℓ : ℕ) : ℤ) ∣ A 1 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hA
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr
    ((show ((M : ℕ) : ℤ) ∣ ((M * ℓ : ℕ) : ℤ) from ⟨ℓ, by push_cast; ring⟩).trans h)

omit [NeZero M] in
theorem Gam'_eq_inf : Gam' M H ℓ = Gamma0 (M * ℓ) ⊓ Gam M H := inf_comm _ _

theorem dedekindPsi_mul_of_dvd : ∀ (ℓ : ℕ), ℓ ≠ 0 → ℓ ∣ M → dedekindPsi (M * ℓ) = ℓ * dedekindPsi M := by
  intro ℓ
  induction ℓ using Nat.strong_induction_on with
  | _ ℓ ih =>
    intro hℓ0 hℓM
    rcases Nat.lt_or_ge ℓ 2 with hlt | hge
    · interval_cases ℓ
      · exact (hℓ0 rfl).elim
      · simp
    · obtain ⟨q, hq, hqℓ⟩ := Nat.exists_prime_and_dvd (show ℓ ≠ 1 by omega)
      obtain ⟨ℓ', rfl⟩ := hqℓ
      have hℓ'0 : ℓ' ≠ 0 := fun h => hℓ0 (by rw [h, mul_zero])
      have hℓ'M : ℓ' ∣ M := (Dvd.intro_left q rfl).trans hℓM
      have hqM : q ∣ M := (Dvd.intro ℓ' rfl).trans hℓM
      have hlt : ℓ' < q * ℓ' := lt_mul_left (Nat.pos_of_ne_zero hℓ'0) hq.one_lt
      have h1 := ih ℓ' hlt hℓ'0 hℓ'M
      haveI : NeZero (M * ℓ') := ⟨mul_ne_zero (NeZero.ne M) hℓ'0⟩
      have h2 := ModularCurve.dedekindPsi_mul_prime (M * ℓ') q hq
      rw [if_pos (hqM.trans (Dvd.intro ℓ' rfl))] at h2
      rw [show M * (q * ℓ') = M * ℓ' * q by ring, h2, h1]
      ring

variable [NeZero ℓ]

theorem relIndex_Gamma0_mul_Gam (hℓM : ℓ ∣ M) : (Gamma0 (M * ℓ)).relIndex (Gam M H) = ℓ := by
  have hℓ0 : ℓ ≠ 0 := NeZero.ne ℓ
  haveI : NeZero (M * ℓ) := ⟨mul_ne_zero (NeZero.ne M) hℓ0⟩

  have hup0 : (Gamma0 (M * ℓ)).relIndex (Gamma0 M) = ℓ := by
    have h := Subgroup.relIndex_mul_index (Gamma0_mul_le M ℓ)
    rw [ModularCurve.Gamma0_index, ModularCurve.Gamma0_index, dedekindPsi_mul_of_dvd M ℓ hℓ0 hℓM] at h
    have hψ : dedekindPsi M ≠ 0 := by
      rw [← ModularCurve.Gamma0_index]; exact Subgroup.FiniteIndex.index_ne_zero
    exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hψ) h
  have hne0 : (Gamma0 (M * ℓ)).relIndex (Gamma0 M) ≠ 0 := by rw [hup0]; exact hℓ0
  have hup : (Gamma0 (M * ℓ)).relIndex (Gam M H) ≤ ℓ :=
    (Subgroup.relIndex_le_of_le_right (CohCarrier.GammaH_le_Gamma0 H) hne0).trans hup0.le

  have hlo0 : (Gamma0 (M * ℓ)).relIndex (Gamma1 M) = ℓ := by
    rw [← Subgroup.inf_relIndex_right, inf_comm]
    exact CongruenceSubgroup.relIndex_gamma1_inf_gamma0_mul_of_dvd M ℓ hℓM
  have hneH : (Gamma0 (M * ℓ)).relIndex (Gam M H) ≠ 0 := by
    rw [← Subgroup.inf_relIndex_right, ← Gam'_eq_inf]
    intro h0
    have hdvd := Subgroup.relIndex_dvd_index_of_le (Gam'_le M H ℓ)
    rw [h0, zero_dvd_iff] at hdvd
    exact Subgroup.FiniteIndex.index_ne_zero hdvd
  have hlo : ℓ ≤ (Gamma0 (M * ℓ)).relIndex (Gam M H) :=
    hlo0.symm.le.trans (Subgroup.relIndex_le_of_le_right (Gamma1_le_GammaH M H) hneH)
  exact le_antisymm hup hlo

theorem relIndex_Gam'_eq (hℓM : ℓ ∣ M) : (Gam' M H ℓ).relIndex (Gam M H) = ℓ := by
  rw [Gam'_eq_inf, Subgroup.inf_relIndex_right]
  exact relIndex_Gamma0_mul_Gam M H ℓ hℓM

end Groups

section RatFields

abbrev FF : IntermediateField ℚ (LaurentSeries ℚ) := qExpFunctionFieldC ℚ (Gam M H)

abbrev FF' : IntermediateField ℚ (LaurentSeries ℚ) := qExpFunctionFieldC ℚ (Gam' M H ℓ)

omit [NeZero M] in
theorem FF_eq : FF M H = xHFunctionField M H := rfl

omit [NeZero M] in
theorem FF'_eq : FF' M H ℓ = xHTopFunctionFieldC ℚ M H (M * ℓ) := rfl

omit [NeZero M] in
theorem FF_le : FF M H ≤ FF' M H ℓ := qExpFunctionFieldC_mono ℚ (Gam'_le M H ℓ)

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

variable [NeZero ℓ]

theorem exists_good_x :
    ∃ x : LaurentSeries ℚ, x ∈ FF M H ∧ Transcendental ℚ x ∧
      relfinrank (adjoin ℚ ({x} : Set (LaurentSeries ℚ))) (FF M H) ≠ 0 ∧
      relfinrank (adjoin ℚ ({x} : Set (LaurentSeries ℚ))) (FF' M H ℓ) ≠ 0 := by
  obtain ⟨x, hxt, hfd⟩ :=
    ModularCurve.JOneES.exists_transcendental_finiteDimensional_qExpFunctionFieldC (Gam M H)
      (translation_mem_GammaH M H)
  obtain ⟨x', hxt', hfd'⟩ :=
    ModularCurve.JOneES.exists_transcendental_finiteDimensional_qExpFunctionFieldC (Gam' M H ℓ)
      (T_mem_Gam' M H ℓ)

  let y : FF' M H ℓ := ⟨(x : LaurentSeries ℚ), FF_le M H ℓ x.2⟩
  have hxE : Transcendental ℚ (x : LaurentSeries ℚ) := fun h =>
    transcendental_of_subsingleton_ratAlgebra _ hxt
      ((IntermediateField.isAlgebraic_iff (K := ℚ) (S := FF M H) (x := x)).mpr h)
  have hyt : Transcendental ℚ y := fun h =>
    hxE ((IntermediateField.isAlgebraic_iff (K := ℚ) (S := FF' M H ℓ) (x := y)).mp
      (isAlgebraic_of_subsingleton_ratAlgebra _ h))
  haveI := hfd'
  have hfdy : FiniteDimensional (adjoin ℚ ({y} : Set (FF' M H ℓ))) (FF' M H ℓ) :=
    AlgebraicCurve.finiteDimensional_adjoin_of_transcendental x' hyt
  refine ⟨_, x.2, hxE,
    relfinrank_adjoin_ne_zero (FF M H) x (finiteDimensional_adjoin_of_subsingleton_ratAlgebra _ hfd),
    relfinrank_adjoin_ne_zero (FF' M H ℓ) y
      (finiteDimensional_adjoin_of_subsingleton_ratAlgebra _ hfdy)⟩

end RatFields

section BaseChange

variable (L : Type*) [Field L] [Algebra ℚ L]

abbrev KL : IntermediateField L (LaurentSeries L) := laurentBaseChange L (FF M H)

abbrev EL : IntermediateField L (LaurentSeries L) := laurentBaseChange L (FF' M H ℓ)

omit [NeZero M] in

theorem laurentBaseChange_mono' {F₀ F₁ : IntermediateField ℚ (LaurentSeries ℚ)} (h : F₀ ≤ F₁) :
    laurentBaseChange L F₀ ≤ laurentBaseChange L F₁ := by
  rw [laurentBaseChange, IntermediateField.adjoin_le_iff]
  rintro _ ⟨y, hy, rfl⟩
  exact coeffEmb_mem_laurentBaseChange L (h hy)

omit [NeZero M] in
theorem KL_le_EL : KL M H L ≤ EL M H ℓ L := laurentBaseChange_mono' L (FF_le M H ℓ)

variable [NeZero ℓ]

theorem relfinrank_KL_EL :
    relfinrank (KL M H L) (EL M H ℓ L) = relfinrank (FF M H) (FF' M H ℓ) := by
  obtain ⟨x, hxF, hxt, hF, -⟩ := exists_good_x M H ℓ
  have h1 := ModularCurve.relfinrank_laurentBaseChange L (FF M H) x hxF hxt
  have h2 := ModularCurve.relfinrank_laurentBaseChange L (FF' M H ℓ) x (FF_le M H ℓ hxF) hxt
  have hxle : adjoin ℚ ({x} : Set (LaurentSeries ℚ)) ≤ FF M H := by
    rw [adjoin_le_iff, Set.singleton_subset_iff]; exact hxF
  have hxLle : adjoin L ({coeffEmb L x} : Set (LaurentSeries L)) ≤ KL M H L := by
    rw [adjoin_le_iff, Set.singleton_subset_iff]; exact coeffEmb_mem_laurentBaseChange L hxF
  have tQ := relfinrank_mul_relfinrank hxle (FF_le M H ℓ)
  have tL := relfinrank_mul_relfinrank hxLle (KL_le_EL M H ℓ L)
  rw [h1, h2, ← tQ] at tL
  exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hF) tL

omit [NeZero M] in
theorem fieldRange_val_comp_inclusion {K E : Type*} [Field K] [Field E] [Algebra K E]
    {A B : IntermediateField K E} (h : A ≤ B) :
    (B.val.comp (IntermediateField.inclusion h)).fieldRange = A := by
  ext x
  constructor
  · rintro ⟨a, rfl⟩
    exact a.2
  · intro hx
    exact ⟨⟨x, hx⟩, rfl⟩

omit [NeZero M] in

theorem finrankAlong_inclusion {K E : Type*} [Field K] [Field E] [Algebra K E]
    {A B : IntermediateField K E} (h : A ≤ B) :
    finrankAlong K (IntermediateField.inclusion h) = relfinrank A B := by
  rw [AlgebraicCurve.finrankAlong_eq_relfinrank_fieldRange, fieldRange_val_comp_inclusion]

omit [NeZero ℓ] [NeZero M] in

theorem finrankAlong_alpha :
    finrankAlong L (heckeAlphaHBar L M H ℓ) = relfinrank (KL M H L) (EL M H ℓ L) := by
  rw [heckeAlphaHBar_eq_inclusion M H ℓ (KL_le_EL M H ℓ L)]
  exact finrankAlong_inclusion (KL_le_EL M H ℓ L)

end BaseChange

section ComplexSide

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

omit [NeZero M] in

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

omit [NeZero M] in

theorem laurentBaseChange_le_An (Δ : Subgroup SL(2, ℤ)) :
    laurentBaseChange ℂ (qExpFunctionFieldC ℚ Δ) ≤ An Δ := by
  rw [qExpFunctionFieldC, ModularCurve.laurentBaseChange_adjoin]
  exact adjoin.mono ℂ _ _ (coeffEmb_image_subset Δ)

theorem An_Gam_le : An (Gam M H) ≤ laurentBaseChange ℂ (FF M H) := by
  rw [adjoin_le_iff]
  rintro _ ⟨k, f, g, hg, rfl⟩
  have hg' : g ≠ 0 := by
    rintro rfl
    exact hg (by rw [ModularForm.coe_zero, qExpansion_zero])
  exact ModularCurve.qExpansion_div_mem_laurentBaseChange_xHFunctionField M H f g hg'

theorem laurentBaseChange_FF_eq_An : laurentBaseChange ℂ (FF M H) = An (Gam M H) :=
  le_antisymm (laurentBaseChange_le_An (Gam M H)) (An_Gam_le M H)

omit [NeZero M] in

theorem relrank_mono_right {K E : Type*} [Field K] [Field E] [Algebra K E]
    {A B C : IntermediateField K E} (hAB : A ≤ B) (hBC : B ≤ C) : relrank A B ≤ relrank A C := by
  rw [← relrank_mul_relrank hAB hBC]
  have h0 : relrank B C ≠ 0 := by
    rw [relrank_eq_rank_of_le hBC]
    exact rank_pos.ne'
  exact Cardinal.le_mul_right h0

variable [NeZero ℓ]

theorem relrank_C_le (hℓM : ℓ ∣ M) :
    relrank (laurentBaseChange ℂ (FF M H)) (laurentBaseChange ℂ (FF' M H ℓ)) ≤ (ℓ : Cardinal) := by
  have hind : (Gam' M H ℓ).relIndex (Gam M H) ≠ 0 := by
    intro h0
    have hdvd := Subgroup.relIndex_dvd_index_of_le (Gam'_le M H ℓ)
    rw [h0, zero_dvd_iff] at hdvd
    exact Subgroup.FiniteIndex.index_ne_zero hdvd
  have hC2 := ModularCurve.relrank_adjoin_qExpansion_div_le_relIndex (Gam M H) (Gam' M H ℓ)
    (Gam'_le M H ℓ) (T_mem_Gam' M H ℓ) hind
  change relrank (An (Gam M H)) (An (Gam' M H ℓ)) ≤ _ at hC2
  calc relrank (laurentBaseChange ℂ (FF M H)) (laurentBaseChange ℂ (FF' M H ℓ))
        ≤ relrank (laurentBaseChange ℂ (FF M H)) (An (Gam' M H ℓ)) :=
          relrank_mono_right (KL_le_EL M H ℓ ℂ) (laurentBaseChange_le_An (Gam' M H ℓ))
    _ = relrank (An (Gam M H)) (An (Gam' M H ℓ)) := by rw [laurentBaseChange_FF_eq_An]
    _ ≤ ((Gam' M H ℓ).relIndex (Gam M H) : Cardinal) := hC2
    _ = (ℓ : Cardinal) := by rw [relIndex_Gam'_eq M H ℓ hℓM]

omit [NeZero M] [NeZero ℓ] in

theorem qExpand_coeffMap {R S : Type*} [CommRing R] [CommRing S] (τ : R →+* S) (N : ℕ) [NeZero N]
    (s : LaurentSeries R) : qExpand S N (coeffMap τ s) = coeffMap τ (qExpand R N s) := by
  ext k
  by_cases hk : (N : ℤ) ∣ k
  · obtain ⟨m, rfl⟩ := hk
    rw [qExpand_coeff_mul, coeffMap_coeff, coeffMap_coeff, qExpand_coeff_mul]
  · rw [qExpand_coeff_of_not_dvd N _ hk, coeffMap_coeff, qExpand_coeff_of_not_dvd N _ hk, map_zero]

omit [NeZero M] [NeZero ℓ] in

theorem coeffEmb_jqNModC (N : ℕ) [NeZero N] : coeffEmb ℂ (jqNModC ℚ N) = jqNModC ℂ N := by
  show coeffMap (algebraMap ℚ ℂ) (qExpand ℚ N (jqModC ℚ)) = qExpand ℂ N (jqModC ℂ)
  rw [← qExpand_coeffMap]
  congr 1
  exact map_jqModC (algebraMap ℚ ℂ)

theorem jqNModC_mem_EL : jqNModC ℂ (M * ℓ) ∈ laurentBaseChange ℂ (FF' M H ℓ) := by
  haveI : NeZero (M * ℓ) := NeZero.mul
  rw [← coeffEmb_jqNModC]
  refine coeffEmb_mem_laurentBaseChange ℂ ?_
  have h1 : jqNModC ℚ (M * ℓ) ∈ modularFunctionFieldFullC ℚ (M * ℓ) :=
    jqModCd_mem_full ℚ (M * ℓ) (dvd_refl _)
  have h2 := ModularCurve.modularFunctionFieldFullC_le_qExpFunctionFieldC_gamma0 ℚ (M * ℓ) h1
  exact qExpFunctionFieldC_mono ℚ (inf_le_right : Gam' M H ℓ ≤ Gamma0 (M * ℓ)) h2

theorem relrank_C_ge (hℓM : ℓ ∣ M) :
    (ℓ : Cardinal) ≤ relrank (laurentBaseChange ℂ (FF M H)) (laurentBaseChange ℂ (FF' M H ℓ)) := by
  haveI : NeZero (M * ℓ) := NeZero.mul
  have h23 := ModularCurve.relIndex_gamma0_le_relrank_adjoin_insert_jqNModC (Gam M H)
    (translation_mem_GammaH M H) (M * ℓ)
  rw [relIndex_Gamma0_mul_Gam M H ℓ hℓM] at h23
  change (ℓ : Cardinal) ≤ relrank (An (Gam M H))
    (adjoin ℂ (insert (jqNModC ℂ (M * ℓ)) (anSet (Gam M H)))) at h23
  have hle1 : An (Gam M H) ≤ adjoin ℂ (insert (jqNModC ℂ (M * ℓ)) (anSet (Gam M H))) :=
    adjoin.mono ℂ _ _ (Set.subset_insert _ _)
  have hle2 : adjoin ℂ (insert (jqNModC ℂ (M * ℓ)) (anSet (Gam M H))) ≤
      laurentBaseChange ℂ (FF' M H ℓ) := by
    rw [adjoin_le_iff, Set.insert_subset_iff]
    refine ⟨jqNModC_mem_EL M H ℓ, ?_⟩
    have h : anSet (Gam M H) ⊆ (An (Gam M H) : Set (LaurentSeries ℂ)) := subset_adjoin ℂ _
    refine h.trans ?_
    rw [← laurentBaseChange_FF_eq_An]
    exact KL_le_EL M H ℓ ℂ
  exact h23.trans (by rw [laurentBaseChange_FF_eq_An]; exact relrank_mono_right hle1 hle2)

end ComplexSide

section Assembly

variable [NeZero ℓ]

theorem relfinrank_FF_FF' (hℓM : ℓ ∣ M) : relfinrank (FF M H) (FF' M H ℓ) = ℓ := by
  have hC := relrank_C_le M H ℓ hℓM
  have hCge := relrank_C_ge M H ℓ hℓM
  have heq : relrank (laurentBaseChange ℂ (FF M H)) (laurentBaseChange ℂ (FF' M H ℓ)) = (ℓ : Cardinal) :=
    le_antisymm hC hCge
  rw [← relfinrank_KL_EL M H ℓ ℂ, relfinrank_eq_toNat_relrank, heq, Cardinal.toNat_natCast]

end Assembly

end FinrankAlphaHDvdSol
p2m_reactivate "P2MW.S_ModularCurve_finrankAlong_heckeAlphaHBar_of_dvd.FinrankAlphaHDvdSol"

theorem solution (L : Type*) [Field L] [Algebra ℚ L] (M : ℕ) [NeZero M]
    (H : Subgroup (ZMod M)ˣ) (p : ℕ) [NeZero p] (hpM : p ∣ M) :
    AlgebraicCurve.finrankAlong L (ModularCurve.heckeAlphaHBar L M H p) = p := by
  rw [FinrankAlphaHDvdSol.finrankAlong_alpha, FinrankAlphaHDvdSol.relfinrank_KL_EL,
    FinrankAlphaHDvdSol.relfinrank_FF_FF' M H p hpM]

end
p2m_reactivate "P2MW.S_ModularCurve_finrankAlong_heckeAlphaHBar_of_dvd.FinrankAlphaHDvdSol"

end S_ModularCurve_finrankAlong_heckeAlphaHBar_of_dvd
end P2MW
export P2MW.S_ModularCurve_finrankAlong_heckeAlphaHBar_of_dvd (solution)
