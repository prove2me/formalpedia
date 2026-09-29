-- Prove2me | solution 1 for ModularCurve.finrank_adjoin_jqModC_laurentBaseChange_qExpFunctionFieldC_gammaH_eq_index
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/f71d6460-6439-5c89-ba59-c4b3d099b83a

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_ModularCurve_XH
import Definitions.Def_ModularCurve_X0ModL
import Theorems.Thm_ModularCurve_finrank_adjoin_jqModC_laurentBaseChange_qExpFunctionFieldC_le_index
import Theorems.Thm_ModularCurve_index_le_relfinrank_qExpFunctionFieldC_gamma0_gammaH_of_charZero
import Theorems.Thm_ModularCurve_dedekindPsi_le_finrank_adjoin_qExpFunctionFieldC_gamma0
import Theorems.Thm_ModularCurve_finrank_adjoin_jqModC_qExpFunctionFieldC_le_index_of_isAlgClosed
import Theorems.Thm_CohCarrier_index_gammaH_eq_index_gamma0_mul_index
import Theorems.Thm_ModularCurve_Gamma0_index
import Theorems.Thm_ModularCurve_jqModC_mem_intFormRatiosC
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_finrank_adjoin_jqModC_laurentBaseChange_qExpFunctionFieldC_gammaH_eq_index
p2m_attr_erase "instance" "ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid"
p2m_attr_erase "simp" "ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero"
p2m_attr_erase "simp" "ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ"
p2m_attr_erase "simp" "ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply ModularCurve.ProjectiveLine.map_mk"

set_option autoImplicit false

namespace ModularCurve
p2m_export "ModularCurve" "intSeriesC intFormRatiosC qExpFunctionFieldC intFormRatiosC_subset qExpFunctionFieldC_mono dedekindPsi coeffMap_single coeffEmb coeffEmb_coeff laurentBaseChange jqModC translation_mem_GammaH Gamma1_le_GammaH GammaH_mono coeffMap_ofPowerSeries finrank_adjoin_jqModC_laurentBaseChange_qExpFunctionFieldC_le_index index_le_relfinrank_qExpFunctionFieldC_gamma0_gammaH_of_charZero dedekindPsi_le_finrank_adjoin_qExpFunctionFieldC_gamma0 finrank_adjoin_jqModC_qExpFunctionFieldC_le_index_of_isAlgClosed Gamma0_index jqModC_mem_intFormRatiosC"
namespace FullnessGammaH
p2m_open "ModularCurve~coeffEmb_injective"

p2m_open "ModularCurve~coeffEmb_injective P2MW.S_ModularCurve_finrank_adjoin_jqModC_laurentBaseChange_qExpFunctionFieldC_gammaH_eq_index.ModularCurve IntermediateField"

theorem finrank_adjoin_eq_relfinrank {K E : Type*} [Field K] [Field E] [Algebra K E]
    (F : IntermediateField K E) (x : F) :
    Module.finrank (IntermediateField.adjoin K ({x} : Set F)) F =
      (IntermediateField.adjoin K ({(x : E)} : Set E)).relfinrank F := by
  have hlift : IntermediateField.lift (IntermediateField.adjoin K ({x} : Set F)) =
      IntermediateField.adjoin K ({(x : E)} : Set E) := by
    rw [IntermediateField.lift_adjoin]; simp
  have hle : IntermediateField.adjoin K ({(x : E)} : Set E) ≤ F := by
    rw [← hlift]; exact IntermediateField.lift_le _
  rw [IntermediateField.relfinrank_eq_finrank_of_le hle]
  let i : (IntermediateField.adjoin K ({x} : Set F)) ≃+*
      (IntermediateField.adjoin K ({(x : E)} : Set E)) :=
    ((IntermediateField.liftAlgEquiv (IntermediateField.adjoin K ({x} : Set F))).trans
      (IntermediateField.equivOfEq hlift)).toRingEquiv
  let j : F ≃+* (IntermediateField.extendScalars hle) := RingEquiv.refl _
  refine Algebra.finrank_eq_of_equiv_equiv i j ?_
  ext a
  rfl

section BaseChange

variable (K : Type*) [Field K] [Algebra ℚ K]

theorem coeffEmb_injective : Function.Injective (coeffEmb K) := by
  intro x y h
  ext n
  have h1 := congrArg (fun s : LaurentSeries K => s.coeff n) h
  simp only [coeffEmb_coeff] at h1
  exact (algebraMap ℚ K).injective h1

theorem coeffEmb_ne_zero_iff (x : LaurentSeries ℚ) : coeffEmb K x ≠ 0 ↔ x ≠ 0 := by
  rw [Ne, ← map_zero (coeffEmb K), (coeffEmb_injective K).eq_iff]

theorem coeffEmb_intSeriesC (p : PowerSeries ℤ) : coeffEmb K (intSeriesC ℚ p) = intSeriesC K p := by
  rw [coeffEmb, intSeriesC, intSeriesC, coeffMap_ofPowerSeries]
  congr 1
  ext n
  simp [PowerSeries.coeff_map]

theorem algebraMap_laurentSeries_eq_C {L : Type*} [Field L] (a : L) :
    algebraMap L (LaurentSeries L) a = HahnSeries.C a := by
  rw [HahnSeries.algebraMap_apply']
  have h1 : algebraMap L (PowerSeries L) a = PowerSeries.C a := by simp
  rw [h1, HahnSeries.ofPowerSeries_C]

theorem coeffEmb_algebraMap (a : ℚ) :
    coeffEmb K (algebraMap ℚ (LaurentSeries ℚ) a) = algebraMap K (LaurentSeries K) (algebraMap ℚ K a) := by
  rw [algebraMap_laurentSeries_eq_C, algebraMap_laurentSeries_eq_C, HahnSeries.C_apply, HahnSeries.C_apply,
    coeffEmb, coeffMap_single]

variable (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ))

theorem image_intFormRatiosC : (coeffEmb K) '' intFormRatiosC ℚ Γ = intFormRatiosC K Γ := by
  ext z
  constructor
  · rintro ⟨y, ⟨w, f, g, pf, pg, hf, hg, hg0, rfl⟩, rfl⟩
    refine ⟨w, f, g, pf, pg, hf, hg, ?_, ?_⟩
    · rw [← coeffEmb_intSeriesC K]; exact (coeffEmb_ne_zero_iff K _).mpr hg0
    · rw [map_div₀, coeffEmb_intSeriesC, coeffEmb_intSeriesC]
  · rintro ⟨w, f, g, pf, pg, hf, hg, hg0, rfl⟩
    refine ⟨intSeriesC ℚ pf / intSeriesC ℚ pg, ⟨w, f, g, pf, pg, hf, hg, ?_, rfl⟩, ?_⟩
    · rw [← coeffEmb_ne_zero_iff K, coeffEmb_intSeriesC]; exact hg0
    · rw [map_div₀, coeffEmb_intSeriesC, coeffEmb_intSeriesC]

variable {Γ}

theorem coeffEmb_mem_adjoin {S : Set (LaurentSeries ℚ)} {y : LaurentSeries ℚ} (hy : y ∈ adjoin ℚ S) :
    coeffEmb K y ∈ adjoin K ((coeffEmb K) '' S) := by
  have hy' : y ∈ (adjoin ℚ S).toSubfield := hy
  rw [adjoin_toSubfield] at hy'
  have hle : Subfield.closure (Set.range (algebraMap ℚ (LaurentSeries ℚ)) ∪ S) ≤
      (adjoin K ((coeffEmb K) '' S)).toSubfield.comap (coeffEmb K) := by
    rw [Subfield.closure_le]
    rintro z (⟨a, rfl⟩ | hz)
    · change coeffEmb K (algebraMap ℚ (LaurentSeries ℚ) a) ∈ adjoin K ((coeffEmb K) '' S)
      rw [coeffEmb_algebraMap]
      exact IntermediateField.algebraMap_mem _ _
    · change coeffEmb K z ∈ adjoin K ((coeffEmb K) '' S)
      exact subset_adjoin K _ ⟨z, hz, rfl⟩
  exact hle hy'

variable (Γ)

theorem laurentBaseChange_qExpFunctionFieldC_eq :
    laurentBaseChange K (qExpFunctionFieldC ℚ Γ) = qExpFunctionFieldC K Γ := by
  apply le_antisymm
  · rw [laurentBaseChange, IntermediateField.adjoin_le_iff]
    rintro _ ⟨y, hy, rfl⟩
    have h := coeffEmb_mem_adjoin K (S := intFormRatiosC ℚ Γ) hy
    rwa [image_intFormRatiosC] at h
  · rw [qExpFunctionFieldC, ← image_intFormRatiosC K Γ, laurentBaseChange]
    exact IntermediateField.adjoin.mono K _ _ (Set.image_mono (intFormRatiosC_subset ℚ Γ))

end BaseChange

section Groups
open scoped MatrixGroups
open CongruenceSubgroup

theorem mem_or_neg_mem_of_mem_sup_zpowers_neg_one {M : ℕ} (H : Subgroup (ZMod M)ˣ)
    {d : (ZMod M)ˣ} (hd : d ∈ H ⊔ Subgroup.zpowers (-1 : (ZMod M)ˣ)) : d ∈ H ∨ -d ∈ H := by
  let S : Subgroup (ZMod M)ˣ :=
    { carrier := {x | x = 1 ∨ x = -1}
      one_mem' := Or.inl rfl
      mul_mem' := by
        rintro a b (rfl | rfl) (rfl | rfl) <;> simp
      inv_mem' := by
        rintro a (rfl | rfl) <;> simp }
  have hS : Subgroup.zpowers (-1 : (ZMod M)ˣ) ≤ S := by
    rw [Subgroup.zpowers_le]
    exact Or.inr rfl
  obtain ⟨h, hh, z, hz, rfl⟩ := Subgroup.mem_sup.mp hd
  rcases hS hz with hz1 | hz1
  · left; rw [hz1, mul_one]; exact hh
  · right; rw [hz1]; simpa using hh

theorem neg_mem_Gamma0 {M : ℕ} {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 M) : -γ ∈ Gamma0 M := by
  have := Gamma0_mem.mp hγ
  rw [Gamma0_mem]
  simp [Matrix.SpecialLinearGroup.coe_neg, this]

theorem gamma0Units_neg {M : ℕ} {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 M) :
    CohCarrier.gamma0Units M ⟨-γ, neg_mem_Gamma0 hγ⟩ = -CohCarrier.gamma0Units M ⟨γ, hγ⟩ := by
  ext
  simp [CohCarrier.gamma0Units, Gamma0Map, Matrix.SpecialLinearGroup.coe_neg]

theorem mem_or_neg_mem_gammaH_of_mem_gammaH_sup {M : ℕ} (H : Subgroup (ZMod M)ˣ) {γ : SL(2, ℤ)}
    (hγ : γ ∈ CohCarrier.GammaH M (H ⊔ Subgroup.zpowers (-1 : (ZMod M)ˣ))) :
    γ ∈ CohCarrier.GammaH M H ∨ -γ ∈ CohCarrier.GammaH M H := by
  obtain ⟨hγ0, hd⟩ := CohCarrier.mem_GammaH_iff.mp hγ
  rcases mem_or_neg_mem_of_mem_sup_zpowers_neg_one H hd with h | h
  · exact Or.inl (CohCarrier.mem_GammaH_iff.mpr ⟨hγ0, h⟩)
  · exact Or.inr (CohCarrier.mem_GammaH_iff.mpr ⟨neg_mem_Gamma0 hγ0, by rw [gamma0Units_neg hγ0]; exact h⟩)

theorem gammaH_sup_zpowers_neg_one_eq (M : ℕ) (H : Subgroup (ZMod M)ˣ) :
    CohCarrier.GammaH M H ⊔ Subgroup.zpowers (-1 : SL(2, ℤ)) =
      CohCarrier.GammaH M (H ⊔ Subgroup.zpowers (-1 : (ZMod M)ˣ)) := by
  apply le_antisymm
  · refine sup_le (ModularCurve.GammaH_mono le_sup_left) ?_
    rw [Subgroup.zpowers_le]
    have hm1 : (-1 : SL(2, ℤ)) ∈ Gamma0 M := neg_mem_Gamma0 (one_mem _)
    refine CohCarrier.mem_GammaH_iff.mpr ⟨hm1, ?_⟩
    have : CohCarrier.gamma0Units M ⟨-1, hm1⟩ = -1 := by
      have h := gamma0Units_neg (M := M) (one_mem (Gamma0 M))
      have h1 : CohCarrier.gamma0Units M ⟨1, one_mem _⟩ = 1 := map_one _
      rw [h1] at h
      convert h using 2
    rw [this]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
  · intro γ hγ
    rcases mem_or_neg_mem_gammaH_of_mem_gammaH_sup H hγ with h | h
    · exact Subgroup.mem_sup_left h
    · have : γ = (-1) * (-γ) := by simp
      rw [this]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_right (Subgroup.mem_zpowers _)) (Subgroup.mem_sup_left h)

end Groups

end ModularCurve.FullnessGammaH

p2m_open "ModularCurve~coeffEmb_injective P2MW.S_ModularCurve_finrank_adjoin_jqModC_laurentBaseChange_qExpFunctionFieldC_gammaH_eq_index.ModularCurve CongruenceSubgroup AlgebraicCurve"
open scoped MatrixGroups

open ModularCurve.FullnessGammaH IntermediateField in
set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 3200000 in
theorem solution
    (K : Type*) [Field K] [Algebra ℚ K] [IsAlgClosed K]
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ)
    (y : ↥(ModularCurve.laurentBaseChange K (ModularCurve.qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))))
    (hy : (y : LaurentSeries K) = ModularCurve.jqModC K) :
    Module.finrank
        ↥(IntermediateField.adjoin K ({y} : Set ↥(ModularCurve.laurentBaseChange K (ModularCurve.qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)))))
        ↥(ModularCurve.laurentBaseChange K (ModularCurve.qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))) =
      (CohCarrier.GammaH M H ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))).index := by
  classical
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ K).injective
  have hMK : (M : K) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne M)

  haveI hfi0 : (Gamma0 M).FiniteIndex := (CongruenceSubgroup.Gamma0_is_congruence M).finiteIndex
  have h10 : (CohCarrier.GammaH M H) ≤ Gamma0 M := CohCarrier.GammaH_le_Gamma0 H
  have hT1 : ModularGroup.T ∈ (CohCarrier.GammaH M H) := ModularCurve.translation_mem_GammaH M H
  have hT0 : ModularGroup.T ∈ Gamma0 M := h10 hT1
  have hsup := gammaH_sup_zpowers_neg_one_eq M H
  have hneg : ∀ γ ∈ (CohCarrier.GammaH M H) ⊔ Subgroup.zpowers (-1 : SL(2, ℤ)), γ ∈ (CohCarrier.GammaH M H) ∨ -γ ∈ (CohCarrier.GammaH M H) := by
    intro γ hγ
    rw [hsup] at hγ
    exact mem_or_neg_mem_gammaH_of_mem_gammaH_sup H hγ
  haveI hfiG : (CohCarrier.GammaH M H).FiniteIndex := by
    haveI : (Gamma1 M).FiniteIndex := (CongruenceSubgroup.Gamma1_is_congruence M).finiteIndex
    exact Subgroup.finiteIndex_of_le (ModularCurve.Gamma1_le_GammaH M H)

  have hle := ModularCurve.finrank_adjoin_jqModC_laurentBaseChange_qExpFunctionFieldC_le_index K
    (CohCarrier.GammaH M H) hT1 ((CohCarrier.GammaH M H) ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))) le_sup_left hneg y hy
  refine le_antisymm hle ?_

  have hidx : ((CohCarrier.GammaH M H) ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))).index =
      dedekindPsi M * (H ⊔ Subgroup.zpowers (-1 : (ZMod M)ˣ)).index := by
    rw [hsup, CohCarrier.index_gammaH_eq_index_gamma0_mul_index, ModularCurve.Gamma0_index]
  have hEE : laurentBaseChange K (qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) = qExpFunctionFieldC K (CohCarrier.GammaH M H) :=
    laurentBaseChange_qExpFunctionFieldC_eq K (CohCarrier.GammaH M H)
  have hF0E : qExpFunctionFieldC K (Gamma0 M) ≤ qExpFunctionFieldC K (CohCarrier.GammaH M H) :=
    ModularCurve.qExpFunctionFieldC_mono K h10
  have hjF0 : jqModC K ∈ qExpFunctionFieldC K (Gamma0 M) :=
    intFormRatiosC_subset K (Gamma0 M) (ModularCurve.jqModC_mem_intFormRatiosC K (Gamma0 M))
  have hJF0 : IntermediateField.adjoin K ({jqModC K} : Set (LaurentSeries K)) ≤ qExpFunctionFieldC K (Gamma0 M) :=
    IntermediateField.adjoin_le_iff.mpr (Set.singleton_subset_iff.mpr hjF0)
  have eJE' : Module.finrank
        ↥(IntermediateField.adjoin K ({y} : Set ↥(laurentBaseChange K (qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)))))
        ↥(laurentBaseChange K (qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))) =
      (IntermediateField.adjoin K ({jqModC K} : Set (LaurentSeries K))).relfinrank
        (laurentBaseChange K (qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))) := by
    have h := finrank_adjoin_eq_relfinrank (laurentBaseChange K (qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))) y
    rw [hy] at h
    exact h
  have eJF0 : dedekindPsi M ≤
      (IntermediateField.adjoin K ({jqModC K} : Set (LaurentSeries K))).relfinrank (qExpFunctionFieldC K (Gamma0 M)) := by
    obtain ⟨hfin, -⟩ := ModularCurve.finrank_adjoin_jqModC_qExpFunctionFieldC_le_index_of_isAlgClosed K
      (Gamma0 M) hT0 (Gamma0 M) le_rfl (fun γ hγ => Or.inl hγ) ⟨jqModC K, hjF0⟩ rfl
    haveI := hfin
    have h := ModularCurve.dedekindPsi_le_finrank_adjoin_qExpFunctionFieldC_gamma0 K M hMK ⟨jqModC K, hjF0⟩ rfl
    have e := finrank_adjoin_eq_relfinrank (qExpFunctionFieldC K (Gamma0 M)) ⟨jqModC K, hjF0⟩
    exact e ▸ h
  have eF0E : (H ⊔ Subgroup.zpowers (-1 : (ZMod M)ˣ)).index ≤
      (qExpFunctionFieldC K (Gamma0 M)).relfinrank (qExpFunctionFieldC K (CohCarrier.GammaH M H)) :=
    ModularCurve.index_le_relfinrank_qExpFunctionFieldC_gamma0_gammaH_of_charZero K M H
  have t1 := IntermediateField.relfinrank_mul_relfinrank hJF0 hF0E
  have key : dedekindPsi M * (H ⊔ Subgroup.zpowers (-1 : (ZMod M)ˣ)).index ≤
      (IntermediateField.adjoin K ({jqModC K} : Set (LaurentSeries K))).relfinrank
        (laurentBaseChange K (qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))) := by
    rw [hEE, ← t1]
    exact Nat.mul_le_mul eJF0 eF0E
  calc ((CohCarrier.GammaH M H) ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))).index
      = dedekindPsi M * (H ⊔ Subgroup.zpowers (-1 : (ZMod M)ˣ)).index := hidx
    _ ≤ (IntermediateField.adjoin K ({jqModC K} : Set (LaurentSeries K))).relfinrank
        (laurentBaseChange K (qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))) := key
    _ = _ := eJE'.symm

end S_ModularCurve_finrank_adjoin_jqModC_laurentBaseChange_qExpFunctionFieldC_gammaH_eq_index
end P2MW
export P2MW.S_ModularCurve_finrank_adjoin_jqModC_laurentBaseChange_qExpFunctionFieldC_gammaH_eq_index (solution)
