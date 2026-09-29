-- Prove2me | solution 1 for ModularCurve.FullLevel.relfinrank_adjoin_qExpand_image_laurentBaseChange_gamma0_fieldBar_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/4c5a5ff3-67a6-563d-8f28-790be0cb779c

import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_X0ModL
import Definitions.Def_CohCarrier_Level
import Theorems.Thm_ModularCurve_finrank_adjoin_jqModC_laurentBaseChange_qExpFunctionFieldC_gamma0_eq_index
import Theorems.Thm_ModularCurve_finiteDimensional_and_finrank_adjoin_jqModC_qExpFunctionFieldC_le_index
import Theorems.Thm_ModularCurve_transcendental_and_finiteDimensional_adjoin_laurentBaseChange_qExpFunctionFieldC_of_coe_eq_jqModC
import Theorems.Thm_ModularCurve_exists_algEquiv_swap_jqModC_jqNModC_modularFunctionFieldFullC
import Theorems.Thm_ModularCurve_relfinrank_qExpFunctionFieldC_gamma0_gammaH_eq_index_of_charZero
import Theorems.Thm_ModularCurve_Gamma0_index
import Theorems.Thm_CohCarrier_index_gammaH_eq_index_gamma0_mul_index
import Theorems.Thm_ModularCurve_dedekindPsi_mul_prime
import Theorems.Thm_ModularCurve_FullLevel_qExpand_coe_mem_fieldBar_of_mem
import Theorems.Thm_ModularCurve_jqModC_mem_intFormRatiosC
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_relfinrank_adjoin_qExpand_image_laurentBaseChange_gamma0_fieldBar_ne_zero
p2m_attr_erase "instance" "ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid"
p2m_attr_erase "simp" "ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal"
p2m_attr_erase "simp" "AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen"
p2m_attr_erase "simp" "ModularCurve.constantCoeff_dedekindEtaUnitQ WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply ModularCurve.ProjectiveLine.map_mk"

set_option autoImplicit false

p2m_open "AlgebraicCurve ModularCurve P2MW.S_ModularCurve_FullLevel_relfinrank_adjoin_qExpand_image_laurentBaseChange_gamma0_fieldBar_ne_zero.ModularCurve ModularCurve.FullLevel P2MW.S_ModularCurve_FullLevel_relfinrank_adjoin_qExpand_image_laurentBaseChange_gamma0_fieldBar_ne_zero.ModularCurve.FullLevel IsLocalRing CongruenceSubgroup IntermediateField"
open scoped MatrixGroups

noncomputable section

namespace ModularCurve
p2m_export "ModularCurve" "xHFunctionFieldBar intSeriesC intFormRatiosC qExpFunctionFieldC intFormRatiosC_subset div_mem_qExpFunctionFieldC qExpFunctionFieldC_mono qExpand qExpand_C qExpand_one_apply dedekindPsi coeffMap_single algebraMap_laurentSeries_eq_single coeffEmb laurentBaseChange coeffEmb_mem_laurentBaseChange jqModC jqNModC map_jqModC coeffMap_ofPowerSeries modularFunctionFieldFullC jqModCd_mem_full jqModC_mem_full finrank_adjoin_jqModC_laurentBaseChange_qExpFunctionFieldC_gamma0_eq_index finiteDimensional_and_finrank_adjoin_jqModC_qExpFunctionFieldC_le_index exists_algEquiv_swap_jqModC_jqNModC_modularFunctionFieldFullC relfinrank_qExpFunctionFieldC_gamma0_gammaH_eq_index_of_charZero Gamma0_index dedekindPsi_mul_prime FullLevel.qExpand_coe_mem_fieldBar_of_mem jqModC_mem_intFormRatiosC"
namespace FullLevel
p2m_export "ModularCurve.FullLevel" "dvd_sq_mul levelH mem_levelH_iff fieldBar qExpand_coe_mem_fieldBar_of_mem"
namespace K1Road
p2m_open "ModularCurve.FullLevel ModularCurve"

variable (q : ℕ) [Fact q.Prime] (M : ℕ) [NeZero M]

abbrev Kone : IntermediateField (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) :=
  laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (Gamma0 (q * M)))

def qExpandBar (N : ℕ) [NeZero N] :
    LaurentSeries (AlgebraicClosure ℚ) →ₐ[AlgebraicClosure ℚ] LaurentSeries (AlgebraicClosure ℚ) where
  __ := qExpand (AlgebraicClosure ℚ) N
  commutes' r := by
    show qExpand (AlgebraicClosure ℚ) N (algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) r) =
      algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) r
    have h1 : algebraMap (AlgebraicClosure ℚ) (PowerSeries (AlgebraicClosure ℚ)) r = PowerSeries.C r := by
      simp
    rw [HahnSeries.algebraMap_apply', h1, HahnSeries.ofPowerSeries_C, qExpand_C]

@[scoped simp] theorem qExpandBar_apply (N : ℕ) [NeZero N] (f : LaurentSeries (AlgebraicClosure ℚ)) :
    qExpandBar N f = qExpand (AlgebraicClosure ℚ) N f := rfl

def KB : IntermediateField (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) :=
  (Kone q M).map (qExpandBar q)

omit [NeZero M] in
theorem mem_KB_iff (x : LaurentSeries (AlgebraicClosure ℚ)) :
    x ∈ KB q M ↔ ∃ g ∈ Kone q M, qExpand (AlgebraicClosure ℚ) q g = x := by
  simp [KB, IntermediateField.mem_map]

theorem q_mul_dvd_sq_mul : q * M ∣ q ^ 2 * M := ⟨q, by ring⟩

abbrev Hsharp : Subgroup (ZMod (q ^ 2 * M))ˣ := (ZMod.unitsMap (q_mul_dvd_sq_mul q M)).ker

abbrev Fsharp : IntermediateField (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) :=
  xHFunctionFieldBar (q ^ 2 * M) (Hsharp q M)

private theorem _root_.ModularCurve.FullLevel.K1Road.qExpand_coe_mem_fieldBar_of_mem (hqM : ¬ q ∣ M)
    (g : LaurentSeries (AlgebraicClosure ℚ)) (hg : g ∈ Kone q M) :
    qExpand (AlgebraicClosure ℚ) q g ∈ fieldBar q M :=
  ModularCurve.FullLevel.qExpand_coe_mem_fieldBar_of_mem q M hqM g hg

p2m_export "ModularCurve.FullLevel.K1Road" "qExpand_coe_mem_fieldBar_of_mem"
omit [Fact q.Prime] [NeZero M] in
theorem laurentBaseChange_mono {F₁ F₂ : IntermediateField ℚ (LaurentSeries ℚ)} (h : F₁ ≤ F₂) :
    laurentBaseChange (AlgebraicClosure ℚ) F₁ ≤ laurentBaseChange (AlgebraicClosure ℚ) F₂ := by
  rw [laurentBaseChange, laurentBaseChange]
  exact IntermediateField.adjoin.mono _ _ _ (Set.image_mono h)

omit [Fact q.Prime] [NeZero M] in
theorem gammaH_mono {N : ℕ} {H₁ H₂ : Subgroup (ZMod N)ˣ} (h : H₁ ≤ H₂) :
    CohCarrier.GammaH N H₁ ≤ CohCarrier.GammaH N H₂ := by
  intro A hA
  obtain ⟨hA0, hH⟩ := CohCarrier.mem_GammaH_iff.mp hA
  exact CohCarrier.mem_GammaH_iff.mpr ⟨hA0, h hH⟩

theorem Hsharp_le_levelH : Hsharp q M ≤ levelH q M := by
  intro u hu
  rw [MonoidHom.mem_ker] at hu
  rw [mem_levelH_iff]
  have hcomp : ZMod.unitsMap (dvd_sq_mul q M) =
      (ZMod.unitsMap (dvd_mul_right q M)).comp (ZMod.unitsMap (q_mul_dvd_sq_mul q M)) :=
    (ZMod.unitsMap_comp (dvd_mul_right q M) (q_mul_dvd_sq_mul q M)).symm
  rw [hcomp, MonoidHom.comp_apply, hu, map_one]

theorem fieldBar_le_Fsharp : fieldBar q M ≤ Fsharp q M :=
  laurentBaseChange_mono (qExpFunctionFieldC_mono ℚ (gammaH_mono (Hsharp_le_levelH q M)))

theorem KB_le_fieldBar (hqM : ¬ q ∣ M) : KB q M ≤ fieldBar q M := by
  intro x hx
  obtain ⟨g, hg, rfl⟩ := (mem_KB_iff q M x).mp hx
  exact qExpand_coe_mem_fieldBar_of_mem q M hqM g hg

theorem KB_le_Fsharp (hqM : ¬ q ∣ M) : KB q M ≤ Fsharp q M :=
  (KB_le_fieldBar q M hqM).trans (fieldBar_le_Fsharp q M)

section WithFact

variable [hqM : Fact (¬ q ∣ M)]

scoped instance algebraKB : Algebra (KB q M) (fieldBar q M) :=
  (IntermediateField.inclusion (KB_le_fieldBar q M hqM.out)).toRingHom.toAlgebra

scoped instance moduleKB : Module (KB q M) (fieldBar q M) := (algebraKB q M).toModule

scoped instance algebraKBsharp : Algebra (KB q M) (Fsharp q M) :=
  (IntermediateField.inclusion (KB_le_Fsharp q M hqM.out)).toRingHom.toAlgebra

scoped instance moduleKBsharp : Module (KB q M) (Fsharp q M) := (algebraKBsharp q M).toModule

def inclSharp : fieldBar q M →+* Fsharp q M :=
  (IntermediateField.inclusion (fieldBar_le_Fsharp q M)).toRingHom

theorem coe_inclSharp (x : fieldBar q M) :
    ((inclSharp q M x : Fsharp q M) : LaurentSeries (AlgebraicClosure ℚ)) = x :=
  IntermediateField.coe_inclusion (fieldBar_le_Fsharp q M) x

theorem inclSharp_comp_algebraMap :
    (inclSharp q M).comp (algebraMap (KB q M) (fieldBar q M)) = algebraMap (KB q M) (Fsharp q M) :=
  RingHom.ext fun _ => rfl

theorem coe_algebraMap_KB (x : KB q M) :
    ((algebraMap (KB q M) (fieldBar q M) x : fieldBar q M) : LaurentSeries (AlgebraicClosure ℚ)) = x := rfl

theorem coe_algebraMap_KBsharp (x : KB q M) :
    ((algebraMap (KB q M) (Fsharp q M) x : Fsharp q M) : LaurentSeries (AlgebraicClosure ℚ)) = x := rfl

theorem finrank_KB_eq_relfinrank :
    Module.finrank (KB q M) (fieldBar q M) = (KB q M).relfinrank (fieldBar q M) := by
  rw [IntermediateField.relfinrank_eq_finrank_of_le (KB_le_fieldBar q M hqM.out)]
  rfl

theorem finrank_KB_Fsharp_eq_relfinrank :
    Module.finrank (KB q M) (Fsharp q M) = (KB q M).relfinrank (Fsharp q M) := by
  rw [IntermediateField.relfinrank_eq_finrank_of_le (KB_le_Fsharp q M hqM.out)]
  rfl

end WithFact

section Count

theorem coeffEmb_intSeriesC (L : Type*) [Field L] [Algebra ℚ L] (p : PowerSeries ℤ) :
    coeffEmb L (intSeriesC ℚ p) = intSeriesC L p := by
  rw [coeffEmb, intSeriesC, intSeriesC, ModularCurve.coeffMap_ofPowerSeries]
  congr 1
  ext n
  simp only [PowerSeries.coeff_map, eq_intCast, map_intCast]

theorem laurentBaseChange_qExpFunctionFieldC_le (L : Type*) [Field L] [Algebra ℚ L] (Γ : Subgroup SL(2, ℤ)) :
    laurentBaseChange L (qExpFunctionFieldC ℚ Γ) ≤ qExpFunctionFieldC L Γ := by
  rw [laurentBaseChange, IntermediateField.adjoin_le_iff]
  rintro _ ⟨x, hx, rfl⟩
  rw [SetLike.mem_coe]
  have hx' : x ∈ IntermediateField.adjoin ℚ (intFormRatiosC ℚ Γ) := hx
  clear hx
  induction hx' using IntermediateField.adjoin_induction with
  | mem z hz =>
    obtain ⟨k, f, g, pf, pg, hf, hg, hg0, rfl⟩ := hz
    have hg0' : intSeriesC L pg ≠ 0 := by
      rw [← coeffEmb_intSeriesC L]
      intro h
      exact hg0 ((coeffEmb L).injective (by rw [h, map_zero]))
    rw [map_div₀, coeffEmb_intSeriesC, coeffEmb_intSeriesC]
    exact div_mem_qExpFunctionFieldC f g hf hg hg0'
  | algebraMap r =>
    rw [algebraMap_laurentSeries_eq_single, coeffEmb, coeffMap_single]
    have e : HahnSeries.single 0 (algebraMap ℚ L r) = algebraMap L (LaurentSeries L) (algebraMap ℚ L r) :=
      (algebraMap_laurentSeries_eq_single L _).symm
    rw [e]
    exact IntermediateField.algebraMap_mem _ _
  | add z w _ _ hz hw => rw [map_add]; exact add_mem hz hw
  | inv z _ hz => rw [map_inv₀]; exact inv_mem hz
  | mul z w _ _ hz hw => rw [map_mul]; exact mul_mem hz hw

theorem relfinrank_adjoin_singleton_eq_finrank {K E : Type*} [Field K] [Field E] [Algebra K E]
    (X : IntermediateField K E) (y : ↥X) :
    (IntermediateField.adjoin K {(y : E)}).relfinrank X =
      Module.finrank ↥(IntermediateField.adjoin K ({y} : Set ↥X)) ↥X := by
  have h := IntermediateField.relfinrank_map_map (IntermediateField.adjoin K ({y} : Set ↥X))
    (⊤ : IntermediateField K ↥X) X.val
  have htop : (⊤ : IntermediateField K ↥X).map X.val = X := by
    rw [← AlgHom.fieldRange_eq_map, IntermediateField.fieldRange_val]
  rw [IntermediateField.adjoin_map, Set.image_singleton, IntermediateField.relfinrank_top_right, htop] at h
  exact h

def J : IntermediateField (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) :=
  IntermediateField.adjoin (AlgebraicClosure ℚ) {jqModC (AlgebraicClosure ℚ)}

def Jq : IntermediateField (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) :=
  IntermediateField.adjoin (AlgebraicClosure ℚ) {qExpand (AlgebraicClosure ℚ) q (jqModC (AlgebraicClosure ℚ))}

abbrev JJ : IntermediateField (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) :=
  modularFunctionFieldFullC (AlgebraicClosure ℚ) q

omit [Fact q.Prime] [NeZero M] in
theorem J_le_JJ : J ≤ JJ q := by
  rw [J, IntermediateField.adjoin_le_iff, Set.singleton_subset_iff]
  exact jqModC_mem_full (AlgebraicClosure ℚ) q

omit [NeZero M] in
theorem Jq_le_JJ : Jq q ≤ JJ q := by
  rw [Jq, IntermediateField.adjoin_le_iff, Set.singleton_subset_iff]
  exact jqModCd_mem_full (AlgebraicClosure ℚ) q (dvd_refl q)

omit [NeZero M] in
theorem Jq_eq_map_J : Jq q = (J).map (qExpandBar q) := by
  rw [J, IntermediateField.adjoin_map, Set.image_singleton]
  rfl

theorem jqModC_mem_laurentBaseChange (Γ : Subgroup SL(2, ℤ)) :
    jqModC (AlgebraicClosure ℚ) ∈ laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ Γ) := by
  have h1 : jqModC ℚ ∈ (qExpFunctionFieldC ℚ Γ : Set (LaurentSeries ℚ)) :=
    intFormRatiosC_subset ℚ _ (ModularCurve.jqModC_mem_intFormRatiosC ℚ _)
  have h2 := coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) h1
  rwa [show coeffEmb (AlgebraicClosure ℚ) (jqModC ℚ) = jqModC (AlgebraicClosure ℚ) from map_jqModC _] at h2

omit [Fact q.Prime] [NeZero M] in
theorem J_le_Kone : J ≤ Kone q M := by
  rw [J, IntermediateField.adjoin_le_iff, Set.singleton_subset_iff]
  exact jqModC_mem_laurentBaseChange _

omit [NeZero M] in
theorem Jq_le_KB : Jq q ≤ KB q M := by
  rw [Jq_eq_map_J]
  exact IntermediateField.map_mono _ (J_le_Kone q M)

theorem JJ_le_fieldBar (hqM : ¬ q ∣ M) : JJ q ≤ fieldBar q M := by
  rw [JJ, modularFunctionFieldFullC, IntermediateField.adjoin_le_iff]
  rintro x ⟨d, hd0, hd, rfl⟩
  rcases (Nat.dvd_prime (Fact.out : q.Prime)).mp hd with h1 | hq'
  · subst h1
    rw [SetLike.mem_coe, qExpand_one_apply]
    exact jqModC_mem_laurentBaseChange _
  · subst hq'
    exact ModularCurve.FullLevel.qExpand_coe_mem_fieldBar_of_mem d M hqM _ (jqModC_mem_laurentBaseChange _)

theorem relfinrank_J_Kone :
    (J).relfinrank (Kone q M) = (Gamma0 (q * M) ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))).index := by
  haveI : NeZero (q * M) := ⟨mul_ne_zero (Fact.out : q.Prime).ne_zero (NeZero.ne M)⟩
  let y : ↥(Kone q M) := ⟨jqModC (AlgebraicClosure ℚ), jqModC_mem_laurentBaseChange _⟩
  have h := relfinrank_adjoin_singleton_eq_finrank (Kone q M) y
  exact h.trans (ModularCurve.finrank_adjoin_jqModC_laurentBaseChange_qExpFunctionFieldC_gamma0_eq_index
    (AlgebraicClosure ℚ) (q * M) y rfl)

theorem relfinrank_Jq_KB :
    (Jq q).relfinrank (KB q M) = (Gamma0 (q * M) ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))).index := by
  rw [Jq_eq_map_J, KB, IntermediateField.relfinrank_map_map, relfinrank_J_Kone]

omit [NeZero M] in

theorem relfinrank_J_JJ_eq_relfinrank_Jq_JJ : (J).relfinrank (JJ q) = (Jq q).relfinrank (JJ q) := by
  have hq0 : ((q : ℕ) : AlgebraicClosure ℚ) ≠ 0 := by exact_mod_cast (Fact.out : q.Prime).ne_zero
  obtain ⟨σ, h1, -, -⟩ :=
    ModularCurve.exists_algEquiv_swap_jqModC_jqNModC_modularFunctionFieldFullC (AlgebraicClosure ℚ) q hq0
  set y1 : ↥(JJ q) := ⟨jqModC (AlgebraicClosure ℚ), jqModC_mem_full (AlgebraicClosure ℚ) q⟩ with hy1
  set y2 : ↥(JJ q) := ⟨jqNModC (AlgebraicClosure ℚ) q, jqModCd_mem_full (AlgebraicClosure ℚ) q (dvd_refl q)⟩ with hy2
  have e1 : (J).relfinrank (JJ q) = Module.finrank ↥(IntermediateField.adjoin (AlgebraicClosure ℚ) ({y1} : Set ↥(JJ q))) ↥(JJ q) :=
    relfinrank_adjoin_singleton_eq_finrank (JJ q) y1
  have e2 : (Jq q).relfinrank (JJ q) = Module.finrank ↥(IntermediateField.adjoin (AlgebraicClosure ℚ) ({y2} : Set ↥(JJ q))) ↥(JJ q) :=
    relfinrank_adjoin_singleton_eq_finrank (JJ q) y2
  rw [e1, e2]

  have h := IntermediateField.relfinrank_map_map (IntermediateField.adjoin (AlgebraicClosure ℚ) ({y1} : Set ↥(JJ q)))
    (⊤ : IntermediateField (AlgebraicClosure ℚ) ↥(JJ q)) σ.toAlgHom
  have htop : (⊤ : IntermediateField (AlgebraicClosure ℚ) ↥(JJ q)).map σ.toAlgHom = ⊤ := by
    rw [← AlgHom.fieldRange_eq_map]
    exact AlgEquiv.fieldRange_eq_top σ
  have hσy : σ.toAlgHom y1 = y2 := h1
  rw [IntermediateField.adjoin_map, Set.image_singleton, hσy, htop, IntermediateField.relfinrank_top_right,
    IntermediateField.relfinrank_top_right] at h
  exact h.symm

omit [Fact q.Prime] [NeZero M] in

theorem relfinrank_J_laurentBaseChange_gammaH_ne_zero_and_le (N : ℕ) [NeZero N] (H : Subgroup (ZMod N)ˣ) :
    (J).relfinrank (laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (CohCarrier.GammaH N H))) ≠ 0 ∧
    (J).relfinrank (laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (CohCarrier.GammaH N H))) ≤
      dedekindPsi N * (H ⊔ Subgroup.zpowers (-1 : (ZMod N)ˣ)).index := by
  set FH : IntermediateField (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) :=
    qExpFunctionFieldC (AlgebraicClosure ℚ) (CohCarrier.GammaH N H) with hFH
  set F0 : IntermediateField (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) :=
    qExpFunctionFieldC (AlgebraicClosure ℚ) (Gamma0 N) with hF0
  have hFB : laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (CohCarrier.GammaH N H)) ≤ FH := laurentBaseChange_qExpFunctionFieldC_le (AlgebraicClosure ℚ) _
  have hjF0 : jqModC (AlgebraicClosure ℚ) ∈ F0 :=
    intFormRatiosC_subset (AlgebraicClosure ℚ) _ (ModularCurve.jqModC_mem_intFormRatiosC (AlgebraicClosure ℚ) _)
  have hJF0 : J ≤ F0 := by
    rw [J, IntermediateField.adjoin_le_iff, Set.singleton_subset_iff]; exact hjF0
  have hF0FH : F0 ≤ FH := qExpFunctionFieldC_mono (AlgebraicClosure ℚ) (CohCarrier.GammaH_le_Gamma0 H)
  have hJFB : J ≤ laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (CohCarrier.GammaH N H)) := by
    rw [J, IntermediateField.adjoin_le_iff, Set.singleton_subset_iff]; exact jqModC_mem_laurentBaseChange _

  have hψ0 : dedekindPsi N ≠ 0 := by
    have h1 : (1 : ℕ) ∈ N.divisors.filter Squarefree :=
      Finset.mem_filter.mpr ⟨Nat.one_mem_divisors.mpr (NeZero.ne N), squarefree_one⟩
    have h := Finset.single_le_sum (f := fun d => N / d) (fun _ _ => Nat.zero_le _) h1
    simp only [Nat.div_one] at h
    exact (lt_of_lt_of_le (Nat.pos_of_ne_zero (NeZero.ne N)) h).ne'
  haveI hfi0 : (Gamma0 N).FiniteIndex := ⟨by rw [ModularCurve.Gamma0_index]; exact hψ0⟩
  haveI hfiH : (CohCarrier.GammaH N H).FiniteIndex := by
    refine ⟨?_⟩
    rw [CohCarrier.index_gammaH_eq_index_gamma0_mul_index, ModularCurve.Gamma0_index]
    exact mul_ne_zero hψ0 Subgroup.FiniteIndex.index_ne_zero
  have hT0 : ModularGroup.T ∈ Gamma0 N := by
    rw [CongruenceSubgroup.Gamma0_mem]; simp [ModularGroup.T]
  have hTH : ModularGroup.T ∈ CohCarrier.GammaH N H := by
    rw [CohCarrier.mem_GammaH_iff]
    refine ⟨hT0, ?_⟩
    have h1 : CohCarrier.gamma0Units N ⟨ModularGroup.T, hT0⟩ = 1 :=
      Units.ext (by simp [CohCarrier.val_gamma0Units, CongruenceSubgroup.Gamma0Map, ModularGroup.T])
    rw [h1]
    exact one_mem _

  let xH : ↥FH := ⟨jqModC (AlgebraicClosure ℚ), hF0FH hjF0⟩
  obtain ⟨hfinH, -⟩ := ModularCurve.finiteDimensional_and_finrank_adjoin_jqModC_qExpFunctionFieldC_le_index
    (AlgebraicClosure ℚ) (CohCarrier.GammaH N H) hTH (CohCarrier.GammaH N H) le_rfl
    (fun γ hγ => Or.inl hγ) xH rfl
  let x0 : ↥F0 := ⟨jqModC (AlgebraicClosure ℚ), hjF0⟩
  obtain ⟨-, hle0⟩ := ModularCurve.finiteDimensional_and_finrank_adjoin_jqModC_qExpFunctionFieldC_le_index
    (AlgebraicClosure ℚ) (Gamma0 N) hT0 (Gamma0 N) le_rfl (fun γ hγ => Or.inl hγ) x0 rfl
  haveI : Module.Finite ↥(IntermediateField.adjoin (AlgebraicClosure ℚ) ({xH} : Set ↥FH)) ↥FH := hfinH
  have hRJFH : (J).relfinrank FH ≠ 0 := by
    rw [show J = IntermediateField.adjoin (AlgebraicClosure ℚ) {(xH : LaurentSeries (AlgebraicClosure ℚ))} from rfl,
      relfinrank_adjoin_singleton_eq_finrank FH xH]
    have hpos := @Module.finrank_pos ↥(IntermediateField.adjoin (AlgebraicClosure ℚ) ({xH} : Set ↥FH)) ↥FH _ _ _ _ hfinH _ _ _
    exact hpos.ne'
  have hRJF0 : (J).relfinrank F0 ≤ dedekindPsi N := by
    rw [show J = IntermediateField.adjoin (AlgebraicClosure ℚ) {(x0 : LaurentSeries (AlgebraicClosure ℚ))} from rfl,
      relfinrank_adjoin_singleton_eq_finrank F0 x0, ← ModularCurve.Gamma0_index]
    exact hle0
  have hR0H : (F0).relfinrank FH = (H ⊔ Subgroup.zpowers (-1 : (ZMod N)ˣ)).index :=
    ModularCurve.relfinrank_qExpFunctionFieldC_gamma0_gammaH_eq_index_of_charZero (AlgebraicClosure ℚ) N H

  have t1 := IntermediateField.relfinrank_mul_relfinrank hJFB hFB
  have t2 := IntermediateField.relfinrank_mul_relfinrank hJF0 hF0FH
  have hdvd : (J).relfinrank (laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (CohCarrier.GammaH N H))) ∣ (J).relfinrank FH := Dvd.intro _ t1
  refine ⟨fun h0 => hRJFH (zero_dvd_iff.mp (h0 ▸ hdvd)), ?_⟩
  calc (J).relfinrank (laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (CohCarrier.GammaH N H))) ≤ (J).relfinrank FH := Nat.le_of_dvd (Nat.pos_of_ne_zero hRJFH) hdvd
    _ = (J).relfinrank F0 * (F0).relfinrank FH := t2.symm
    _ ≤ dedekindPsi N * (H ⊔ Subgroup.zpowers (-1 : (ZMod N)ˣ)).index := by
        rw [hR0H]; exact Nat.mul_le_mul_right _ hRJF0

theorem relfinrank_J_fieldBar_le :
    haveI : NeZero (q ^ 2 * M) := ⟨mul_ne_zero (pow_ne_zero _ (Fact.out : q.Prime).ne_zero) (NeZero.ne M)⟩
    (J).relfinrank (fieldBar q M) ≤
      dedekindPsi (q ^ 2 * M) * ((levelH q M) ⊔ Subgroup.zpowers (-1 : (ZMod (q ^ 2 * M))ˣ)).index := by
  haveI : NeZero (q ^ 2 * M) := ⟨mul_ne_zero (pow_ne_zero _ (Fact.out : q.Prime).ne_zero) (NeZero.ne M)⟩
  exact (relfinrank_J_laurentBaseChange_gammaH_ne_zero_and_le (q ^ 2 * M) (levelH q M)).2

theorem index_levelH_sup (hq : 5 ≤ q) :
    haveI : NeZero (q ^ 2 * M) := ⟨mul_ne_zero (pow_ne_zero _ (Fact.out : q.Prime).ne_zero) (NeZero.ne M)⟩
    ((levelH q M) ⊔ Subgroup.zpowers (-1 : (ZMod (q ^ 2 * M))ˣ)).index = (q - 1) / 2 := by
  haveI : NeZero (q ^ 2 * M) := ⟨mul_ne_zero (pow_ne_zero _ (Fact.out : q.Prime).ne_zero) (NeZero.ne M)⟩
  have hqp : q.Prime := Fact.out
  haveI : Fact (1 < q) := ⟨hqp.one_lt⟩
  set π := ZMod.unitsMap (dvd_sq_mul q M) with hπ
  have hsurj : Function.Surjective π := ZMod.unitsMap_surjective _
  have hπneg : π (-1) = -1 := by
    apply Units.ext
    rw [hπ, ZMod.unitsMap_def, Units.coe_map, Units.val_neg, Units.val_one, MonoidHom.coe_coe, map_neg, map_one,
      Units.val_neg, Units.val_one]
  have hsup : levelH q M ⊔ Subgroup.zpowers (-1 : (ZMod (q ^ 2 * M))ˣ) =
      (Subgroup.zpowers (-1 : (ZMod q)ˣ)).comap π := by
    rw [← hπneg, ← MonoidHom.map_zpowers, Subgroup.comap_map_eq, sup_comm]
    rfl
  rw [hsup, Subgroup.index_comap_of_surjective _ hsurj]
  have hcard : Nat.card (ZMod q)ˣ = q - 1 := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient, Nat.totient_prime hqp]
  have hord : Nat.card ↥(Subgroup.zpowers (-1 : (ZMod q)ˣ)) = 2 := by
    rw [Nat.card_zpowers, ← orderOf_units, Units.val_neg, Units.val_one, orderOf_neg_one, ZMod.ringChar_zmod_n,
      if_neg (by omega)]
  have h := Subgroup.index_mul_card (Subgroup.zpowers (-1 : (ZMod q)ˣ))
  rw [hord, hcard] at h
  omega

omit [NeZero M] in
theorem index_Gamma0_sup (N : ℕ) [NeZero N] :
    (Gamma0 N ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))).index = dedekindPsi N := by
  have h : Subgroup.zpowers (-1 : SL(2, ℤ)) ≤ Gamma0 N := by
    rw [Subgroup.zpowers_le]
    rw [CongruenceSubgroup.Gamma0_mem]
    simp
  rw [sup_eq_left.mpr h, ModularCurve.Gamma0_index]

theorem dedekindPsi_q_mul (hqM : ¬ q ∣ M) : dedekindPsi (q * M) = (q + 1) * dedekindPsi M := by
  rw [mul_comm q M, ModularCurve.dedekindPsi_mul_prime M q (Fact.out : q.Prime), if_neg hqM]

theorem dedekindPsi_sq_mul : dedekindPsi (q ^ 2 * M) = q * dedekindPsi (q * M) := by
  haveI : NeZero (q * M) := ⟨mul_ne_zero (Fact.out : q.Prime).ne_zero (NeZero.ne M)⟩
  rw [show q ^ 2 * M = q * M * q by ring, ModularCurve.dedekindPsi_mul_prime (q * M) q (Fact.out : q.Prime),
    if_pos (dvd_mul_right q M)]

end Count

section WithFact2

variable [hqM : Fact (¬ q ∣ M)]

theorem finrank_KB_le (hq : 5 ≤ q) : Module.finrank (KB q M) (fieldBar q M) ≤ q * (q - 1) / 2 := by
  haveI : NeZero (q ^ 2 * M) := ⟨mul_ne_zero (pow_ne_zero _ (Fact.out : q.Prime).ne_zero) (NeZero.ne M)⟩
  have hqp : q.Prime := Fact.out
  rw [finrank_KB_eq_relfinrank]

  have t1 := IntermediateField.relfinrank_mul_relfinrank (Jq_le_KB q M) (KB_le_fieldBar q M hqM.out)
  have t2 := IntermediateField.relfinrank_mul_relfinrank (Jq_le_JJ q) (JJ_le_fieldBar q M hqM.out)
  have t3 := IntermediateField.relfinrank_mul_relfinrank (J_le_JJ q) (JJ_le_fieldBar q M hqM.out)
  have hsw := relfinrank_J_JJ_eq_relfinrank_Jq_JJ q
  have hJFB : (Jq q).relfinrank (fieldBar q M) = (J).relfinrank (fieldBar q M) := by
    rw [← t2, ← t3, hsw]
  rw [relfinrank_Jq_KB, index_Gamma0_sup, hJFB] at t1

  have hub := relfinrank_J_fieldBar_le q M
  rw [index_levelH_sup q M hq, dedekindPsi_sq_mul] at hub
  rw [← t1] at hub
  have hψ : 0 < dedekindPsi M := by
    have h1 : (1 : ℕ) ∈ M.divisors.filter Squarefree :=
      Finset.mem_filter.mpr ⟨Nat.one_mem_divisors.mpr (NeZero.ne M), squarefree_one⟩
    have h := Finset.single_le_sum (f := fun d => M / d) (fun _ _ => Nat.zero_le _) h1
    simp only [Nat.div_one] at h
    exact lt_of_lt_of_le (Nat.pos_of_ne_zero (NeZero.ne M)) h
  have hpos : 0 < dedekindPsi (q * M) := by
    rw [dedekindPsi_q_mul q M hqM.out]
    exact Nat.mul_pos (Nat.succ_pos q) hψ
  have hodd : q * (q - 1) / 2 = q * ((q - 1) / 2) := by
    obtain ⟨k, hk⟩ : 2 ∣ q - 1 := (Nat.Odd.sub_odd (hqp.eq_two_or_odd'.resolve_left (by omega)) odd_one).two_dvd
    rw [hk, Nat.mul_div_cancel_left k two_pos, ← mul_assoc, mul_comm q 2, mul_assoc, Nat.mul_div_cancel_left _ two_pos]
  rw [hodd]
  have h' : dedekindPsi (q * M) * (KB q M).relfinrank (fieldBar q M) ≤
      dedekindPsi (q * M) * (q * ((q - 1) / 2)) := by
    calc dedekindPsi (q * M) * (KB q M).relfinrank (fieldBar q M)
        ≤ q * dedekindPsi (q * M) * ((q - 1) / 2) := hub
      _ = dedekindPsi (q * M) * (q * ((q - 1) / 2)) := by ring
  exact Nat.le_of_mul_le_mul_left h' hpos

theorem relfinrank_KB_xHFunctionFieldBar_le (H' : Subgroup (ZMod (q ^ 2 * M))ˣ) (hH' : H' ≤ levelH q M) :
    (KB q M).relfinrank (xHFunctionFieldBar (q ^ 2 * M) H') ≤
      q * (H' ⊔ Subgroup.zpowers (-1 : (ZMod (q ^ 2 * M))ˣ)).index := by
  haveI : NeZero (q ^ 2 * M) := ⟨mul_ne_zero (pow_ne_zero _ (Fact.out : q.Prime).ne_zero) (NeZero.ne M)⟩
  have hqp : q.Prime := Fact.out
  set F' : IntermediateField (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) :=
    xHFunctionFieldBar (q ^ 2 * M) H' with hF'
  have hFB : fieldBar q M ≤ F' := laurentBaseChange_mono (qExpFunctionFieldC_mono ℚ (gammaH_mono hH'))
  have hKB : KB q M ≤ F' := (KB_le_fieldBar q M hqM.out).trans hFB
  have hJJ : JJ q ≤ F' := (JJ_le_fieldBar q M hqM.out).trans hFB
  have t1 := IntermediateField.relfinrank_mul_relfinrank (Jq_le_KB q M) hKB
  have t2 := IntermediateField.relfinrank_mul_relfinrank (Jq_le_JJ q) hJJ
  have t3 := IntermediateField.relfinrank_mul_relfinrank (J_le_JJ q) hJJ
  have hsw := relfinrank_J_JJ_eq_relfinrank_Jq_JJ q
  have hJF : (Jq q).relfinrank F' = (J).relfinrank F' := by rw [← t2, ← t3, hsw]
  rw [relfinrank_Jq_KB, index_Gamma0_sup, hJF] at t1
  have hub := (relfinrank_J_laurentBaseChange_gammaH_ne_zero_and_le (q ^ 2 * M) H').2
  rw [dedekindPsi_sq_mul] at hub
  have hub' : (J).relfinrank F' ≤ q * dedekindPsi (q * M) * (H' ⊔ Subgroup.zpowers (-1 : (ZMod (q ^ 2 * M))ˣ)).index := hub
  rw [← t1] at hub'
  have hψ : 0 < dedekindPsi M := by
    have h1 : (1 : ℕ) ∈ M.divisors.filter Squarefree :=
      Finset.mem_filter.mpr ⟨Nat.one_mem_divisors.mpr (NeZero.ne M), squarefree_one⟩
    have h := Finset.single_le_sum (f := fun d => M / d) (fun _ _ => Nat.zero_le _) h1
    simp only [Nat.div_one] at h
    exact lt_of_lt_of_le (Nat.pos_of_ne_zero (NeZero.ne M)) h
  have hpos : 0 < dedekindPsi (q * M) := by
    rw [dedekindPsi_q_mul q M hqM.out]
    exact Nat.mul_pos (Nat.succ_pos q) hψ
  have h' : dedekindPsi (q * M) * (KB q M).relfinrank F' ≤
      dedekindPsi (q * M) * (q * (H' ⊔ Subgroup.zpowers (-1 : (ZMod (q ^ 2 * M))ˣ)).index) := by
    calc dedekindPsi (q * M) * (KB q M).relfinrank F'
        ≤ q * dedekindPsi (q * M) * (H' ⊔ Subgroup.zpowers (-1 : (ZMod (q ^ 2 * M))ˣ)).index := hub'
      _ = dedekindPsi (q * M) * (q * (H' ⊔ Subgroup.zpowers (-1 : (ZMod (q ^ 2 * M))ˣ)).index) := by ring
  exact Nat.le_of_mul_le_mul_left h' hpos

omit hqM in

theorem index_Hsharp_sup (hq : 5 ≤ q) :
    ((Hsharp q M) ⊔ Subgroup.zpowers (-1 : (ZMod (q ^ 2 * M))ˣ)).index = Nat.totient (q * M) / 2 := by
  haveI : NeZero (q ^ 2 * M) := ⟨mul_ne_zero (pow_ne_zero _ (Fact.out : q.Prime).ne_zero) (NeZero.ne M)⟩
  haveI : NeZero (q * M) := ⟨mul_ne_zero (Fact.out : q.Prime).ne_zero (NeZero.ne M)⟩
  haveI : Fact (1 < q * M) := ⟨by have : 1 ≤ M := Nat.pos_of_ne_zero (NeZero.ne M); nlinarith⟩
  set π := ZMod.unitsMap (q_mul_dvd_sq_mul q M) with hπ
  have hsurj : Function.Surjective π := ZMod.unitsMap_surjective _
  have hπneg : π (-1) = -1 := by
    apply Units.ext
    rw [hπ, ZMod.unitsMap_def, Units.coe_map, Units.val_neg, Units.val_one, MonoidHom.coe_coe, map_neg, map_one,
      Units.val_neg, Units.val_one]
  have hsup : Hsharp q M ⊔ Subgroup.zpowers (-1 : (ZMod (q ^ 2 * M))ˣ) =
      (Subgroup.zpowers (-1 : (ZMod (q * M))ˣ)).comap π := by
    rw [← hπneg, ← MonoidHom.map_zpowers, Subgroup.comap_map_eq, sup_comm]
  rw [hsup, Subgroup.index_comap_of_surjective _ hsurj]
  have hcard : Nat.card (ZMod (q * M))ˣ = Nat.totient (q * M) := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]
  have hqM2 : q * M ≠ 2 := by
    have : 1 ≤ M := Nat.pos_of_ne_zero (NeZero.ne M)
    nlinarith
  have hord : Nat.card ↥(Subgroup.zpowers (-1 : (ZMod (q * M))ˣ)) = 2 := by
    rw [Nat.card_zpowers, ← orderOf_units, Units.val_neg, Units.val_one, orderOf_neg_one, ZMod.ringChar_zmod_n,
      if_neg hqM2]
  have h := Subgroup.index_mul_card (Subgroup.zpowers (-1 : (ZMod (q * M))ˣ))
  rw [hord, hcard] at h
  omega

theorem relfinrank_KB_xHFunctionFieldBar_Hsharp_le (hq : 5 ≤ q) :
    (KB q M).relfinrank (xHFunctionFieldBar (q ^ 2 * M) (Hsharp q M)) ≤
      Nat.totient M * (q * (q - 1) / 2) := by
  have hqp : q.Prime := Fact.out
  have h := relfinrank_KB_xHFunctionFieldBar_le q M (Hsharp q M) (Hsharp_le_levelH q M)
  rw [index_Hsharp_sup q M hq, Nat.totient_mul ((Nat.Prime.coprime_iff_not_dvd hqp).mpr hqM.out),
    Nat.totient_prime hqp] at h
  obtain ⟨k, hk⟩ : 2 ∣ q - 1 := (Nat.Odd.sub_odd (hqp.eq_two_or_odd'.resolve_left (by omega)) odd_one).two_dvd
  have e1 : (q - 1) * Nat.totient M / 2 = k * Nat.totient M := by
    rw [hk, mul_assoc, Nat.mul_div_cancel_left _ two_pos]
  have e2 : q * (q - 1) / 2 = q * k := by
    rw [hk, ← mul_assoc, mul_comm q 2, mul_assoc, Nat.mul_div_cancel_left _ two_pos]
  rw [e1] at h
  rw [e2]
  calc (KB q M).relfinrank (xHFunctionFieldBar (q ^ 2 * M) (Hsharp q M)) ≤ q * (k * Nat.totient M) := h
    _ = Nat.totient M * (q * k) := by ring

theorem relfinrank_KB_Fsharp_ne_zero : (KB q M).relfinrank (Fsharp q M) ≠ 0 := by
  haveI : NeZero (q ^ 2 * M) := ⟨mul_ne_zero (pow_ne_zero _ (Fact.out : q.Prime).ne_zero) (NeZero.ne M)⟩
  have hKB : KB q M ≤ Fsharp q M := KB_le_Fsharp q M hqM.out
  have hJJ : JJ q ≤ Fsharp q M := (JJ_le_fieldBar q M hqM.out).trans (fieldBar_le_Fsharp q M)
  have t1 := IntermediateField.relfinrank_mul_relfinrank (Jq_le_KB q M) hKB
  have t2 := IntermediateField.relfinrank_mul_relfinrank (Jq_le_JJ q) hJJ
  have t3 := IntermediateField.relfinrank_mul_relfinrank (J_le_JJ q) hJJ
  have hsw := relfinrank_J_JJ_eq_relfinrank_Jq_JJ q
  have hJF : (Jq q).relfinrank (Fsharp q M) = (J).relfinrank (Fsharp q M) := by rw [← t2, ← t3, hsw]
  have hne := (relfinrank_J_laurentBaseChange_gammaH_ne_zero_and_le (q ^ 2 * M) (Hsharp q M)).1
  intro h0
  apply hne
  show (J).relfinrank (Fsharp q M) = 0
  rw [← hJF, ← t1, h0, mul_zero]

theorem finiteDimensional_KB_Fsharp : FiniteDimensional (KB q M) (Fsharp q M) := by
  have h := relfinrank_KB_Fsharp_ne_zero q M
  rw [← finrank_KB_Fsharp_eq_relfinrank] at h
  exact Module.finite_of_finrank_pos (Nat.pos_of_ne_zero h)

theorem finrank_KB_Fsharp_le (hq : 5 ≤ q) :
    Module.finrank (KB q M) (Fsharp q M) ≤ Nat.totient M * (q * (q - 1) / 2) := by
  rw [finrank_KB_Fsharp_eq_relfinrank]
  exact relfinrank_KB_xHFunctionFieldBar_Hsharp_le q M hq

theorem relfinrank_KB_fieldBar_ne_zero : (KB q M).relfinrank (fieldBar q M) ≠ 0 := by
  haveI : NeZero (q ^ 2 * M) := ⟨mul_ne_zero (pow_ne_zero _ (Fact.out : q.Prime).ne_zero) (NeZero.ne M)⟩
  have t1 := IntermediateField.relfinrank_mul_relfinrank (Jq_le_KB q M) (KB_le_fieldBar q M hqM.out)
  have t2 := IntermediateField.relfinrank_mul_relfinrank (Jq_le_JJ q) (JJ_le_fieldBar q M hqM.out)
  have t3 := IntermediateField.relfinrank_mul_relfinrank (J_le_JJ q) (JJ_le_fieldBar q M hqM.out)
  have hsw := relfinrank_J_JJ_eq_relfinrank_Jq_JJ q
  have hJF : (Jq q).relfinrank (fieldBar q M) = (J).relfinrank (fieldBar q M) := by rw [← t2, ← t3, hsw]
  have hne := (relfinrank_J_laurentBaseChange_gammaH_ne_zero_and_le (q ^ 2 * M) (levelH q M)).1
  intro h0
  apply hne
  show (J).relfinrank (fieldBar q M) = 0
  rw [← hJF, ← t1, h0, mul_zero]

theorem finiteDimensional_KB : FiniteDimensional (KB q M) (fieldBar q M) := by
  have h := relfinrank_KB_fieldBar_ne_zero q M
  rw [← finrank_KB_eq_relfinrank] at h
  exact Module.finite_of_finrank_pos (Nat.pos_of_ne_zero h)

omit [NeZero M] hqM in
theorem KB_eq_adjoin_image :
    KB q M = IntermediateField.adjoin (AlgebraicClosure ℚ)
      (qExpand (AlgebraicClosure ℚ) q ''
        (laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (Gamma0 (q * M))) :
          Set (LaurentSeries (AlgebraicClosure ℚ)))) := by
  rw [KB]
  conv_lhs => rw [← IntermediateField.adjoin_self (AlgebraicClosure ℚ) (Kone q M)]
  rw [IntermediateField.adjoin_map]
  congr 1

end WithFact2

end ModularCurve.FullLevel.K1Road
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_relfinrank_adjoin_qExpand_image_laurentBaseChange_gamma0_fieldBar_ne_zero.ModularCurve P2MW.S_ModularCurve_FullLevel_relfinrank_adjoin_qExpand_image_laurentBaseChange_gamma0_fieldBar_ne_zero.ModularCurve.FullLevel P2MW.S_ModularCurve_FullLevel_relfinrank_adjoin_qExpand_image_laurentBaseChange_gamma0_fieldBar_ne_zero.ModularCurve.FullLevel.K1Road"
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_relfinrank_adjoin_qExpand_image_laurentBaseChange_gamma0_fieldBar_ne_zero.ModularCurve P2MW.S_ModularCurve_FullLevel_relfinrank_adjoin_qExpand_image_laurentBaseChange_gamma0_fieldBar_ne_zero.ModularCurve.FullLevel"
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_relfinrank_adjoin_qExpand_image_laurentBaseChange_gamma0_fieldBar_ne_zero.ModularCurve"

open ModularCurve.FullLevel.K1Road in
theorem solution
    (q : ℕ) [Fact q.Prime] (M : ℕ) [NeZero M] (hqM : ¬ q ∣ M) :
    (IntermediateField.adjoin (AlgebraicClosure ℚ)
        (qExpand (AlgebraicClosure ℚ) q ''
          (laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (Gamma0 (q * M))) :
            Set (LaurentSeries (AlgebraicClosure ℚ))))).relfinrank (fieldBar q M) ≠ 0 := by
  haveI : Fact (¬ q ∣ M) := ⟨hqM⟩
  have h := relfinrank_KB_fieldBar_ne_zero q M
  rw [KB_eq_adjoin_image] at h
  exact h

end
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_relfinrank_adjoin_qExpand_image_laurentBaseChange_gamma0_fieldBar_ne_zero.ModularCurve P2MW.S_ModularCurve_FullLevel_relfinrank_adjoin_qExpand_image_laurentBaseChange_gamma0_fieldBar_ne_zero.ModularCurve.FullLevel P2MW.S_ModularCurve_FullLevel_relfinrank_adjoin_qExpand_image_laurentBaseChange_gamma0_fieldBar_ne_zero.ModularCurve.FullLevel.K1Road"

end S_ModularCurve_FullLevel_relfinrank_adjoin_qExpand_image_laurentBaseChange_gamma0_fieldBar_ne_zero
end P2MW
export P2MW.S_ModularCurve_FullLevel_relfinrank_adjoin_qExpand_image_laurentBaseChange_gamma0_fieldBar_ne_zero (solution)
