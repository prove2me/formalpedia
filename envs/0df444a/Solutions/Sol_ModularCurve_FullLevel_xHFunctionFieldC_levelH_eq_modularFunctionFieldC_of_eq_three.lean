-- Prove2me | solution 1 for ModularCurve.FullLevel.xHFunctionFieldC_levelH_eq_modularFunctionFieldC_of_eq_three
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/86ddfd9a-0687-5732-88c1-05c85b25e504

import Mathlib
import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_FLTPrelim_Modularity
import Theorems.Thm_ModularCurve_qExpFunctionFieldC_gamma0_eq_modularFunctionFieldC_of_not_dvd
import Definitions.Def_ModularCurve_IgusaFunctionField
import Definitions.Def_ModularCurve_FullLevelSemistableCovering
import Definitions.Def_FLTPrelim_Ramification
import Theorems.Thm_ModularCurve_FullLevel_qExpand_coe_mem_fieldBar_of_mem
import Theorems.Thm_ModularCurve_qExpand_linearIndependent_pow
import Theorems.Thm_ModularCurve_qExpand_mem_qExpFunctionFieldC_of_charP
import Theorems.Thm_ModularCurve_FullLevel_exists_jInvariant_mem_integers
import Theorems.Thm_ModularCurve_FullLevel_relfinrank_adjoin_qExpand_image_laurentBaseChange_gamma0_fieldBar_le_of_eq_three
import Theorems.Thm_ModularCurve_FullLevel_relfinrank_adjoin_qExpand_image_laurentBaseChange_gamma0_fieldBar_ne_zero
import Theorems.Thm_ModularCurve_FullLevel_exists_mem_qExpFunctionFieldC_gamma0_and_residue_eq_qExpand_of_coe_eq_qExpand
import Theorems.Thm_ModularCurve_exists_regularProlongation_laurentBaseChange_qExpFunctionFieldC_residue_div
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_xHFunctionFieldC_levelH_eq_modularFunctionFieldC_of_eq_three
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid CuspForm.instModuleZModIntTwoCuspForms CuspForm.instAddCommGroupIntTwoCuspForms ModularCurve.instAlgebraIntermediateFieldLaurent ModularCurve.instIsScalarTowerKaehlerIntermediateFieldLaurent ModularCurve.instIsScalarTowerIntermediateFieldLaurent ModularCurve.instModuleKaehlerIntermediateFieldLaurent ModularCurve.Gamma0Pair.isElliptic CuspForm.instModuleTwoCuspForms CuspForm.instIsScalarTowerTwoCuspForms CuspForm.instAddCommGroupTwoCuspForms CuspForm.instIsScalarTowerSelfTwoCuspForms CuspForm.instModuleQuotientTwoCuspForms CuspForm.GammaH_finiteIndex"
p2m_attr_erase "simp" "ModularCurve.qExpandAlgHomC_apply ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.CharPReduction.coeffRed_coeff ModularCurve.CharPReduction.redLocHom_apply ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero"
p2m_attr_erase "simp" "ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.ProjectiveLine.map_mk ModularCurve.coe_heckeBetaModLHOf ModularCurve.pairDiagModL_apply ModularCurve.coe_heckeAlphaModLH ModularCurve.pairUpModL_apply ModularCurve.coeff_qDecimate ModularCurve.coe_qExpFrobeniusModL ModularCurve.coe_qExpFrobeniusDegZeroPullbackModL ModularCurve.coe_qExpFrobeniusDegZeroPushforwardModL ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL"
p2m_attr_erase "simp" "ModularCurve.coe_frobeniusDegZeroPushforwardModL ModularCurve.qEulerFun_coeff ModularCurve.diffQExp_D ModularCurve.qEulerOn_apply ModularCurve.qEuler_coeff ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.gluedPolarDifferentials.coe_fst_apply AlgebraicCurve.gluedPolarDifferentials.coe_snd_apply ModularCurve.gamma0PairMap_gen ModularCurve.moduliPointMapRingHom_mk ModularCurve.Gamma0Pair.mk.injEq ModularCurve.ModuliPoint.j_mk ModularCurve.Gamma0Pair.mk.sizeOf_spec ModularCurve.gamma0PairMap_toCurve WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero WeierstrassCurve.ratPointHom_apply WeierstrassCurve.ratPointMap_zero CuspForm.heckeGenH_T CuspForm.coe_twoCuspEnd_apply CuspForm.twoCuspEndMod_reduce CuspForm.heckeGenH_U CuspForm.heckeGenH_dia ModularForm.AtkinLehnerDatum.mk.injEq ModularForm.AtkinLehnerDatum.alGL_coe ModularForm.AtkinLehnerDatum.mk.sizeOf_spec ModularForm.AtkinLehnerDatum.sqUnitSL_coe ModularForm.AtkinLehnerDatum.det_sqUnit ModularForm.AtkinLehnerDatum.det_mat ModularCurve.baseAut_x1ArithFrobC_apply ModularCurve.coe_qExpCoeffRingAut_apply ModularCurve.qExpCoeffSemilinearAutHom_apply"
p2m_attr_erase "simp" "ModularCurve.baseAut_x1x0ArithFrobC_apply ModularCurve.baseAut_qExpArithFrobC_apply ModularCurve.baseAut_qExpCoeffSemilinearAut ModularCurve.toRingAut_qExpCoeffSemilinearAut ModularForm.coe_atkinLehnerLin_apply CuspForm.coe_atkinLehnerLin_apply CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000

p2m_open "ModularCurve P2MW.S_ModularCurve_FullLevel_xHFunctionFieldC_levelH_eq_modularFunctionFieldC_of_eq_three.ModularCurve ModularCurve.FullLevel P2MW.S_ModularCurve_FullLevel_xHFunctionFieldC_levelH_eq_modularFunctionFieldC_of_eq_three.ModularCurve.FullLevel CongruenceSubgroup"
open scoped MatrixGroups ArithmeticFunction.sigma

open AlgebraicCurve IsLocalRing

noncomputable section

namespace ModularCurve
p2m_export "ModularCurve" "FullLevel.levelH translation_mem_GammaH xHFunctionFieldC qExpFunctionFieldC qExpFunctionFieldC_mono qExpand qExpand_C coeffMap laurentBaseChange modularFunctionFieldC qExpFunctionFieldC_gamma0_eq_modularFunctionFieldC_of_not_dvd FullLevel.qExpand_coe_mem_fieldBar_of_mem qExpand_linearIndependent_pow qExpand_mem_qExpFunctionFieldC_of_charP FullLevel.exists_jInvariant_mem_integers FullLevel.relfinrank_adjoin_qExpand_image_laurentBaseChange_gamma0_fieldBar_le_of_eq_three FullLevel.relfinrank_adjoin_qExpand_image_laurentBaseChange_gamma0_fieldBar_ne_zero FullLevel.exists_mem_qExpFunctionFieldC_gamma0_and_residue_eq_qExpand_of_coe_eq_qExpand exists_regularProlongation_laurentBaseChange_qExpFunctionFieldC_residue_div"
namespace FullLevel
p2m_export "ModularCurve.FullLevel" "levelH fieldBar qExpand_coe_mem_fieldBar_of_mem exists_jInvariant_mem_integers relfinrank_adjoin_qExpand_image_laurentBaseChange_gamma0_fieldBar_le_of_eq_three relfinrank_adjoin_qExpand_image_laurentBaseChange_gamma0_fieldBar_ne_zero exists_mem_qExpFunctionFieldC_gamma0_and_residue_eq_qExpand_of_coe_eq_qExpand"
namespace IgCount3
p2m_open "ModularCurve.FullLevel ModularCurve"

variable (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M']

abbrev Kone : IntermediateField (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) :=
  laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (Gamma0 (q * M')))

abbrev Kzero : IntermediateField (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) :=
  laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (Gamma0 M'))

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
  (Kone q M').map (qExpandBar q)

omit [NeZero M'] in
theorem mem_KB_iff (x : LaurentSeries (AlgebraicClosure ℚ)) :
    x ∈ KB q M' ↔ ∃ g ∈ Kone q M', qExpand (AlgebraicClosure ℚ) q g = x := by
  simp [KB, IntermediateField.mem_map]

private theorem _root_.ModularCurve.FullLevel.IgCount3.qExpand_coe_mem_fieldBar_of_mem (hqM' : ¬ q ∣ M')
    (g : LaurentSeries (AlgebraicClosure ℚ)) (hg : g ∈ Kone q M') :
    qExpand (AlgebraicClosure ℚ) q g ∈ fieldBar q M' :=
  ModularCurve.FullLevel.qExpand_coe_mem_fieldBar_of_mem q M' hqM' g hg

p2m_export "ModularCurve.FullLevel.IgCount3" "qExpand_coe_mem_fieldBar_of_mem"
theorem KB_le_fieldBar (hqM' : ¬ q ∣ M') : KB q M' ≤ fieldBar q M' := by
  intro x hx
  obtain ⟨g, hg, rfl⟩ := (mem_KB_iff q M' x).mp hx
  exact qExpand_coe_mem_fieldBar_of_mem q M' hqM' g hg

section WithFact

variable [hqM : Fact (¬ q ∣ M')]

scoped instance algebraKB : Algebra (KB q M') (fieldBar q M') :=
  (IntermediateField.inclusion (KB_le_fieldBar q M' hqM.out)).toRingHom.toAlgebra

scoped instance moduleKB : Module (KB q M') (fieldBar q M') := (algebraKB q M').toModule

theorem coe_algebraMap_KB (x : KB q M') :
    ((algebraMap (KB q M') (fieldBar q M') x : fieldBar q M') : LaurentSeries (AlgebraicClosure ℚ)) = x := rfl

theorem finrank_KB_eq_relfinrank :
    Module.finrank (KB q M') (fieldBar q M') = (KB q M').relfinrank (fieldBar q M') := by
  rw [IntermediateField.relfinrank_eq_finrank_of_le (KB_le_fieldBar q M' hqM.out)]
  rfl

omit [NeZero M'] hqM in
theorem KB_eq_adjoin_image :
    KB q M' = IntermediateField.adjoin (AlgebraicClosure ℚ)
      (qExpand (AlgebraicClosure ℚ) q ''
        (laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (Gamma0 (q * M'))) :
          Set (LaurentSeries (AlgebraicClosure ℚ)))) := by
  rw [KB]
  conv_lhs => rw [← IntermediateField.adjoin_self (AlgebraicClosure ℚ) (Kone q M')]
  rw [IntermediateField.adjoin_map]
  congr 1

theorem finiteDimensional_KB : FiniteDimensional (KB q M') (fieldBar q M') := by
  have h := ModularCurve.FullLevel.relfinrank_adjoin_qExpand_image_laurentBaseChange_gamma0_fieldBar_ne_zero q M' hqM.out
  rw [← KB_eq_adjoin_image, ← finrank_KB_eq_relfinrank] at h
  exact Module.finite_of_finrank_pos (Nat.pos_of_ne_zero h)

theorem finrank_KB_le (hq3 : q = 3) : Module.finrank (KB q M') (fieldBar q M') ≤ q * (q - 1) / 2 := by
  rw [finrank_KB_eq_relfinrank, KB_eq_adjoin_image]
  exact ModularCurve.FullLevel.relfinrank_adjoin_qExpand_image_laurentBaseChange_gamma0_fieldBar_le_of_eq_three q hq3 M' hqM.out

end WithFact

section Family

variable [hqM : Fact (¬ q ∣ M')]
variable (A : ValuationSubring (AlgebraicClosure ℚ))

theorem exists_regularProlongation_integers_eq_res
    (O : ValuationSubring (fieldBar q M'))
    (hO : ∀ f : fieldBar q M', f ∈ O ↔
      ∃ x y : LaurentSeries A, coeffMap (IsLocalRing.residue A) y ≠ 0 ∧
        (f : LaurentSeries (AlgebraicClosure ℚ)) * coeffMap A.subtype y = coeffMap A.subtype x) :
    ∃ R : RegularProlongation A (fieldBar q M')
        (qExpFunctionFieldC (ResidueField A) (CohCarrier.GammaH (q ^ 2 * M') (levelH q M'))),
      R.integers = O ∧
      (∀ (f : fieldBar q M') (hf : f ∈ R.integers) (x y : LaurentSeries A),
        coeffMap (IsLocalRing.residue A) y ≠ 0 →
          (f : LaurentSeries (AlgebraicClosure ℚ)) * coeffMap A.subtype y = coeffMap A.subtype x →
            ((R.residue ⟨f, hf⟩ : qExpFunctionFieldC (ResidueField A)
                (CohCarrier.GammaH (q ^ 2 * M') (levelH q M'))) : LaurentSeries (ResidueField A)) *
              coeffMap (IsLocalRing.residue A) y = coeffMap (IsLocalRing.residue A) x) ∧
      ∀ (y : LaurentSeries A) (hy : coeffMap A.subtype y ∈ fieldBar q M'),
        ∃ hOy : (⟨coeffMap A.subtype y, hy⟩ : fieldBar q M') ∈ R.integers,
          ((R.residue ⟨_, hOy⟩ : qExpFunctionFieldC (ResidueField A)
              (CohCarrier.GammaH (q ^ 2 * M') (levelH q M'))) : LaurentSeries (ResidueField A)) =
            coeffMap (IsLocalRing.residue A) y := by
  obtain ⟨R, hR1, hR2, hR3⟩ :=
    ModularCurve.exists_regularProlongation_laurentBaseChange_qExpFunctionFieldC_residue_div
      (AlgebraicClosure ℚ) A (CohCarrier.GammaH (q ^ 2 * M') (levelH q M')) (ModularCurve.translation_mem_GammaH _ _)
  refine ⟨R, ?_, fun f hf x y hy h => hR2 ⟨f, hf⟩ x y hy h, hR3⟩
  ext f
  exact (hR1 f).trans (hO f).symm

variable (R : RegularProlongation A (fieldBar q M')
  (qExpFunctionFieldC (ResidueField A) (CohCarrier.GammaH (q ^ 2 * M') (levelH q M'))))

theorem residue_algebraMap_KB_eq_qExpand (hA : A.LiesOverPrime q)
    (hR : ∀ f : fieldBar q M', f ∈ R.integers ↔
      ∃ x y : LaurentSeries A, coeffMap (IsLocalRing.residue A) y ≠ 0 ∧
        (f : LaurentSeries (AlgebraicClosure ℚ)) * coeffMap A.subtype y = coeffMap A.subtype x)
    (hpin : ∀ (y : LaurentSeries A) (hy : coeffMap A.subtype y ∈ fieldBar q M'),
        ∃ hOy : (⟨coeffMap A.subtype y, hy⟩ : fieldBar q M') ∈ R.integers,
          ((R.residue ⟨_, hOy⟩ : qExpFunctionFieldC (ResidueField A)
              (CohCarrier.GammaH (q ^ 2 * M') (levelH q M'))) : LaurentSeries (ResidueField A)) =
            coeffMap (IsLocalRing.residue A) y)
    (hres : ∀ (f : fieldBar q M') (hf : f ∈ R.integers) (x y : LaurentSeries A),
      coeffMap (IsLocalRing.residue A) y ≠ 0 →
        (f : LaurentSeries (AlgebraicClosure ℚ)) * coeffMap A.subtype y = coeffMap A.subtype x →
          ((R.residue ⟨f, hf⟩ : qExpFunctionFieldC (ResidueField A)
              (CohCarrier.GammaH (q ^ 2 * M') (levelH q M'))) : LaurentSeries (ResidueField A)) *
            coeffMap (IsLocalRing.residue A) y = coeffMap (IsLocalRing.residue A) x)
    (k : KB q M') (hk : algebraMap (KB q M') (fieldBar q M') k ∈ R.integers) :
    ∃ e : LaurentSeries (ResidueField A), e ∈ qExpFunctionFieldC (ResidueField A) (Gamma0 M') ∧
      ((R.residue ⟨_, hk⟩ : qExpFunctionFieldC (ResidueField A)
          (CohCarrier.GammaH (q ^ 2 * M') (levelH q M'))) : LaurentSeries (ResidueField A)) =
        qExpand (ResidueField A) q e := by
  obtain ⟨g, hg, hgk⟩ := (mem_KB_iff q M' (k : LaurentSeries (AlgebraicClosure ℚ))).mp k.2
  exact ModularCurve.FullLevel.exists_mem_qExpFunctionFieldC_gamma0_and_residue_eq_qExpand_of_coe_eq_qExpand
    q M' hqM.out A hA R hR hres g hg _ (by rw [coe_algebraMap_KB, hgk]) hk

private theorem _root_.ModularCurve.FullLevel.IgCount3.qExpand_linearIndependent_pow (κ : Type*) [Field κ] [CharP κ q]
    (j : LaurentSeries κ) (hj : j.coeff (-1) ≠ 0) (e : Fin q → LaurentSeries κ)
    (h : ∑ m, qExpand κ q (e m) * j ^ (m : ℕ) = 0) : ∀ m, e m = 0 :=
  ModularCurve.qExpand_linearIndependent_pow κ q j hj e h

p2m_export "ModularCurve.FullLevel.IgCount3" "qExpand_linearIndependent_pow"

theorem qExpand_mem_qExpFunctionFieldC_of_mem (hA : A.LiesOverPrime q)
    (e : LaurentSeries (ResidueField A)) (he : e ∈ qExpFunctionFieldC (ResidueField A) (Gamma0 M')) :
    qExpand (ResidueField A) q e ∈ qExpFunctionFieldC (ResidueField A) (Gamma0 M') := by
  haveI : CharP (ResidueField A) q := ValuationSubring.charP_residueField_of_liesOverPrime_def Fact.out hA
  exact ModularCurve.qExpand_mem_qExpFunctionFieldC_of_charP (ResidueField A) q (Gamma0 M') e he

theorem exists_j (hA : A.LiesOverPrime q)
    (hR : ∀ f : fieldBar q M', f ∈ R.integers ↔
      ∃ x y : LaurentSeries A, coeffMap (IsLocalRing.residue A) y ≠ 0 ∧
        (f : LaurentSeries (AlgebraicClosure ℚ)) * coeffMap A.subtype y = coeffMap A.subtype x)
    (hpin : ∀ (y : LaurentSeries A) (hy : coeffMap A.subtype y ∈ fieldBar q M'),
        ∃ hOy : (⟨coeffMap A.subtype y, hy⟩ : fieldBar q M') ∈ R.integers,
          ((R.residue ⟨_, hOy⟩ : qExpFunctionFieldC (ResidueField A)
              (CohCarrier.GammaH (q ^ 2 * M') (levelH q M'))) : LaurentSeries (ResidueField A)) =
            coeffMap (IsLocalRing.residue A) y) :
    ∃ (j : fieldBar q M') (hj : j ∈ R.integers),
      (j : LaurentSeries (AlgebraicClosure ℚ)) ∈ Kzero M' ∧
      ((R.residue ⟨j, hj⟩ : qExpFunctionFieldC (ResidueField A)
          (CohCarrier.GammaH (q ^ 2 * M') (levelH q M'))) : LaurentSeries (ResidueField A)).coeff (-1) ≠ 0 ∧
      ((R.residue ⟨j, hj⟩ : qExpFunctionFieldC (ResidueField A)
          (CohCarrier.GammaH (q ^ 2 * M') (levelH q M'))) : LaurentSeries (ResidueField A)) ∈
        qExpFunctionFieldC (ResidueField A) (Gamma0 M') :=
  ModularCurve.FullLevel.exists_jInvariant_mem_integers q M' A R hA hR hpin

end Family

section Assembly

variable [hqM : Fact (¬ q ∣ M')]
variable (A : ValuationSubring (AlgebraicClosure ℚ))
variable (R : RegularProlongation A (fieldBar q M')
  (qExpFunctionFieldC (ResidueField A) (CohCarrier.GammaH (q ^ 2 * M') (levelH q M'))))

theorem valuation_lt_one_iff_residue_eq_zero (z : R.integers) :
    R.integers.valuation (z : fieldBar q M') < 1 ↔ R.residue z = 0 := by
  rw [← ValuationSubring.valuation_lt_one_iff, ← R.ker_residue, RingHom.mem_ker]

theorem coe_sum_mul_pow {n : ℕ} (x : Fin n → R.integers) (y : R.integers) :
    ((∑ m, x m * y ^ (m : ℕ) : R.integers) : fieldBar q M') = ∑ m, (x m : fieldBar q M') * (y : fieldBar q M') ^ (m : ℕ) := by
  rw [AddSubmonoidClass.coe_finsetSum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [MulMemClass.coe_mul, SubmonoidClass.coe_pow]

theorem residue_sub_eq_zero_iff (x y : R.integers) : R.residue (x - y) = 0 ↔ R.residue x = R.residue y := by
  rw [map_sub, sub_eq_zero]

theorem residue_sum_mul_pow {n : ℕ} (x : Fin n → R.integers) (y : R.integers) :
    R.residue (∑ m, x m * y ^ (m : ℕ)) = ∑ m, R.residue (x m) * R.residue y ^ (m : ℕ) := by
  rw [map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [map_mul, map_pow]

theorem coe_residue_sum_mul_pow {n : ℕ}
    (x : Fin n → qExpFunctionFieldC (ResidueField A) (CohCarrier.GammaH (q ^ 2 * M') (levelH q M')))
    (y : qExpFunctionFieldC (ResidueField A) (CohCarrier.GammaH (q ^ 2 * M') (levelH q M'))) :
    ((∑ m, x m * y ^ (m : ℕ) : qExpFunctionFieldC (ResidueField A) (CohCarrier.GammaH (q ^ 2 * M') (levelH q M'))) :
      LaurentSeries (ResidueField A)) =
      ∑ m, (x m : LaurentSeries (ResidueField A)) * (y : LaurentSeries (ResidueField A)) ^ (m : ℕ) := by
  rw [AddSubmonoidClass.coe_finsetSum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [MulMemClass.coe_mul, SubmonoidClass.coe_pow]

theorem liftIndep_pow_j (hA : A.LiesOverPrime q)
    (hR : ∀ f : fieldBar q M', f ∈ R.integers ↔
      ∃ x y : LaurentSeries A, coeffMap (IsLocalRing.residue A) y ≠ 0 ∧
        (f : LaurentSeries (AlgebraicClosure ℚ)) * coeffMap A.subtype y = coeffMap A.subtype x)
    (hpin : ∀ (y : LaurentSeries A) (hy : coeffMap A.subtype y ∈ fieldBar q M'),
        ∃ hOy : (⟨coeffMap A.subtype y, hy⟩ : fieldBar q M') ∈ R.integers,
          ((R.residue ⟨_, hOy⟩ : qExpFunctionFieldC (ResidueField A)
              (CohCarrier.GammaH (q ^ 2 * M') (levelH q M'))) : LaurentSeries (ResidueField A)) =
            coeffMap (IsLocalRing.residue A) y)
    (hres : ∀ (f : fieldBar q M') (hf : f ∈ R.integers) (x y : LaurentSeries A),
      coeffMap (IsLocalRing.residue A) y ≠ 0 →
        (f : LaurentSeries (AlgebraicClosure ℚ)) * coeffMap A.subtype y = coeffMap A.subtype x →
          ((R.residue ⟨f, hf⟩ : qExpFunctionFieldC (ResidueField A)
              (CohCarrier.GammaH (q ^ 2 * M') (levelH q M'))) : LaurentSeries (ResidueField A)) *
            coeffMap (IsLocalRing.residue A) y = coeffMap (IsLocalRing.residue A) x)
    (j : fieldBar q M') (hj : j ∈ R.integers)
    (hjc : ((R.residue ⟨j, hj⟩ : qExpFunctionFieldC (ResidueField A)
          (CohCarrier.GammaH (q ^ 2 * M') (levelH q M'))) : LaurentSeries (ResidueField A)).coeff (-1) ≠ 0)
    (c : Fin q → KB q M') (hc : ∀ m, algebraMap (KB q M') (fieldBar q M') (c m) ∈ R.integers)
    (hlt : R.integers.valuation (∑ m, algebraMap (KB q M') (fieldBar q M') (c m) * j ^ (m : ℕ)) < 1) :
    ∀ m, R.integers.valuation (algebraMap (KB q M') (fieldBar q M') (c m)) < 1 := by
  classical
  haveI : CharP (ResidueField A) q := ValuationSubring.charP_residueField_of_liesOverPrime_def Fact.out hA

  have hres := fun m => residue_algebraMap_KB_eq_qExpand q M' A R hA hR hpin hres (c m) (hc m)
  choose e heE0 he using hres

  let cO : Fin q → R.integers := fun m => ⟨algebraMap (KB q M') (fieldBar q M') (c m), hc m⟩
  let jO : R.integers := ⟨j, hj⟩
  have hsum0 : R.residue (∑ m, cO m * jO ^ (m : ℕ)) = 0 := by
    rw [← valuation_lt_one_iff_residue_eq_zero q M' A R, coe_sum_mul_pow q M' A R]
    exact hlt
  rw [residue_sum_mul_pow q M' A R] at hsum0

  have hser : ∑ m, qExpand (ResidueField A) q (e m) *
      ((R.residue jO : qExpFunctionFieldC (ResidueField A) (CohCarrier.GammaH (q ^ 2 * M') (levelH q M'))) :
        LaurentSeries (ResidueField A)) ^ (m : ℕ) = 0 := by
    have h := congrArg Subtype.val hsum0
    rw [ZeroMemClass.coe_zero, coe_residue_sum_mul_pow q M' A] at h
    rw [← h]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [← he m]
  have hzero := qExpand_linearIndependent_pow q (ResidueField A) _ hjc e hser
  intro m
  have hm : R.residue (cO m) = 0 := by
    apply Subtype.ext
    rw [he m, hzero m, map_zero, ZeroMemClass.coe_zero]
  exact (valuation_lt_one_iff_residue_eq_zero q M' A R (cO m)).mpr hm

omit [Fact (Nat.Prime q)] [NeZero M'] hqM in
theorem linearIndependent_of_liftIndep {K L : Type*} [Field K] [Field L] [Algebra K L]
    (O : ValuationSubring L) {β : Type*} [Fintype β] (b : β → L)
    (hli : ∀ c : β → K, (∀ k, algebraMap K L (c k) ∈ O) →
      O.valuation (∑ k, algebraMap K L (c k) * b k) < 1 → ∀ k, O.valuation (algebraMap K L (c k)) < 1) :
    LinearIndependent K b := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro g hg
  by_contra hne
  push Not at hne
  obtain ⟨k₁, hk₁⟩ := hne

  obtain ⟨k₀, -, hmax⟩ := Finset.exists_max_image Finset.univ
    (fun k => O.valuation (algebraMap K L (g k))) ⟨k₁, Finset.mem_univ _⟩
  have hg0 : g k₀ ≠ 0 := by
    intro h0
    have h := hmax k₁ (Finset.mem_univ _)
    rw [h0, map_zero, map_zero, le_zero_iff, Valuation.zero_iff, map_eq_zero] at h
    exact hk₁ h
  have hg0' : algebraMap K L (g k₀) ≠ 0 := (map_ne_zero _).mpr hg0

  let c : β → K := fun k => g k / g k₀
  have hc : ∀ k, algebraMap K L (c k) ∈ O := by
    intro k
    rw [← O.valuation_le_one_iff]
    show O.valuation (algebraMap K L (g k / g k₀)) ≤ 1
    rw [map_div₀, map_div₀]
    exact div_le_one_of_le₀ (hmax k (Finset.mem_univ _)) zero_le'
  have hsum : ∑ k, algebraMap K L (c k) * b k = 0 := by
    have h : ∑ k, algebraMap K L (c k) * b k = (algebraMap K L (g k₀))⁻¹ * ∑ k, g k • b k := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      show algebraMap K L (g k / g k₀) * b k = _
      rw [Algebra.smul_def, map_div₀, div_eq_mul_inv]
      ring
    rw [h, hg, mul_zero]
  have hlt := hli c hc (by rw [hsum, map_zero]; exact zero_lt_one)
  have h1 := hlt k₀
  rw [show c k₀ = 1 from div_self hg0, map_one, map_one] at h1
  exact lt_irrefl _ h1

omit hqM in
theorem mul_sub_one_div_two (hq3 : q = 3) : q * (q - 1) / 2 = q * ((q - 1) / 2) := by
  have hodd : Odd q := (Fact.out : q.Prime).odd_of_ne_two (by omega)
  obtain ⟨t, ht⟩ := Nat.Odd.sub_odd hodd odd_one
  rw [ht, ← two_mul, Nat.mul_div_cancel_left _ two_pos, Nat.mul_left_comm, Nat.mul_div_cancel_left _ two_pos]

set_option maxHeartbeats 1600000 in
theorem card_le_of_forall_sum_mul_eq_zero (hq3 : q = 3) (hA : A.LiesOverPrime q)
    (hR : ∀ f : fieldBar q M', f ∈ R.integers ↔
      ∃ x y : LaurentSeries A, coeffMap (IsLocalRing.residue A) y ≠ 0 ∧
        (f : LaurentSeries (AlgebraicClosure ℚ)) * coeffMap A.subtype y = coeffMap A.subtype x)
    (hpin : ∀ (y : LaurentSeries A) (hy : coeffMap A.subtype y ∈ fieldBar q M'),
        ∃ hOy : (⟨coeffMap A.subtype y, hy⟩ : fieldBar q M') ∈ R.integers,
          ((R.residue ⟨_, hOy⟩ : qExpFunctionFieldC (ResidueField A)
              (CohCarrier.GammaH (q ^ 2 * M') (levelH q M'))) : LaurentSeries (ResidueField A)) =
            coeffMap (IsLocalRing.residue A) y)
    (hres : ∀ (f : fieldBar q M') (hf : f ∈ R.integers) (x y : LaurentSeries A),
      coeffMap (IsLocalRing.residue A) y ≠ 0 →
        (f : LaurentSeries (AlgebraicClosure ℚ)) * coeffMap A.subtype y = coeffMap A.subtype x →
          ((R.residue ⟨f, hf⟩ : qExpFunctionFieldC (ResidueField A)
              (CohCarrier.GammaH (q ^ 2 * M') (levelH q M'))) : LaurentSeries (ResidueField A)) *
            coeffMap (IsLocalRing.residue A) y = coeffMap (IsLocalRing.residue A) x)
    {m : ℕ} (x : Fin m → qExpFunctionFieldC (ResidueField A) (CohCarrier.GammaH (q ^ 2 * M') (levelH q M')))
    (hx : ∀ e : Fin m → LaurentSeries (ResidueField A),
      (∀ i, e i ∈ qExpFunctionFieldC (ResidueField A) (Gamma0 M')) →
        ∑ i, e i * (x i : LaurentSeries (ResidueField A)) = 0 → ∀ i, e i = 0) :
    m ≤ (q - 1) / 2 := by
  classical
  haveI : CharP (ResidueField A) q := ValuationSubring.charP_residueField_of_liesOverPrime_def Fact.out hA

  obtain ⟨j, hj, -, hjc, hjE0⟩ := exists_j q M' A R hA hR hpin
  have hsurj := R.residue_surjective
  choose u hu using fun i => hsurj (x i)

  let b : Fin m × Fin q → fieldBar q M' := fun p => (u p.1 : fieldBar q M') * j ^ ((p.2 : Fin q) : ℕ)
  have hli : ∀ c : Fin m × Fin q → KB q M', (∀ p, algebraMap (KB q M') (fieldBar q M') (c p) ∈ R.integers) →
      R.integers.valuation (∑ p, algebraMap (KB q M') (fieldBar q M') (c p) * b p) < 1 →
        ∀ p, R.integers.valuation (algebraMap (KB q M') (fieldBar q M') (c p)) < 1 := by
    intro c hc hlt

    have hsum : ∑ p, algebraMap (KB q M') (fieldBar q M') (c p) * b p =
        ∑ i, (∑ l, algebraMap (KB q M') (fieldBar q M') (c (i, l)) * j ^ (l : ℕ)) * (u i : fieldBar q M') := by
      rw [Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun l _ => ?_
      show _ * ((u i : fieldBar q M') * j ^ (l : ℕ)) = _
      rw [← mul_assoc, mul_right_comm]
    rw [hsum] at hlt

    have hres' := fun i l => residue_algebraMap_KB_eq_qExpand q M' A R hA hR hpin hres (c (i, l)) (hc (i, l))
    choose e heE0 he using hres'

    obtain ⟨cO, hcO⟩ : ∃ cO : Fin m → Fin q → R.integers,
        ∀ i l, cO i l = ⟨algebraMap (KB q M') (fieldBar q M') (c (i, l)), hc (i, l)⟩ := ⟨_, fun _ _ => rfl⟩
    obtain ⟨dO, hdOdef⟩ : ∃ dO : Fin m → R.integers,
        ∀ i, dO i = ∑ l, cO i l * (⟨j, hj⟩ : R.integers) ^ (l : ℕ) := ⟨_, fun _ => rfl⟩
    have hdO : ∀ i, (dO i : fieldBar q M') = ∑ l, algebraMap (KB q M') (fieldBar q M') (c (i, l)) * j ^ (l : ℕ) := by
      intro i
      rw [hdOdef, coe_sum_mul_pow q M' A R]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [hcO]

    obtain ⟨sO, hsO⟩ : ∃ sO : R.integers, sO = ∑ i, dO i * u i := ⟨_, rfl⟩
    have hcoe : (sO : fieldBar q M') =
        ∑ i, (∑ l, algebraMap (KB q M') (fieldBar q M') (c (i, l)) * j ^ (l : ℕ)) * (u i : fieldBar q M') := by
      rw [hsO, AddSubmonoidClass.coe_finsetSum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [MulMemClass.coe_mul, hdO]
    have hsum0 : R.residue sO = 0 := by
      rw [← valuation_lt_one_iff_residue_eq_zero q M' A R, hcoe]
      exact hlt
    rw [hsO, map_sum] at hsum0
    have hsum0' : ∑ i, R.residue (dO i) * x i = 0 := by
      rw [← hsum0]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_mul, hu]

    have hdres : ∀ i, ((R.residue (dO i) : qExpFunctionFieldC (ResidueField A)
        (CohCarrier.GammaH (q ^ 2 * M') (levelH q M'))) : LaurentSeries (ResidueField A)) =
          ∑ l, qExpand (ResidueField A) q (e i l) *
            ((R.residue ⟨j, hj⟩ : qExpFunctionFieldC (ResidueField A) (CohCarrier.GammaH (q ^ 2 * M') (levelH q M'))) :
              LaurentSeries (ResidueField A)) ^ (l : ℕ) := by
      intro i
      rw [hdOdef, residue_sum_mul_pow q M' A R, coe_residue_sum_mul_pow q M' A]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [← he i l, hcO]
    have hdE0 : ∀ i, ((R.residue (dO i) : qExpFunctionFieldC (ResidueField A)
        (CohCarrier.GammaH (q ^ 2 * M') (levelH q M'))) : LaurentSeries (ResidueField A)) ∈
          qExpFunctionFieldC (ResidueField A) (Gamma0 M') := by
      intro i
      rw [hdres i]
      refine sum_mem fun l _ => mul_mem ?_ (pow_mem hjE0 _)
      exact qExpand_mem_qExpFunctionFieldC_of_mem q M' A hA _ (heE0 i l)

    have hsumres : ∑ i, ((R.residue (dO i) : qExpFunctionFieldC (ResidueField A)
        (CohCarrier.GammaH (q ^ 2 * M') (levelH q M'))) : LaurentSeries (ResidueField A)) *
          (x i : LaurentSeries (ResidueField A)) = 0 := by
      have h := congrArg Subtype.val hsum0'
      rw [ZeroMemClass.coe_zero, AddSubmonoidClass.coe_finsetSum] at h
      rw [← h]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [MulMemClass.coe_mul]
    have hd0 := hx (fun i => ((R.residue (dO i) : qExpFunctionFieldC (ResidueField A)
        (CohCarrier.GammaH (q ^ 2 * M') (levelH q M'))) : LaurentSeries (ResidueField A))) hdE0 hsumres

    intro p
    obtain ⟨i, l⟩ := p
    have hser : ∑ l', qExpand (ResidueField A) q (e i l') *
        ((R.residue ⟨j, hj⟩ : qExpFunctionFieldC (ResidueField A) (CohCarrier.GammaH (q ^ 2 * M') (levelH q M'))) :
          LaurentSeries (ResidueField A)) ^ (l' : ℕ) = 0 := by
      rw [← hdres i]; exact hd0 i
    have hzero := qExpand_linearIndependent_pow q (ResidueField A) _ hjc (e i) hser
    have hm : R.residue (cO i l) = 0 := by
      apply Subtype.ext
      rw [hcO, he i l, hzero l, map_zero, ZeroMemClass.coe_zero]
    have hv := (valuation_lt_one_iff_residue_eq_zero q M' A R (cO i l)).mpr hm
    rwa [hcO] at hv

  have hlin : LinearIndependent (KB q M') b := linearIndependent_of_liftIndep (R.integers) b hli
  haveI := finiteDimensional_KB q M'
  have hcard := hlin.fintype_card_le_finrank
  rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin] at hcard
  have hle := le_trans hcard (finrank_KB_le q M' hq3)
  rw [mul_sub_one_div_two q hq3, mul_comm] at hle
  exact Nat.le_of_mul_le_mul_left hle (Fact.out : q.Prime).pos

end Assembly

end ModularCurve.FullLevel.IgCount3
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_xHFunctionFieldC_levelH_eq_modularFunctionFieldC_of_eq_three.ModularCurve P2MW.S_ModularCurve_FullLevel_xHFunctionFieldC_levelH_eq_modularFunctionFieldC_of_eq_three.ModularCurve.FullLevel P2MW.S_ModularCurve_FullLevel_xHFunctionFieldC_levelH_eq_modularFunctionFieldC_of_eq_three.ModularCurve.FullLevel.IgCount3"
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_xHFunctionFieldC_levelH_eq_modularFunctionFieldC_of_eq_three.ModularCurve P2MW.S_ModularCurve_FullLevel_xHFunctionFieldC_levelH_eq_modularFunctionFieldC_of_eq_three.ModularCurve.FullLevel"
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_xHFunctionFieldC_levelH_eq_modularFunctionFieldC_of_eq_three.ModularCurve"
end
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_xHFunctionFieldC_levelH_eq_modularFunctionFieldC_of_eq_three.ModularCurve P2MW.S_ModularCurve_FullLevel_xHFunctionFieldC_levelH_eq_modularFunctionFieldC_of_eq_three.ModularCurve.FullLevel P2MW.S_ModularCurve_FullLevel_xHFunctionFieldC_levelH_eq_modularFunctionFieldC_of_eq_three.ModularCurve.FullLevel.IgCount3"

noncomputable section

namespace ModularCurve
p2m_export "ModularCurve" "FullLevel.levelH translation_mem_GammaH xHFunctionFieldC qExpFunctionFieldC qExpFunctionFieldC_mono qExpand qExpand_C coeffMap laurentBaseChange modularFunctionFieldC qExpFunctionFieldC_gamma0_eq_modularFunctionFieldC_of_not_dvd FullLevel.qExpand_coe_mem_fieldBar_of_mem qExpand_linearIndependent_pow qExpand_mem_qExpFunctionFieldC_of_charP FullLevel.exists_jInvariant_mem_integers FullLevel.relfinrank_adjoin_qExpand_image_laurentBaseChange_gamma0_fieldBar_le_of_eq_three FullLevel.relfinrank_adjoin_qExpand_image_laurentBaseChange_gamma0_fieldBar_ne_zero FullLevel.exists_mem_qExpFunctionFieldC_gamma0_and_residue_eq_qExpand_of_coe_eq_qExpand exists_regularProlongation_laurentBaseChange_qExpFunctionFieldC_residue_div"
namespace FullLevel
p2m_export "ModularCurve.FullLevel" "levelH fieldBar qExpand_coe_mem_fieldBar_of_mem exists_jInvariant_mem_integers relfinrank_adjoin_qExpand_image_laurentBaseChange_gamma0_fieldBar_le_of_eq_three relfinrank_adjoin_qExpand_image_laurentBaseChange_gamma0_fieldBar_ne_zero exists_mem_qExpFunctionFieldC_gamma0_and_residue_eq_qExpand_of_coe_eq_qExpand"
namespace IgFieldId3
p2m_open "ModularCurve.FullLevel ModularCurve"

p2m_open "AlgebraicCurve ModularCurve P2MW.S_ModularCurve_FullLevel_xHFunctionFieldC_levelH_eq_modularFunctionFieldC_of_eq_three.ModularCurve ModularCurve.FullLevel P2MW.S_ModularCurve_FullLevel_xHFunctionFieldC_levelH_eq_modularFunctionFieldC_of_eq_three.ModularCurve.FullLevel IsLocalRing CongruenceSubgroup IntermediateField"

set_option maxHeartbeats 3200000 in

theorem main (q : ℕ) [Fact q.Prime] (hq3 : q = 3) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q) :
    xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M') = modularFunctionFieldC (ResidueField A) M' := by
  classical
  haveI : Fact (¬ q ∣ M') := ⟨hqM'⟩
  haveI : CharP (ResidueField A) q := ValuationSubring.charP_residueField_of_liesOverPrime_def Fact.out hA
  obtain ⟨E₀, hE₀def⟩ : ∃ E₀ : IntermediateField (ResidueField A) (LaurentSeries (ResidueField A)),
      E₀ = modularFunctionFieldC (ResidueField A) M' := ⟨_, rfl⟩
  obtain ⟨E, hEdef⟩ : ∃ E : IntermediateField (ResidueField A) (LaurentSeries (ResidueField A)),
      E = xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M') := ⟨_, rfl⟩
  rw [← hE₀def, ← hEdef]
  have hE₀' : qExpFunctionFieldC (ResidueField A) (Gamma0 M') = E₀ := by
    rw [hE₀def]; exact ModularCurve.qExpFunctionFieldC_gamma0_eq_modularFunctionFieldC_of_not_dvd (ResidueField A) M' q hqM'

  have hE₀E : E₀ ≤ E := by
    rw [← hE₀', hEdef, xHFunctionFieldC]
    refine qExpFunctionFieldC_mono (ResidueField A) ?_
    intro γ hγ
    have h0 := CohCarrier.GammaH_le_Gamma0 _ hγ
    rw [Gamma0_mem] at h0 ⊢
    have := congrArg (ZMod.castHom (dvd_mul_left M' (q ^ 2)) (ZMod M')) h0
    rwa [map_intCast, map_zero] at this

  obtain ⟨R₀, hR₀, -, -⟩ :=
    ModularCurve.exists_regularProlongation_laurentBaseChange_qExpFunctionFieldC_residue_div
      (AlgebraicClosure ℚ) A (CohCarrier.GammaH (q ^ 2 * M') (levelH q M')) (ModularCurve.translation_mem_GammaH _ _)
  obtain ⟨R, hRint, hres, hpin⟩ := IgCount3.exists_regularProlongation_integers_eq_res q M' A R₀.integers hR₀
  have hR : ∀ f : fieldBar q M', f ∈ R.integers ↔
      ∃ x y : LaurentSeries A, coeffMap (IsLocalRing.residue A) y ≠ 0 ∧
        (f : LaurentSeries (AlgebraicClosure ℚ)) * coeffMap A.subtype y = coeffMap A.subtype x := by
    intro f; rw [hRint]; exact hR₀ f
  have hn : (q - 1) / 2 = 1 := by omega

  have hbound : ∀ s : Finset (extendScalars hE₀E),
      LinearIndependent E₀ (fun i : s => (i : extendScalars hE₀E)) → s.card ≤ 1 := by
    intro s hs
    have hs' := (linearIndependent_equiv s.equivFin.symm).mpr hs
    let xx : Fin s.card → xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M') := fun k =>
      ⟨((s.equivFin.symm k : s) : extendScalars hE₀E), hEdef ▸ ((s.equivFin.symm k : s) : extendScalars hE₀E).2⟩
    rw [← hn]
    refine IgCount3.card_le_of_forall_sum_mul_eq_zero q M' A R hq3 hA hR hpin hres xx ?_
    intro e he hsum
    have he' : ∀ i, e i ∈ E₀ := fun i => hE₀' ▸ he i
    have hzero := Fintype.linearIndependent_iff.mp hs' (fun i => ⟨e i, he' i⟩) (by
      apply Subtype.ext
      rw [ZeroMemClass.coe_zero, ← hsum, AddSubmonoidClass.coe_finsetSum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [IntermediateField.coe_smul, Algebra.smul_def]
      rfl)
    intro i
    exact (congrArg Subtype.val (hzero i)).trans (ZeroMemClass.coe_zero E₀)
  have hrank : Module.rank E₀ (extendScalars hE₀E) ≤ (1 : ℕ) := rank_le (R := E₀) (M := extendScalars hE₀E) hbound
  haveI : Module.Finite E₀ (extendScalars hE₀E) :=
    Module.rank_lt_aleph0_iff.mp (lt_of_le_of_lt hrank (Cardinal.natCast_lt_aleph0))
  have hfinV : Module.finrank E₀ (extendScalars hE₀E) ≤ 1 := Module.finrank_le_of_rank_le hrank
  have hfin1 : Module.finrank E₀ (extendScalars hE₀E) = 1 :=
    le_antisymm hfinV (Nat.one_le_iff_ne_zero.mpr Module.finrank_pos.ne')
  have hbot : extendScalars hE₀E = ⊥ := IntermediateField.finrank_eq_one_iff.mp hfin1
  have h2 := IntermediateField.extendScalars_restrictScalars hE₀E
  rw [hbot, IntermediateField.restrictScalars_bot_eq_self] at h2
  exact h2.symm

end ModularCurve.FullLevel.IgFieldId3
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_xHFunctionFieldC_levelH_eq_modularFunctionFieldC_of_eq_three.ModularCurve P2MW.S_ModularCurve_FullLevel_xHFunctionFieldC_levelH_eq_modularFunctionFieldC_of_eq_three.ModularCurve.FullLevel P2MW.S_ModularCurve_FullLevel_xHFunctionFieldC_levelH_eq_modularFunctionFieldC_of_eq_three.ModularCurve.FullLevel.IgCount3"
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_xHFunctionFieldC_levelH_eq_modularFunctionFieldC_of_eq_three.ModularCurve P2MW.S_ModularCurve_FullLevel_xHFunctionFieldC_levelH_eq_modularFunctionFieldC_of_eq_three.ModularCurve.FullLevel P2MW.S_ModularCurve_FullLevel_xHFunctionFieldC_levelH_eq_modularFunctionFieldC_of_eq_three.ModularCurve.FullLevel.IgCount3"
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_xHFunctionFieldC_levelH_eq_modularFunctionFieldC_of_eq_three.ModularCurve P2MW.S_ModularCurve_FullLevel_xHFunctionFieldC_levelH_eq_modularFunctionFieldC_of_eq_three.ModularCurve.FullLevel P2MW.S_ModularCurve_FullLevel_xHFunctionFieldC_levelH_eq_modularFunctionFieldC_of_eq_three.ModularCurve.FullLevel.IgCount3"

end
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_xHFunctionFieldC_levelH_eq_modularFunctionFieldC_of_eq_three.ModularCurve P2MW.S_ModularCurve_FullLevel_xHFunctionFieldC_levelH_eq_modularFunctionFieldC_of_eq_three.ModularCurve.FullLevel P2MW.S_ModularCurve_FullLevel_xHFunctionFieldC_levelH_eq_modularFunctionFieldC_of_eq_three.ModularCurve.FullLevel.IgCount3"

theorem solution
    (q : ℕ) [Fact q.Prime] (hq3 : q = 3) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q) :
    ModularCurve.xHFunctionFieldC (IsLocalRing.ResidueField A) (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M') =
      ModularCurve.modularFunctionFieldC (IsLocalRing.ResidueField A) M' :=
  ModularCurve.FullLevel.IgFieldId3.main q hq3 M' hqM' A hA

end S_ModularCurve_FullLevel_xHFunctionFieldC_levelH_eq_modularFunctionFieldC_of_eq_three
end P2MW
export P2MW.S_ModularCurve_FullLevel_xHFunctionFieldC_levelH_eq_modularFunctionFieldC_of_eq_three (solution)
