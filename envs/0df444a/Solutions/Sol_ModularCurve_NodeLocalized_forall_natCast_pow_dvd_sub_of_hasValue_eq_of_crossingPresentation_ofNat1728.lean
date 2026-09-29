-- Prove2me | solution 1 for ModularCurve.NodeLocalized.forall_natCast_pow_dvd_sub_of_hasValue_eq_of_crossingPresentation_ofNat1728
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/8743cb30-061b-55cc-9d19-0f782831b751

import Mathlib
import Theorems.Thm_ModularCurve_transcendental_jqModC
import Theorems.Thm_ModularCurve_qExpand_jqModC_eq_pow_unconditional
import Theorems.Thm_ModularCurve_deg_eq_one_modularFunctionFieldBar
import Definitions.Def_ModularCurve_NodeLocalized
import Definitions.Def_ModularCurve_NodeDescent
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_AlgebraicCurve_GluedPic0
import Definitions.Def_FieldTheory_RatAlgClosureGalois
import Definitions.Def_ModularCurve_JWidth
import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_ModularCurve_CuspidalClass
import Definitions.Def_AlgebraicCurve_StandardAnnulus
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_NodeLocalized_forall_natCast_pow_dvd_sub_of_hasValue_eq_of_crossingPresentation_ofNat1728
p2m_attr_erase "instance" "AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.PhiGen.instNeZeroPhiGenCosetA"
p2m_attr_erase "simp" "AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X"
p2m_attr_erase "simp" "ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ"
set_option autoImplicit false

noncomputable section

namespace ModularCurve
p2m_export "ModularCurve" "transcendental_jqModC jqModC jqNModC jqModC_rat map_jqModC jqModC_eq_map_intCast qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd jq jq_mem jqd_mem_full modularFunctionField_le_full qExpand_jqModC_eq_pow_unconditional deg_eq_one_modularFunctionFieldBar modularFunctionFieldBar coeffEmb coeffEmb_coeff coeffEmb_mem_laurentBaseChange CharPReduction.coeffRed_coeff CharPReduction.redRes CharPReduction.redRes_apply CharPReduction.constSeries CharPReduction.modularRing CharPReduction.jqModC_mem_modularRing CharPReduction.jqNModC_mem_modularRing CharPReduction.constSeries_mem_modularRing CharPReduction.jqModC_mem_integralCoeffs CharPReduction.modularRing_le_integralCoeffs ssJSet jWidth jWidth_of_eq_1728"
p2m_open "ModularCurve~coeffEmb_jq"

open AlgebraicCurve IsLocalRing

variable {q : ℕ} [Fact q.Prime] [NeZero (1 * q)] {A : ValuationSubring (AlgebraicClosure ℚ)}
variable {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k]

private def jEltBar (q : ℕ) [NeZero (1 * q)] : ↥(modularFunctionFieldBar (1 * q)) :=
  ⟨coeffEmb (AlgebraicClosure ℚ) jq,
    coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
      (modularFunctionField_le_full (1 * q) (jq_mem (1 * q)))⟩

private def jqEltBar (q : ℕ) [NeZero (1 * q)] : ↥(modularFunctionFieldBar (1 * q)) :=
  ⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * q) jq),
    coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
      (jqd_mem_full (1 * q) (dvd_refl (1 * q)))⟩

private def ssNodeCoord (q : ℕ) [NeZero (1 * q)] : ↥(modularFunctionFieldBar (1 * q)) :=
  jqEltBar q - jEltBar q ^ q

private def IsCentredAt (red : A →+* k) (a : k)
    (W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))) : Prop :=
  (∃ x : A, red x = a ∧
    0 < W.ord (jEltBar q
      - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (x : AlgebraicClosure ℚ))) ∧
  (∃ y : A, red y = a ^ q ∧
    0 < W.ord (jqEltBar q
      - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (y : AlgebraicClosure ℚ)))

section Bridges

private theorem _root_.AlgebraicCurve.Place.evalAt_eq_of_hasValue {L F : Type*} [Field L] [Field F]
    [Algebra L F] {v : Place L F} (hv : v.IsRational) {g : F} {a : L} (h : v.HasValue g a) :
    v.evalAt g = a := by
  obtain ⟨hm, hres⟩ := h
  have h1 := v.algebraMap_evalAt hv hm
  exact (algebraMap L v.ResidueField).injective (h1.trans hres)

p2m_alias "P2MW.S_ModularCurve_NodeLocalized_forall_natCast_pow_dvd_sub_of_hasValue_eq_of_crossingPresentation_ofNat1728.AlgebraicCurve.Place.evalAt_eq_of_hasValue" "AlgebraicCurve.Place.evalAt_eq_of_hasValue"

private theorem _root_.AlgebraicCurve.Place.hasValue_evalAt {L F : Type*} [Field L] [Field F]
    [Algebra L F] {v : Place L F} (hv : v.IsRational) {g : F}
    (hm : g ∈ v.toValuationSubring) : v.HasValue g (v.evalAt g) :=
  ⟨hm, (v.algebraMap_evalAt hv hm).symm⟩

p2m_alias "P2MW.S_ModularCurve_NodeLocalized_forall_natCast_pow_dvd_sub_of_hasValue_eq_of_crossingPresentation_ofNat1728.AlgebraicCurve.Place.hasValue_evalAt" "AlgebraicCurve.Place.hasValue_evalAt"

private theorem _root_.AlgebraicCurve.Place.isRational_of_deg_eq_one {L F : Type*} [Field L] [Field F]
    [Algebra L F] (v : Place L F) (h : v.deg = 1) : v.IsRational := by
  intro z
  unfold Place.deg at h
  have hbt : (⊥ : Subalgebra L v.ResidueField) = ⊤ := Subalgebra.bot_eq_top_of_finrank_eq_one h
  have hz : z ∈ (⊥ : Subalgebra L v.ResidueField) := by
    rw [hbt]
    exact Algebra.mem_top
  exact Algebra.mem_bot.mp hz

p2m_alias "P2MW.S_ModularCurve_NodeLocalized_forall_natCast_pow_dvd_sub_of_hasValue_eq_of_crossingPresentation_ofNat1728.AlgebraicCurve.Place.isRational_of_deg_eq_one" "AlgebraicCurve.Place.isRational_of_deg_eq_one"

private theorem isRational_place_modularFunctionFieldBar (M : ℕ) [NeZero M]
    (w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar M)) : w.IsRational :=
  w.isRational_of_deg_eq_one (deg_eq_one_modularFunctionFieldBar M w)

omit [Fact (Nat.Prime q)] [NeZero (1 * q)] [IsAlgClosed k] [DecidableEq k] in

private theorem natCast_mem_maximalIdeal_of_charP (red : A →+* k)
    (hker : ∀ c : A, red c = 0 ↔ c ∈ IsLocalRing.maximalIdeal A) :
    ((q : ℕ) : A) ∈ IsLocalRing.maximalIdeal A :=
  (hker _).mp (by rw [map_natCast]; exact CharP.cast_eq_zero k q)

end Bridges

end ModularCurve

p2m_open "AlgebraicCurve IsLocalRing ModularCurve~coeffEmb_jq P2MW.S_ModularCurve_NodeLocalized_forall_natCast_pow_dvd_sub_of_hasValue_eq_of_crossingPresentation_ofNat1728.ModularCurve"
open ModularCurve.NodeLocalized

namespace ModularCurve
p2m_export "ModularCurve" "transcendental_jqModC jqModC jqNModC jqModC_rat map_jqModC jqModC_eq_map_intCast qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd jq jq_mem jqd_mem_full modularFunctionField_le_full qExpand_jqModC_eq_pow_unconditional deg_eq_one_modularFunctionFieldBar modularFunctionFieldBar coeffEmb coeffEmb_coeff coeffEmb_mem_laurentBaseChange CharPReduction.coeffRed_coeff CharPReduction.redRes CharPReduction.redRes_apply CharPReduction.constSeries CharPReduction.modularRing CharPReduction.jqModC_mem_modularRing CharPReduction.jqNModC_mem_modularRing CharPReduction.constSeries_mem_modularRing CharPReduction.jqModC_mem_integralCoeffs CharPReduction.modularRing_le_integralCoeffs ssJSet jWidth jWidth_of_eq_1728"
namespace CrossingAnnulus
p2m_open "ModularCurve~coeffEmb_jq"

private theorem qExpand_one_mul {K : Type*} [CommRing K] (q : ℕ) [NeZero q] (x : LaurentSeries K) :
    qExpand K (1 * q) x = qExpand K q x := by
  ext n
  by_cases h : (q : ℤ) ∣ n
  · obtain ⟨m, rfl⟩ := h
    have e : ((1 * q : ℕ) : ℤ) * m = (q : ℤ) * m := by rw [one_mul]
    rw [qExpand_coeff_mul]
    conv_lhs => rw [← e]
    rw [qExpand_coeff_mul]
  · have h' : ¬ ((1 * q : ℕ) : ℤ) ∣ n := by rwa [one_mul]
    rw [qExpand_coeff_of_not_dvd _ _ h', qExpand_coeff_of_not_dvd _ _ h]

private theorem jqNModC_one_mul_eq_pow (K : Type*) [CommRing K] (q : ℕ) [Fact q.Prime] [CharP K q] :
    jqNModC K (1 * q) = jqModC K ^ q := by
  haveI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
  rw [jqNModC, qExpand_one_mul, qExpand_jqModC_eq_pow_unconditional K]

private theorem coeffEmb_jq : coeffEmb (AlgebraicClosure ℚ) jq = jqModC (AlgebraicClosure ℚ) := by
  rw [← jqModC_rat]
  exact map_jqModC (algebraMap ℚ (AlgebraicClosure ℚ))

private theorem coeffEmb_qExpand_jq (N : ℕ) [NeZero N] :
    coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ N jq) = jqNModC (AlgebraicClosure ℚ) N := by
  rw [jqNModC, ← coeffEmb_jq]
  ext n
  by_cases h : (N : ℤ) ∣ n
  · obtain ⟨m, rfl⟩ := h
    rw [coeffEmb_coeff, qExpand_coeff_mul, qExpand_coeff_mul, coeffEmb_coeff]
  · rw [coeffEmb_coeff, qExpand_coeff_of_not_dvd _ _ h, qExpand_coeff_of_not_dvd _ _ h, map_zero]

private theorem algebraMap_eq_single' {K : Type*} [CommRing K] (c : K) :
    algebraMap K (LaurentSeries K) c = HahnSeries.single 0 c := by
  rw [HahnSeries.algebraMap_apply', show algebraMap K (PowerSeries K) c = PowerSeries.C c from by simp,
    HahnSeries.ofPowerSeries_C]
  rfl

section Red

variable {q : ℕ} [Fact q.Prime] {A₀ : Subring (AlgebraicClosure ℚ)}
  {k : Type*} [Field k] (red₀ : ↥A₀ →+* k)

private theorem red_coeff_jqModC (n : ℤ) (h : (jqModC (AlgebraicClosure ℚ)).coeff n ∈ A₀) :
    red₀ ⟨(jqModC (AlgebraicClosure ℚ)).coeff n, h⟩ = (jqModC k).coeff n := by
  have hz : (⟨(jqModC (AlgebraicClosure ℚ)).coeff n, h⟩ : ↥A₀)
      = ((jqModC ℤ).coeff n : ↥A₀) := by
    apply Subtype.ext
    show (jqModC (AlgebraicClosure ℚ)).coeff n = (((jqModC ℤ).coeff n : ↥A₀) : AlgebraicClosure ℚ)
    rw [jqModC_eq_map_intCast (K := AlgebraicClosure ℚ), HahnSeries.map_coeff, eq_intCast, SubringClass.coe_intCast]
  rw [hz, map_intCast, jqModC_eq_map_intCast (K := k), HahnSeries.map_coeff, eq_intCast]

private theorem redRes_jqModC :
    CharPReduction.redRes A₀ red₀ (CharPReduction.modularRing (1 * q) A₀)
        (CharPReduction.modularRing_le_integralCoeffs (1 * q) A₀)
        ⟨jqModC (AlgebraicClosure ℚ), CharPReduction.jqModC_mem_modularRing (1 * q) A₀⟩
      = jqModC k := by
  ext n
  rw [CharPReduction.redRes_apply, CharPReduction.coeffRed_coeff]
  exact red_coeff_jqModC red₀ n _

private theorem redRes_jqNModC :
    CharPReduction.redRes A₀ red₀ (CharPReduction.modularRing (1 * q) A₀)
        (CharPReduction.modularRing_le_integralCoeffs (1 * q) A₀)
        ⟨jqNModC (AlgebraicClosure ℚ) (1 * q), CharPReduction.jqNModC_mem_modularRing (1 * q) A₀⟩
      = jqNModC k (1 * q) := by
  ext n
  rw [CharPReduction.redRes_apply, CharPReduction.coeffRed_coeff]
  show red₀ ⟨(jqNModC (AlgebraicClosure ℚ) (1 * q)).coeff n, _⟩ = (jqNModC k (1 * q)).coeff n
  by_cases h : ((1 * q : ℕ) : ℤ) ∣ n
  · obtain ⟨m, rfl⟩ := h
    have hm : (jqModC (AlgebraicClosure ℚ)).coeff m ∈ A₀ := CharPReduction.jqModC_mem_integralCoeffs A₀ m
    have hx : (⟨(jqNModC (AlgebraicClosure ℚ) (1 * q)).coeff ((1 * q : ℕ) * m), CharPReduction.modularRing_le_integralCoeffs
          (1 * q) A₀ (CharPReduction.jqNModC_mem_modularRing (1 * q) A₀) _⟩ : ↥A₀)
        = ⟨(jqModC (AlgebraicClosure ℚ)).coeff m, hm⟩ :=
      Subtype.ext (by show (jqNModC (AlgebraicClosure ℚ) (1 * q)).coeff _ = _; rw [jqNModC, qExpand_coeff_mul])
    rw [hx, red_coeff_jqModC red₀ m hm, jqNModC, qExpand_coeff_mul]
  · have hx : (⟨(jqNModC (AlgebraicClosure ℚ) (1 * q)).coeff n, CharPReduction.modularRing_le_integralCoeffs
          (1 * q) A₀ (CharPReduction.jqNModC_mem_modularRing (1 * q) A₀) _⟩ : ↥A₀) = 0 :=
      Subtype.ext (by show (jqNModC (AlgebraicClosure ℚ) (1 * q)).coeff n = ((0 : ↥A₀) : AlgebraicClosure ℚ)
                      rw [jqNModC, qExpand_coeff_of_not_dvd _ _ h]; rfl)
    rw [hx, map_zero, jqNModC, qExpand_coeff_of_not_dvd _ _ h]

private theorem modularEval_mem_modularRing (N : ℕ) [NeZero N] (P : MvPolynomial (Fin 2) ↥A₀) :
    modularEval N A₀ P ∈ CharPReduction.modularRing N A₀ := by
  induction P using MvPolynomial.induction_on with
  | C c =>
      rw [modularEval, MvPolynomial.eval₂Hom_C]
      exact CharPReduction.constSeries_mem_modularRing N A₀ c
  | add p r hp hr => rw [map_add]; exact add_mem hp hr
  | mul_X p i hp =>
      rw [map_mul]
      refine mul_mem hp ?_
      rw [modularEval, MvPolynomial.eval₂Hom_X']
      revert i
      refine Fin.forall_fin_two.mpr ⟨?_, ?_⟩
      · exact CharPReduction.jqModC_mem_modularRing N A₀
      · exact CharPReduction.jqNModC_mem_modularRing N A₀

private theorem redRes_modularEval [CharP k q] (P : MvPolynomial (Fin 2) ↥A₀) :
    CharPReduction.redRes A₀ red₀ (CharPReduction.modularRing (1 * q) A₀)
        (CharPReduction.modularRing_le_integralCoeffs (1 * q) A₀)
        ⟨modularEval (1 * q) A₀ P, modularEval_mem_modularRing (1 * q) P⟩
      = Polynomial.aeval (jqModC k)
          (MvPolynomial.eval₂Hom (Polynomial.C.comp red₀) ![Polynomial.X, Polynomial.X ^ q] P) := by

  let φ : MvPolynomial (Fin 2) ↥A₀ →+* LaurentSeries k :=
    (CharPReduction.redRes A₀ red₀ (CharPReduction.modularRing (1 * q) A₀)
        (CharPReduction.modularRing_le_integralCoeffs (1 * q) A₀)).comp
      ((modularEval (1 * q) A₀).codRestrict (CharPReduction.modularRing (1 * q) A₀)
        (modularEval_mem_modularRing (1 * q)))
  let ψ : MvPolynomial (Fin 2) ↥A₀ →+* LaurentSeries k :=
    (Polynomial.aeval (jqModC k)).toRingHom.comp
      (MvPolynomial.eval₂Hom (Polynomial.C.comp red₀) ![Polynomial.X, Polynomial.X ^ q])
  have hφψ : φ = ψ := by
    refine MvPolynomial.ringHom_ext (fun c => ?_) (Fin.forall_fin_two.mpr ⟨?_, ?_⟩)
    ·
      have hC : (⟨modularEval (1 * q) A₀ (MvPolynomial.C c), modularEval_mem_modularRing (1 * q) _⟩ :
            ↥(CharPReduction.modularRing (1 * q) A₀))
          = ⟨CharPReduction.constSeries A₀ c, CharPReduction.constSeries_mem_modularRing (1 * q) _ c⟩ :=
        Subtype.ext (MvPolynomial.eval₂Hom_C _ _ c)
      show CharPReduction.redRes A₀ red₀ _ _ ⟨modularEval (1 * q) A₀ (MvPolynomial.C c), _⟩
        = Polynomial.aeval (jqModC k) (MvPolynomial.eval₂Hom (Polynomial.C.comp red₀) ![Polynomial.X, Polynomial.X ^ q]
            (MvPolynomial.C c))
      rw [hC, MvPolynomial.eval₂Hom_C, RingHom.comp_apply, Polynomial.aeval_C, algebraMap_eq_single' (red₀ c)]
      ext n
      rw [CharPReduction.redRes_apply, CharPReduction.coeffRed_coeff, HahnSeries.coeff_single]
      show red₀ ⟨(CharPReduction.constSeries A₀ c).coeff n, _⟩ = _
      have hcs : ∀ m : ℤ, (CharPReduction.constSeries A₀ c).coeff m = if m = 0 then (c : AlgebraicClosure ℚ) else 0 := by
        intro m
        show (algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) (c : AlgebraicClosure ℚ)).coeff m = _
        rw [algebraMap_eq_single', HahnSeries.coeff_single]
        split_ifs <;> rfl
      by_cases hn : n = 0
      · subst hn
        have hx : (⟨(CharPReduction.constSeries A₀ c).coeff 0, CharPReduction.modularRing_le_integralCoeffs (1 * q)
            A₀ (CharPReduction.constSeries_mem_modularRing (1 * q) _ c) 0⟩ : ↥A₀) = c :=
          Subtype.ext (by show (CharPReduction.constSeries A₀ c).coeff 0 = c; rw [hcs, if_pos rfl])
        rw [hx, if_pos rfl]
      · have hx : (⟨(CharPReduction.constSeries A₀ c).coeff n, CharPReduction.modularRing_le_integralCoeffs (1 * q)
            A₀ (CharPReduction.constSeries_mem_modularRing (1 * q) _ c) n⟩ : ↥A₀) = 0 :=
          Subtype.ext (by show (CharPReduction.constSeries A₀ c).coeff n = ((0 : ↥A₀) : AlgebraicClosure ℚ);
                          rw [hcs, if_neg hn]; rfl)
        rw [hx, map_zero, if_neg hn]
    ·
      have hX : (⟨modularEval (1 * q) A₀ (MvPolynomial.X 0), modularEval_mem_modularRing (1 * q) _⟩ :
            ↥(CharPReduction.modularRing (1 * q) A₀))
          = ⟨jqModC (AlgebraicClosure ℚ), CharPReduction.jqModC_mem_modularRing (1 * q) A₀⟩ :=
        Subtype.ext (MvPolynomial.eval₂Hom_X' _ _ 0)
      show CharPReduction.redRes A₀ red₀ _ _ ⟨modularEval (1 * q) A₀ (MvPolynomial.X 0), _⟩
        = Polynomial.aeval (jqModC k) (MvPolynomial.eval₂Hom (Polynomial.C.comp red₀) ![Polynomial.X, Polynomial.X ^ q]
            (MvPolynomial.X 0))
      rw [hX, redRes_jqModC, MvPolynomial.eval₂Hom_X', Matrix.cons_val_zero, Polynomial.aeval_X]
    ·
      have hX : (⟨modularEval (1 * q) A₀ (MvPolynomial.X 1), modularEval_mem_modularRing (1 * q) _⟩ :
            ↥(CharPReduction.modularRing (1 * q) A₀))
          = ⟨jqNModC (AlgebraicClosure ℚ) (1 * q), CharPReduction.jqNModC_mem_modularRing (1 * q) A₀⟩ :=
        Subtype.ext (MvPolynomial.eval₂Hom_X' _ _ 1)
      show CharPReduction.redRes A₀ red₀ _ _ ⟨modularEval (1 * q) A₀ (MvPolynomial.X 1), _⟩
        = Polynomial.aeval (jqModC k) (MvPolynomial.eval₂Hom (Polynomial.C.comp red₀) ![Polynomial.X, Polynomial.X ^ q]
            (MvPolynomial.X 1))
      rw [hX, redRes_jqNModC, jqNModC_one_mul_eq_pow, MvPolynomial.eval₂Hom_X', Matrix.cons_val_one, Matrix.cons_val_zero,
        map_pow, Polynomial.aeval_X]
  exact RingHom.congr_fun hφψ P

omit [Fact q.Prime] in

private theorem eval_graphReduce (a : k) (P : MvPolynomial (Fin 2) ↥A₀) :
    Polynomial.eval a (MvPolynomial.eval₂Hom (Polynomial.C.comp red₀) ![Polynomial.X, Polynomial.X ^ q] P)
      = MvPolynomial.eval₂Hom red₀ ![a, a ^ q] P := by
  let φ : MvPolynomial (Fin 2) ↥A₀ →+* k :=
    (Polynomial.evalRingHom a).comp (MvPolynomial.eval₂Hom (Polynomial.C.comp red₀) ![Polynomial.X, Polynomial.X ^ q])
  have hφ : φ = MvPolynomial.eval₂Hom red₀ ![a, a ^ q] := by
    refine MvPolynomial.ringHom_ext (fun c => ?_) (Fin.forall_fin_two.mpr ⟨?_, ?_⟩)
    · show Polynomial.eval a (MvPolynomial.eval₂Hom _ _ (MvPolynomial.C c)) = _
      rw [MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_C, RingHom.comp_apply, Polynomial.eval_C]
    · show Polynomial.eval a (MvPolynomial.eval₂Hom _ _ (MvPolynomial.X 0)) = _
      rw [MvPolynomial.eval₂Hom_X', MvPolynomial.eval₂Hom_X', Matrix.cons_val_zero, Matrix.cons_val_zero, Polynomial.eval_X]
    · show Polynomial.eval a (MvPolynomial.eval₂Hom _ _ (MvPolynomial.X 1)) = _
      rw [MvPolynomial.eval₂Hom_X', MvPolynomial.eval₂Hom_X', Matrix.cons_val_one, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_zero, Polynomial.eval_pow, Polynomial.eval_X]
  exact RingHom.congr_fun hφ P

end Red

end ModularCurve.CrossingAnnulus

namespace ModularCurve
p2m_export "ModularCurve" "transcendental_jqModC jqModC jqNModC jqModC_rat map_jqModC jqModC_eq_map_intCast qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd jq jq_mem jqd_mem_full modularFunctionField_le_full qExpand_jqModC_eq_pow_unconditional deg_eq_one_modularFunctionFieldBar modularFunctionFieldBar coeffEmb coeffEmb_coeff coeffEmb_mem_laurentBaseChange CharPReduction.coeffRed_coeff CharPReduction.redRes CharPReduction.redRes_apply CharPReduction.constSeries CharPReduction.modularRing CharPReduction.jqModC_mem_modularRing CharPReduction.jqNModC_mem_modularRing CharPReduction.constSeries_mem_modularRing CharPReduction.jqModC_mem_integralCoeffs CharPReduction.modularRing_le_integralCoeffs ssJSet jWidth jWidth_of_eq_1728"
namespace CrossingAnnulus
p2m_open "ModularCurve~coeffEmb_jq"

section HasValueCalculus

variable {L F : Type*} [Field L] [Field F] [Algebra L F] {v : Place L F}

private theorem hasValue_add {g g' : F} {a a' : L} (h : v.HasValue g a) (h' : v.HasValue g' a') :
    v.HasValue (g + g') (a + a') := by
  obtain ⟨hg, hr⟩ := h
  obtain ⟨hg', hr'⟩ := h'
  refine ⟨add_mem hg hg', ?_⟩
  have hx : (⟨g + g', add_mem hg hg'⟩ : v.toValuationSubring) = ⟨g, hg⟩ + ⟨g', hg'⟩ := rfl
  rw [hx, map_add, hr, hr', map_add]

private theorem hasValue_pow {g : F} {a : L} (h : v.HasValue g a) (n : ℕ) : v.HasValue (g ^ n) (a ^ n) := by
  induction n with
  | zero => rw [pow_zero, pow_zero]; exact v.hasValue_one
  | succ n ih => rw [pow_succ, pow_succ]; exact ih.mul h

private theorem hasValue_zero_of_ord_pos (hv : v.IsRational) {g : F} (hg : 0 < v.ord g) : v.HasValue g 0 := by
  rcases eq_or_ne g 0 with rfl | hg0
  · have h := v.hasValue_algebraMap (0 : L)
    rwa [map_zero] at h
  have hmem := GaussReduction.mem_of_ord_nonneg_gen v hg0 hg.le
  have h := Place.hasValue_evalAt hv hmem
  rwa [StandardAnnulus.evalAt_eq_zero_of_ord_pos v hg0 hg] at h

private theorem hasValue_of_ord_sub_algebraMap_pos (hv : v.IsRational) {g : F} {c : L}
    (h : 0 < v.ord (g - algebraMap L F c)) : v.HasValue g c := by
  have h1 := hasValue_add (hasValue_zero_of_ord_pos hv h) (v.hasValue_algebraMap c)
  rwa [sub_add_cancel, zero_add] at h1

end HasValueCalculus

section Transfer

variable {q : ℕ} [Fact q.Prime] {A₀ : Subring (AlgebraicClosure ℚ)} {k : Type*} [Field k] [CharP k q]
  (red₀ : ↥A₀ →+* k)

private theorem pointEval_eq_zero_of_modularEval_eq_zero (a : k) {P : MvPolynomial (Fin 2) ↥A₀}
    (hP : modularEval (1 * q) A₀ P = 0) : pointEval A₀ red₀ a (a ^ q) P = 0 := by
  have hred := redRes_modularEval red₀ P
  have hzero : (⟨modularEval (1 * q) A₀ P, modularEval_mem_modularRing (1 * q) P⟩ :
      ↥(CharPReduction.modularRing (1 * q) A₀)) = 0 := Subtype.ext hP
  rw [hzero, map_zero] at hred
  have hQ : MvPolynomial.eval₂Hom (Polynomial.C.comp red₀) ![Polynomial.X, Polynomial.X ^ q] P = 0 := by
    by_contra hne
    exact transcendental_jqModC k ⟨_, hne, hred.symm⟩
  show MvPolynomial.eval₂Hom red₀ ![a, a ^ q] P = 0
  rw [← eval_graphReduce red₀ a P, hQ, Polynomial.eval_zero]

private theorem modularEval_ne_zero_of_pointEval_ne_zero (a : k) {P : MvPolynomial (Fin 2) ↥A₀}
    (h : pointEval A₀ red₀ a (a ^ q) P ≠ 0) : modularEval (1 * q) A₀ P ≠ 0 :=
  fun hP => h (pointEval_eq_zero_of_modularEval_eq_zero red₀ a hP)

private theorem modularEval_mem_modularFunctionFieldBar (P : MvPolynomial (Fin 2) ↥A₀) :
    modularEval (1 * q) A₀ P ∈ modularFunctionFieldBar (1 * q) := by
  induction P using MvPolynomial.induction_on with
  | C c =>
      rw [modularEval, MvPolynomial.eval₂Hom_C]
      exact (modularFunctionFieldBar (1 * q)).algebraMap_mem (c : AlgebraicClosure ℚ)
  | add p r hp hr => rw [map_add]; exact add_mem hp hr
  | mul_X p i hp =>
      rw [map_mul]
      refine mul_mem hp ?_
      rw [modularEval, MvPolynomial.eval₂Hom_X']
      revert i
      refine Fin.forall_fin_two.mpr ⟨?_, ?_⟩
      · have h : coeffEmb (AlgebraicClosure ℚ) jq ∈ modularFunctionFieldBar (1 * q) := (jEltBar q).2
        rw [coeffEmb_jq] at h
        exact h
      · have h : coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * q) jq) ∈ modularFunctionFieldBar (1 * q) :=
          (jqEltBar q).2
        rw [coeffEmb_qExpand_jq] at h
        exact h

end Transfer

section Point

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {k : Type*} [Field k] [CharP k q]
  (red : A →+* k) (K : IntermediateField ℚ (AlgebraicClosure ℚ))

private theorem coeffSubring_le : coeffSubring A K ≤ A.toSubring := inf_le_left

private def inclA : ↥(coeffSubring A K) →+* ↥A := Subring.inclusion (coeffSubring_le (A := A) K)

private def evalA (x y : ↥A) : MvPolynomial (Fin 2) ↥(coeffSubring A K) →+* ↥A :=
  MvPolynomial.eval₂Hom (inclA K) ![x, y]

private theorem red_evalA (x y : ↥A) (P : MvPolynomial (Fin 2) ↥(coeffSubring A K)) :
    red (evalA K x y P) = pointEval (coeffSubring A K) (redRestrict red K) (red x) (red y) P := by
  show ((red : ↥A →+* k).comp (evalA K x y)) P
    = (MvPolynomial.eval₂Hom (redRestrict red K) ![red x, red y]) P
  refine RingHom.congr_fun (MvPolynomial.ringHom_ext (fun c => ?_) (Fin.forall_fin_two.mpr ⟨?_, ?_⟩)) P
  · rw [RingHom.comp_apply, evalA, MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_C]
    rfl
  · rw [RingHom.comp_apply, evalA, MvPolynomial.eval₂Hom_X', MvPolynomial.eval₂Hom_X']
    rfl
  · rw [RingHom.comp_apply, evalA, MvPolynomial.eval₂Hom_X', MvPolynomial.eval₂Hom_X']
    rfl

variable {K} in

private theorem isUnit_evalA_of_pointEval_ne_zero (hker : ∀ c : A, red c = 0 ↔ c ∈ IsLocalRing.maximalIdeal A)
    {x y : ↥A} {P : MvPolynomial (Fin 2) ↥(coeffSubring A K)}
    (h : pointEval (coeffSubring A K) (redRestrict red K) (red x) (red y) P ≠ 0) : IsUnit (evalA K x y P) := by
  have hne : red (evalA K x y P) ≠ 0 := by rwa [red_evalA]
  by_contra hnu
  exact hne ((hker _).mpr ((IsLocalRing.mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr hnu)))

private theorem coe_unit_inv {s : ↥A} (hs : IsUnit s) :
    (((hs.unit⁻¹ : (↥A)ˣ) : ↥A) : AlgebraicClosure ℚ) = ((s : ↥A) : AlgebraicClosure ℚ)⁻¹ := by
  have h : ((s : ↥A) : AlgebraicClosure ℚ) * (((hs.unit⁻¹ : (↥A)ˣ) : ↥A) : AlgebraicClosure ℚ) = 1 := by
    rw [← MulMemClass.coe_mul, IsUnit.mul_val_inv, OneMemClass.coe_one]
  exact eq_inv_of_mul_eq_one_right h

variable (q) in

private def evalF : MvPolynomial (Fin 2) ↥(coeffSubring A K) →+* ↥(modularFunctionFieldBar (1 * q)) :=
  MvPolynomial.eval₂Hom
    ((algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))).comp (coeffSubring A K).subtype) ![jEltBar q, jqEltBar q]

private theorem evalF_X_zero : evalF q K (MvPolynomial.X 0 : MvPolynomial (Fin 2) ↥(coeffSubring A K)) = jEltBar q := by
  rw [evalF, MvPolynomial.eval₂Hom_X']
  rfl

private theorem evalF_X_one : evalF q K (MvPolynomial.X 1 : MvPolynomial (Fin 2) ↥(coeffSubring A K)) = jqEltBar q := by
  rw [evalF, MvPolynomial.eval₂Hom_X']
  rfl

private theorem evalA_X_zero (x y : ↥A) : evalA K x y (MvPolynomial.X 0) = x := by
  rw [evalA, MvPolynomial.eval₂Hom_X']
  rfl

private theorem evalA_X_one (x y : ↥A) : evalA K x y (MvPolynomial.X 1) = y := by
  rw [evalA, MvPolynomial.eval₂Hom_X']
  rfl

private theorem modularEval_X_zero : modularEval (1 * q) (coeffSubring A K) (MvPolynomial.X 0) = jqModC (AlgebraicClosure ℚ) := by
  rw [modularEval, MvPolynomial.eval₂Hom_X']
  rfl

private theorem modularEval_X_one : modularEval (1 * q) (coeffSubring A K) (MvPolynomial.X 1) = jqNModC (AlgebraicClosure ℚ) (1 * q) := by
  rw [modularEval, MvPolynomial.eval₂Hom_X']
  rfl

private theorem coe_evalF (P : MvPolynomial (Fin 2) ↥(coeffSubring A K)) :
    ((evalF q K P : ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ)) = modularEval (1 * q) (coeffSubring A K) P := by
  induction P using MvPolynomial.induction_on with
  | C c =>
      rw [evalF, modularEval, MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_C]
      rfl
  | add p r hp hr => rw [map_add, map_add, IntermediateField.coe_add, hp, hr]
  | mul_X p i hp =>
      rw [map_mul, map_mul, IntermediateField.coe_mul, hp]
      revert i
      refine Fin.forall_fin_two.mpr ⟨?_, ?_⟩
      · rw [evalF_X_zero, modularEval_X_zero]
        exact congrArg (fun z => modularEval (1 * q) (coeffSubring A K) p * z) coeffEmb_jq
      · rw [evalF_X_one, modularEval_X_one]
        exact congrArg (fun z => modularEval (1 * q) (coeffSubring A K) p * z) (coeffEmb_qExpand_jq (1 * q))

private theorem hasValue_evalF {W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))} {x y : ↥A}
    (hx : W.HasValue (jEltBar q) (x : AlgebraicClosure ℚ)) (hy : W.HasValue (jqEltBar q) (y : AlgebraicClosure ℚ))
    (P : MvPolynomial (Fin 2) ↥(coeffSubring A K)) :
    W.HasValue (evalF q K P) ((evalA K x y P : ↥A) : AlgebraicClosure ℚ) := by
  induction P using MvPolynomial.induction_on with
  | C c =>
      rw [evalF, evalA, MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_C]
      exact W.hasValue_algebraMap (c : AlgebraicClosure ℚ)
  | add p r hp hr =>
      rw [map_add, map_add, AddMemClass.coe_add]
      exact hasValue_add hp hr
  | mul_X p i hp =>
      rw [map_mul, map_mul, MulMemClass.coe_mul]
      revert i
      refine Fin.forall_fin_two.mpr ⟨?_, ?_⟩
      · rw [evalF_X_zero, evalA_X_zero]
        exact hp.mul hx
      · rw [evalF_X_one, evalA_X_one]
        exact hp.mul hy

variable {K} (a : k)

private theorem mem_modularFunctionFieldBar_of_mem {f : LaurentSeries (AlgebraicClosure ℚ)}
    (hf : f ∈ modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)) :
    f ∈ modularFunctionFieldBar (1 * q) := by
  obtain ⟨r, s, hs, hfs⟩ := hf
  have hs0 : modularEval (1 * q) (coeffSubring A K) s ≠ 0 := modularEval_ne_zero_of_pointEval_ne_zero (redRestrict red K) a hs
  have hf' : f = modularEval (1 * q) (coeffSubring A K) r * (modularEval (1 * q) (coeffSubring A K) s)⁻¹ := by
    rw [← hfs, mul_assoc, mul_inv_cancel₀ hs0, mul_one]
  rw [hf']
  exact mul_mem (modularEval_mem_modularFunctionFieldBar r) (inv_mem (modularEval_mem_modularFunctionFieldBar s))

private def toFHom : ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)) →+* ↥(modularFunctionFieldBar (1 * q)) where
  toFun f := ⟨(f : LaurentSeries (AlgebraicClosure ℚ)), mem_modularFunctionFieldBar_of_mem red a f.2⟩
  map_one' := Subtype.ext rfl
  map_mul' _ _ := Subtype.ext rfl
  map_zero' := Subtype.ext rfl
  map_add' _ _ := Subtype.ext rfl

private theorem coe_toFHom (f : ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))) : ((toFHom red a f : ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ)) = f := rfl

private theorem toFHom_injective : Function.Injective (toFHom (K := K) red a) := by
  intro f g h
  exact Subtype.ext (congrArg (fun z : ↥(modularFunctionFieldBar (1 * q)) => (z : LaurentSeries (AlgebraicClosure ℚ))) h)

private theorem isUnit_of_pointEval_ne_zero {f : ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))}
    {r s : MvPolynomial (Fin 2) ↥(coeffSubring A K)} (hr : pointEval (coeffSubring A K) (redRestrict red K) a (a ^ q) r ≠ 0)
    (hfs : (f : LaurentSeries (AlgebraicClosure ℚ)) * modularEval (1 * q) (coeffSubring A K) s = modularEval (1 * q) (coeffSubring A K) r) : IsUnit f := by
  have hr0 : modularEval (1 * q) (coeffSubring A K) r ≠ 0 := modularEval_ne_zero_of_pointEval_ne_zero (redRestrict red K) a hr
  have hf0 : (f : LaurentSeries (AlgebraicClosure ℚ)) ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hfs
    exact hr0 hfs.symm
  have hinv : (f : LaurentSeries (AlgebraicClosure ℚ))⁻¹ ∈ modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) := by
    refine ⟨s, r, hr, ?_⟩
    rw [← hfs, ← mul_assoc, inv_mul_cancel₀ hf0, one_mul (modularEval (1 * q) (coeffSubring A K) s)]
  refine IsUnit.of_mul_eq_one ⟨_, hinv⟩ (Subtype.ext ?_)
  show (f : LaurentSeries (AlgebraicClosure ℚ)) * (f : LaurentSeries (AlgebraicClosure ℚ))⁻¹ = 1
  exact mul_inv_cancel₀ hf0

private theorem isLocalRing_nodeRing :
    IsLocalRing ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)) := by
  refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun f => ?_
  obtain ⟨r, s, hs, hfs⟩ := f.2
  by_cases hr : pointEval (coeffSubring A K) (redRestrict red K) a (a ^ q) r = 0
  · right
    refine isUnit_of_pointEval_ne_zero red a (r := s - r) (s := s) ?_ ?_
    · rw [map_sub, hr, sub_zero]
      exact hs
    · show ((1 : LaurentSeries (AlgebraicClosure ℚ)) - (f : LaurentSeries (AlgebraicClosure ℚ))) * modularEval (1 * q) (coeffSubring A K) s = modularEval (1 * q) (coeffSubring A K) (s - r)
      rw [map_sub, sub_mul, one_mul (modularEval (1 * q) (coeffSubring A K) s), hfs]
  · left
    exact isUnit_of_pointEval_ne_zero red a hr hfs

private theorem pointEval_eq_zero_of_not_isUnit {f : ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))} (hf : ¬ IsUnit f)
    {r s : MvPolynomial (Fin 2) ↥(coeffSubring A K)}
    (hfs : (f : LaurentSeries (AlgebraicClosure ℚ)) * modularEval (1 * q) (coeffSubring A K) s = modularEval (1 * q) (coeffSubring A K) r) : pointEval (coeffSubring A K) (redRestrict red K) a (a ^ q) r = 0 := by
  by_contra hr
  exact hf (isUnit_of_pointEval_ne_zero red a hr hfs)

private theorem pointEval_ne_zero_of_isUnit {f : ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))} (hf : IsUnit f)
    {r s : MvPolynomial (Fin 2) ↥(coeffSubring A K)} (hs : pointEval (coeffSubring A K) (redRestrict red K) a (a ^ q) s ≠ 0)
    (hfs : (f : LaurentSeries (AlgebraicClosure ℚ)) * modularEval (1 * q) (coeffSubring A K) s = modularEval (1 * q) (coeffSubring A K) r) : pointEval (coeffSubring A K) (redRestrict red K) a (a ^ q) r ≠ 0 := by
  obtain ⟨g, hg⟩ := hf.exists_right_inv
  obtain ⟨r', s', hs', hgs⟩ := g.2
  have hfg : (f : LaurentSeries (AlgebraicClosure ℚ)) * (g : LaurentSeries (AlgebraicClosure ℚ)) = 1 := by
    have h := congrArg Subtype.val hg
    exact h
  have h1 : modularEval (1 * q) (coeffSubring A K) (s * s') = modularEval (1 * q) (coeffSubring A K) (r * r') := by
    rw [map_mul, map_mul, ← hfs, ← hgs]
    calc modularEval (1 * q) (coeffSubring A K) s * modularEval (1 * q) (coeffSubring A K) s' = ((f : LaurentSeries (AlgebraicClosure ℚ)) * (g : LaurentSeries (AlgebraicClosure ℚ))) * (modularEval (1 * q) (coeffSubring A K) s * modularEval (1 * q) (coeffSubring A K) s') := by
          rw [hfg]; exact (one_mul _).symm
      _ = (f : LaurentSeries (AlgebraicClosure ℚ)) * modularEval (1 * q) (coeffSubring A K) s * ((g : LaurentSeries (AlgebraicClosure ℚ)) * modularEval (1 * q) (coeffSubring A K) s') := by ring
  have h2 : pointEval (coeffSubring A K) (redRestrict red K) a (a ^ q) (s * s' - r * r') = 0 :=
    pointEval_eq_zero_of_modularEval_eq_zero (redRestrict red K) a (by rw [map_sub, h1, sub_self])
  rw [map_sub, map_mul, map_mul, sub_eq_zero] at h2
  intro hr
  rw [hr, zero_mul] at h2
  exact mul_ne_zero hs hs' h2

private theorem exists_value (hker : ∀ c : A, red c = 0 ↔ c ∈ IsLocalRing.maximalIdeal A)
    {W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))} {x y : ↥A} (hxa : red x = a) (hya : red y = a ^ q)
    (hx : W.HasValue (jEltBar q) (x : AlgebraicClosure ℚ)) (hy : W.HasValue (jqEltBar q) (y : AlgebraicClosure ℚ))
    (f : ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))) :
    ∃ c : ↥A, W.HasValue (toFHom red a f) (c : AlgebraicClosure ℚ) ∧
      (¬ IsUnit f → c ∈ IsLocalRing.maximalIdeal A) ∧ (IsUnit f → IsUnit c) := by
  obtain ⟨r, s, hs, hfs⟩ := f.2
  have hsU : IsUnit (evalA K x y s) := isUnit_evalA_of_pointEval_ne_zero red hker (by rwa [hxa, hya])
  have hs0 : ((evalA K x y s : ↥A) : AlgebraicClosure ℚ) ≠ 0 := fun h => hsU.ne_zero (Subtype.ext h)
  have hvs := hasValue_evalF K hx hy s
  have hvr := hasValue_evalF K hx hy r
  have hF : toFHom red a f * evalF q K s = evalF q K r := by
    apply Subtype.ext
    show (f : LaurentSeries (AlgebraicClosure ℚ)) * ((evalF q K s : ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ)) = ((evalF q K r : ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ))
    rw [coe_evalF, coe_evalF]
    exact hfs
  have h1 : toFHom red a f = evalF q K r * (evalF q K s)⁻¹ := by
    rw [← hF, mul_assoc, mul_inv_cancel₀ (hvs.ne_zero hs0), mul_one]
  refine ⟨evalA K x y r * ((hsU.unit⁻¹ : (↥A)ˣ) : ↥A), ?_, ?_, ?_⟩
  · rw [MulMemClass.coe_mul, coe_unit_inv, h1]
    exact hvr.mul (hvs.inv hs0)
  · intro hf
    have hr : pointEval (coeffSubring A K) (redRestrict red K) a (a ^ q) r = 0 := pointEval_eq_zero_of_not_isUnit red a hf hfs
    apply (hker _).mp
    rw [map_mul, red_evalA, hxa, hya, hr, zero_mul]
  · intro hf
    have hr := pointEval_ne_zero_of_isUnit red a hf hs hfs
    have hrU : IsUnit (evalA K x y r) := isUnit_evalA_of_pointEval_ne_zero red hker (by rwa [hxa, hya])
    exact hrU.mul (Units.isUnit _)

end Point

end ModularCurve.CrossingAnnulus

namespace ModularCurve
p2m_export "ModularCurve" "transcendental_jqModC jqModC jqNModC jqModC_rat map_jqModC jqModC_eq_map_intCast qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd jq jq_mem jqd_mem_full modularFunctionField_le_full qExpand_jqModC_eq_pow_unconditional deg_eq_one_modularFunctionFieldBar modularFunctionFieldBar coeffEmb coeffEmb_coeff coeffEmb_mem_laurentBaseChange CharPReduction.coeffRed_coeff CharPReduction.redRes CharPReduction.redRes_apply CharPReduction.constSeries CharPReduction.modularRing CharPReduction.jqModC_mem_modularRing CharPReduction.jqNModC_mem_modularRing CharPReduction.constSeries_mem_modularRing CharPReduction.jqModC_mem_integralCoeffs CharPReduction.modularRing_le_integralCoeffs ssJSet jWidth jWidth_of_eq_1728"
namespace CrossingBootstrap
p2m_open "ModularCurve~coeffEmb_jq"

open Polynomial ModularCurve.CrossingAnnulus

section Basic

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {k : Type*} [Field k] [CharP k q]
  (red : A →+* k) (hker : ∀ c : A, red c = 0 ↔ c ∈ IsLocalRing.maximalIdeal A)

omit [Fact (Nat.Prime q)] in

private theorem exists_eq_pow_mul_of_not_dvd {t : ↥A} (i : ℕ) (h : ¬ ((q : ℕ) : ↥A) ∣ t ^ i) :
    ∃ u : ↥A, u ∈ IsLocalRing.maximalIdeal A ∧ ((q : ℕ) : ↥A) = t ^ i * u := by
  rcases ValuationRing.dvd_total (t ^ i) ((q : ℕ) : ↥A) with ⟨u, hu⟩ | hdvd
  · refine ⟨u, ?_, hu⟩
    by_contra hum
    have hU : IsUnit u := by
      by_contra hnu
      exact hum ((IsLocalRing.mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr hnu))
    apply h
    refine ⟨((hU.unit⁻¹ : (↥A)ˣ) : ↥A), ?_⟩
    rw [hu, mul_assoc, IsUnit.mul_val_inv, mul_one]
  · exact absurd hdvd h

include hker in

private theorem exists_natCast_dvd_pow {t : ↥A} (ht : t ∈ IsLocalRing.maximalIdeal A) :
    ∃ M : ℕ, ((q : ℕ) : ↥A) ∣ t ^ M := by
  have hFq : q.Prime := Fact.out
  by_cases ht0 : t = 0
  · exact ⟨1, by rw [ht0, pow_one]; exact dvd_zero _⟩
  by_contra hno
  push Not at hno

  have halg : IsAlgebraic ℤ ((t : ↥A) : AlgebraicClosure ℚ) :=
    (IsFractionRing.isAlgebraic_iff ℤ ℚ (AlgebraicClosure ℚ)).mpr (Algebra.IsAlgebraic.isAlgebraic _)
  obtain ⟨P, hP0, hPt⟩ := halg
  have hinj : Function.Injective (Int.castRingHom ↥A) := Int.cast_injective
  have hevalP : P.eval₂ (Int.castRingHom ↥A) t = 0 := by
    have h1 : (algebraMap ↥A (AlgebraicClosure ℚ)) (P.eval₂ (Int.castRingHom ↥A) t) = 0 := by
      rw [Polynomial.hom_eval₂,
        Subsingleton.elim ((algebraMap ↥A (AlgebraicClosure ℚ)).comp (Int.castRingHom ↥A)) (algebraMap ℤ (AlgebraicClosure ℚ)),
        ← Polynomial.aeval_def]
      exact hPt
    exact Subtype.ext h1
  have heval : P.primPart.eval₂ (Int.castRingHom ↥A) t = 0 := Polynomial.eval₂_primPart_eq_zero hinj hP0 hevalP

  have hcoeff : ∀ i, (q : ℤ) ∣ P.primPart.coeff i := by
    intro i
    induction i using Nat.strong_induction_on with
    | _ i IH =>
      by_cases hi : P.primPart.natDegree < i
      · rw [Polynomial.coeff_eq_zero_of_natDegree_lt hi]
        exact dvd_zero _
      push Not at hi
      have hsum := heval
      rw [Polynomial.eval₂_eq_sum_range, Finset.range_eq_Ico,
        ← Finset.sum_Ico_consecutive _ (Nat.zero_le i) (Nat.le_succ_of_le hi),
        ← Finset.sum_Ico_consecutive _ (Nat.le_succ i) (Nat.succ_le_succ hi), Nat.Ico_succ_singleton,
        Finset.sum_singleton] at hsum
      obtain ⟨u, hum, hqu⟩ := exists_eq_pow_mul_of_not_dvd i (hno i)
      have hlow : t ^ i * u ∣ ∑ j ∈ Finset.Ico 0 i, (Int.castRingHom ↥A) (P.primPart.coeff j) * t ^ j := by
        rw [← hqu]
        refine Finset.dvd_sum fun j hj => ?_
        obtain ⟨b, hb⟩ := IH j (Finset.mem_Ico.mp hj).2
        refine ⟨(b : ↥A) * t ^ j, ?_⟩
        rw [hb, map_mul, map_natCast, eq_intCast, mul_assoc]
      have hhigh : t ^ i * t ∣ ∑ j ∈ Finset.Ico (i + 1) (P.primPart.natDegree + 1),
          (Int.castRingHom ↥A) (P.primPart.coeff j) * t ^ j := by
        refine Finset.dvd_sum fun j hj => ?_
        rw [← pow_succ]
        exact Dvd.dvd.mul_left (pow_dvd_pow t (Finset.mem_Ico.mp hj).1) _
      obtain ⟨ℓ, hℓ⟩ := hlow
      obtain ⟨h', hh'⟩ := hhigh
      rw [hℓ, hh'] at hsum
      have hai : (Int.castRingHom ↥A) (P.primPart.coeff i) = -(u * ℓ) - t * h' := by
        have hti : t ^ i ≠ 0 := pow_ne_zero i ht0
        apply mul_left_cancel₀ hti
        linear_combination hsum
      have hmi : (Int.castRingHom ↥A) (P.primPart.coeff i) ∈ IsLocalRing.maximalIdeal A := by
        rw [hai]
        exact sub_mem (neg_mem (Ideal.mul_mem_right _ _ hum)) (Ideal.mul_mem_right _ _ ht)
      have hred : red ((P.primPart.coeff i : ℤ) : ↥A) = 0 := (hker _).mpr (by rwa [eq_intCast] at hmi)
      rw [map_intCast] at hred
      exact (CharP.intCast_eq_zero_iff k q _).mp hred
  have hC : Polynomial.C (q : ℤ) ∣ P.primPart := (Polynomial.C_dvd_iff_dvd_coeff _ _).mpr hcoeff
  have hU : IsUnit (q : ℤ) := (Polynomial.isPrimitive_iff_isUnit_of_C_dvd.mp P.isPrimitive_primPart) _ hC
  exact hFq.ne_one (Nat.isUnit_iff.mp (Int.ofNat_isUnit.mp hU))

variable (K : IntermediateField ℚ (AlgebraicClosure ℚ))

omit [Fact (Nat.Prime q)] [CharP k q] in
include hker in

private theorem isUnit_of_redRestrict_ne_zero {z : ↥(coeffSubring A K)} (hz : redRestrict red K z ≠ 0) : IsUnit z := by
  have hzA : IsUnit (inclA K z) := by
    by_contra hnu
    exact hz ((hker _).mpr ((IsLocalRing.mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr hnu)))
  have hz0 : (z : AlgebraicClosure ℚ) ≠ 0 := by
    intro h0
    apply hz
    rw [show z = 0 from Subtype.ext h0, map_zero]
  obtain ⟨v, hv⟩ := hzA.exists_right_inv
  have hv' : (v : AlgebraicClosure ℚ) = (z : AlgebraicClosure ℚ)⁻¹ := by
    have h : (z : AlgebraicClosure ℚ) * (v : AlgebraicClosure ℚ) = 1 := by
      have h' := congrArg (fun w : ↥A => (w : AlgebraicClosure ℚ)) hv
      exact h'
    exact (eq_inv_of_mul_eq_one_right h).trans rfl
  have hinv : (z : AlgebraicClosure ℚ)⁻¹ ∈ coeffSubring A K := by
    refine ⟨?_, ?_⟩
    · rw [← hv']
      exact v.2
    · exact K.inv_mem (show (z : AlgebraicClosure ℚ) ∈ K from z.2.2)
  exact IsUnit.of_mul_eq_one ⟨_, hinv⟩ (Subtype.ext (mul_inv_cancel₀ hz0))

omit [Fact (Nat.Prime q)] [CharP k q] in

private theorem redRestrict_eval (x₀ y₀ : ↥(coeffSubring A K)) (P : MvPolynomial (Fin 2) ↥(coeffSubring A K)) :
    redRestrict red K (MvPolynomial.eval ![x₀, y₀] P)
      = pointEval (coeffSubring A K) (redRestrict red K) (redRestrict red K x₀) (redRestrict red K y₀) P := by
  show ((redRestrict red K).comp (MvPolynomial.eval ![x₀, y₀])) P
    = (MvPolynomial.eval₂Hom (redRestrict red K) ![redRestrict red K x₀, redRestrict red K y₀]) P
  refine RingHom.congr_fun (MvPolynomial.ringHom_ext (fun c => ?_) (Fin.forall_fin_two.mpr ⟨?_, ?_⟩)) P
  · rw [RingHom.comp_apply, MvPolynomial.eval_C, MvPolynomial.eval₂Hom_C]
  · rw [RingHom.comp_apply, MvPolynomial.eval_X, MvPolynomial.eval₂Hom_X']
    rfl
  · rw [RingHom.comp_apply, MvPolynomial.eval_X, MvPolynomial.eval₂Hom_X']
    rfl

end Basic

section Ev

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {k : Type*} [Field k] [CharP k q]
  (red : A →+* k) (hker : ∀ c : A, red c = 0 ↔ c ∈ IsLocalRing.maximalIdeal A) (a : k)
  {K : IntermediateField ℚ (AlgebraicClosure ℚ)}
  {W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))} {x y : ↥A} (hxa : red x = a) (hya : red y = a ^ q)
  (hx : W.HasValue (jEltBar q) (x : AlgebraicClosure ℚ)) (hy : W.HasValue (jqEltBar q) (y : AlgebraicClosure ℚ))

private noncomputable def ev (f : ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))) : ↥A :=
  Classical.choose (exists_value (K := K) red a hker hxa hya hx hy f)

private theorem hasValue_ev (f : ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))) :
    W.HasValue (toFHom red a f) (ev red hker a hxa hya hx hy f : AlgebraicClosure ℚ) :=
  (Classical.choose_spec (exists_value (K := K) red a hker hxa hya hx hy f)).1

private theorem isUnit_ev {f : ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))} (hf : IsUnit f) : IsUnit (ev red hker a hxa hya hx hy f) :=
  (Classical.choose_spec (exists_value (K := K) red a hker hxa hya hx hy f)).2.2 hf

private theorem ev_eq {f : ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))} {c : ↥A} (h : W.HasValue (toFHom red a f) (c : AlgebraicClosure ℚ)) :
    ev red hker a hxa hya hx hy f = c :=
  Subtype.ext ((hasValue_ev red hker a hxa hya hx hy f).unique h)

private noncomputable def evHom : ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)) →+* ↥A where
  toFun := ev red hker a hxa hya hx hy
  map_one' := by
    apply ev_eq
    rw [map_one, OneMemClass.coe_one]
    have h := W.hasValue_algebraMap (1 : AlgebraicClosure ℚ)
    rwa [map_one] at h
  map_mul' f g := by
    apply ev_eq
    rw [map_mul, MulMemClass.coe_mul]
    exact (hasValue_ev red hker a hxa hya hx hy f).mul (hasValue_ev red hker a hxa hya hx hy g)
  map_zero' := by
    apply ev_eq
    rw [map_zero, ZeroMemClass.coe_zero]
    have h := W.hasValue_algebraMap (0 : AlgebraicClosure ℚ)
    rwa [map_zero] at h
  map_add' f g := by
    apply ev_eq
    rw [map_add, AddMemClass.coe_add]
    exact hasValue_add (hasValue_ev red hker a hxa hya hx hy f) (hasValue_ev red hker a hxa hya hx hy g)

private theorem hasValue_evHom (f : ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))) :
    W.HasValue (toFHom red a f) (evHom red hker a hxa hya hx hy f : AlgebraicClosure ℚ) :=
  hasValue_ev red hker a hxa hya hx hy f

private theorem evHom_eq {f : ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))} {c : ↥A} (h : W.HasValue (toFHom red a f) (c : AlgebraicClosure ℚ)) :
    evHom red hker a hxa hya hx hy f = c :=
  ev_eq red hker a hxa hya hx hy h

private theorem isUnit_evHom {f : ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))} (hf : IsUnit f) : IsUnit (evHom red hker a hxa hya hx hy f) :=
  isUnit_ev red hker a hxa hya hx hy hf

private theorem evHom_modularEval (P : MvPolynomial (Fin 2) ↥(coeffSubring A K)) :
    evHom red hker a hxa hya hx hy ⟨modularEval (1 * q) (coeffSubring A K) P,
        modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) P⟩
      = evalA K x y P := by
  apply evHom_eq
  have h : toFHom red a ⟨modularEval (1 * q) (coeffSubring A K) P,
      modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) P⟩ = evalF q K P := by
    apply Subtype.ext
    rw [coe_toFHom, coe_evalF]
  rw [h]
  exact hasValue_evalF K hx hy P

private theorem evHom_const (c₀ : ↥(coeffSubring A K)) :
    evHom red hker a hxa hya hx hy ⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C c₀),
        modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩
      = inclA K c₀ := by
  rw [evHom_modularEval, evalA, MvPolynomial.eval₂Hom_C]

end Ev

section Decomp

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {k : Type*} [Field k] [CharP k q]
  (red : A →+* k) (hker : ∀ c : A, red c = 0 ↔ c ∈ IsLocalRing.maximalIdeal A) (a : k)
  {K : IntermediateField ℚ (AlgebraicClosure ℚ)}

include hker in

private theorem exists_decomp [IsLocalRing ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))] (ϖ : ↥(coeffSubring A K)) (G' H' : ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)))
    (hmax : IsLocalRing.maximalIdeal ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)) = Ideal.span {(⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ),
      modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ :
      ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))), G', H'})
    (x₀ y₀ : ↥(coeffSubring A K)) (hx₀ : redRestrict red K x₀ = a) (hy₀ : redRestrict red K y₀ = a ^ q)
    (f : ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))) :
    ∃ (a₀ : ↥(coeffSubring A K)) (r₁ r₂ r₃ : ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))),
      f = ⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C a₀),
            modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩
          + (⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ),
      modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ :
      ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))) * r₁ + G' * r₂ + H' * r₃ := by
  obtain ⟨r, s, hs, hfs⟩ := f.2
  have hredE : ∀ P : MvPolynomial (Fin 2) ↥(coeffSubring A K),
      redRestrict red K (MvPolynomial.eval ![x₀, y₀] P) = pointEval (coeffSubring A K) (redRestrict red K) a (a ^ q) P := by
    intro P
    rw [redRestrict_eval, hx₀, hy₀]
  have hsU : IsUnit (MvPolynomial.eval ![x₀, y₀] s) :=
    isUnit_of_redRestrict_ne_zero red hker K (by rw [hredE]; exact hs)
  set a₀ : ↥(coeffSubring A K) := MvPolynomial.eval ![x₀, y₀] r * ((hsU.unit⁻¹ : (↥(coeffSubring A K))ˣ) :
    ↥(coeffSubring A K)) with ha₀
  have hreda₀ : redRestrict red K a₀ * pointEval (coeffSubring A K) (redRestrict red K) a (a ^ q) s
      = pointEval (coeffSubring A K) (redRestrict red K) a (a ^ q) r := by
    rw [ha₀, ← hredE s, ← hredE r, ← map_mul, mul_assoc, IsUnit.val_inv_mul, mul_one]
  set f₀ : ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)) := ⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C a₀),
    modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ with hf₀
  have key : ((f - f₀ : ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))) : LaurentSeries (AlgebraicClosure ℚ)) * modularEval (1 * q) (coeffSubring A K) s
      = modularEval (1 * q) (coeffSubring A K) (r - MvPolynomial.C a₀ * s) := by
    rw [AddSubgroupClass.coe_sub, map_sub, map_mul, sub_mul, hfs]
  have hpt : pointEval (coeffSubring A K) (redRestrict red K) a (a ^ q) (r - MvPolynomial.C a₀ * s) = 0 := by
    rw [map_sub, map_mul, show pointEval (coeffSubring A K) (redRestrict red K) a (a ^ q) (MvPolynomial.C a₀)
      = redRestrict red K a₀ from MvPolynomial.eval₂Hom_C _ _ _, hreda₀, sub_self]
  have hnu : ¬ IsUnit (f - f₀) := fun hU => (pointEval_ne_zero_of_isUnit red a hU hs key) hpt
  have hmem : f - f₀ ∈ IsLocalRing.maximalIdeal ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)) :=
    (IsLocalRing.mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr hnu)
  rw [hmax] at hmem
  obtain ⟨b₁, h1⟩ := (Ideal.mem_span_insert' _ _ _).mp hmem
  obtain ⟨b₂, h2⟩ := (Ideal.mem_span_insert' _ _ _).mp h1
  obtain ⟨b₃, h3⟩ := Ideal.mem_span_singleton'.mp h2
  refine ⟨a₀, -b₁, -b₂, b₃, ?_⟩
  linear_combination -h3

end Decomp

section Bootstrap

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {k : Type*} [Field k] [CharP k q]
  (red : A →+* k) (hker : ∀ c : A, red c = 0 ↔ c ∈ IsLocalRing.maximalIdeal A) (a : k)
  (K : IntermediateField ℚ (AlgebraicClosure ℚ))

omit [CharP k q] in

private theorem exists_lifts {W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))} (hW : IsCentredAt red a W) :
    ∃ x y : ↥A, red x = a ∧ red y = a ^ q ∧
      W.HasValue (jEltBar q) (x : AlgebraicClosure ℚ) ∧ W.HasValue (jqEltBar q) (y : AlgebraicClosure ℚ) := by
  obtain ⟨⟨x, hxa, hxo⟩, ⟨y, hya, hyo⟩⟩ := hW
  exact ⟨x, y, hxa, hya,
    hasValue_of_ord_sub_algebraMap_pos (isRational_place_modularFunctionFieldBar (1 * q) W) hxo,
    hasValue_of_ord_sub_algebraMap_pos (isRational_place_modularFunctionFieldBar (1 * q) W) hyo⟩

omit [Fact (Nat.Prime q)] [CharP k q] in

private theorem exists_common_dvd (u v w : ↥A) : ∃ t : ↥A, (t = u ∨ t = v ∨ t = w) ∧ t ∣ u ∧ t ∣ v ∧ t ∣ w := by
  rcases ValuationRing.dvd_total u v with huv | hvu
  · rcases ValuationRing.dvd_total u w with huw | hwu
    · exact ⟨u, Or.inl rfl, dvd_rfl, huv, huw⟩
    · exact ⟨w, Or.inr (Or.inr rfl), hwu, hwu.trans huv, dvd_rfl⟩
  · rcases ValuationRing.dvd_total v w with hvw | hwv
    · exact ⟨v, Or.inr (Or.inl rfl), hvu, dvd_rfl, hvw⟩
    · exact ⟨w, Or.inr (Or.inr rfl), hwv.trans hvu, hwv, dvd_rfl⟩

include hker in

private theorem forall_natCast_pow_dvd_sub
    (x₀ y₀ : ↥(coeffSubring A K)) (hx₀ : redRestrict red K x₀ = a) (hy₀ : redRestrict red K y₀ = a ^ q)
    (ϖ : ↥(coeffSubring A K)) (hϖ : inclA K ϖ ∈ IsLocalRing.maximalIdeal A)
    (eK : ℕ) (ε : ↥(coeffSubring A K)) (hε : IsUnit ε) (hqϖ : ((q : ℕ) : ↥(coeffSubring A K)) = ϖ ^ eK * ε)
    (e : ℕ) (G' H' w : ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)))
    (hGH : G' * H' = (⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ),
      modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ :
      ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))) ^ (e * eK) * w)
    [IsLocalRing ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))]
    (hmax : IsLocalRing.maximalIdeal ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)) = Ideal.span {(⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ),
      modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ :
      ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))), G', H'})
    (c m : ↥A) (hc : c ∈ IsLocalRing.maximalIdeal A) (hm : m ∈ IsLocalRing.maximalIdeal A)
    (hcm : c * m = ((q : ℕ) : ↥A) ^ e)
    {W₁ W₂ : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))} (hW₁ : IsCentredAt red a W₁) (hW₂ : IsCentredAt red a W₂)
    (hG₁ : W₁.HasValue (toFHom red a G') (c : AlgebraicClosure ℚ))
    (hG₂ : W₂.HasValue (toFHom red a G') (c : AlgebraicClosure ℚ))
    (g : ↥(modularFunctionFieldBar (1 * q))) (hg : (g : LaurentSeries (AlgebraicClosure ℚ)) ∈
      modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)) :
    ∃ c₁ c₂ : ↥A, W₁.HasValue g (c₁ : AlgebraicClosure ℚ) ∧ W₂.HasValue g (c₂ : AlgebraicClosure ℚ) ∧
      ∀ n : ℕ, ((q : ℕ) : ↥A) ^ n ∣ (c₁ - c₂) := by
  have hFq : q.Prime := Fact.out

  obtain ⟨x₁, y₁, hx₁a, hy₁a, hx₁, hy₁⟩ := exists_lifts red a hW₁
  obtain ⟨x₂, y₂, hx₂a, hy₂a, hx₂, hy₂⟩ := exists_lifts red a hW₂
  let ev₁ : ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)) →+* ↥A := evHom red hker a hx₁a hy₁a hx₁ hy₁
  let ev₂ : ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)) →+* ↥A := evHom red hker a hx₂a hy₂a hx₂ hy₂
  have hev₁G : ev₁ G' = c := evHom_eq red hker a hx₁a hy₁a hx₁ hy₁ hG₁
  have hev₂G : ev₂ G' = c := evHom_eq red hker a hx₂a hy₂a hx₂ hy₂ hG₂
  have hev₁ϖ : ev₁ (⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ),
      modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ :
      ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))) = inclA K ϖ := evHom_const red hker a hx₁a hy₁a hx₁ hy₁ ϖ
  have hev₂ϖ : ev₂ (⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ),
      modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ :
      ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))) = inclA K ϖ := evHom_const red hker a hx₂a hy₂a hx₂ hy₂ ϖ

  set ϖA : ↥A := inclA K ϖ with hϖA
  have hεA : IsUnit (inclA K ε) := hε.map _
  set u : ↥A := ((hεA.unit⁻¹ : (↥A)ˣ) : ↥A) with hu
  have hqA : ((q : ℕ) : ↥A) = ϖA ^ eK * inclA K ε := by
    have h := congrArg (inclA K) hqϖ
    rwa [map_natCast, map_mul, map_pow] at h
  have hϖeK : ϖA ^ eK = ((q : ℕ) : ↥A) * u := by
    rw [hqA, hu, mul_assoc, IsUnit.mul_val_inv, mul_one]
  have hq0 : ((q : ℕ) : ↥A) ≠ 0 := Nat.cast_ne_zero.mpr hFq.ne_zero
  have hc0 : c ≠ 0 := by
    intro h0
    apply pow_ne_zero e hq0
    rw [← hcm, h0, zero_mul]
  have hpow : ϖA ^ (e * eK) = c * (m * u ^ e) := by
    rw [pow_mul', hϖeK, mul_pow, ← hcm, mul_assoc]
  have hh : ∀ (evw evH : ↥A), c * evH = ϖA ^ (e * eK) * evw → evH = m * (u ^ e * evw) := by
    intro evw evH h
    apply mul_left_cancel₀ hc0
    rw [h, hpow]
    ring
  have hGH₁ : c * ev₁ H' = ϖA ^ (e * eK) * ev₁ w := by
    have h := congrArg ev₁ hGH
    rwa [map_mul, map_mul, map_pow, hev₁G, hev₁ϖ] at h
  have hGH₂ : c * ev₂ H' = ϖA ^ (e * eK) * ev₂ w := by
    have h := congrArg ev₂ hGH
    rwa [map_mul, map_mul, map_pow, hev₂G, hev₂ϖ] at h
  have hH₁ : ev₁ H' = m * (u ^ e * ev₁ w) := hh _ _ hGH₁
  have hH₂ : ev₂ H' = m * (u ^ e * ev₂ w) := hh _ _ hGH₂

  obtain ⟨t, htcases, htϖ, htc, htm⟩ := exists_common_dvd ϖA c m
  have ht : t ∈ IsLocalRing.maximalIdeal A := by
    rcases htcases with rfl | rfl | rfl
    · exact hϖ
    · exact hc
    · exact hm
  obtain ⟨M, hM⟩ := exists_natCast_dvd_pow red hker ht

  have hind : ∀ n : ℕ, ∀ f : ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)), t ^ n ∣ ev₁ f - ev₂ f := by
    intro n
    induction n with
    | zero => intro f; rw [pow_zero]; exact one_dvd _
    | succ n IH =>
      intro f
      obtain ⟨a₀, r₁, r₂, r₃, hdec⟩ := exists_decomp red hker a ϖ G' H' hmax x₀ y₀ hx₀ hy₀ f
      have h₁ : ev₁ f = inclA K a₀ + ϖA * ev₁ r₁ + c * ev₁ r₂ + ev₁ H' * ev₁ r₃ := by
        rw [hdec, map_add, map_add, map_add, map_mul, map_mul, map_mul, evHom_const, hev₁ϖ, hev₁G]
      have h₂ : ev₂ f = inclA K a₀ + ϖA * ev₂ r₁ + c * ev₂ r₂ + ev₂ H' * ev₂ r₃ := by
        rw [hdec, map_add, map_add, map_add, map_mul, map_mul, map_mul, evHom_const, hev₂ϖ, hev₂G]
      have hdiff : ev₁ f - ev₂ f = ϖA * (ev₁ r₁ - ev₂ r₁) + c * (ev₁ r₂ - ev₂ r₂)
          + m * (u ^ e * ev₁ w) * (ev₁ r₃ - ev₂ r₃) + m * (u ^ e * (ev₁ w - ev₂ w)) * ev₂ r₃ := by
        rw [h₁, h₂, hH₁, hH₂]
        ring
      rw [hdiff, pow_succ]
      refine dvd_add (dvd_add (dvd_add ?_ ?_) ?_) ?_
      · rw [mul_comm (t ^ n) t]
        exact mul_dvd_mul htϖ (IH r₁)
      · rw [mul_comm (t ^ n) t]
        exact mul_dvd_mul htc (IH r₂)
      · rw [mul_comm (t ^ n) t]
        exact mul_dvd_mul (dvd_mul_of_dvd_left htm _) (IH r₃)
      · rw [mul_comm (t ^ n) t]
        refine dvd_mul_of_dvd_left (mul_dvd_mul htm (dvd_mul_of_dvd_right (IH w) _)) _

  have hgF : toFHom red a ⟨(g : LaurentSeries (AlgebraicClosure ℚ)), hg⟩ = g := Subtype.ext rfl
  refine ⟨ev₁ ⟨_, hg⟩, ev₂ ⟨_, hg⟩, ?_, ?_, fun n => ?_⟩
  · have h := hasValue_evHom red hker a hx₁a hy₁a hx₁ hy₁ ⟨(g : LaurentSeries (AlgebraicClosure ℚ)), hg⟩
    rw [hgF] at h
    exact h
  · have h := hasValue_evHom red hker a hx₂a hy₂a hx₂ hy₂ ⟨(g : LaurentSeries (AlgebraicClosure ℚ)), hg⟩
    rw [hgF] at h
    exact h
  · calc ((q : ℕ) : ↥A) ^ n ∣ (t ^ M) ^ n := pow_dvd_pow_of_dvd hM n
      _ = t ^ (M * n) := (pow_mul t M n).symm
      _ ∣ ev₁ ⟨_, hg⟩ - ev₂ ⟨_, hg⟩ := hind (M * n) _

end Bootstrap

end ModularCurve.CrossingBootstrap

end

p2m_open "AlgebraicCurve IsLocalRing ModularCurve~coeffEmb_jq P2MW.S_ModularCurve_NodeLocalized_forall_natCast_pow_dvd_sub_of_hasValue_eq_of_crossingPresentation_ofNat1728.ModularCurve"
open ModularCurve.NodeLocalized

theorem solution
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k] (red : A →+* k)
    (hker : ∀ c : A, red c = 0 ↔ c ∈ IsLocalRing.maximalIdeal A)
    (hq : 5 ≤ q) (ha : (1728 : k) ∈ ssJSet q k)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (ϖ : ↥(coeffSubring A K)) (hϖ : ∀ c : ↥(coeffSubring A K), redRestrict red K c = 0 ↔ ∃ d, c = ϖ * d)
    (eK : ℕ) (ε : ↥(coeffSubring A K)) (hε : IsUnit ε)
    (hqϖ : ((q : ℕ) : ↥(coeffSubring A K)) = ϖ ^ eK * ε)
    (G' H' w : ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (1728 : k) ((1728 : k) ^ q)))
    (hw : IsUnit w)
    (hGH : G' * H' = (⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (1728 : k) ((1728 : k) ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (1728 : k) ((1728 : k) ^ q))) ^ (jWidth (1728 : k) * eK) * w)
    (hmax : ∀ [IsLocalRing ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (1728 : k) ((1728 : k) ^ q))],
      IsLocalRing.maximalIdeal ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (1728 : k) ((1728 : k) ^ q)) =
        Ideal.span {(⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (1728 : k) ((1728 : k) ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (1728 : k) ((1728 : k) ^ q))), G', H'})
    (heK1 : 1 ≤ eK)
    (hpr1 : (Ideal.span {(⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (1728 : k) ((1728 : k) ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (1728 : k) ((1728 : k) ^ q))), G'}).IsPrime)
    (hpr2 : (Ideal.span {(⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (1728 : k) ((1728 : k) ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (1728 : k) ((1728 : k) ^ q))), H'}).IsPrime)
    (hnm1 : H' ∉ Ideal.span {(⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (1728 : k) ((1728 : k) ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (1728 : k) ((1728 : k) ^ q))), G'})
    (hnm2 : G' ∉ Ideal.span {(⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (1728 : k) ((1728 : k) ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (1728 : k) ((1728 : k) ^ q))), H'})
    (hsp1 : Ideal.span {(⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (1728 : k) ((1728 : k) ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (1728 : k) ((1728 : k) ^ q))), G'} = Ideal.span {(⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (1728 : k) ((1728 : k) ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (1728 : k) ((1728 : k) ^ q))), (⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.X 1 - MvPolynomial.X 0 ^ q),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (1728 : k) ((1728 : k) ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (1728 : k) ((1728 : k) ^ q)))})
    (hsp2 : Ideal.span {(⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (1728 : k) ((1728 : k) ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (1728 : k) ((1728 : k) ^ q))), H'} = Ideal.span {(⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (1728 : k) ((1728 : k) ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (1728 : k) ((1728 : k) ^ q))), (⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.X 0 - MvPolynomial.X 1 ^ q),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (1728 : k) ((1728 : k) ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (1728 : k) ((1728 : k) ^ q)))}) :
    ∀ Gf : ↥(modularFunctionFieldBar (1 * q)),
      (Gf : LaurentSeries (AlgebraicClosure ℚ)) = (G' : LaurentSeries (AlgebraicClosure ℚ)) →
      ∀ c : A, c ∈ IsLocalRing.maximalIdeal A →
        (∃ m, m ∈ IsLocalRing.maximalIdeal A ∧ c * m = ((q : ℕ) : A) ^ 2) →
          ∀ W₁ W₂ : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)),
            ((∃ x : A, red x = (1728 : k) ∧
              0 < W₁.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
              (modularFunctionField_le_full (1 * q) (jq_mem (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (x : AlgebraicClosure ℚ))) ∧
              (∃ y : A, red y = (1728 : k) ^ q ∧
              0 < W₁.ord ((⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * q) jq),
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
              (jqd_mem_full (1 * q) (dvd_refl (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (y : AlgebraicClosure ℚ)))) → ((∃ x : A, red x = (1728 : k) ∧
              0 < W₂.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
              (modularFunctionField_le_full (1 * q) (jq_mem (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (x : AlgebraicClosure ℚ))) ∧
              (∃ y : A, red y = (1728 : k) ^ q ∧
              0 < W₂.ord ((⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * q) jq),
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
              (jqd_mem_full (1 * q) (dvd_refl (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (y : AlgebraicClosure ℚ)))) →
            W₁.HasValue Gf (c : AlgebraicClosure ℚ) → W₂.HasValue Gf (c : AlgebraicClosure ℚ) →
              ∀ g : ↥(modularFunctionFieldBar (1 * q)),
                (g : LaurentSeries (AlgebraicClosure ℚ)) ∈
                  modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (1728 : k) ((1728 : k) ^ q) →
                ∃ c₁ c₂ : ↥A, W₁.HasValue g (c₁ : AlgebraicClosure ℚ) ∧
                  W₂.HasValue g (c₂ : AlgebraicClosure ℚ) ∧
                  ∀ n : ℕ, ((q : ℕ) : ↥A) ^ n ∣ (c₁ - c₂) := by
  intro Gf hGf c hc hadm W₁ W₂ hW₁ hW₂ hv₁ hv₂ g hg
  have _ := ha
  have _ := hw
  have _ := heK1
  have _ := hpr1
  have _ := hpr2
  have _ := hnm1
  have _ := hnm2
  have _ := hsp1
  have _ := hsp2
  have hFq : q.Prime := Fact.out
  have h1728ne : (1728 : k) ≠ 0 := by
    intro h0
    have h' : ((1728 : ℕ) : k) = 0 := by exact_mod_cast h0
    have hdvd : q ∣ 2 ^ 6 * 3 ^ 3 := by
      have h := (CharP.cast_eq_zero_iff k q 1728).mp h'
      norm_num
      exact h
    rcases (Nat.Prime.dvd_mul hFq).mp hdvd with h | h
    · have h2 : q ≤ 2 := Nat.le_of_dvd (by norm_num) (hFq.dvd_of_dvd_pow h)
      omega
    · have h3 : q ≤ 3 := Nat.le_of_dvd (by norm_num) (hFq.dvd_of_dvd_pow h)
      omega
  have h1728q : (1728 : k) ^ q = 1728 := by
    have h := map_natCast (frobenius k q) 1728
    rw [frobenius_def] at h
    exact_mod_cast h
  haveI hloc : IsLocalRing ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (1728 : k) ((1728 : k) ^ q)) :=
    ModularCurve.CrossingAnnulus.isLocalRing_nodeRing red (1728 : k)
  obtain ⟨m, hm, hcm⟩ := hadm
  have hcm' : c * m = ((q : ℕ) : ↥A) ^ jWidth (1728 : k) := by
    rw [jWidth_of_eq_1728 rfl h1728ne]
    exact hcm
  have hϖm : ModularCurve.CrossingAnnulus.inclA K ϖ ∈ IsLocalRing.maximalIdeal A :=
    (hker _).mp ((hϖ ϖ).mpr ⟨1, (mul_one ϖ).symm⟩)
  have hGf' : ModularCurve.CrossingAnnulus.toFHom red (1728 : k) G' = Gf :=
    Subtype.ext (by rw [ModularCurve.CrossingAnnulus.coe_toFHom]; exact hGf.symm)
  have hv₁' : W₁.HasValue (ModularCurve.CrossingAnnulus.toFHom red (1728 : k) G') (c : AlgebraicClosure ℚ) := by
    rw [hGf']
    exact hv₁
  have hv₂' : W₂.HasValue (ModularCurve.CrossingAnnulus.toFHom red (1728 : k) G') (c : AlgebraicClosure ℚ) := by
    rw [hGf']
    exact hv₂
  exact ModularCurve.CrossingBootstrap.forall_natCast_pow_dvd_sub red hker (1728 : k) K 1728 1728 (map_ofNat _ 1728)
    (by rw [map_ofNat, h1728q]) ϖ hϖm eK ε hε hqϖ (jWidth (1728 : k)) G' H' w hGH hmax
    c m hc hm hcm' hW₁ hW₂ hv₁' hv₂' g hg

#print axioms solution

end S_ModularCurve_NodeLocalized_forall_natCast_pow_dvd_sub_of_hasValue_eq_of_crossingPresentation_ofNat1728
end P2MW
export P2MW.S_ModularCurve_NodeLocalized_forall_natCast_pow_dvd_sub_of_hasValue_eq_of_crossingPresentation_ofNat1728 (solution)
