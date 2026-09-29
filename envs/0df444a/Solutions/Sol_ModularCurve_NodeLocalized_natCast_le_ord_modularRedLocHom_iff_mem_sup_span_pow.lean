-- Prove2me | solution 1 for ModularCurve.NodeLocalized.natCast_le_ord_modularRedLocHom_iff_mem_sup_span_pow
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/78f7cfaf-2228-5154-91d8-50585f157431

import Mathlib
import Definitions.Def_ModularCurve_NodeDescent
import Definitions.Def_ModularCurve_SupersingularNodes
import Definitions.Def_ModularCurve_CuspidalClass
import Definitions.Def_ModularCurve_NodeLocalizedPresentation
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_AlgebraicCurve_RatFuncPlaces
import Theorems.Thm_ModularCurve_NodeLocalized_pointEval_eq_zero_of_modularEval_eq_zero
import Theorems.Thm_ModularCurve_transcendental_jqModC
import Theorems.Thm_ModularCurve_frobenius_identity_geom_unconditional
import Theorems.Thm_ValuationSubring_map_eq_zero_of_valuation_lt_one_of_charP
import Theorems.Thm_ModularCurve_CharPReduction_modularRedLocHom_mem
import Theorems.Thm_ModularCurve_ord_charLGeomPlaceOfPoint_jqModC_sub_pow_sq_eq_one
import Theorems.Thm_AlgebraicCurve_RationalFunctionField_ord_placeOfPoint_algebraMap
import Theorems.Thm_ModularCurve_modularFunctionFieldC_self_collapse_unconditional
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_NodeLocalized_natCast_le_ord_modularRedLocHom_iff_mem_sup_span_pow
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy"
p2m_attr_erase "simp" "ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom"
p2m_attr_erase "simp" "AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar"
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000
set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.NodeLocalized

namespace FltWs29
namespace BCD

open ModularCurve ModularCurve.NodeLocalized ModularCurve.CharPReduction Polynomial

section Eval
variable (N : ℕ) [NeZero N] {L : Type*} [Field L] (A : Subring L) {k : Type*} [Field k] (red : A →+* k)

theorem modularEval_mem_modularRing (p : MvPolynomial (Fin 2) A) :
    modularEval N A p ∈ modularRing N A := by
  induction p using MvPolynomial.induction_on with
  | C c =>
    rw [modularEval, MvPolynomial.eval₂Hom_C]
    exact constSeries_mem_modularRing N A c
  | add p q hp hq => rw [map_add]; exact add_mem hp hq
  | mul_X p i hp =>
    rw [map_mul]
    refine mul_mem hp ?_
    rw [modularEval, MvPolynomial.eval₂Hom_X']
    fin_cases i
    · exact jqModC_mem_modularRing N A
    · exact jqNModC_mem_modularRing N A

noncomputable def modularEvalRing : MvPolynomial (Fin 2) A →+* modularRing N A :=
  (modularEval N A).codRestrict _ (modularEval_mem_modularRing N A)

@[scoped simp] theorem coe_modularEvalRing (p : MvPolynomial (Fin 2) A) :
    (modularEvalRing N A p : LaurentSeries L) = modularEval N A p := rfl

noncomputable def modularEvalRed : MvPolynomial (Fin 2) A →+* LaurentSeries k :=
  MvPolynomial.eval₂Hom ((algebraMap k (LaurentSeries k)).comp red) ![jqModC k, jqNModC k N]

theorem red_mk_eq {x : L} (hx : x ∈ A) (y : A) (h : x = (y : L)) : red ⟨x, hx⟩ = red y := by
  subst h; rfl

theorem coeffRed_constSeries (c : A) :
    coeffRed A red ⟨constSeries A c, constSeries_mem_integralCoeffs A c⟩ = algebraMap k (LaurentSeries k) (red c) := by
  have hc : ∀ n : ℤ, (constSeries A c).coeff n = if n = 0 then (c : L) else 0 := fun n => by
    show ((algebraMap L (LaurentSeries L)) (c : L)).coeff n = _
    rw [algebraMap_laurentSeries_eq_single, HahnSeries.coeff_single]
    split_ifs <;> rfl
  ext n
  rw [coeffRed_coeff, algebraMap_laurentSeries_eq_single, HahnSeries.coeff_single]
  by_cases h : n = 0
  · subst h
    rw [if_pos rfl]
    exact red_mk_eq A red _ c (by rw [show (↑(⟨constSeries A c, constSeries_mem_integralCoeffs A c⟩ : integralCoeffs A) : LaurentSeries L) = constSeries A c from rfl, hc, if_pos rfl])
  · rw [if_neg h]
    rw [red_mk_eq A red _ 0 (by rw [show (↑(⟨constSeries A c, constSeries_mem_integralCoeffs A c⟩ : integralCoeffs A) : LaurentSeries L) = constSeries A c from rfl, hc, if_neg h, ZeroMemClass.coe_zero])]
    exact map_zero red

theorem coeffRed_jqModC :
    coeffRed A red ⟨jqModC L, jqModC_mem_integralCoeffs A⟩ = jqModC k := by
  ext n
  rw [coeffRed_coeff]
  rw [red_mk_eq A red _ (((jqModC ℤ).coeff n : ℤ) : A) (by
      show (jqModC L).coeff n = (((((jqModC ℤ).coeff n : ℤ) : A)) : L)
      rw [jqModC_eq_map_intCast (K := L), HahnSeries.map_coeff]; simp)]
  rw [map_intCast, jqModC_eq_map_intCast (K := k), HahnSeries.map_coeff]
  simp

theorem coeffRed_jqNModC :
    coeffRed A red ⟨jqNModC L N, jqNModC_mem_integralCoeffs N A⟩ = jqNModC k N := by
  ext n
  rw [coeffRed_coeff]
  by_cases h : (N : ℤ) ∣ n
  · obtain ⟨m, rfl⟩ := h
    rw [red_mk_eq A red _ (((jqModC ℤ).coeff m : ℤ) : A) (by
        show (jqNModC L N).coeff (N * m) = (((((jqModC ℤ).coeff m : ℤ) : A)) : L)
        rw [jqNModC, qExpand_coeff_mul, jqModC_eq_map_intCast (K := L), HahnSeries.map_coeff]; simp)]
    rw [map_intCast, jqNModC, qExpand_coeff_mul, jqModC_eq_map_intCast (K := k), HahnSeries.map_coeff]
    simp
  · rw [red_mk_eq A red _ 0 (by
        show (jqNModC L N).coeff n = ((0 : A) : L)
        rw [jqNModC, qExpand_coeff_of_not_dvd _ _ h, ZeroMemClass.coe_zero])]
    rw [map_zero, jqNModC, qExpand_coeff_of_not_dvd _ _ h]

theorem redRes_modularEvalRing (p : MvPolynomial (Fin 2) A) :
    redRes A red (modularRing N A) (modularRing_le_integralCoeffs N A) (modularEvalRing N A p)
      = modularEvalRed N A red p := by
  have key : (redRes A red (modularRing N A) (modularRing_le_integralCoeffs N A)).comp (modularEvalRing N A)
      = modularEvalRed N A red := by
    refine MvPolynomial.ringHom_ext (fun c => ?_) (fun i => ?_)
    · rw [RingHom.comp_apply, redRes_apply, modularEvalRed, MvPolynomial.eval₂Hom_C, RingHom.comp_apply,
        ← coeffRed_constSeries A red c]
      exact congrArg _ (Subtype.ext (by rw [coe_modularEvalRing, modularEval, MvPolynomial.eval₂Hom_C]))
    · rw [RingHom.comp_apply, redRes_apply, modularEvalRed, MvPolynomial.eval₂Hom_X']
      fin_cases i
      · rw [← coeffRed_jqModC A red (L := L)]
        exact congrArg _ (Subtype.ext (by rw [coe_modularEvalRing, modularEval, MvPolynomial.eval₂Hom_X']; rfl))
      · rw [← coeffRed_jqNModC N A red (L := L)]
        exact congrArg _ (Subtype.ext (by rw [coe_modularEvalRing, modularEval, MvPolynomial.eval₂Hom_X']; rfl))
  exact RingHom.congr_fun key p

theorem modularEval_map_inclusion {B : Subring L} (h : B ≤ A) (p : MvPolynomial (Fin 2) B) :
    modularEval N A (MvPolynomial.map (Subring.inclusion h) p) = modularEval N B p := by
  have key : (modularEval N A).comp (MvPolynomial.map (Subring.inclusion h)) = modularEval N B := by
    refine MvPolynomial.ringHom_ext (fun c => ?_) (fun i => ?_)
    · rw [RingHom.comp_apply, MvPolynomial.map_C, modularEval, MvPolynomial.eval₂Hom_C, modularEval, MvPolynomial.eval₂Hom_C]
      rfl
    · rw [RingHom.comp_apply, MvPolynomial.map_X, modularEval, MvPolynomial.eval₂Hom_X', modularEval,
        MvPolynomial.eval₂Hom_X']
  exact RingHom.congr_fun key p

end Eval

section OneVar
variable (q : ℕ) {B : Type*} [CommRing B] {k : Type*} [Field k] (red : B →+* k)

noncomputable def nodePoly : MvPolynomial (Fin 2) B →+* k[X] :=
  MvPolynomial.eval₂Hom (Polynomial.C.comp red) ![X, X ^ q]

theorem eval_nodePoly (p : MvPolynomial (Fin 2) B) (b : k) :
    (nodePoly q red p).eval b = MvPolynomial.eval₂Hom red ![b, b ^ q] p := by
  rw [nodePoly, ← Polynomial.coe_evalRingHom, ← RingHom.comp_apply, MvPolynomial.comp_eval₂Hom]
  congr 2
  · ext c; simp
  · funext i; fin_cases i <;> simp

theorem aeval_nodePoly (p : MvPolynomial (Fin 2) B) {S : Type*} [CommRing S] [Algebra k S] (x : S) :
    Polynomial.aeval x (nodePoly q red p)
      = MvPolynomial.eval₂Hom ((algebraMap k S).comp red) ![x, x ^ q] p := by
  rw [nodePoly, ← AlgHom.coe_toRingHom, ← RingHom.comp_apply, MvPolynomial.comp_eval₂Hom]
  congr 2
  · ext c; simp
  · funext i; fin_cases i <;> simp

theorem nodePoly_map {B' : Type*} [CommRing B'] (φ : B →+* B') (red' : B' →+* k) (h : red'.comp φ = red)
    (p : MvPolynomial (Fin 2) B) : nodePoly q red' (MvPolynomial.map φ p) = nodePoly q red p := by
  rw [nodePoly, MvPolynomial.eval₂Hom_map_hom, RingHom.comp_assoc, h]
  rfl

theorem nodePoly_C (c : B) : nodePoly q red (MvPolynomial.C c) = Polynomial.C (red c) := by
  rw [nodePoly, MvPolynomial.eval₂Hom_C, RingHom.comp_apply]

theorem nodePoly_G : nodePoly q red (MvPolynomial.X 1 - MvPolynomial.X 0 ^ q) = 0 := by
  rw [map_sub, map_pow, nodePoly, MvPolynomial.eval₂Hom_X', MvPolynomial.eval₂Hom_X']
  simp

end OneVar

section Kron
variable (q : ℕ) [Fact q.Prime] (k : Type*) [Field k] [CharP k q]

theorem jqNModC_one_mul_eq_pow : jqNModC k (1 * q) = jqModC k ^ q := by
  rw [show jqNModC k (1 * q) = jqNModC k q from qExpand_congr (one_mul q) _]
  exact frobenius_identity_geom_unconditional k

variable {q k}

theorem modularEvalRed_eq_aeval {L : Type*} [Field L] (B : Subring L) (red' : B →+* k) (p : MvPolynomial (Fin 2) B) :
    modularEvalRed (1 * q) B red' p = Polynomial.aeval (jqModC k) (nodePoly q red' p) := by
  rw [aeval_nodePoly, modularEvalRed, ← jqNModC_one_mul_eq_pow q k]

theorem aeval_jqModC_ne_zero {p : k[X]} (hp : p ≠ 0) : Polynomial.aeval (jqModC k) p ≠ 0 :=
  fun h => transcendental_jqModC k ⟨p, hp, h⟩

theorem aeval_jqModC_eq_zero_iff (p : k[X]) : Polynomial.aeval (jqModC k) p = 0 ↔ p = 0 :=
  ⟨fun h => by_contra fun hp => aeval_jqModC_ne_zero hp h, fun h => by rw [h, map_zero]⟩

end Kron

section Upstairs

variable (q : ℕ) (B : Type*) [CommRing B]

noncomputable abbrev ι₀ : Polynomial B →+* MvPolynomial (Fin 2) B := Polynomial.eval₂RingHom MvPolynomial.C (MvPolynomial.X 0)

noncomputable abbrev σ₀ : MvPolynomial (Fin 2) B →+* Polynomial B :=
  MvPolynomial.eval₂Hom Polynomial.C ![Polynomial.X, Polynomial.X ^ q]

theorem sub_ι₀_σ₀_mem (s : MvPolynomial (Fin 2) B) :
    s - ι₀ B (σ₀ q B s) ∈ Ideal.span {(MvPolynomial.X 1 : MvPolynomial (Fin 2) B) - MvPolynomial.X 0 ^ q} := by
  induction s using MvPolynomial.induction_on with
  | C c =>
    rw [MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_C, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C, sub_self]
    exact zero_mem _
  | add p r hp hr =>
    have : p + r - ι₀ B (σ₀ q B (p + r)) = (p - ι₀ B (σ₀ q B p)) + (r - ι₀ B (σ₀ q B r)) := by
      rw [map_add, map_add]; ring
    rw [this]; exact add_mem hp hr
  | mul_X p j hp =>
    have key : p * MvPolynomial.X j - ι₀ B (σ₀ q B (p * MvPolynomial.X j))
        = (p - ι₀ B (σ₀ q B p)) * MvPolynomial.X j
          + ι₀ B (σ₀ q B p) * (MvPolynomial.X j - ι₀ B (![Polynomial.X, Polynomial.X ^ q] j)) := by
      rw [map_mul, map_mul, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_X]; ring
    rw [key]
    refine add_mem (Ideal.mul_mem_right _ _ hp) (Ideal.mul_mem_left _ _ ?_)
    fin_cases j <;> simp [Polynomial.coe_eval₂RingHom]

variable {q B} {k : Type*} [Field k] (red : B →+* k) (ϖ : B) (hϖ : ∀ c : B, red c = 0 ↔ ∃ d, c = ϖ * d)

theorem nodePoly_eq_mapRingHom_comp : nodePoly q red = (Polynomial.mapRingHom red).comp (σ₀ q B) := by
  refine MvPolynomial.ringHom_ext (fun c => ?_) (fun j => ?_)
  · simp [nodePoly, Polynomial.coe_mapRingHom]
  · fin_cases j <;> simp [nodePoly, Polynomial.coe_mapRingHom]

include hϖ in
theorem C_dvd_of_map_eq_zero (P : Polynomial B) (hP : P.map red = 0) : Polynomial.C ϖ ∣ P := by
  rw [Polynomial.C_dvd_iff_dvd_coeff]
  intro n
  have hn := congrArg (fun Q => Polynomial.coeff Q n) hP
  simp only [Polynomial.coeff_map, Polynomial.coeff_zero] at hn
  obtain ⟨d, hd⟩ := (hϖ _).mp hn
  exact ⟨d, hd⟩

include hϖ in

theorem mem_span_pair_iff_nodePoly_eq_zero (s : MvPolynomial (Fin 2) B) :
    s ∈ Ideal.span {MvPolynomial.C ϖ, (MvPolynomial.X 1 : MvPolynomial (Fin 2) B) - MvPolynomial.X 0 ^ q}
      ↔ nodePoly q red s = 0 := by
  constructor
  · intro hs
    have hle : Ideal.span {MvPolynomial.C ϖ, (MvPolynomial.X 1 : MvPolynomial (Fin 2) B) - MvPolynomial.X 0 ^ q}
        ≤ RingHom.ker (nodePoly q red) := by
      rw [Ideal.span_le]
      rintro _ (rfl | rfl)
      · rw [SetLike.mem_coe, RingHom.mem_ker, nodePoly_C, (hϖ ϖ).mpr ⟨1, (mul_one _).symm⟩, map_zero]
      · rw [SetLike.mem_coe, RingHom.mem_ker, nodePoly_G]
    exact (RingHom.mem_ker).mp (hle hs)
  · intro hs
    rw [nodePoly_eq_mapRingHom_comp, RingHom.comp_apply, Polynomial.coe_mapRingHom] at hs
    obtain ⟨t, ht⟩ := C_dvd_of_map_eq_zero red ϖ hϖ _ hs
    have : s = (s - ι₀ B (σ₀ q B s)) + ι₀ B (σ₀ q B s) := by ring
    rw [this]
    refine add_mem (Ideal.span_mono (Set.subset_insert _ _) (sub_ι₀_σ₀_mem q B s)) ?_
    rw [ht, map_mul, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C]
    exact Ideal.mul_mem_right _ _ (Ideal.subset_span (Set.mem_insert _ _))

end Upstairs

section NodeRing

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
  {k : Type*} [Field k] [CharP k q] (red : A →+* k) (a : k)
  (K : IntermediateField ℚ (AlgebraicClosure ℚ))

theorem redRestrict_comp : (red.comp (Subring.inclusion (inf_le_left : coeffSubring A K ≤ A.toSubring)))
    = redRestrict red K := rfl

omit [Fact q.Prime] [CharP k q] in

theorem nodePoly_map_inclusion (p : MvPolynomial (Fin 2) (coeffSubring A K)) :
    nodePoly q (show A.toSubring →+* k from red) (MvPolynomial.map (Subring.inclusion (inf_le_left : coeffSubring A K ≤ A.toSubring)) p)
      = nodePoly q (redRestrict red K) p :=
  nodePoly_map q _ _ _ (redRestrict_comp red K) p

omit [Fact q.Prime] [CharP k q] in

theorem eval_nodePoly_eq_pointEval (p : MvPolynomial (Fin 2) (coeffSubring A K)) :
    (nodePoly q (redRestrict red K) p).eval a = pointEval (coeffSubring A K) (redRestrict red K) a (a ^ q) p := by
  rw [eval_nodePoly]
  rfl

theorem nodePoly_ne_zero_of_pointEval_ne_zero {s : MvPolynomial (Fin 2) (coeffSubring A K)}
    (hs : pointEval (coeffSubring A K) (redRestrict red K) a (a ^ q) s ≠ 0) :
    nodePoly q (redRestrict red K) s ≠ 0 := by
  intro h
  apply hs
  rw [← eval_nodePoly_eq_pointEval, h, Polynomial.eval_zero]

noncomputable def liftRing (p : MvPolynomial (Fin 2) (coeffSubring A K)) : modularRing (1 * q) A.toSubring :=
  modularEvalRing (1 * q) A.toSubring (MvPolynomial.map (Subring.inclusion (inf_le_left : coeffSubring A K ≤ A.toSubring)) p)

theorem coe_liftRing (p : MvPolynomial (Fin 2) (coeffSubring A K)) :
    (liftRing (q := q) K p : LaurentSeries (AlgebraicClosure ℚ)) = modularEval (1 * q) (coeffSubring A K) p := by
  rw [liftRing, coe_modularEvalRing, modularEval_map_inclusion]
  rfl

theorem redRes_liftRing (p : MvPolynomial (Fin 2) (coeffSubring A K)) :
    redRes A.toSubring red (modularRing (1 * q) A.toSubring) (modularRing_le_integralCoeffs (1 * q) A.toSubring) (liftRing (q := q) K p)
      = Polynomial.aeval (jqModC k) (nodePoly q (redRestrict red K) p) := by
  rw [liftRing, redRes_modularEvalRing, modularEvalRed_eq_aeval, nodePoly_map_inclusion]

theorem liftRing_notMem_redKer {s : MvPolynomial (Fin 2) (coeffSubring A K)}
    (hs : pointEval (coeffSubring A K) (redRestrict red K) a (a ^ q) s ≠ 0) :
    liftRing (q := q) K s ∉ redKer A.toSubring red (modularRing (1 * q) A.toSubring) (modularRing_le_integralCoeffs (1 * q) A.toSubring) := by
  rw [notMem_redKer_iff, redRes_liftRing]
  exact aeval_jqModC_ne_zero (nodePoly_ne_zero_of_pointEval_ne_zero red a K hs)

theorem le_modularLocalized :
    (modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) : Subring (LaurentSeries (AlgebraicClosure ℚ)))
      ≤ modularLocalized (1 * q) A.toSubring red := by
  intro g hg
  obtain ⟨r, s, hs, hgs⟩ := hg
  refine ⟨liftRing (q := q) K r, liftRing (q := q) K s, liftRing_notMem_redKer red a K hs, ?_⟩
  rw [coe_liftRing, coe_liftRing]
  exact hgs

theorem modularRedLocHom_mul_aeval_eq {g : LaurentSeries (AlgebraicClosure ℚ)}
    (h₁ : g ∈ modularLocalized (1 * q) A.toSubring red)
    {r s : MvPolynomial (Fin 2) (coeffSubring A K)}
    (hgs : g * modularEval (1 * q) (coeffSubring A K) s = modularEval (1 * q) (coeffSubring A K) r) :
    modularRedLocHom (1 * q) A.toSubring red ⟨g, h₁⟩ * Polynomial.aeval (jqModC k) (nodePoly q (redRestrict red K) s)
      = Polynomial.aeval (jqModC k) (nodePoly q (redRestrict red K) r) := by
  have h := redLoc_spec (A := A.toSubring) (red := red) (R := modularRing (1 * q) A.toSubring)
    (hR := modularRing_le_integralCoeffs (1 * q) A.toSubring) ⟨g, h₁⟩ (r := liftRing (q := q) K r)
    (s := liftRing (q := q) K s) (by
      show g * (liftRing (q := q) K s : LaurentSeries (AlgebraicClosure ℚ)) = liftRing (q := q) K r
      rw [coe_liftRing, coe_liftRing]
      exact hgs)
  rw [redRes_liftRing, redRes_liftRing] at h
  exact h

theorem modularRedLocHom_modularEval (p : MvPolynomial (Fin 2) (coeffSubring A K))
    (h₁ : modularEval (1 * q) (coeffSubring A K) p ∈ modularLocalized (1 * q) A.toSubring red) :
    modularRedLocHom (1 * q) A.toSubring red ⟨_, h₁⟩ = Polynomial.aeval (jqModC k) (nodePoly q (redRestrict red K) p) := by
  have h := modularRedLocHom_mul_aeval_eq red K h₁ (r := p) (s := 1) (by rw [map_one, mul_one])
  rwa [map_one, map_one, mul_one] at h

noncomputable def piZero : modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) →+* LaurentSeries k :=
  (modularRedLocHom (1 * q) A.toSubring red).comp (Subring.inclusion (le_modularLocalized red a K))

theorem piZero_apply (g : modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))
    (h₁ : (g : LaurentSeries (AlgebraicClosure ℚ)) ∈ modularLocalized (1 * q) A.toSubring red) :
    piZero red a K g = modularRedLocHom (1 * q) A.toSubring red ⟨_, h₁⟩ := rfl

theorem piZero_modularEvalAt (p : MvPolynomial (Fin 2) (coeffSubring A K)) :
    piZero red a K (modularEvalAt (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) p)
      = Polynomial.aeval (jqModC k) (nodePoly q (redRestrict red K) p) :=
  modularRedLocHom_modularEval red K p _

end NodeRing

section CardB

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
  {k : Type*} [Field k] [CharP k q] [DecidableEq k]

set_option maxHeartbeats 6400000 in
theorem cardB (red : A →+* k) (a : k) (ha2 : a ^ (q ^ 2) = a)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (ϖ : ↥(coeffSubring A K)) (hϖ : ∀ c : ↥(coeffSubring A K), redRestrict red K c = 0 ↔ ∃ d, c = ϖ * d)
    (g : ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)))
    (h₁ : (g : LaurentSeries (AlgebraicClosure ℚ)) ∈ CharPReduction.modularLocalized (1 * q) A.toSubring red) :
    CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, h₁⟩ = 0 ↔
      g ∈ Ideal.span {modularEvalAt (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) (MvPolynomial.C ϖ),
                      modularEvalAt (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) (MvPolynomial.X 1 - MvPolynomial.X 0 ^ q)} := by
  classical
  haveI hfact : Fact (RingHom.ker (modularEval (1 * q) (coeffSubring A K)) ≤
      RingHom.ker (pointEval (coeffSubring A K) (redRestrict red K) a (a ^ q))) :=
    ⟨fun s hs => (RingHom.mem_ker).mpr
      (ModularCurve.NodeLocalized.pointEval_eq_zero_of_modularEval_eq_zero red a K s ((RingHom.mem_ker).mp hs))⟩
  have hπ : CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, h₁⟩ = piZero red a K g := rfl
  rw [hπ]
  constructor
  ·
    intro h0
    obtain ⟨r, s, hs, hgs⟩ := g.2
    have key := modularRedLocHom_mul_aeval_eq red K (le_modularLocalized red a K g.2) hgs
    rw [← piZero_apply red a K g, h0, zero_mul, eq_comm, aeval_jqModC_eq_zero_iff] at key
    have hr : r ∈ Ideal.span {MvPolynomial.C ϖ, (MvPolynomial.X 1 : MvPolynomial (Fin 2) (coeffSubring A K)) - MvPolynomial.X 0 ^ q} :=
      (mem_span_pair_iff_nodePoly_eq_zero (redRestrict red K) ϖ hϖ r).mpr key
    have hEr : modularEvalAt (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) r ∈ Ideal.span {modularEvalAt (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) (MvPolynomial.C ϖ), modularEvalAt (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) (MvPolynomial.X 1 - MvPolynomial.X 0 ^ q)} := by
      have := Ideal.mem_map_of_mem (modularEvalAt (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)) hr
      rwa [Ideal.map_span, Set.image_insert_eq, Set.image_singleton] at this
    obtain ⟨u, hu⟩ := isUnit_modularEvalAt (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) hs
    have hgE : g * modularEvalAt (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) s = modularEvalAt (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) r := Subtype.ext hgs
    have hg : g = modularEvalAt (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) r * ↑u⁻¹ := by
      rw [← hgE, ← hu, mul_assoc, Units.mul_inv, mul_one]
    rw [hg]
    exact Ideal.mul_mem_right _ _ hEr
  ·
    intro hg
    obtain ⟨u, w, huw⟩ := Ideal.mem_span_pair.mp hg
    rw [← huw, map_add, map_mul, map_mul, piZero_modularEvalAt, piZero_modularEvalAt, nodePoly_C,
      (hϖ ϖ).mpr ⟨1, (mul_one _).symm⟩, map_zero, map_zero, mul_zero, nodePoly_G, map_zero, mul_zero, add_zero]

end CardB

end FltWs29.BCD
p2m_reactivate "P2MW.S_ModularCurve_NodeLocalized_natCast_le_ord_modularRedLocHom_iff_mem_sup_span_pow.FltWs29 P2MW.S_ModularCurve_NodeLocalized_natCast_le_ord_modularRedLocHom_iff_mem_sup_span_pow.FltWs29.BCD"
p2m_reactivate "P2MW.S_ModularCurve_NodeLocalized_natCast_le_ord_modularRedLocHom_iff_mem_sup_span_pow.FltWs29"

namespace FltWs29
namespace BCD

open ModularCurve ModularCurve.NodeLocalized ModularCurve.CharPReduction Polynomial AlgebraicCurve

section JLine

variable (k : Type*) [Field k]

noncomputable abbrev JT : ↥(modularFunctionFieldC k 1) := ⟨jqModC k, jqModC_mem k 1⟩

theorem coe_aeval_JT (P : k[X]) :
    ((Polynomial.aeval (JT k) P : ↥(modularFunctionFieldC k 1)) : LaurentSeries k) = Polynomial.aeval (jqModC k) P :=
  (Polynomial.aeval_algHom_apply (modularFunctionFieldC k 1).val (JT k) P).symm

theorem aeval_JT_ne_zero {P : k[X]} (hP : P ≠ 0) : Polynomial.aeval (JT k) P ≠ 0 := by
  intro h
  apply aeval_jqModC_ne_zero (k := k) hP
  rw [← coe_aeval_JT, h]
  rfl

theorem ratFuncEquivCharLOneC_X' : ratFuncEquivCharLOneC k RatFunc.X = JT k := by
  apply Subtype.ext
  show ((ratFuncEquivCharLOneC k RatFunc.X : modularFunctionFieldC k 1) : LaurentSeries k) = jqModC k
  rw [ratFuncEquivCharLOneC, AlgEquiv.trans_apply]
  exact RatFunc.algEquivOfTranscendental_X (jqModC k) (transcendental_jqModC k)

theorem ratFuncEquivCharLOneC_algebraMap (P : k[X]) :
    ratFuncEquivCharLOneC k (algebraMap k[X] (RatFunc k) P) = Polynomial.aeval (JT k) P := by
  rw [← RatFunc.aeval_X_left_eq_algebraMap, ← Polynomial.aeval_algHom_apply, ratFuncEquivCharLOneC_X']

theorem ord_charLGeomPlaceOfPoint_aeval (a : k) {P : k[X]} (hP : P ≠ 0) :
    (charLGeomPlaceOfPoint k a).ord (Polynomial.aeval (JT k) P) = P.rootMultiplicity a := by
  rw [← ratFuncEquivCharLOneC_algebraMap]
  exact (Place.ord_congrRingEquiv (ratFuncEquivCharLOneC k).toRingEquiv (fun c => (ratFuncEquivCharLOneC k).commutes c)
    (RationalFunctionField.placeOfPoint k a) _).trans (RationalFunctionField.ord_placeOfPoint_algebraMap a hP)

end JLine
p2m_reactivate "P2MW.S_ModularCurve_NodeLocalized_natCast_le_ord_modularRedLocHom_iff_mem_sup_span_pow.FltWs29 P2MW.S_ModularCurve_NodeLocalized_natCast_le_ord_modularRedLocHom_iff_mem_sup_span_pow.FltWs29.BCD"

section Collapse
variable (q : ℕ) [Fact q.Prime] (k : Type*) [Field k] [CharP k q]

theorem modularFunctionFieldC_one_mul : modularFunctionFieldC k (1 * q) = modularFunctionFieldC k 1 := by
  have h : ∀ (n : ℕ) [NeZero n] [Fact n.Prime] [CharP k n], modularFunctionFieldC k n = modularFunctionFieldC k 1 :=
    fun n _ _ _ => modularFunctionFieldC_self_collapse_unconditional k
  haveI : Fact (1 * q).Prime := ⟨by rw [one_mul]; exact Fact.out⟩
  haveI : CharP k (1 * q) := by rw [one_mul]; infer_instance
  exact h (1 * q)

end Collapse
p2m_reactivate "P2MW.S_ModularCurve_NodeLocalized_natCast_le_ord_modularRedLocHom_iff_mem_sup_span_pow.FltWs29 P2MW.S_ModularCurve_NodeLocalized_natCast_le_ord_modularRedLocHom_iff_mem_sup_span_pow.FltWs29.BCD"

section Orders

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
  {k : Type*} [Field k] [CharP k q] (red : A →+* k) (a : k)
  (K : IntermediateField ℚ (AlgebraicClosure ℚ))

theorem mk_modularRedLocHom_mul_aeval {g : LaurentSeries (AlgebraicClosure ℚ)}
    (h₁ : g ∈ modularLocalized (1 * q) A.toSubring red)
    (h₁F : modularRedLocHom (1 * q) A.toSubring red ⟨g, h₁⟩ ∈ modularFunctionFieldC k 1)
    {r s : MvPolynomial (Fin 2) (coeffSubring A K)}
    (hgs : g * modularEval (1 * q) (coeffSubring A K) s = modularEval (1 * q) (coeffSubring A K) r) :
    (⟨_, h₁F⟩ : ↥(modularFunctionFieldC k 1)) * Polynomial.aeval (JT k) (nodePoly q (redRestrict red K) s)
      = Polynomial.aeval (JT k) (nodePoly q (redRestrict red K) r) := by
  apply Subtype.ext
  rw [MulMemClass.coe_mul, coe_aeval_JT, coe_aeval_JT]
  exact modularRedLocHom_mul_aeval_eq red K h₁ hgs

theorem ord_mk_modularRedLocHom {g : LaurentSeries (AlgebraicClosure ℚ)}
    (h₁ : g ∈ modularLocalized (1 * q) A.toSubring red)
    (h₁F : modularRedLocHom (1 * q) A.toSubring red ⟨g, h₁⟩ ∈ modularFunctionFieldC k 1)
    (h0 : modularRedLocHom (1 * q) A.toSubring red ⟨g, h₁⟩ ≠ 0)
    {r s : MvPolynomial (Fin 2) (coeffSubring A K)}
    (hs : pointEval (coeffSubring A K) (redRestrict red K) a (a ^ q) s ≠ 0)
    (hgs : g * modularEval (1 * q) (coeffSubring A K) s = modularEval (1 * q) (coeffSubring A K) r) :
    nodePoly q (redRestrict red K) r ≠ 0 ∧
    (charLGeomPlaceOfPoint k a).ord (⟨_, h₁F⟩ : ↥(modularFunctionFieldC k 1))
      = (nodePoly q (redRestrict red K) r).rootMultiplicity a := by
  have hsne := nodePoly_ne_zero_of_pointEval_ne_zero red a K hs
  have key := mk_modularRedLocHom_mul_aeval red K h₁ h₁F hgs
  have hg0 : (⟨_, h₁F⟩ : ↥(modularFunctionFieldC k 1)) ≠ 0 := fun h => h0 (congrArg Subtype.val h)
  have hrne : nodePoly q (redRestrict red K) r ≠ 0 := by
    intro hr
    rw [hr, map_zero, mul_eq_zero] at key
    rcases key with h | h
    · exact hg0 h
    · exact aeval_JT_ne_zero k hsne h
  refine ⟨hrne, ?_⟩
  have hord := congrArg (charLGeomPlaceOfPoint k a).ord key
  have hmult0 : (nodePoly q (redRestrict red K) s).rootMultiplicity a = 0 := by
    apply Polynomial.rootMultiplicity_eq_zero
    rw [IsRoot, eval_nodePoly_eq_pointEval]
    exact hs
  rw [Place.ord_mul _ hg0 (aeval_JT_ne_zero k hsne), ord_charLGeomPlaceOfPoint_aeval k a hsne,
    ord_charLGeomPlaceOfPoint_aeval k a hrne, hmult0, Nat.cast_zero, add_zero] at hord
  exact hord

theorem ord_mk_modularRedLocHom_nonneg
    (g : modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))
    (h₁ : (g : LaurentSeries (AlgebraicClosure ℚ)) ∈ modularLocalized (1 * q) A.toSubring red)
    (h₁F : modularRedLocHom (1 * q) A.toSubring red ⟨_, h₁⟩ ∈ modularFunctionFieldC k 1) :
    0 ≤ (charLGeomPlaceOfPoint k a).ord (⟨_, h₁F⟩ : ↥(modularFunctionFieldC k 1)) := by
  by_cases h0 : modularRedLocHom (1 * q) A.toSubring red ⟨_, h₁⟩ = 0
  · have : (⟨_, h₁F⟩ : ↥(modularFunctionFieldC k 1)) = 0 := Subtype.ext h0
    rw [this, Place.ord_zero]
  · obtain ⟨r, s, hs, hgs⟩ := g.2
    rw [(ord_mk_modularRedLocHom red a K h₁ h₁F h0 hs hgs).2]
    exact Nat.cast_nonneg _

theorem mk_modularRedLocHom_modularEval (p : MvPolynomial (Fin 2) (coeffSubring A K))
    (h₁ : modularEval (1 * q) (coeffSubring A K) p ∈ modularLocalized (1 * q) A.toSubring red)
    (h₁F : modularRedLocHom (1 * q) A.toSubring red ⟨_, h₁⟩ ∈ modularFunctionFieldC k 1) :
    (⟨_, h₁F⟩ : ↥(modularFunctionFieldC k 1)) = Polynomial.aeval (JT k) (nodePoly q (redRestrict red K) p) := by
  apply Subtype.ext
  rw [coe_aeval_JT]
  exact modularRedLocHom_modularEval red K p h₁

theorem nodePoly_H : nodePoly q (redRestrict red K) (MvPolynomial.X 0 - MvPolynomial.X 1 ^ q) = X - X ^ (q ^ 2) := by
  rw [map_sub, map_pow, nodePoly, MvPolynomial.eval₂Hom_X', MvPolynomial.eval₂Hom_X']
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, ← pow_mul, sq]

private theorem _root_.AlgebraicCurve.Place.ord_pow' {K₁ F : Type*} [Field K₁] [Field F] [Algebra K₁ F] (v : Place K₁ F)
    {f : F} (hf : f ≠ 0) (n : ℕ) : v.ord (f ^ n) = n * v.ord f := by
  induction n with
  | zero => simp [Place.ord_one]
  | succ n ih =>
    rw [pow_succ, Place.ord_mul _ (pow_ne_zero _ hf) hf, ih]
    push_cast
    ring

p2m_alias "P2MW.S_ModularCurve_NodeLocalized_natCast_le_ord_modularRedLocHom_iff_mem_sup_span_pow.AlgebraicCurve.Place.ord_pow'" "AlgebraicCurve.Place.ord_pow'"

theorem mk_piZero_H (hmem : piZero red a K (modularEvalAt (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)
      (MvPolynomial.X 0 - MvPolynomial.X 1 ^ q)) ∈ modularFunctionFieldC k 1) :
    (⟨_, hmem⟩ : ↥(modularFunctionFieldC k 1)) = JT k - JT k ^ (q ^ 2) :=
  (mk_modularRedLocHom_modularEval red K _ _ hmem).trans (by rw [nodePoly_H, map_sub, map_pow, Polynomial.aeval_X])

theorem ord_piZero_H [DecidableEq k] (ha2 : a ^ (q ^ 2) = a)
    (hmem : piZero red a K (modularEvalAt (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)
      (MvPolynomial.X 0 - MvPolynomial.X 1 ^ q)) ∈ modularFunctionFieldC k 1) :
    (charLGeomPlaceOfPoint k a).ord (⟨_, hmem⟩ : ↥(modularFunctionFieldC k 1)) = 1 := by
  rw [mk_piZero_H red a K hmem]
  exact ord_charLGeomPlaceOfPoint_jqModC_sub_pow_sq_eq_one a ha2

theorem piZero_H_ne_zero [DecidableEq k] (ha2 : a ^ (q ^ 2) = a)
    (hmem : piZero red a K (modularEvalAt (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)
      (MvPolynomial.X 0 - MvPolynomial.X 1 ^ q)) ∈ modularFunctionFieldC k 1) :
    (⟨_, hmem⟩ : ↥(modularFunctionFieldC k 1)) ≠ 0 := by
  intro h
  have := congrArg (charLGeomPlaceOfPoint k a).ord h
  rw [ord_piZero_H red a K ha2 hmem, Place.ord_zero] at this
  exact one_ne_zero this

theorem ord_piZero_nonneg (w : modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))
    (hF : piZero red a K w ∈ modularFunctionFieldC k 1) :
    0 ≤ (charLGeomPlaceOfPoint k a).ord (⟨piZero red a K w, hF⟩ : ↥(modularFunctionFieldC k 1)) :=
  ord_mk_modularRedLocHom_nonneg red a K w (le_modularLocalized red a K w.2) hF

theorem ord_piZero_eq (w : modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))
    (hF : piZero red a K w ∈ modularFunctionFieldC k 1) (h0 : piZero red a K w ≠ 0)
    {r s : MvPolynomial (Fin 2) (coeffSubring A K)}
    (hs : pointEval (coeffSubring A K) (redRestrict red K) a (a ^ q) s ≠ 0)
    (hws : (w : LaurentSeries (AlgebraicClosure ℚ)) * modularEval (1 * q) (coeffSubring A K) s = modularEval (1 * q) (coeffSubring A K) r) :
    nodePoly q (redRestrict red K) r ≠ 0 ∧
    (charLGeomPlaceOfPoint k a).ord (⟨piZero red a K w, hF⟩ : ↥(modularFunctionFieldC k 1))
      = (nodePoly q (redRestrict red K) r).rootMultiplicity a :=
  ord_mk_modularRedLocHom red a K (le_modularLocalized red a K w.2) hF h0 hs hws

end Orders
p2m_reactivate "P2MW.S_ModularCurve_NodeLocalized_natCast_le_ord_modularRedLocHom_iff_mem_sup_span_pow.FltWs29 P2MW.S_ModularCurve_NodeLocalized_natCast_le_ord_modularRedLocHom_iff_mem_sup_span_pow.FltWs29.BCD"

section ImageField

variable {A : ValuationSubring (AlgebraicClosure ℚ)}
  {k : Type*} [Field k] (red : A →+* k)
  (K : IntermediateField ℚ (AlgebraicClosure ℚ)) (q : ℕ) [Fact q.Prime]

include red in
theorem liesOverPrime_of_red (hq : CharP k q) : A.LiesOverPrime q := by
  haveI := hq
  have hqA : ((q : ℕ) : AlgebraicClosure ℚ) ∈ A := natCast_mem A q
  show ((q : ℕ) : AlgebraicClosure ℚ) ∈ A.nonunits
  rw [ValuationSubring.mem_nonunits_iff]
  by_contra hlt
  have h1 : A.valuation (((⟨(q : ℕ), hqA⟩ : A) : AlgebraicClosure ℚ)) = 1 :=
    le_antisymm (A.valuation_le_one _) (not_lt.mp hlt)
  have hu : IsUnit (⟨((q : ℕ) : AlgebraicClosure ℚ), hqA⟩ : A) := (A.valuation_eq_one_iff _).mpr h1
  obtain ⟨c, hc⟩ := hu.exists_right_inv
  have hred : red ⟨((q : ℕ) : AlgebraicClosure ℚ), hqA⟩ = 0 := by
    have : (⟨((q : ℕ) : AlgebraicClosure ℚ), hqA⟩ : A) = ((q : ℕ) : A) := Subtype.ext (by push_cast; rfl)
    rw [this, map_natCast, CharP.cast_eq_zero]
  have := congrArg red hc
  rw [map_mul, hred, zero_mul, map_one] at this
  exact zero_ne_one this

theorem isUnit_of_red_ne_zero (hq : CharP k q) {c : A} (hc : red c ≠ 0) : IsUnit c := by
  haveI := hq
  rw [ValuationSubring.valuation_eq_one_iff]
  rcases (A.valuation_le_one c).lt_or_eq with h | h
  · exact absurd (ValuationSubring.map_eq_zero_of_valuation_lt_one_of_charP A q (liesOverPrime_of_red red q hq) red c h) hc
  · exact h

noncomputable def imageField (hq : CharP k q) : Subfield k where
  carrier := Set.range (redRestrict red K)
  mul_mem' := by rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩; exact ⟨x * y, map_mul _ _ _⟩
  one_mem' := ⟨1, map_one _⟩
  add_mem' := by rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩; exact ⟨x + y, map_add _ _ _⟩
  zero_mem' := ⟨0, map_zero _⟩
  neg_mem' := by rintro _ ⟨x, rfl⟩; exact ⟨-x, map_neg _ _⟩
  inv_mem' := by
    rintro _ ⟨x, rfl⟩
    by_cases hx : redRestrict red K x = 0
    · exact ⟨0, by rw [hx, inv_zero, map_zero]⟩
    · have hcx : red (Subring.inclusion (inf_le_left : coeffSubring A K ≤ A.toSubring) x) = redRestrict red K x := rfl
      obtain ⟨c', hc'⟩ := (isUnit_of_red_ne_zero red q hq (by rw [hcx]; exact hx)).exists_right_inv
      have hxc : (x : AlgebraicClosure ℚ) * (c' : AlgebraicClosure ℚ) = 1 := by
        have := congrArg (fun t : A => (t : AlgebraicClosure ℚ)) hc'
        simpa using this
      have hc'K : ((c' : A) : AlgebraicClosure ℚ) ∈ K := by
        rw [eq_inv_of_mul_eq_one_right hxc]
        exact inv_mem x.2.2
      refine ⟨⟨(c' : AlgebraicClosure ℚ), Subring.mem_inf.mpr ⟨c'.2, hc'K⟩⟩, ?_⟩
      apply eq_inv_of_mul_eq_one_right
      rw [← hcx, show redRestrict red K ⟨(c' : AlgebraicClosure ℚ), _⟩ = red c' from rfl, ← map_mul, hc', map_one]

theorem mem_imageField_iff (hq : CharP k q) {y : k} : y ∈ imageField red K q hq ↔ ∃ x, redRestrict red K x = y := Iff.rfl

noncomputable def redF (hq : CharP k q) : coeffSubring A K →+* ↥(imageField red K q hq) :=
  (redRestrict red K).codRestrict _ fun x => ⟨x, rfl⟩

theorem redF_surjective (hq : CharP k q) : Function.Surjective (redF red K q hq) := by
  rintro ⟨_, x, rfl⟩
  exact ⟨x, rfl⟩

theorem subtype_comp_redF (hq : CharP k q) : (imageField red K q hq).subtype.comp (redF red K q hq) = redRestrict red K := rfl

theorem exists_map_redF_eq (hq : CharP k q) (P : Polynomial ↥(imageField red K q hq)) : ∃ Q : Polynomial (coeffSubring A K), Q.map (redF red K q hq) = P :=
  Polynomial.map_surjective _ (redF_surjective red K q hq) P

end ImageField
p2m_reactivate "P2MW.S_ModularCurve_NodeLocalized_natCast_le_ord_modularRedLocHom_iff_mem_sup_span_pow.FltWs29 P2MW.S_ModularCurve_NodeLocalized_natCast_le_ord_modularRedLocHom_iff_mem_sup_span_pow.FltWs29.BCD"

section Sublemma

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
  {k : Type*} [Field k] [CharP k q] [DecidableEq k] (red : A →+* k) (a : k)
  (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]

theorem exists_mul_eq_P_mul (ha2 : a ^ (q ^ 2) = a) (R : Polynomial ↥(imageField red K q inferInstance))
    (hR : (R.map (imageField red K q inferInstance).subtype).eval a = 0) :
    ∃ t c : Polynomial ↥(imageField red K q inferInstance), ((c.map (imageField red K q inferInstance).subtype).eval a ≠ 0) ∧
      R * c = (X - X ^ (q ^ 2)) * t := by
  letI : Algebra (↥(imageField red K q inferInstance)) k := (imageField red K q inferInstance).subtype.toAlgebra
  have halg : ∀ P : Polynomial ↥(imageField red K q inferInstance), Polynomial.aeval a P = (P.map (imageField red K q inferInstance).subtype).eval a :=
    fun P => by rw [Polynomial.aeval_def, Polynomial.eval_map]; rfl
  obtain ⟨Pq, hPq⟩ : ∃ P : Polynomial ↥(imageField red K q inferInstance), P = X - X ^ (q ^ 2) := ⟨_, rfl⟩
  have hq1 : 1 < q ^ 2 := Nat.one_lt_pow two_ne_zero (Fact.out : q.Prime).one_lt
  have hPq0 : Pq ≠ 0 := by
    intro h
    have := congrArg natDegree h
    rw [hPq, natDegree_sub_eq_right_of_natDegree_lt (by rw [natDegree_X_pow, natDegree_X]; exact hq1), natDegree_X_pow, natDegree_zero] at this
    omega
  have hPqa : Polynomial.aeval a Pq = 0 := by
    rw [halg, hPq, Polynomial.map_sub, Polynomial.map_pow, map_X, eval_sub, eval_pow, eval_X, ha2, sub_self]

  have hmonic : (-Pq).Monic := by
    rw [hPq, neg_sub, Monic, leadingCoeff_sub_of_degree_lt (by rw [degree_X_pow, degree_X]; exact_mod_cast hq1), leadingCoeff_X_pow]
  have hint : IsIntegral (↥(imageField red K q inferInstance)) a := ⟨-Pq, hmonic, by rw [← Polynomial.aeval_def, map_neg, hPqa, neg_zero]⟩
  have hmPq : minpoly (↥(imageField red K q inferInstance)) a ∣ Pq := minpoly.dvd _ a hPqa
  obtain ⟨c, hc⟩ := hmPq
  have hRa : Polynomial.aeval a R = 0 := by rw [halg]; exact hR
  obtain ⟨t, ht⟩ := minpoly.dvd _ a hRa

  have hsep : Pq.Separable := by
    rw [separable_def, hPq, derivative_sub, derivative_X, derivative_X_pow]
    haveI : CharP (↥(imageField red K q inferInstance)) q := (RingHom.charP_iff_charP (imageField red K q inferInstance).subtype q).mpr inferInstance
    have h0 : (C ((q ^ 2 : ℕ) : ↥(imageField red K q inferInstance)) : Polynomial ↥(imageField red K q inferInstance)) = 0 := by
      rw [Nat.cast_pow, CharP.cast_eq_zero _ q, zero_pow two_ne_zero, map_zero]
    rw [h0, zero_mul, sub_zero]
    exact isCoprime_one_right
  have hca : (c.map (imageField red K q inferInstance).subtype).eval a ≠ 0 := by
    intro hca0
    have hcd : minpoly (↥(imageField red K q inferInstance)) a ∣ c := minpoly.dvd _ a (by rw [halg]; exact hca0)
    obtain ⟨d, hd⟩ := hcd
    have hmm : minpoly (↥(imageField red K q inferInstance)) a * minpoly (↥(imageField red K q inferInstance)) a ∣ Pq := ⟨d, by rw [hc, hd]; ring⟩
    have hunit := hsep.squarefree _ hmm
    exact minpoly.not_isUnit _ a hunit
  refine ⟨t, c, hca, ?_⟩
  rw [← hPq, ht, hc]
  ring

variable (ϖ : ↥(coeffSubring A K)) (hϖ : ∀ c : ↥(coeffSubring A K), redRestrict red K c = 0 ↔ ∃ d, c = ϖ * d)

set_option maxHeartbeats 6400000 in
include hϖ in

theorem mem_sup_span_H_of_isRoot (ha2 : a ^ (q ^ 2) = a)
    (w : modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))
    {r s : MvPolynomial (Fin 2) (coeffSubring A K)}
    (hs : pointEval (coeffSubring A K) (redRestrict red K) a (a ^ q) s ≠ 0)
    (hws : (w : LaurentSeries (AlgebraicClosure ℚ)) * modularEval (1 * q) (coeffSubring A K) s = modularEval (1 * q) (coeffSubring A K) r)
    (hroot : (nodePoly q (redRestrict red K) r).IsRoot a) :
    w ∈ Ideal.span {modularEvalAt (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) (MvPolynomial.C ϖ),
                    modularEvalAt (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) (MvPolynomial.X 1 - MvPolynomial.X 0 ^ q)}
      ⊔ Ideal.span {modularEvalAt (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) (MvPolynomial.X 0 - MvPolynomial.X 1 ^ q)} := by
  classical
  haveI hfact : Fact (RingHom.ker (modularEval (1 * q) (coeffSubring A K)) ≤
      RingHom.ker (pointEval (coeffSubring A K) (redRestrict red K) a (a ^ q))) :=
    ⟨fun s hs => (RingHom.mem_ker).mpr
      (ModularCurve.NodeLocalized.pointEval_eq_zero_of_modularEval_eq_zero red a K s ((RingHom.mem_ker).mp hs))⟩

  set F₀ := imageField red K q inferInstance with hF₀
  set R₀ : Polynomial ↥F₀ := (σ₀ q _ r).map (redF red K q inferInstance) with hR₀
  set S₀ : Polynomial ↥F₀ := (σ₀ q _ s).map (redF red K q inferInstance) with hS₀
  have hΨ : ∀ p : MvPolynomial (Fin 2) (coeffSubring A K),
      nodePoly q (redRestrict red K) p = ((σ₀ q _ p).map (redF red K q inferInstance)).map F₀.subtype := by
    intro p
    rw [Polynomial.map_map, subtype_comp_redF red K q inferInstance, nodePoly_eq_mapRingHom_comp, RingHom.comp_apply, Polynomial.coe_mapRingHom]
  have hR₀a : (R₀.map F₀.subtype).eval a = 0 := by
    rw [hR₀, ← hΨ]
    exact hroot
  obtain ⟨t, c, hca, htc⟩ := exists_mul_eq_P_mul red a K ha2 R₀ hR₀a

  obtain ⟨T, hT⟩ := exists_map_redF_eq red K q inferInstance t
  obtain ⟨U, hU⟩ := exists_map_redF_eq red K q inferInstance (c * S₀)

  have hΨι : ∀ P : Polynomial (coeffSubring A K), nodePoly q (redRestrict red K) (ι₀ _ P) = P.map (redRestrict red K) := by
    intro P
    rw [nodePoly_eq_mapRingHom_comp, RingHom.comp_apply, Polynomial.coe_mapRingHom]
    congr 1
    show (σ₀ q _).comp (ι₀ _) P = P
    have : (σ₀ q (↥(coeffSubring A K))).comp (ι₀ _) = RingHom.id _ := by
      refine Polynomial.ringHom_ext (fun c => ?_) ?_
      · simp
      · simp
    rw [this, RingHom.id_apply]
  have hUeval : pointEval (coeffSubring A K) (redRestrict red K) a (a ^ q) (ι₀ _ U) ≠ 0 := by
    rw [← eval_nodePoly_eq_pointEval, hΨι, ← subtype_comp_redF red K q inferInstance, ← Polynomial.map_map, hU, Polynomial.map_mul,
      eval_mul]
    refine mul_ne_zero hca ?_
    rw [hS₀, ← hΨ, eval_nodePoly_eq_pointEval]
    exact hs
  obtain ⟨uU, huU⟩ := isUnit_modularEvalAt (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) hUeval
  obtain ⟨w₁, hw₁⟩ : ∃ w₁ : modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q),
      w₁ = modularEvalAt (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) (ι₀ _ T) * ↑uU⁻¹ := ⟨_, rfl⟩

  have hker : piZero red a K (w - (modularEvalAt (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) (MvPolynomial.X 0 - MvPolynomial.X 1 ^ q)) * w₁) = 0 := by

    have hS : Polynomial.aeval (jqModC k) (nodePoly q (redRestrict red K) s) ≠ 0 :=
      aeval_jqModC_ne_zero (nodePoly_ne_zero_of_pointEval_ne_zero red a K hs)
    have hUz : Polynomial.aeval (jqModC k) (nodePoly q (redRestrict red K) (ι₀ _ U)) ≠ 0 :=
      aeval_jqModC_ne_zero (nodePoly_ne_zero_of_pointEval_ne_zero red a K hUeval)
    apply mul_right_cancel₀ hS
    apply mul_right_cancel₀ hUz
    rw [zero_mul, zero_mul, map_sub, map_mul, sub_mul, sub_mul]

    have hw : piZero red a K w * Polynomial.aeval (jqModC k) (nodePoly q (redRestrict red K) s)
        = Polynomial.aeval (jqModC k) (nodePoly q (redRestrict red K) r) :=
      modularRedLocHom_mul_aeval_eq red K (le_modularLocalized red a K w.2) hws

    have hw₁E : w₁ * modularEvalAt (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) (ι₀ _ U)
        = modularEvalAt (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) (ι₀ _ T) := by
      rw [hw₁, ← huU, mul_assoc, Units.inv_mul, mul_one]
    have hw₁' : piZero red a K w₁ * Polynomial.aeval (jqModC k) (nodePoly q (redRestrict red K) (ι₀ _ U))
        = Polynomial.aeval (jqModC k) (nodePoly q (redRestrict red K) (ι₀ _ T)) := by
      have := congrArg (piZero red a K) hw₁E
      rwa [map_mul, piZero_modularEvalAt, piZero_modularEvalAt] at this
    have hH : piZero red a K (modularEvalAt (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) (MvPolynomial.X 0 - MvPolynomial.X 1 ^ q)) = Polynomial.aeval (jqModC k) (X - X ^ (q ^ 2) : k[X]) := by
      rw [piZero_modularEvalAt, nodePoly_H]

    have hΨι' : ∀ P : Polynomial (coeffSubring A K),
        nodePoly q (redRestrict red K) (ι₀ _ P) = (P.map (redF red K q inferInstance)).map F₀.subtype := by
      intro P
      rw [Polynomial.map_map, subtype_comp_redF]
      exact hΨι P
    have e1 : R₀ * (c * S₀) = (X - X ^ (q ^ 2)) * t * S₀ := by rw [← mul_assoc, htc]
    have hpoly : nodePoly q (redRestrict red K) r * nodePoly q (redRestrict red K) (ι₀ _ U)
        = (X - X ^ (q ^ 2)) * nodePoly q (redRestrict red K) (ι₀ _ T) * nodePoly q (redRestrict red K) s := by
      calc nodePoly q (redRestrict red K) r * nodePoly q (redRestrict red K) (ι₀ _ U)
          = R₀.map F₀.subtype * (c * S₀).map F₀.subtype := by rw [hΨι' U, hU, hΨ r, ← hR₀]
        _ = (R₀ * (c * S₀)).map F₀.subtype := by simp only [Polynomial.map_mul]
        _ = ((X - X ^ (q ^ 2)) * t * S₀).map F₀.subtype := by rw [e1]
        _ = (X - X ^ (q ^ 2)) * t.map F₀.subtype * S₀.map F₀.subtype := by
            simp only [Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_pow, map_X]
        _ = (X - X ^ (q ^ 2)) * nodePoly q (redRestrict red K) (ι₀ _ T) * nodePoly q (redRestrict red K) s := by
            rw [hΨι' T, hT, hΨ s, ← hS₀]
    calc piZero red a K w * Polynomial.aeval (jqModC k) (nodePoly q (redRestrict red K) s)
          * Polynomial.aeval (jqModC k) (nodePoly q (redRestrict red K) (ι₀ _ U))
          - piZero red a K (modularEvalAt (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) (MvPolynomial.X 0 - MvPolynomial.X 1 ^ q)) * piZero red a K w₁ * Polynomial.aeval (jqModC k) (nodePoly q (redRestrict red K) s)
          * Polynomial.aeval (jqModC k) (nodePoly q (redRestrict red K) (ι₀ _ U))
        = Polynomial.aeval (jqModC k) (nodePoly q (redRestrict red K) r * nodePoly q (redRestrict red K) (ι₀ _ U))
          - Polynomial.aeval (jqModC k) ((X - X ^ (q ^ 2)) * nodePoly q (redRestrict red K) (ι₀ _ T) * nodePoly q (redRestrict red K) s) := by
          rw [map_mul, ← hw, map_mul, map_mul, ← hw₁', hH]; ring
      _ = 0 := by rw [hpoly, sub_self]

  have hmem : w - (modularEvalAt (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) (MvPolynomial.X 0 - MvPolynomial.X 1 ^ q)) * w₁ ∈ Ideal.span {modularEvalAt (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) (MvPolynomial.C ϖ),
      modularEvalAt (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) (MvPolynomial.X 1 - MvPolynomial.X 0 ^ q)} :=
    (cardB red a ha2 K ϖ hϖ (w - (modularEvalAt (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) (MvPolynomial.X 0 - MvPolynomial.X 1 ^ q)) * w₁) (le_modularLocalized red a K (w - (modularEvalAt (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) (MvPolynomial.X 0 - MvPolynomial.X 1 ^ q)) * w₁).2)).mp hker
  have : w = (w - (modularEvalAt (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) (MvPolynomial.X 0 - MvPolynomial.X 1 ^ q)) * w₁) + (modularEvalAt (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) (MvPolynomial.X 0 - MvPolynomial.X 1 ^ q)) * w₁ := by ring
  rw [this]
  exact Submodule.add_mem_sup hmem (Ideal.mul_mem_right _ _ (Ideal.subset_span (Set.mem_singleton _)))

end Sublemma
p2m_reactivate "P2MW.S_ModularCurve_NodeLocalized_natCast_le_ord_modularRedLocHom_iff_mem_sup_span_pow.FltWs29 P2MW.S_ModularCurve_NodeLocalized_natCast_le_ord_modularRedLocHom_iff_mem_sup_span_pow.FltWs29.BCD"

section CardC

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
  {k : Type*} [Field k] [CharP k q] [DecidableEq k]

set_option maxHeartbeats 6400000 in
theorem cardC (red : A →+* k) (a : k) (ha2 : a ^ (q ^ 2) = a)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (ϖ : ↥(coeffSubring A K)) (hϖ : ∀ c : ↥(coeffSubring A K), redRestrict red K c = 0 ↔ ∃ d, c = ϖ * d)
    (g : ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)))
    (h₁ : (g : LaurentSeries (AlgebraicClosure ℚ)) ∈ CharPReduction.modularLocalized (1 * q) A.toSubring red)
    (h₁F : CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, h₁⟩ ∈ modularFunctionFieldC k 1)
    (h0 : CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, h₁⟩ ≠ 0) (n : ℕ) :
    (n : ℤ) ≤ (frobNodePair q a).1.ord (⟨_, h₁F⟩ : ↥(modularFunctionFieldC k 1)) ↔
      g ∈ Ideal.span {modularEvalAt (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) (MvPolynomial.C ϖ),
                      modularEvalAt (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) (MvPolynomial.X 1 - MvPolynomial.X 0 ^ q)}
          ⊔ Ideal.span {modularEvalAt (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) (MvPolynomial.X 0 - MvPolynomial.X 1 ^ q) ^ n} := by
  classical
  haveI hfact : Fact (RingHom.ker (modularEval (1 * q) (coeffSubring A K)) ≤
      RingHom.ker (pointEval (coeffSubring A K) (redRestrict red K) a (a ^ q))) :=
    ⟨fun s hs => (RingHom.mem_ker).mpr
      (ModularCurve.NodeLocalized.pointEval_eq_zero_of_modularEval_eq_zero red a K s ((RingHom.mem_ker).mp hs))⟩

  have hfst : (frobNodePair q a).1 = charLGeomPlaceOfPoint k a := rfl
  rw [hfst]

  have hmemF : ∀ x : modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q),
      piZero red a K x ∈ modularFunctionFieldC k 1 := fun x => by
    have h := modularRedLocHom_mem A.toSubring red (1 * q) ⟨_, le_modularLocalized red a K x.2⟩
    rw [modularFunctionFieldC_one_mul q k] at h
    exact h

  have hordH := ord_piZero_H red a K ha2 (hmemF (modularEvalAt (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) (MvPolynomial.X 0 - MvPolynomial.X 1 ^ q)))
  have hHne := piZero_H_ne_zero red a K ha2 (hmemF (modularEvalAt (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) (MvPolynomial.X 0 - MvPolynomial.X 1 ^ q)))

  have decomp : ∀ (m : ℕ) (p w : modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)),
      p ∈ Ideal.span {modularEvalAt (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) (MvPolynomial.C ϖ),
        modularEvalAt (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) (MvPolynomial.X 1 - MvPolynomial.X 0 ^ q)} →
      g = p + (modularEvalAt (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) (MvPolynomial.X 0 - MvPolynomial.X 1 ^ q)) ^ m * w →
      (⟨piZero red a K w, hmemF w⟩ : ↥(modularFunctionFieldC k 1)) ≠ 0 ∧
      (charLGeomPlaceOfPoint k a).ord (⟨_, h₁F⟩ : ↥(modularFunctionFieldC k 1))
        = m + (charLGeomPlaceOfPoint k a).ord (⟨piZero red a K w, hmemF w⟩ : ↥(modularFunctionFieldC k 1)) := by
    intro m p w hp hg
    have hπp : piZero red a K p = 0 := (cardB red a ha2 K ϖ hϖ p (le_modularLocalized red a K p.2)).mpr hp
    have hπg : piZero red a K g = piZero red a K (modularEvalAt (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) (MvPolynomial.X 0 - MvPolynomial.X 1 ^ q)) ^ m * piZero red a K w := by
      rw [hg, map_add, hπp, zero_add, map_mul, map_pow]
    have hmk : (⟨_, h₁F⟩ : ↥(modularFunctionFieldC k 1))
        = (⟨piZero red a K (modularEvalAt (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) (MvPolynomial.X 0 - MvPolynomial.X 1 ^ q)), hmemF (modularEvalAt (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) (MvPolynomial.X 0 - MvPolynomial.X 1 ^ q))⟩ : ↥(modularFunctionFieldC k 1)) ^ m * ⟨piZero red a K w, hmemF w⟩ := by
      apply Subtype.ext
      show modularRedLocHom (1 * q) A.toSubring red ⟨_, h₁⟩ = _
      rw [MulMemClass.coe_mul, SubmonoidClass.coe_pow]
      exact hπg
    have hw0 : (⟨piZero red a K w, hmemF w⟩ : ↥(modularFunctionFieldC k 1)) ≠ 0 := by
      intro hw
      apply h0
      have := hmk
      rw [hw, mul_zero] at this
      exact congrArg Subtype.val this
    refine ⟨hw0, ?_⟩
    rw [hmk, Place.ord_mul _ (pow_ne_zero _ hHne) hw0, Place.ord_pow' _ hHne, hordH, mul_one]
  constructor
  ·
    intro hn
    induction n with
    | zero =>
      rw [pow_zero, Ideal.span_singleton_one]
      exact Submodule.mem_sup_right Submodule.mem_top
    | succ n ih =>
      have hn' : (n : ℤ) ≤ (charLGeomPlaceOfPoint k a).ord (⟨_, h₁F⟩ : ↥(modularFunctionFieldC k 1)) := by
        push_cast at hn; omega
      obtain ⟨p, hp, z, hz, hpz⟩ := Submodule.mem_sup.mp (ih hn')
      obtain ⟨w, rfl⟩ := Ideal.mem_span_singleton'.mp hz
      obtain ⟨hw0, hord⟩ := decomp n p w hp (by rw [← hpz]; ring)

      obtain ⟨r, s, hs, hws⟩ := w.2
      have hw0' : piZero red a K w ≠ 0 := fun h => hw0 (Subtype.ext h)
      obtain ⟨hrne, hordw⟩ := ord_piZero_eq red a K w (hmemF w) hw0' hs hws
      have hmult : 1 ≤ (nodePoly q (redRestrict red K) r).rootMultiplicity a := by
        have : (1 : ℤ) ≤ (charLGeomPlaceOfPoint k a).ord (⟨piZero red a K w, hmemF w⟩ : ↥(modularFunctionFieldC k 1)) := by
          push_cast at hn; omega
        rw [hordw] at this
        exact_mod_cast this
      have hroot : (nodePoly q (redRestrict red K) r).IsRoot a :=
        (Polynomial.rootMultiplicity_pos hrne).mp hmult
      have hwmem := mem_sup_span_H_of_isRoot red a K ϖ hϖ ha2 w hs hws hroot
      obtain ⟨p', hp', z', hz', hpz'⟩ := Submodule.mem_sup.mp hwmem
      obtain ⟨w', rfl⟩ := Ideal.mem_span_singleton'.mp hz'

      have : g = (p + (modularEvalAt (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) (MvPolynomial.X 0 - MvPolynomial.X 1 ^ q)) ^ n * p') + w' * (modularEvalAt (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) (MvPolynomial.X 0 - MvPolynomial.X 1 ^ q)) ^ (n + 1) := by
        rw [← hpz, ← hpz']; ring
      rw [this]
      refine Submodule.add_mem_sup (Ideal.add_mem _ hp (Ideal.mul_mem_left _ _ hp')) (Ideal.mem_span_singleton'.mpr ⟨w', rfl⟩)
  ·
    intro hg
    obtain ⟨p, hp, z, hz, hpz⟩ := Submodule.mem_sup.mp hg
    obtain ⟨w, rfl⟩ := Ideal.mem_span_singleton'.mp hz
    obtain ⟨hw0, hord⟩ := decomp n p w hp (by rw [← hpz]; ring)
    rw [hord]
    have := ord_piZero_nonneg red a K w (hmemF w)
    omega

end CardC
p2m_reactivate "P2MW.S_ModularCurve_NodeLocalized_natCast_le_ord_modularRedLocHom_iff_mem_sup_span_pow.FltWs29 P2MW.S_ModularCurve_NodeLocalized_natCast_le_ord_modularRedLocHom_iff_mem_sup_span_pow.FltWs29.BCD"

section CardD

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
  {k : Type*} [Field k] [CharP k q] [DecidableEq k]

set_option maxHeartbeats 6400000 in
theorem cardD (red : A →+* k) (a : k) (ha2 : a ^ (q ^ 2) = a)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (ϖ : ↥(coeffSubring A K)) (hϖ : ∀ c : ↥(coeffSubring A K), redRestrict red K c = 0 ↔ ∃ d, c = ϖ * d)
    (g : ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)))
    (h₁ : (g : LaurentSeries (AlgebraicClosure ℚ)) ∈ CharPReduction.modularLocalized (1 * q) A.toSubring red)
    (h₁F : CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, h₁⟩ ∈ modularFunctionFieldC k 1)
    (h0 : CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, h₁⟩ ≠ 0) (n : ℕ) :
    (frobNodePair q a).1.ord (⟨_, h₁F⟩ : ↥(modularFunctionFieldC k 1)) = n ↔
      ∃ u : ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)), IsUnit u ∧
        g - modularEvalAt (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) (MvPolynomial.X 0 - MvPolynomial.X 1 ^ q) ^ n * u
          ∈ Ideal.span {modularEvalAt (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) (MvPolynomial.C ϖ),
                        modularEvalAt (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) (MvPolynomial.X 1 - MvPolynomial.X 0 ^ q)} := by
  classical
  haveI hfact : Fact (RingHom.ker (modularEval (1 * q) (coeffSubring A K)) ≤
      RingHom.ker (pointEval (coeffSubring A K) (redRestrict red K) a (a ^ q))) :=
    ⟨fun s hs => (RingHom.mem_ker).mpr
      (ModularCurve.NodeLocalized.pointEval_eq_zero_of_modularEval_eq_zero red a K s ((RingHom.mem_ker).mp hs))⟩
  have hmemF : ∀ x : modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q),
      piZero red a K x ∈ modularFunctionFieldC k 1 := fun x => by
    have h := modularRedLocHom_mem A.toSubring red (1 * q) ⟨_, le_modularLocalized red a K x.2⟩
    rw [modularFunctionFieldC_one_mul q k] at h
    exact h

  have ord_unit : ∀ u : modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q), IsUnit u →
      (charLGeomPlaceOfPoint k a).ord (⟨piZero red a K u, hmemF u⟩ : ↥(modularFunctionFieldC k 1)) = 0 := by
    intro u hu
    obtain ⟨v, hv⟩ := hu.exists_right_inv
    have h1 : (⟨piZero red a K u, hmemF u⟩ : ↥(modularFunctionFieldC k 1)) * ⟨piZero red a K v, hmemF v⟩ = 1 := by
      apply Subtype.ext
      rw [MulMemClass.coe_mul, OneMemClass.coe_one, ← map_mul, hv, map_one]
    have hu0 : (⟨piZero red a K u, hmemF u⟩ : ↥(modularFunctionFieldC k 1)) ≠ 0 := left_ne_zero_of_mul_eq_one h1
    have hv0 : (⟨piZero red a K v, hmemF v⟩ : ↥(modularFunctionFieldC k 1)) ≠ 0 := right_ne_zero_of_mul_eq_one h1
    have h2 := congrArg (charLGeomPlaceOfPoint k a).ord h1
    rw [Place.ord_mul _ hu0 hv0, Place.ord_one] at h2
    have h3 := ord_piZero_nonneg red a K u (hmemF u)
    have h4 := ord_piZero_nonneg red a K v (hmemF v)
    omega
  have hfst : (frobNodePair q a).1 = charLGeomPlaceOfPoint k a := rfl
  rw [hfst]
  constructor
  · intro hn

    have hC := (cardC red a ha2 K ϖ hϖ g h₁ h₁F h0 n).mp (by rw [hfst]; exact hn.ge)
    obtain ⟨p, hp, z, hz, hpz⟩ := Submodule.mem_sup.mp hC
    obtain ⟨w, rfl⟩ := Ideal.mem_span_singleton'.mp hz

    have hπp : piZero red a K p = 0 := (cardB red a ha2 K ϖ hϖ p (le_modularLocalized red a K p.2)).mpr hp
    have hπg : piZero red a K g = piZero red a K (modularEvalAt (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) (MvPolynomial.X 0 - MvPolynomial.X 1 ^ q)) ^ n * piZero red a K w := by
      rw [← hpz, map_add, hπp, zero_add, map_mul, map_pow, mul_comm]
    have hHmem := hmemF (modularEvalAt (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) (MvPolynomial.X 0 - MvPolynomial.X 1 ^ q))
    have hordH : (charLGeomPlaceOfPoint k a).ord (⟨piZero red a K (modularEvalAt (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) (MvPolynomial.X 0 - MvPolynomial.X 1 ^ q)), hHmem⟩ : ↥(modularFunctionFieldC k 1)) = 1 :=
      ord_piZero_H red a K ha2 hHmem
    have hHne : (⟨piZero red a K (modularEvalAt (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) (MvPolynomial.X 0 - MvPolynomial.X 1 ^ q)), hHmem⟩ : ↥(modularFunctionFieldC k 1)) ≠ 0 := piZero_H_ne_zero red a K ha2 hHmem
    have hmk : (⟨_, h₁F⟩ : ↥(modularFunctionFieldC k 1))
        = (⟨piZero red a K (modularEvalAt (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) (MvPolynomial.X 0 - MvPolynomial.X 1 ^ q)), hHmem⟩ : ↥(modularFunctionFieldC k 1)) ^ n * ⟨piZero red a K w, hmemF w⟩ := by
      apply Subtype.ext
      show modularRedLocHom (1 * q) A.toSubring red ⟨_, h₁⟩ = _
      rw [MulMemClass.coe_mul, SubmonoidClass.coe_pow]
      exact hπg
    have hw0 : (⟨piZero red a K w, hmemF w⟩ : ↥(modularFunctionFieldC k 1)) ≠ 0 := by
      intro hw; apply h0
      have := hmk; rw [hw, mul_zero] at this; exact congrArg Subtype.val this
    have hordw : (charLGeomPlaceOfPoint k a).ord (⟨piZero red a K w, hmemF w⟩ : ↥(modularFunctionFieldC k 1)) = 0 := by
      have := congrArg (charLGeomPlaceOfPoint k a).ord hmk
      rw [Place.ord_mul _ (pow_ne_zero _ hHne) hw0, Place.ord_pow' _ hHne, hordH, mul_one, hn] at this
      omega
    obtain ⟨r, s, hs, hws⟩ := w.2
    have hw0' : piZero red a K w ≠ 0 := fun h => hw0 (Subtype.ext h)
    obtain ⟨hrne, hordw'⟩ := ord_piZero_eq red a K w (hmemF w) hw0' hs hws
    rw [hordw] at hordw'
    have hra : pointEval (coeffSubring A K) (redRestrict red K) a (a ^ q) r ≠ 0 := by
      intro h
      have hroot : (nodePoly q (redRestrict red K) r).IsRoot a := by
        rw [IsRoot, eval_nodePoly_eq_pointEval]; exact h
      have := (Polynomial.rootMultiplicity_pos hrne).mpr hroot
      omega

    obtain ⟨ur, hur⟩ := isUnit_modularEvalAt (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) hra
    obtain ⟨us, hus⟩ := isUnit_modularEvalAt (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) hs
    have hwE : w * modularEvalAt (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) s
        = modularEvalAt (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) r := Subtype.ext hws
    have hwu : IsUnit w := by
      have : w = ↑ur * ↑us⁻¹ := by
        rw [hur, ← hwE, ← hus, mul_assoc, Units.mul_inv, mul_one]
      rw [this]
      exact (Units.isUnit _).mul (Units.isUnit _)
    refine ⟨w, hwu, ?_⟩
    have : g - (modularEvalAt (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) (MvPolynomial.X 0 - MvPolynomial.X 1 ^ q)) ^ n * w = p := by rw [← hpz]; ring
    rw [this]
    exact hp
  · rintro ⟨u, hu, hmem⟩
    have hπp : piZero red a K (g - (modularEvalAt (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) (MvPolynomial.X 0 - MvPolynomial.X 1 ^ q)) ^ n * u) = 0 :=
      (cardB red a ha2 K ϖ hϖ _ (le_modularLocalized red a K (g - (modularEvalAt (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) (MvPolynomial.X 0 - MvPolynomial.X 1 ^ q)) ^ n * u).2)).mpr hmem
    have hπg : piZero red a K g = piZero red a K (modularEvalAt (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) (MvPolynomial.X 0 - MvPolynomial.X 1 ^ q)) ^ n * piZero red a K u := by
      rw [map_sub, sub_eq_zero, map_mul, map_pow] at hπp
      exact hπp
    have hHmem := hmemF (modularEvalAt (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) (MvPolynomial.X 0 - MvPolynomial.X 1 ^ q))
    have hordH : (charLGeomPlaceOfPoint k a).ord (⟨piZero red a K (modularEvalAt (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) (MvPolynomial.X 0 - MvPolynomial.X 1 ^ q)), hHmem⟩ : ↥(modularFunctionFieldC k 1)) = 1 :=
      ord_piZero_H red a K ha2 hHmem
    have hHne : (⟨piZero red a K (modularEvalAt (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) (MvPolynomial.X 0 - MvPolynomial.X 1 ^ q)), hHmem⟩ : ↥(modularFunctionFieldC k 1)) ≠ 0 := piZero_H_ne_zero red a K ha2 hHmem
    have hmk : (⟨_, h₁F⟩ : ↥(modularFunctionFieldC k 1))
        = (⟨piZero red a K (modularEvalAt (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) (MvPolynomial.X 0 - MvPolynomial.X 1 ^ q)), hHmem⟩ : ↥(modularFunctionFieldC k 1)) ^ n * ⟨piZero red a K u, hmemF u⟩ := by
      apply Subtype.ext
      show modularRedLocHom (1 * q) A.toSubring red ⟨_, h₁⟩ = _
      rw [MulMemClass.coe_mul, SubmonoidClass.coe_pow]
      exact hπg
    have hu0 : (⟨piZero red a K u, hmemF u⟩ : ↥(modularFunctionFieldC k 1)) ≠ 0 := by
      intro hu'; apply h0
      have := hmk; rw [hu', mul_zero] at this; exact congrArg Subtype.val this
    rw [hmk, Place.ord_mul _ (pow_ne_zero _ hHne) hu0, Place.ord_pow' _ hHne, hordH, mul_one, ord_unit u hu, add_zero]

end CardD
p2m_reactivate "P2MW.S_ModularCurve_NodeLocalized_natCast_le_ord_modularRedLocHom_iff_mem_sup_span_pow.FltWs29 P2MW.S_ModularCurve_NodeLocalized_natCast_le_ord_modularRedLocHom_iff_mem_sup_span_pow.FltWs29.BCD"

end FltWs29.BCD
p2m_reactivate "P2MW.S_ModularCurve_NodeLocalized_natCast_le_ord_modularRedLocHom_iff_mem_sup_span_pow.FltWs29 P2MW.S_ModularCurve_NodeLocalized_natCast_le_ord_modularRedLocHom_iff_mem_sup_span_pow.FltWs29.BCD"
p2m_reactivate "P2MW.S_ModularCurve_NodeLocalized_natCast_le_ord_modularRedLocHom_iff_mem_sup_span_pow.FltWs29 P2MW.S_ModularCurve_NodeLocalized_natCast_le_ord_modularRedLocHom_iff_mem_sup_span_pow.FltWs29.BCD"

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.NodeLocalized in
theorem solution
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] [DecidableEq k] (red : A →+* k) (a : k) (ha2 : a ^ (q ^ 2) = a)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (ϖ : ↥(coeffSubring A K)) (hϖ : ∀ c : ↥(coeffSubring A K), redRestrict red K c = 0 ↔ ∃ d, c = ϖ * d)
    (g : ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)))
    (h₁ : (g : LaurentSeries (AlgebraicClosure ℚ)) ∈ CharPReduction.modularLocalized (1 * q) A.toSubring red)
    (h₁F : CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, h₁⟩ ∈ modularFunctionFieldC k 1)
    (h0 : CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, h₁⟩ ≠ 0) (n : ℕ) :
    (n : ℤ) ≤ (frobNodePair q a).1.ord (⟨_, h₁F⟩ : ↥(modularFunctionFieldC k 1)) ↔
      g ∈ Ideal.span {(⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ),
        modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ : ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))),
                      (⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.X 1 - MvPolynomial.X 0 ^ q),
        modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ : ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)))}
          ⊔ Ideal.span {(⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.X 0 - MvPolynomial.X 1 ^ q),
        modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ : ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))) ^ n} :=
  FltWs29.BCD.cardC red a ha2 K ϖ hϖ g h₁ h₁F h0 n

end S_ModularCurve_NodeLocalized_natCast_le_ord_modularRedLocHom_iff_mem_sup_span_pow
end P2MW
export P2MW.S_ModularCurve_NodeLocalized_natCast_le_ord_modularRedLocHom_iff_mem_sup_span_pow (solution)
