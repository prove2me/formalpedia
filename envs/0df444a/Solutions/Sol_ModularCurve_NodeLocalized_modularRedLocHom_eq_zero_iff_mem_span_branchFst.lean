-- Prove2me | solution 1 for ModularCurve.NodeLocalized.modularRedLocHom_eq_zero_iff_mem_span_branchFst
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/9dc5b6fd-cc27-5b64-af2c-0910d16c5b73

import Mathlib
import Definitions.Def_ModularCurve_NodeDescent
import Definitions.Def_ModularCurve_SupersingularNodes
import Definitions.Def_ModularCurve_CuspidalClass
import Definitions.Def_ModularCurve_NodeLocalizedPresentation
import Theorems.Thm_ModularCurve_NodeLocalized_pointEval_eq_zero_of_modularEval_eq_zero
import Theorems.Thm_ModularCurve_transcendental_jqModC
import Theorems.Thm_ModularCurve_frobenius_identity_geom_unconditional
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_NodeLocalized_modularRedLocHom_eq_zero_iff_mem_span_branchFst
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy"
p2m_attr_erase "simp" "ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom"
p2m_attr_erase "simp" "AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar"
p2m_attr_erase "simp" "ModularCurve.coe_heckeAlphaBar"
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
p2m_reactivate "P2MW.S_ModularCurve_NodeLocalized_modularRedLocHom_eq_zero_iff_mem_span_branchFst.FltWs29 P2MW.S_ModularCurve_NodeLocalized_modularRedLocHom_eq_zero_iff_mem_span_branchFst.FltWs29.BCD"
p2m_reactivate "P2MW.S_ModularCurve_NodeLocalized_modularRedLocHom_eq_zero_iff_mem_span_branchFst.FltWs29"

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.NodeLocalized in
theorem solution
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] [DecidableEq k] (red : A →+* k) (a : k) (ha2 : a ^ (q ^ 2) = a)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (ϖ : ↥(coeffSubring A K)) (hϖ : ∀ c : ↥(coeffSubring A K), redRestrict red K c = 0 ↔ ∃ d, c = ϖ * d)
    (g : ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)))
    (h₁ : (g : LaurentSeries (AlgebraicClosure ℚ)) ∈ CharPReduction.modularLocalized (1 * q) A.toSubring red) :
    CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, h₁⟩ = 0 ↔
      g ∈ Ideal.span {(⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ),
        modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ : ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))),
                      (⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.X 1 - MvPolynomial.X 0 ^ q),
        modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ : ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)))} :=
  FltWs29.BCD.cardB red a ha2 K ϖ hϖ g h₁

end S_ModularCurve_NodeLocalized_modularRedLocHom_eq_zero_iff_mem_span_branchFst
end P2MW
export P2MW.S_ModularCurve_NodeLocalized_modularRedLocHom_eq_zero_iff_mem_span_branchFst (solution)
