-- Prove2me | solution 1 for ModularCurve.minpoly_heckeAlphaBar_along_heckeBetaBar
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/526651ce-e35f-5a0a-9f05-19cb414beda1

import Definitions.Def_ModularCurve_HeckeOperator
import Definitions.Def_ModularCurve_PhiGen
import Theorems.Thm_ModularCurve_finrankAlong_heckeBetaBar
import Mathlib.FieldTheory.Minpoly.Basic
import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.LinearAlgebra.Dimension.Free
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_minpoly_heckeAlphaBar_along_heckeBetaBar
p2m_attr_erase "instance" "ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy"
p2m_attr_erase "simp" "ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.jqNModC_one ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk"
p2m_attr_erase "simp" "ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ"

set_option autoImplicit false

noncomputable section

p2m_open "ModularCurve~dedekindPsi_prime~coeffEmb_qExpand AlgebraicCurve Polynomial"

namespace CharpS10bB
namespace DB

private abbrev Qb : Type := AlgebraicClosure ℚ

private abbrev Fb (M : ℕ) [NeZero M] : IntermediateField Qb (LaurentSeries Qb) :=
  laurentBaseChange Qb (modularFunctionFieldFull M)

private def J (N : ℕ) [NeZero N] : Fb N :=
  ⟨coeffEmb Qb jq, coeffEmb_mem_laurentBaseChange Qb (modularFunctionField_le_full N (jq_mem N))⟩

@[scoped simp] private theorem coe_J (N : ℕ) [NeZero N] : ((J N : Fb N) : LaurentSeries Qb) = coeffEmb Qb jq := rfl

private theorem coeffMap_eval₂Bivar {R S : Type*} [CommRing R] [CommRing S] (Φ : Polynomial (Polynomial ℤ))
    (f : R →+* S) (u v : LaurentSeries R) :
    coeffMap f (Φ.eval₂ (Polynomial.aeval (R := ℤ) u).toRingHom v)
      = Φ.eval₂ (Polynomial.aeval (R := ℤ) (coeffMap f u)).toRingHom (coeffMap f v) := by
  rw [Polynomial.hom_eval₂]
  congr 1
  apply Polynomial.ringHom_ext
  · intro a
    simp only [AlgHom.toRingHom_eq_coe, eq_intCast, map_intCast]
  · simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
      Polynomial.aeval_X]

private theorem coeffEmb_eval₂Bivar (Φ : Polynomial (Polynomial ℤ)) (u v : LaurentSeries ℚ) :
    coeffEmb Qb (Φ.eval₂ (Polynomial.aeval (R := ℤ) u).toRingHom v)
      = Φ.eval₂ (Polynomial.aeval (R := ℤ) (coeffEmb Qb u)).toRingHom (coeffEmb Qb v) :=
  coeffMap_eval₂Bivar Φ (algebraMap ℚ Qb) u v

private theorem coeffEmb_qExpand (n : ℕ) [NeZero n] (x : LaurentSeries ℚ) :
    coeffEmb Qb (qExpand ℚ n x) = qExpand Qb n (coeffEmb Qb x) := by
  ext k
  by_cases h : (n : ℤ) ∣ k
  · obtain ⟨m, rfl⟩ := h
    rw [coeffEmb_coeff, qExpand_coeff_mul, qExpand_coeff_mul, coeffEmb_coeff]
  · rw [coeffEmb_coeff, qExpand_coeff_of_not_dvd _ _ h, qExpand_coeff_of_not_dvd _ _ h, map_zero]

private theorem dedekindPsi_prime (ℓ : ℕ) [hℓ : Fact ℓ.Prime] : dedekindPsi ℓ = ℓ + 1 := by
  have hp := hℓ.out
  rw [dedekindPsi, Nat.Prime.divisors hp, Finset.filter_insert, if_pos squarefree_one,
    Finset.filter_singleton, if_pos hp.prime.squarefree, Finset.sum_insert (by
      rw [Finset.mem_singleton]; exact hp.one_lt.ne), Finset.sum_singleton, Nat.div_one,
    Nat.div_self hp.pos, add_comm]

section Main

variable (N ℓ : ℕ) [NeZero N] [hℓ : Fact ℓ.Prime]

private abbrev S : Fb (N * ℓ) →+* LaurentSeries Qb := algebraMap (Fb (N * ℓ)) (LaurentSeries Qb)

private theorem S_apply (y : Fb (N * ℓ)) : S N ℓ y = (y : LaurentSeries Qb) := rfl

private theorem aeval_eq_zero (data : ModularPolynomialData ℓ) (hsym : EvalSymm data.Φ) :
    letI := algebraAlong (heckeBetaBar Qb N ℓ)
    Polynomial.aeval (heckeAlphaBar Qb N ℓ (J N))
        (data.Φ.map (Polynomial.aeval (R := ℤ) (J N)).toRingHom) = 0 := by
  letI : Algebra (Fb N) (Fb (N * ℓ)) := algebraAlong (heckeBetaBar Qb N ℓ)
  apply (S N ℓ).injective
  rw [map_zero, Polynomial.aeval_def, Polynomial.eval₂_map, Polynomial.hom_eval₂]
  have hcomp : ((S N ℓ).comp ((algebraMap (Fb N) (Fb (N * ℓ))).comp
      (Polynomial.aeval (R := ℤ) (J N)).toRingHom))
      = (Polynomial.aeval (R := ℤ) (qExpand Qb ℓ (coeffEmb Qb jq))).toRingHom := by
    apply Polynomial.ringHom_ext
    · intro a
      simp only [AlgHom.toRingHom_eq_coe, eq_intCast, map_intCast]
    · simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
        Polynomial.aeval_X]
      show ((heckeBetaBar Qb N ℓ (J N) : Fb (N * ℓ)) : LaurentSeries Qb) = _
      rw [coe_heckeBetaBar, coe_J]
  rw [hcomp, S_apply, coe_heckeAlphaBar, coe_J, ← coeffEmb_qExpand,
    show qExpand ℚ ℓ jq = jqN ℓ from rfl, ← coeffEmb_eval₂Bivar,
    ← hsym jq (jqN ℓ), show (Polynomial.aeval (R := ℤ) jq).toRingHom = evalAtJ from rfl,
    data.eval_eq_zero, map_zero]

private theorem le_natDegree_minpoly (hint : letI := algebraAlong (heckeBetaBar Qb N ℓ)
      IsIntegral (Fb N) (heckeAlphaBar Qb N ℓ (J N))) :
    letI := algebraAlong (heckeBetaBar Qb N ℓ)
    ℓ ≤ (minpoly (Fb N) (heckeAlphaBar Qb N ℓ (J N))).natDegree := by
  letI : Algebra (Fb N) (Fb (N * ℓ)) := algebraAlong (heckeBetaBar Qb N ℓ)
  set x : Fb (N * ℓ) := heckeAlphaBar Qb N ℓ (J N) with hx
  have hp := hℓ.out
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Qb ℓ
  have hζ0 : ζ ≠ 0 := hζ.ne_zero hp.ne_zero
  set u : Qbˣ := Units.mk0 ζ hζ0 with hu
  have hul : u ^ ℓ = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_mk0, hζ.pow_eq_one, Units.val_one])

  have hT : ∀ i : ℕ, (((qTwist (u ^ i)).comp (S N ℓ)).comp (algebraMap (Fb N) (Fb (N * ℓ))))
      = (S N ℓ).comp (algebraMap (Fb N) (Fb (N * ℓ))) := by
    intro i
    apply RingHom.ext
    intro f
    show qTwist (u ^ i) ((heckeBetaBar Qb N ℓ f : Fb (N * ℓ)) : LaurentSeries Qb)
      = ((heckeBetaBar Qb N ℓ f : Fb (N * ℓ)) : LaurentSeries Qb)
    have hz : (u ^ i) ^ (ℓ : ℤ) = 1 := by
      rw [zpow_natCast, ← pow_mul, mul_comm, pow_mul, hul, one_pow]
    rw [coe_heckeBetaBar, qTwist_qExpand, hz, qTwist_one_apply]

  set g : Fb N →+* LaurentSeries Qb := (S N ℓ).comp (algebraMap (Fb N) (Fb (N * ℓ))) with hg
  set mS := (minpoly (Fb N) x).map g with hmS
  have hmS0 : mS ≠ 0 := Polynomial.map_ne_zero (minpoly.ne_zero hint)
  set r : ℕ → LaurentSeries Qb := fun i => qTwist (u ^ i) (coeffEmb Qb jq) with hr
  have hroot : ∀ i : ℕ, mS.IsRoot (r i) := by
    intro i
    have h0 := minpoly.aeval (Fb N) x
    have h1 := congrArg ((qTwist (u ^ i)).comp (S N ℓ)) h0
    rw [map_zero, Polynomial.aeval_def, Polynomial.hom_eval₂, hT i] at h1
    rw [Polynomial.IsRoot, hmS, Polynomial.eval_map]
    convert h1 using 2 <;> try rfl

  have hcoeff : ∀ i : ℕ, (r i).coeff (-1) = ((u ^ i)⁻¹ : Qbˣ) := by
    intro i
    show (qTwist (u ^ i) (coeffEmb Qb jq)).coeff (-1) = _
    rw [qTwist_coeff, coeffEmb_coeff, coeff_jq_neg_one, map_one, mul_one, zpow_neg, zpow_one]
  have hinj : ∀ i j : ℕ, i < ℓ → j < ℓ → r i = r j → i = j := by
    intro i j hi hj hij
    have h := congrArg (fun f : LaurentSeries Qb => f.coeff (-1)) hij
    simp only [hcoeff] at h
    have h' : u ^ i = u ^ j := inv_injective (Units.val_injective h)
    have h'' : ζ ^ i = ζ ^ j := by
      have := congrArg (fun w : Qbˣ => (w : Qb)) h'
      simpa only [Units.val_pow_eq_pow_val, hu, Units.val_mk0] using this
    exact hζ.pow_inj hi hj h''

  classical
  have hsub : (Finset.image (fun i : Fin ℓ => r i) Finset.univ) ⊆ mS.roots.toFinset := by
    intro y hy
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hy
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hmS0]
    exact hroot i
  have hcard : (Finset.image (fun i : Fin ℓ => r i) Finset.univ).card = ℓ := by
    rw [Finset.card_image_of_injective _ (fun i j h => Fin.ext (hinj i j i.2 j.2 h)),
      Finset.card_univ, Fintype.card_fin]
  calc ℓ = (Finset.image (fun i : Fin ℓ => r i) Finset.univ).card := hcard.symm
    _ ≤ mS.roots.toFinset.card := Finset.card_le_card hsub
    _ ≤ Multiset.card mS.roots := Multiset.toFinset_card_le _
    _ ≤ mS.natDegree := Polynomial.card_roots' _
    _ = (minpoly (Fb N) x).natDegree := Polynomial.natDegree_map _

private theorem minpoly_eq (hlN : ¬ ℓ ∣ N) (data : ModularPolynomialData ℓ) (hsym : EvalSymm data.Φ) :
    letI := algebraAlong (heckeBetaBar Qb N ℓ)
    minpoly (Fb N) (heckeAlphaBar Qb N ℓ (J N))
      = data.Φ.map (Polynomial.aeval (R := ℤ) (J N)).toRingHom := by
  letI : Algebra (Fb N) (Fb (N * ℓ)) := algebraAlong (heckeBetaBar Qb N ℓ)
  set x : Fb (N * ℓ) := heckeAlphaBar Qb N ℓ (J N) with hx
  set P := data.Φ.map (Polynomial.aeval (R := ℤ) (J N)).toRingHom with hP
  have hp := hℓ.out
  have hPm : P.Monic := data.monic.map _
  have hPdeg : P.natDegree = ℓ + 1 := by
    rw [hP, (data.monic).natDegree_map, data.natDegree_eq, dedekindPsi_prime]
  have hfin : Module.finrank (Fb N) (Fb (N * ℓ)) = ℓ + 1 := by
    have h : finrankAlong Qb (heckeBetaBar Qb N ℓ) = if ℓ ∣ N then ℓ else ℓ + 1 :=
      finrankAlong_heckeBetaBar Qb N ℓ
    rw [if_neg hlN] at h
    exact h
  haveI : FiniteDimensional (Fb N) (Fb (N * ℓ)) := Module.finite_of_finrank_pos (by omega)
  have hint : IsIntegral (Fb N) x := IsIntegral.of_finite (Fb N) x
  have hrootP : Polynomial.aeval x P = 0 := aeval_eq_zero N ℓ data hsym
  have hge : ℓ ≤ (minpoly (Fb N) x).natDegree := le_natDegree_minpoly N ℓ hint
  have hdvd : (minpoly (Fb N) x).natDegree ∣ ℓ + 1 := by
    refine ⟨Module.finrank (IntermediateField.adjoin (Fb N) {x}) (Fb (N * ℓ)), ?_⟩
    rw [← IntermediateField.adjoin.finrank hint, Module.finrank_mul_finrank, hfin]
  have hdeg : (minpoly (Fb N) x).natDegree = ℓ + 1 := by
    obtain ⟨c, hc⟩ := hdvd
    set d := (minpoly (Fb N) x).natDegree with hd
    have h2 : 2 ≤ ℓ := hp.two_le
    rcases Nat.lt_or_ge c 2 with hc2 | hc2
    · interval_cases c
      · omega
      · omega
    · exfalso
      have hmul : d * 2 ≤ d * c := Nat.mul_le_mul_left d hc2
      omega
  have hdvdP : minpoly (Fb N) x ∣ P := minpoly.dvd (Fb N) x hrootP
  exact (Polynomial.eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hint) hPm hdvdP
    (by rw [hPdeg, hdeg])).symm

end Main

end DB
p2m_reactivate "P2MW.S_ModularCurve_minpoly_heckeAlphaBar_along_heckeBetaBar.CharpS10bB.DB"
end CharpS10bB
p2m_reactivate "P2MW.S_ModularCurve_minpoly_heckeAlphaBar_along_heckeBetaBar.CharpS10bB.DB P2MW.S_ModularCurve_minpoly_heckeAlphaBar_along_heckeBetaBar.CharpS10bB"

theorem solution
    (N ℓ : ℕ) [NeZero N] [Fact ℓ.Prime] (hlN : ¬ ℓ ∣ N)
    (data : ModularCurve.ModularPolynomialData ℓ) (hsym : ModularCurve.EvalSymm data.Φ) :
    letI := AlgebraicCurve.algebraAlong (ModularCurve.heckeBetaBar (AlgebraicClosure ℚ) N ℓ)
    minpoly (ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.modularFunctionFieldFull N))
        (ModularCurve.heckeAlphaBar (AlgebraicClosure ℚ) N ℓ
          ⟨ModularCurve.coeffEmb (AlgebraicClosure ℚ) ModularCurve.jq,
            ModularCurve.coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
              (ModularCurve.modularFunctionField_le_full N (ModularCurve.jq_mem N))⟩)
      = data.Φ.map (Polynomial.aeval (R := ℤ)
          (⟨ModularCurve.coeffEmb (AlgebraicClosure ℚ) ModularCurve.jq,
            ModularCurve.coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
              (ModularCurve.modularFunctionField_le_full N (ModularCurve.jq_mem N))⟩
            : ModularCurve.laurentBaseChange (AlgebraicClosure ℚ)
                (ModularCurve.modularFunctionFieldFull N))).toRingHom :=
  CharpS10bB.DB.minpoly_eq N ℓ hlN data hsym

end
p2m_reactivate "P2MW.S_ModularCurve_minpoly_heckeAlphaBar_along_heckeBetaBar.CharpS10bB.DB P2MW.S_ModularCurve_minpoly_heckeAlphaBar_along_heckeBetaBar.CharpS10bB"

end S_ModularCurve_minpoly_heckeAlphaBar_along_heckeBetaBar
end P2MW
export P2MW.S_ModularCurve_minpoly_heckeAlphaBar_along_heckeBetaBar (solution)
