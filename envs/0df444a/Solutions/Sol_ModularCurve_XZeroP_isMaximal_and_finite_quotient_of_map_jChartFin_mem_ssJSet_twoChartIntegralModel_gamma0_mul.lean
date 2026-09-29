-- Prove2me | solution 1 for ModularCurve.XZeroP.isMaximal_and_finite_quotient_of_map_jChartFin_mem_ssJSet_twoChartIntegralModel_gamma0_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/f64a5d0e-3b8f-53e4-9bed-d9b0d436ad63

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_SupersingularModuli
import Theorems.Thm_ModularCurve_finiteDimensional_adjoin_of_coe_eq_coeffEmb_jq_of_eq_laurentBaseChange
import Theorems.Thm_ModularCurve_transcendental_of_coe_eq_coeffEmb_jq
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_finiteType_chartAlgFin_and_chartAlgInf
import Theorems.Thm_IsCyclotomicExtension_Rat_surjective_algebraMap_int_residueField_of_isDiscreteValuationRing
import Theorems.Thm_ModularCurve_pow_q_sq_eq_self_of_mem_ssJSet
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XZeroP_isMaximal_and_finite_quotient_of_map_jChartFin_mem_ssJSet_twoChartIntegralModel_gamma0_mul
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "ModularCurve.jqNModC_one ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆"
p2m_attr_erase "simp" "Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two"

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry AlgebraicCurve.TwoChartIntegralModel

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 3200000 in
theorem solution
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hM : 5 ≤ M) (hpM : ¬ p ∣ M)
    (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {p} ℚ L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ p)
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 (M * p))))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAp : (p : A) ∈ IsLocalRing.maximalIdeal A) (hζA : ∃ z : A, algebraMap A L z = ζ)
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]
    (ϖ : A) (hϖ : IsLocalRing.maximalIdeal A = Ideal.span {ϖ})

    (y : ↥(XFin A (↥K) j))
    (hyϖ : algebraMap A ↥(chartAlgFin A (↥K) j) ϖ ∈ y.asIdeal)

    (hss : ∀ (Ω : Type) [Field Ω] [CharP Ω p] [IsAlgClosed Ω] [DecidableEq Ω]
      (φ : ↥(chartAlgFin A (↥K) j) →+* Ω),
      RingHom.ker φ = y.asIdeal → φ (jChartFin A (↥K) j) ∈ ModularCurve.ssJSet p Ω) :
    y.asIdeal.IsMaximal ∧ Finite (↥(chartAlgFin A (↥K) j) ⧸ y.asIdeal) := by
  classical
  have hp : p.Prime := Fact.out
  haveI : NeZero (M * p) := ⟨Nat.mul_ne_zero (NeZero.ne M) hp.ne_zero⟩

  have hT : ModularGroup.T ∈ CongruenceSubgroup.Gamma0 (M * p) := by
    rw [CongruenceSubgroup.Gamma0_mem]; simp [ModularGroup.T]
  haveI hFD := ModularCurve.finiteDimensional_adjoin_of_coe_eq_coeffEmb_jq_of_eq_laurentBaseChange
    (CongruenceSubgroup.Gamma0 (M * p)) hT L K hK j hj
  have htj : Transcendental A j := ModularCurve.transcendental_of_coe_eq_coeffEmb_jq L K A j hj
  have hsep : Algebra.IsSeparable ↥(IntermediateField.adjoin L ({j} : Set ↥K)) ↥K := Algebra.IsSeparable.of_integral _ _
  obtain ⟨hft, -⟩ := AlgebraicCurve.TwoChartIntegralModel.finiteType_chartAlgFin_and_chartAlgInf A L (↥K) j htj hFD hsep
  haveI := hft
  set B := chartAlgFin A (↥K) j with hBdef
  haveI hyp : y.asIdeal.IsPrime := y.isPrime

  haveI : IsDomain (↥B ⧸ y.asIdeal) := Ideal.Quotient.isDomain y.asIdeal
  have hpy : ((p : ℕ) : ↥B) ∈ y.asIdeal := by
    have hmem : ((p : ℕ) : A) ∈ Ideal.span {ϖ} := hϖ ▸ hAp
    obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp hmem
    have : ((p : ℕ) : ↥B) = algebraMap A ↥B a * algebraMap A ↥B ϖ := by
      rw [← map_natCast (algebraMap A ↥B), ← ha, map_mul]
    rw [this]
    exact y.asIdeal.mul_mem_left _ hyϖ
  have h0T : ((p : ℕ) : ↥B ⧸ y.asIdeal) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk y.asIdeal), Ideal.Quotient.eq_zero_iff_mem]
    exact hpy
  haveI : CharP (↥B ⧸ y.asIdeal) p := ringChar.of_eq (CharP.ringChar_of_prime_eq_zero hp h0T)

  let Ω := AlgebraicClosure (FractionRing (↥B ⧸ y.asIdeal))
  have hinjΩ : Function.Injective (algebraMap (↥B ⧸ y.asIdeal) Ω) := by
    rw [IsScalarTower.algebraMap_eq (↥B ⧸ y.asIdeal) (FractionRing (↥B ⧸ y.asIdeal)) Ω]
    exact (algebraMap (FractionRing (↥B ⧸ y.asIdeal)) Ω).injective.comp (IsFractionRing.injective _ _)
  haveI : CharP Ω p := charP_of_injective_algebraMap hinjΩ p
  let φ : ↥B →+* Ω := (algebraMap (↥B ⧸ y.asIdeal) Ω).comp (Ideal.Quotient.mk y.asIdeal)
  have hker : RingHom.ker φ = y.asIdeal := by
    ext b
    rw [RingHom.mem_ker, RingHom.comp_apply, ← map_zero (algebraMap (↥B ⧸ y.asIdeal) Ω), hinjΩ.eq_iff,
      Ideal.Quotient.eq_zero_iff_mem]
  have hssj := hss Ω φ hker
  have hpow := ModularCurve.pow_q_sq_eq_self_of_mem_ssJSet p hssj
  set jb : ↥B ⧸ y.asIdeal := Ideal.Quotient.mk y.asIdeal (jChartFin A (↥K) j) with hjb
  have hjb2 : jb ^ (p ^ 2) = jb := hinjΩ (by rw [map_pow]; exact hpow)
  have hjint : IsIntegral A jb := by
    refine ⟨Polynomial.X ^ (p ^ 2) - Polynomial.X, Polynomial.monic_X_pow_sub ?_, ?_⟩
    · rw [Polynomial.degree_X]
      exact_mod_cast Nat.one_lt_pow two_ne_zero hp.one_lt
    · simp [hjb2]

  let S : Subalgebra A (↥B ⧸ y.asIdeal) := Algebra.adjoin A {jb}
  haveI : Algebra.IsIntegral A ↥S := Algebra.IsIntegral.adjoin (by rintro x rfl; exact hjint)

  have hR₀ : Algebra.adjoin A ({j} : Set ↥K) ≤ B := AlgebraicCurve.TwoChartIntegralModel.adjoin_le_chartAlg A (↥K) _
  let ρ : ↥(Algebra.adjoin A ({j} : Set ↥K)) →ₐ[A] (↥B ⧸ y.asIdeal) :=
    (Ideal.Quotient.mkₐ A y.asIdeal).comp (Subalgebra.inclusion hR₀)
  have hρS : ∀ r, ρ r ∈ S := by
    intro r
    obtain ⟨Q, hQ⟩ : (r : ↥K) ∈ (Polynomial.aeval (R := A) (j : ↥K)).range := by
      rw [← Algebra.adjoin_singleton_eq_range_aeval]; exact r.2
    have hcoe : ((Polynomial.aeval (jChartFin A (↥K) j) Q : ↥B) : ↥K) = Polynomial.aeval (R := A) (j : ↥K) Q :=
      (Polynomial.aeval_algHom_apply B.val (jChartFin A (↥K) j) Q).symm
    have hr : Subalgebra.inclusion hR₀ r = Polynomial.aeval (jChartFin A (↥K) j) Q := by
      apply Subtype.ext
      show (r : ↥K) = ((Polynomial.aeval (jChartFin A (↥K) j) Q : ↥B) : ↥K)
      rw [hcoe]
      exact hQ.symm
    show (Ideal.Quotient.mkₐ A y.asIdeal) (Subalgebra.inclusion hR₀ r) ∈ S
    rw [hr, ← Polynomial.aeval_algHom_apply]
    exact Polynomial.aeval_mem_adjoin_singleton A _
  let ρ' : ↥(Algebra.adjoin A ({j} : Set ↥K)) →+* ↥S := (ρ : _ →+* (↥B ⧸ y.asIdeal)).codRestrict S hρS
  have hρ' : ∀ r, ((ρ' r : ↥S) : ↥B ⧸ y.asIdeal) = ρ r := fun r => rfl
  have hint : Algebra.IsIntegral A (↥B ⧸ y.asIdeal) := by
    refine ⟨fun z => ?_⟩
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective z

    obtain ⟨P, hPm, hPb⟩ := (AlgebraicCurve.TwoChartIntegralModel.mem_chartAlg_iff A (↥K)).mp b.2

    have hz : IsIntegral ↥S (Ideal.Quotient.mk y.asIdeal b) := by
      refine ⟨P.map ρ', hPm.map _, ?_⟩
      rw [Polynomial.eval₂_map]

      have hcomp : (algebraMap ↥S (↥B ⧸ y.asIdeal)).comp ρ' = (Ideal.Quotient.mk y.asIdeal).comp (Subalgebra.inclusion hR₀).toRingHom := by
        ext r; rfl
      rw [hcomp, ← Polynomial.hom_eval₂, ]

      have h0 : Polynomial.eval₂ (Subalgebra.inclusion hR₀).toRingHom b P = 0 := by
        apply Subtype.ext
        have h := Polynomial.hom_eval₂ P (Subalgebra.inclusion hR₀).toRingHom (B.val.toRingHom) b
        have hcomp2 : (B.val.toRingHom).comp (Subalgebra.inclusion hR₀).toRingHom =
            algebraMap ↥(Algebra.adjoin A ({j} : Set ↥K)) ↥K := by ext r; rfl
        rw [hcomp2] at h
        change (B.val.toRingHom) (Polynomial.eval₂ (Subalgebra.inclusion hR₀).toRingHom b P) = _
        rw [h]
        simpa using hPb
      rw [h0, map_zero]
    exact isIntegral_trans _ hz

  have hkerA : IsLocalRing.maximalIdeal A ≤ RingHom.ker ((Ideal.Quotient.mk y.asIdeal).comp (algebraMap A ↥B)) := by
    rw [hϖ, Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, RingHom.mem_ker, RingHom.comp_apply,
      Ideal.Quotient.eq_zero_iff_mem]
    exact hyϖ
  let ψ : IsLocalRing.ResidueField A →+* ↥B ⧸ y.asIdeal :=
    Ideal.Quotient.lift (IsLocalRing.maximalIdeal A) ((Ideal.Quotient.mk y.asIdeal).comp (algebraMap A ↥B)) (fun a ha => hkerA ha)
  letI : Algebra (IsLocalRing.ResidueField A) (↥B ⧸ y.asIdeal) := ψ.toAlgebra
  haveI : IsScalarTower A (IsLocalRing.ResidueField A) (↥B ⧸ y.asIdeal) := IsScalarTower.of_algebraMap_eq (fun a => rfl)
  haveI : Algebra.IsIntegral (IsLocalRing.ResidueField A) (↥B ⧸ y.asIdeal) := Algebra.IsIntegral.tower_top (R := A)
  have hTfield : IsField (↥B ⧸ y.asIdeal) :=
    isField_of_isIntegral_of_isField' (R := IsLocalRing.ResidueField A) (Field.toIsField _)
  have hymax : y.asIdeal.IsMaximal := Ideal.Quotient.maximal_of_isField _ hTfield
  refine ⟨hymax, ?_⟩

  have h0p : ((p : ℕ) : IsLocalRing.ResidueField A) = 0 := by
    rw [← map_natCast (IsLocalRing.residue A), IsLocalRing.residue_eq_zero_iff]; exact hAp
  haveI : CharP (IsLocalRing.ResidueField A) p := ringChar.of_eq (CharP.ringChar_of_prime_eq_zero hp h0p)
  haveI : Finite (IsLocalRing.ResidueField A) := by
    refine Finite.of_surjective (ZMod.castHom (dvd_refl p) (IsLocalRing.ResidueField A)) (fun x => ?_)
    obtain ⟨n, hn⟩ := IsCyclotomicExtension.Rat.surjective_algebraMap_int_residueField_of_isDiscreteValuationRing p L A hAp x
    exact ⟨(n : ZMod p), by rw [map_intCast, ← hn, eq_intCast]⟩
  haveI : Algebra.FiniteType A (↥B ⧸ y.asIdeal) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ A y.asIdeal) (Ideal.Quotient.mkₐ_surjective A y.asIdeal)
  haveI : Algebra.FiniteType (IsLocalRing.ResidueField A) (↥B ⧸ y.asIdeal) :=
    Algebra.FiniteType.of_restrictScalars_finiteType A _ _
  haveI : Module.Finite (IsLocalRing.ResidueField A) (↥B ⧸ y.asIdeal) := Algebra.IsIntegral.finite
  exact Module.finite_of_finite (IsLocalRing.ResidueField A)

end S_ModularCurve_XZeroP_isMaximal_and_finite_quotient_of_map_jChartFin_mem_ssJSet_twoChartIntegralModel_gamma0_mul
end P2MW
export P2MW.S_ModularCurve_XZeroP_isMaximal_and_finite_quotient_of_map_jChartFin_mem_ssJSet_twoChartIntegralModel_gamma0_mul (solution)
