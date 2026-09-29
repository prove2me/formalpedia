-- Prove2me | solution 1 for ModularCurve.FullLevel.AuxLevelOne.isMaximal_asIdeal_and_algebraMap_mem_of_mem_ssJSet_of_ringHom_of_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.339302+00:00
-- url     : https://prove2.me/submissions/e79e7900-01e9-57b9-bcfd-0eccc6c5de1f

import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_DrinfeldCurve_LocalChart
import Definitions.Def_ModularCurve_FullLevelLevelAutAt
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_exists_stalk_iso_localization_chartAlgFin
import Theorems.Thm_ModularCurve_pow_q_sq_eq_self_of_mem_ssJSet
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_AuxLevelOne_isMaximal_asIdeal_and_algebraMap_mem_of_mem_ssJSet_of_ringHom_of_dvd
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two"

set_option autoImplicit false
open CategoryTheory AlgebraicGeometry
open scoped MatrixGroups

open AlgebraicCurve.TwoChartIntegralModel

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 3200000 in

theorem solution
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')

    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ12 : ℓ % 12 = 11) (hℓM' : ℓ ∣ M')
    (L : Type) [Field L] [CharZero L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ q)
    (hι : ∃ ι : L →+* ℂ, ι ζ = Complex.exp (2 * Real.pi * Complex.I / q))
    (H₁ : Subgroup (ZMod (q ^ 2 * M'))ˣ)
    (hH₁ : H₁ = ModularCurve.FullLevel.levelH q M' ⊓ (ZMod.unitsMap (Dvd.dvd.mul_left hℓM' (q ^ 2))).ker)
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L (ModularCurve.xHFunctionField (q ^ 2 * M') H₁))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAq : (q : A) ∈ IsLocalRing.maximalIdeal A) (hζA : ∃ x : A, algebraMap A L x = ζ)
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]
    (ϖ : A) (hϖ : IsLocalRing.maximalIdeal A = Ideal.span {ϖ})
    (z : ↥(AlgebraicCurve.TwoChartIntegralModel A (↥K) j))
    (ϖz : (AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)
    (hϖz : ϖz = ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.germ ⊤ z trivial).hom
      (((AlgebraicCurve.TwoChartIntegralModel.toBase A (↥K) j).appTop).hom
        ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom ϖ)))
    (hz : ϖz ∈ IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z))
    (y : ↥(AlgebraicCurve.TwoChartIntegralModel.XFin A (↥K) j))
    (hy : (AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j).base y = z)
    (hss : ∀ (Ω : Type) [Field Ω] [CharP Ω q] [IsAlgClosed Ω] [DecidableEq Ω]
      (φ : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) →+* Ω),
      RingHom.ker φ = y.asIdeal →
        φ (AlgebraicCurve.TwoChartIntegralModel.jChartFin A (↥K) j) ∈ ModularCurve.ssJSet q Ω) :
    y.asIdeal.IsMaximal ∧
      algebraMap A ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) ϖ ∈ y.asIdeal := by
  classical
  have hp : q.Prime := Fact.out
  subst hy

  obtain ⟨e, he1, -⟩ :=
    AlgebraicCurve.TwoChartIntegralModel.exists_stalk_iso_localization_chartAlgFin A (↥K) j y ⟨y, trivial, rfl⟩
  have hyϖ : algebraMap A ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) ϖ ∈ y.asIdeal := by
    have h1 : e.hom.hom ϖz = algebraMap A (Localization.AtPrime y.asIdeal) ϖ := by rw [hϖz]; exact he1 ϖ
    have hzu : ¬ IsUnit ϖz := (IsLocalRing.mem_maximalIdeal _).mp hz
    have hnu : ¬ IsUnit (algebraMap A (Localization.AtPrime y.asIdeal) ϖ) := by
      intro hu
      apply hzu
      rw [← h1] at hu
      have h2 : e.inv.hom (e.hom.hom ϖz) = ϖz := by
        rw [← RingHom.comp_apply, ← CommRingCat.hom_comp, e.hom_inv_id, CommRingCat.hom_id, RingHom.id_apply]
      rw [← h2]
      exact hu.map e.inv.hom
    have hmem : algebraMap A (Localization.AtPrime y.asIdeal) ϖ ∈
        IsLocalRing.maximalIdeal (Localization.AtPrime y.asIdeal) :=
      (IsLocalRing.mem_maximalIdeal _).mpr hnu
    rw [IsScalarTower.algebraMap_apply A ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)
      (Localization.AtPrime y.asIdeal)] at hmem
    exact (IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime y.asIdeal) y.asIdeal _).mp hmem
  refine ⟨?_, hyϖ⟩

  set B := chartAlgFin A (↥K) j with hBdef
  haveI hyp : y.asIdeal.IsPrime := y.isPrime

  haveI : IsDomain (↥B ⧸ y.asIdeal) := Ideal.Quotient.isDomain y.asIdeal
  have hpy : ((q : ℕ) : ↥B) ∈ y.asIdeal := by
    have hmem : ((q : ℕ) : A) ∈ Ideal.span {ϖ} := hϖ ▸ hAq
    obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp hmem
    have : ((q : ℕ) : ↥B) = algebraMap A ↥B a * algebraMap A ↥B ϖ := by
      rw [← map_natCast (algebraMap A ↥B), ← ha, map_mul]
    rw [this]
    exact y.asIdeal.mul_mem_left _ hyϖ
  have h0T : ((q : ℕ) : ↥B ⧸ y.asIdeal) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk y.asIdeal), Ideal.Quotient.eq_zero_iff_mem]
    exact hpy
  haveI : CharP (↥B ⧸ y.asIdeal) q := ringChar.of_eq (CharP.ringChar_of_prime_eq_zero hp h0T)

  let Ω := AlgebraicClosure (FractionRing (↥B ⧸ y.asIdeal))
  have hinjΩ : Function.Injective (algebraMap (↥B ⧸ y.asIdeal) Ω) := by
    rw [IsScalarTower.algebraMap_eq (↥B ⧸ y.asIdeal) (FractionRing (↥B ⧸ y.asIdeal)) Ω]
    exact (algebraMap (FractionRing (↥B ⧸ y.asIdeal)) Ω).injective.comp (IsFractionRing.injective _ _)
  haveI : CharP Ω q := charP_of_injective_algebraMap hinjΩ q
  let φ : ↥B →+* Ω := (algebraMap (↥B ⧸ y.asIdeal) Ω).comp (Ideal.Quotient.mk y.asIdeal)
  have hker : RingHom.ker φ = y.asIdeal := by
    ext b
    rw [RingHom.mem_ker, RingHom.comp_apply, ← map_zero (algebraMap (↥B ⧸ y.asIdeal) Ω), hinjΩ.eq_iff,
      Ideal.Quotient.eq_zero_iff_mem]
  have hssj := hss Ω φ hker
  have hpow := ModularCurve.pow_q_sq_eq_self_of_mem_ssJSet q hssj
  set jb : ↥B ⧸ y.asIdeal := Ideal.Quotient.mk y.asIdeal (jChartFin A (↥K) j) with hjb
  have hjb2 : jb ^ (q ^ 2) = jb := hinjΩ (by rw [map_pow]; exact hpow)
  have hjint : IsIntegral A jb := by
    refine ⟨Polynomial.X ^ (q ^ 2) - Polynomial.X, Polynomial.monic_X_pow_sub ?_, ?_⟩
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
  exact hymax

end S_ModularCurve_FullLevel_AuxLevelOne_isMaximal_asIdeal_and_algebraMap_mem_of_mem_ssJSet_of_ringHom_of_dvd
end P2MW
export P2MW.S_ModularCurve_FullLevel_AuxLevelOne_isMaximal_asIdeal_and_algebraMap_mem_of_mem_ssJSet_of_ringHom_of_dvd (solution)
