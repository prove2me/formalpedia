-- Prove2me | solution 1 for HuangN13.N13MarkedQuadraticExistence.exists_saturated_data_of_irreducible
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-10-30T15:05:44.397342+00:00
-- url     : https://prove2.me/submissions/af5944c4-9d35-4fa3-84a3-5d22c08cdb20

import Mathlib
import Definitions.Def_MazurN13_L4
import Definitions.Def_HuangN13_InfinityMultiplicityCore
import Definitions.Def_HuangN13_IntegralTensorDataCore
import Definitions.Def_HuangN13_PrimitiveAffineComparisonCore
import Theorems.Thm_HuangN13_N13MarkedQuadraticExistence_exists_reciprocal_saturated_data
import Theorems.Thm_HuangN13_N13MarkedQuadraticExistence_exists_saturated_data_of_finite
import Theorems.Thm_MazurProof_N13GeneralizedMumfordIntegral_recompose

set_option autoImplicit false

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13QuotientFiniteness
noncomputable section
universe u v
variable {R : Type u} {A : Type v}
variable [CommRing R] [CommRing A] [Algebra R A]
/--
A rank-two polynomial normal form together with one monic relation in the
first coordinate makes every ideal quotient finite over the base ring.
-/
theorem quotient_finite_of_monic_relation_of_rankTwoNormalForm
    (x y : A)
    (normalForm :
      ∀ a : A,
        ∃ P Q : R[X],
          a = aeval x P + aeval x Q * y)
    (I : Ideal A)
    {m : R[X]}
    (hm : m.Monic)
    (hmI : aeval x m ∈ I) :
    Module.Finite R (A ⧸ I) := by
  let xq : A ⧸ I := Ideal.Quotient.mk I x
  let yq : A ⧸ I := Ideal.Quotient.mk I y
  have aeval_mk (p : R[X]) :
      aeval xq p =
        Ideal.Quotient.mk I (aeval x p) := by
    simp only [aeval_def, xq]
    exact
      (Polynomial.hom_eval₂ p
        (algebraMap R A) (Ideal.Quotient.mk I) x).symm
  have hmRoot : aeval xq m = 0 := by
    calc
      aeval xq m =
          Ideal.Quotient.mk I (aeval x m) := aeval_mk m
      _ = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hmI
  let φ : AdjoinRoot m →ₐ[R] A ⧸ I :=
    AdjoinRoot.liftAlgHom m (Algebra.ofId R (A ⧸ I)) xq hmRoot
  let L : (AdjoinRoot m × AdjoinRoot m) →ₗ[R] A ⧸ I := {
    toFun z := φ z.1 + φ z.2 * yq
    map_add' p q := by
      change
        φ (p.1 + q.1) + φ (p.2 + q.2) * yq =
          (φ p.1 + φ p.2 * yq) + (φ q.1 + φ q.2 * yq)
      rw [map_add, map_add]
      ring
    map_smul' r p := by
      rw [Prod.smul_fst, Prod.smul_snd, RingHom.id_apply,
        map_smul, map_smul, smul_add, Algebra.smul_mul_assoc]
  }
  letI : Module.Finite R (AdjoinRoot m) :=
    hm.finite_adjoinRoot
  refine Module.Finite.of_surjective L ?_
  intro z
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective z
  obtain ⟨P, Q, hPQ⟩ := normalForm a
  refine ⟨(AdjoinRoot.mk m P, AdjoinRoot.mk m Q), ?_⟩
  change
    φ (AdjoinRoot.mk m P) +
        φ (AdjoinRoot.mk m Q) * yq =
      Ideal.Quotient.mk I a
  have hφ (p : R[X]) : φ (AdjoinRoot.mk m p) = aeval xq p :=
    AdjoinRoot.liftAlgHom_mk m (Algebra.ofId R (A ⧸ I)) xq hmRoot p
  rw [hφ P, hφ Q]
  rw [aeval_mk P, aeval_mk Q]
  dsimp only [yq]
  rw [← map_mul, ← map_add, hPQ]
end
end MazurProof.N13QuotientFiniteness
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13IrreducibleQuadraticChart
noncomputable section
attribute [local instance] MazurProof.N13IrreducibleQuadraticChart.instFactPrimeOfNatNat_fLT
/-- If the constant term is strictly smaller than the square of a
nonintegral linear coefficient, Hensel's lemma produces a root near the
linear term.  Hence the quadratic is reducible. -/
theorem quadratic_reducible_of_norm_const_lt_sq_linear
    (a b : Q₂)
    (ha : 1 < ‖a‖)
    (hb : ‖b‖ < ‖a‖ ^ 2) :
    ¬ Irreducible
        (X ^ 2 + C a * X + C b : Q₂[X]) := by
  intro hirr
  have ha0 : a ≠ 0 := by
    intro h
    rw [h, norm_zero] at ha
    norm_num at ha
  let cQ : Q₂ := b / a ^ 2
  have hcQnorm : ‖cQ‖ < 1 := by
    rw [show ‖cQ‖ = ‖b‖ / ‖a‖ ^ 2 by
      simp [cQ, norm_div, norm_pow]]
    exact (div_lt_one (by positivity)).2 hb
  let c : Z₂ := ⟨cQ, le_of_lt hcQnorm⟩
  let F : Z₂[X] := X ^ 2 + X + C c
  have hFroot (z : Z₂) : F.aeval z = z ^ 2 + z + c := by
    simp [F, Polynomial.aeval_def, Polynomial.eval₂_C]
  have hFminus : F.aeval (-1 : Z₂) = c := by
    simpa using hFroot (-1)
  have hFderiv : F.derivative.aeval (-1 : Z₂) = -1 := by
    norm_num [F, Polynomial.aeval_def, Polynomial.eval₂_C]
  have hHensel :
      ‖F.aeval (-1 : Z₂)‖ <
        ‖F.derivative.aeval (-1 : Z₂)‖ ^ 2 := by
    rw [hFminus, hFderiv]
    simpa [c] using hcQnorm
  obtain ⟨z, hz, _⟩ := hensels_lemma hHensel
  have hzQ :
      (z : Q₂) ^ 2 + (z : Q₂) + cQ = 0 := by
    have hz₀ : F.aeval z = 0 := hz
    rw [hFroot] at hz₀
    have hz' := congrArg (fun w : Z₂ ↦ (w : Q₂)) hz₀
    push_cast at hz'
    simpa [c] using hz'
  let r : Q₂ := a * z
  have hr :
      (X ^ 2 + C a * X + C b : Q₂[X]).IsRoot r := by
    rw [IsRoot]
    simp only [eval_add, eval_pow, eval_X, eval_mul, eval_C]
    calc
      r ^ 2 + a * r + b =
          a ^ 2 * ((z : Q₂) ^ 2 + (z : Q₂) + cQ) := by
            dsimp [r, cQ]
            field_simp
      _ = 0 := by rw [hzQ, mul_zero]
  have hdegree :=
    Polynomial.degree_eq_one_of_irreducible_of_root hirr hr
  have hdegreeTwo :
      (X ^ 2 + C a * X + C b : Q₂[X]).degree = 2 := by
    compute_degree <;> norm_num
  rw [hdegreeTwo] at hdegree
  norm_num at hdegree
end
end MazurProof.N13IrreducibleQuadraticChart
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13IrreducibleQuadraticChart
noncomputable section
attribute [local instance] MazurProof.N13IrreducibleQuadraticChart.instFactPrimeOfNatNat_fLT
/-- Root-free Newton dichotomy for an irreducible monic quadratic:
either its ordinary coefficients are integral, or the coefficients after
passing to the reciprocal monic polynomial are integral. -/
theorem irreducible_quadratic_norm_chart
    (a b : Q₂)
    (hirr :
      Irreducible
        (X ^ 2 + C a * X + C b : Q₂[X])) :
    (‖a‖ ≤ 1 ∧ ‖b‖ ≤ 1) ∨
      (‖a / b‖ ≤ 1 ∧ ‖b⁻¹‖ ≤ 1) := by
  by_cases ha : ‖a‖ ≤ 1
  · by_cases hb : ‖b‖ ≤ 1
    · exact Or.inl ⟨ha, hb⟩
    · right
      have hb1 : 1 < ‖b‖ := lt_of_not_ge hb
      constructor
      · rw [norm_div, div_le_one (by positivity)]
        exact ha.trans hb1.le
      · rw [norm_inv, inv_le_one₀ (by positivity)]
        exact hb1.le
  · right
    have ha1 : 1 < ‖a‖ := lt_of_not_ge ha
    have hab : ‖a‖ ^ 2 ≤ ‖b‖ := by
      by_contra h
      exact
        (quadratic_reducible_of_norm_const_lt_sq_linear
          a b ha1 (lt_of_not_ge h)) hirr
    have hbpos : 0 < ‖b‖ := by
      exact lt_of_lt_of_le (by positivity : 0 < ‖a‖ ^ 2) hab
    constructor
    · rw [norm_div, div_le_one hbpos]
      exact (le_self_pow₀ ha1.le (by norm_num : 2 ≠ 0)).trans hab
    · rw [norm_inv, inv_le_one₀ hbpos]
      exact ha1.le.trans
        ((le_self_pow₀ ha1.le (by norm_num : 2 ≠ 0)).trans hab)
end
end MazurProof.N13IrreducibleQuadraticChart
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13IrreducibleQuadraticChart
noncomputable section
attribute [local instance] MazurProof.N13IrreducibleQuadraticChart.instFactPrimeOfNatNat_fLT
/-- Coefficient form of a monic quadratic. -/
theorem monic_quadratic_eq
    (p : Q₂[X])
    (hp : p.Monic)
    (hdeg : p.natDegree = 2) :
    p = X ^ 2 + C (p.coeff 1) * X + C (p.coeff 0) := by
  have hc₂ : p.coeff 2 = 1 := by
    calc
      p.coeff 2 = p.coeff p.natDegree :=
        congrArg p.coeff hdeg.symm
      _ = 1 := hp.coeff_natDegree
  have hpDegreeLe : p.degree ≤ 2 := by
    rw [degree_eq_natDegree hp.ne_zero, hdeg]
    norm_num
  calc
    p =
        C (p.coeff 2) * X ^ 2 +
          C (p.coeff 1) * X +
          C (p.coeff 0) :=
      p.eq_quadratic_of_degree_le_two hpDegreeLe
    _ = X ^ 2 + C (p.coeff 1) * X + C (p.coeff 0) := by
      rw [hc₂, C_1]
      ring
end
end MazurProof.N13IrreducibleQuadraticChart
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13IrreducibleQuadraticChart
noncomputable section
attribute [local instance] MazurProof.N13IrreducibleQuadraticChart.instFactPrimeOfNatNat_fLT
/-- An irreducible monic quadratic has a literal integral horizontal
equation on one of the two ordinary charts.  In the second alternative
the displayed polynomial is the monic reciprocal equation for `t = x⁻¹`. -/
theorem irreducible_monic_quadratic_has_integral_chart
    (p : Q₂[X])
    (hp : p.Monic)
    (hdeg : p.natDegree = 2)
    (hirr : Irreducible p) :
    (∃ a b : Z₂,
        p =
          X ^ 2 + C (a : Q₂) * X + C (b : Q₂)) ∨
      (p.coeff 0 ≠ 0 ∧
        ∃ a b : Z₂,
          (X ^ 2 + C (a : Q₂) * X + C (b : Q₂) : Q₂[X]) =
            X ^ 2 +
              C (p.coeff 1 / p.coeff 0) * X +
              C ((p.coeff 0)⁻¹)) := by
  have hshape := monic_quadratic_eq p hp hdeg
  have hirrShape :
      Irreducible
        (X ^ 2 +
          C (p.coeff 1) * X +
          C (p.coeff 0) : Q₂[X]) := by
    rw [← hshape]
    exact hirr
  have hconst : p.coeff 0 ≠ 0 := by
    intro hzero
    have hroot : p.IsRoot 0 := by
      rw [hshape, hzero]
      simp [IsRoot]
    have hdegree :=
      Polynomial.degree_eq_one_of_irreducible_of_root hirr hroot
    have hpdegree : p.degree = 2 := by
      rw [degree_eq_natDegree hp.ne_zero, hdeg]
      norm_num
    rw [hpdegree] at hdegree
    norm_num at hdegree
  rcases
      irreducible_quadratic_norm_chart
        (p.coeff 1) (p.coeff 0) hirrShape with
    hAffine | hInfinity
  · left
    let a : Z₂ := ⟨p.coeff 1, hAffine.1⟩
    let b : Z₂ := ⟨p.coeff 0, hAffine.2⟩
    exact ⟨a, b, by simpa [a, b] using hshape⟩
  · right
    refine ⟨hconst, ?_⟩
    let a : Z₂ :=
      ⟨p.coeff 1 / p.coeff 0, hInfinity.1⟩
    let b : Z₂ :=
      ⟨(p.coeff 0)⁻¹, hInfinity.2⟩
    exact ⟨a, b, by simp [a, b]⟩
end
end MazurProof.N13IrreducibleQuadraticChart
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13InfinityNormCarrier
noncomputable section
universe u
variable {R : Type u} [CommRing R]
/-- Polynomial evaluation at the affine coordinate agrees with `xClass`. -/
theorem aeval_xCoordinate
    (p : R[X]) :
    aeval
        (N13GeneralizedMumfordIntegral.xClass (X : R[X])) p =
      N13GeneralizedMumfordIntegral.xClass p := by
  let ψ : R[X] →ₐ[R] CoordinateRing (R := R) :=
    IsScalarTower.toAlgHom R R[X] (CoordinateRing (R := R))
  have h :
      aeval
          (N13GeneralizedMumfordIntegral.xClass (X : R[X])) =
        ψ := by
    apply Polynomial.algHom_ext
    rw [Polynomial.aeval_X]
    rfl
  calc
    aeval
        (N13GeneralizedMumfordIntegral.xClass (X : R[X])) p =
        ψ p := DFunLike.congr_fun h p
    _ = N13GeneralizedMumfordIntegral.xClass p := rfl
end
end MazurProof.N13InfinityNormCarrier
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13InfinityNormCarrier
noncomputable section
universe u
variable {R : Type u} [CommRing R]
/-- The actual N13 affine coordinate ring has the generic rank-two
polynomial normal form used by the finiteness theorem. -/
theorem rankTwoPolynomialNormalForm
    [Nontrivial R] :
    ∀ z : CoordinateRing (R := R),
      ∃ P Q : R[X],
        z =
          aeval
              (N13GeneralizedMumfordIntegral.xClass (X : R[X])) P +
            aeval
                (N13GeneralizedMumfordIntegral.xClass (X : R[X])) Q *
              N13GeneralizedMumfordIntegral.yClass := by
  intro z
  refine ⟨
    N13GeneralizedMumfordIntegral.coeff0 z,
    N13GeneralizedMumfordIntegral.coeffY z,
    ?_⟩
  rw [aeval_xCoordinate, aeval_xCoordinate]
  exact (N13GeneralizedMumfordIntegral.recompose z).symm
end
end MazurProof.N13InfinityNormCarrier
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13InfinityNormCarrier
noncomputable section
universe u
variable {R : Type u} [CommRing R]
/-- One monic `xClass` relation in an ideal makes the actual N13 affine
quotient finite over the base ring. -/
theorem quotient_finite_of_monic_xClass_mem
    [Nontrivial R]
    (I : Ideal (CoordinateRing (R := R)))
    {m : R[X]}
    (hm : m.Monic)
    (hmI : N13GeneralizedMumfordIntegral.xClass m ∈ I) :
    Module.Finite R (CoordinateRing (R := R) ⧸ I) := by
  apply
    MazurProof.N13QuotientFiniteness.quotient_finite_of_monic_relation_of_rankTwoNormalForm
        (N13GeneralizedMumfordIntegral.xClass (X : R[X]))
        N13GeneralizedMumfordIntegral.yClass
        rankTwoPolynomialNormalForm I hm
  rwa [aeval_xCoordinate]
end
end MazurProof.N13InfinityNormCarrier
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13IrreducibleQuadraticFinite
noncomputable section
attribute [local instance] MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
/-- An integral horizontal equation whose coefficient extension is the
generic Mumford equation belongs to the canonical contraction. -/
theorem xClass_mem_contract_of_mapPoly_eq_u
    (D : SexticMumford.SemiMumford Model)
    (m : R₂[X])
    (hm :
      N13TwoAdicCoordinateBaseChange.mapPoly m = D.u) :
    N13GeneralizedMumfordIntegral.xClass m ∈
      N13IntegralModelContraction.contractIdeal
        (N13CanonicalContractionQuotient.graphIdeal D) := by
  change
    N13TwoAdicCoordinateBaseChange.integralToSextic
        (N13GeneralizedMumfordIntegral.xClass m) ∈
      N13CanonicalContractionQuotient.graphIdeal D
  rw [N13TwoAdicCoordinateBaseChange.integralToSextic,
    RingHom.comp_apply,
    N13TwoAdicCoordinateBaseChange.extend_xClass,
    N13GoodSexticCoordinateEquiv.toSextic_xClass,
    hm]
  exact
    SexticMumford.xClass_mem_mumfordIdeal
      Model D.u D.v
end
end MazurProof.N13IrreducibleQuadraticFinite
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13IrreducibleQuadraticFinite
noncomputable section
attribute [local instance] MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
/-- A monic integral horizontal equation makes the canonical contracted
quotient finite over `ℤ₂`. -/
theorem contractQuotient_finite_of_integral_u
    (D : SexticMumford.SemiMumford Model)
    (m : R₂[X])
    (hmMonic : m.Monic)
    (hm :
      N13TwoAdicCoordinateBaseChange.mapPoly m = D.u) :
    Module.Finite R₂
      (IntegralRing ⧸
        N13IntegralModelContraction.contractIdeal
          (N13CanonicalContractionQuotient.graphIdeal D)) := by
  apply
    N13InfinityNormCarrier.quotient_finite_of_monic_xClass_mem
  · exact hmMonic
  · exact xClass_mem_contract_of_mapPoly_eq_u D m hm
end
end MazurProof.N13IrreducibleQuadraticFinite
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13IrreducibleQuadraticFinite
noncomputable section
attribute [local instance] MazurProof.N13IrreducibleQuadraticChart.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
/-- For an irreducible quadratic graph, either the canonical affine
quotient is finite or the reciprocal monic equation is literally integral
on the infinity chart. -/
theorem contractQuotient_finite_or_integral_reciprocal
    (D : SexticMumford.Mumford Model)
    (hdeg : D.u.natDegree = 2)
    (hirr : Irreducible D.u) :
    Module.Finite R₂
        (IntegralRing ⧸
          N13IntegralModelContraction.contractIdeal
            (N13CanonicalContractionQuotient.graphIdeal D.toSemi)) ∨
      (D.u.coeff 0 ≠ 0 ∧
        ∃ a b : R₂,
          (X ^ 2 + C (a : Q₂) * X + C (b : Q₂) : Q₂[X]) =
            X ^ 2 +
              C (D.u.coeff 1 / D.u.coeff 0) * X +
              C ((D.u.coeff 0)⁻¹)) := by
  rcases
      N13IrreducibleQuadraticChart.irreducible_monic_quadratic_has_integral_chart
        D.u D.u_monic hdeg hirr with hAffine | hInfinity
  · left
    obtain ⟨a, b, hu⟩ := hAffine
    let m : R₂[X] := X ^ 2 + C a * X + C b
    apply contractQuotient_finite_of_integral_u D.toSemi m
    · dsimp [m]
      monicity <;> norm_num
    · simpa [m,
        N13TwoAdicCoordinateBaseChange.mapPoly,
        N13TwoAdicCoordinateBaseChange.coeffMap,
        N13TwoAdicMumfordTransport.mapPoly,
        N13TwoAdicMumfordTransport.coeffMap] using hu.symm
  · exact Or.inr hInfinity
end
end MazurProof.N13IrreducibleQuadraticFinite
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13MarkedQuadraticExistence
noncomputable section
open Polynomial N13InfinityChartMarking
open N13SplitQuadraticPicardRealization N13SplitQuadraticSpecialRestriction
attribute [local instance] MazurProof.N13InfinityBaseChange.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
theorem exists_saturated_data_of_irreducible
    (D : SexticMumford.Mumford Model)
    (hdeg : D.u.natDegree = 2)
    (hirr : Irreducible D.u) :
    ∃ R : N13TwoChartPicardRealization.Data,
      N13TwoChartPicardRealization.genericRaw
          R.charts R.infinityOrder =
        SexticMumford.mumfordRaw Model D ∧
      R.toGenericPic =
        SexticMumford.classOf
          Model
          (N13Infinity.positiveInfinityOrder Q₂)
          D ∧
      N13TwoChartPicardRealization.AffineVerticallySaturated R.charts ∧
      HasInfinityMultiplicities R.charts 0 0 := by
  rcases
      N13IrreducibleQuadraticFinite.contractQuotient_finite_or_integral_reciprocal
          D hdeg hirr with
    hfinite | ⟨h0, a, b, hm⟩
  · exact HuangN13.N13MarkedQuadraticExistence.exists_saturated_data_of_finite D hdeg hfinite
  · exact
      HuangN13.N13MarkedQuadraticExistence.exists_reciprocal_saturated_data
        D hdeg h0 a b hm
end
end MazurProof.N13MarkedQuadraticExistence
end
end


set_option autoImplicit false
open Polynomial
attribute [local instance] MazurProof.N13InfinityBaseChange.instFactPrimeOfNatNat_fLT
theorem solution
    (D : MazurProof.SexticMumford.Mumford MazurProof.N13MarkedQuadraticExistence.Model)
    (hdeg : D.u.natDegree = 2)
    (hirr : Irreducible D.u) :
    ∃ R : MazurProof.N13TwoChartPicardRealization.Data,
      MazurProof.N13TwoChartPicardRealization.genericRaw
          R.charts R.infinityOrder =
        MazurProof.SexticMumford.mumfordRaw MazurProof.N13MarkedQuadraticExistence.Model D ∧
      R.toGenericPic =
        MazurProof.SexticMumford.classOf
          MazurProof.N13MarkedQuadraticExistence.Model
          (MazurProof.N13Infinity.positiveInfinityOrder MazurProof.N13MarkedQuadraticExistence.Q₂)
          D ∧
      MazurProof.N13TwoChartPicardRealization.AffineVerticallySaturated R.charts ∧
      MazurProof.N13InfinityChartMarking.HasInfinityMultiplicities R.charts 0 0 := by
  exact MazurProof.N13MarkedQuadraticExistence.exists_saturated_data_of_irreducible D hdeg hirr
