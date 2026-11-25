-- Prove2me | solution 1 for HodgeComputer.FourPlusTwoResidual.exists_hermite_pade_flat_moment_section_e3
-- status  : ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-25T12:49:13.033589+00:00
-- url     : https://prove2.me/submissions/32ada366-5d00-49b1-9aa3-9ffe66d74443

import Definitions.Def_HodgeComputerFourPlusTwoRationalCurrent
import Mathlib.Algebra.CharP.Algebra
import Mathlib.Algebra.Exact.Basic
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.RingTheory.Derivation.Basic
import Mathlib.RingTheory.Etale.Basic
import Mathlib.RingTheory.Kaehler.Basic
import Mathlib.RingTheory.Kaehler.JacobiZariski
import Mathlib.RingTheory.Kaehler.Polynomial
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Smooth.Basic
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.RingTheory.Unramified.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySimpa false
noncomputable section

open HodgeComputer.FourPlusTwoResidual
open MvPolynomial KaehlerDifferential
open scoped BigOperators TensorProduct

/-!
Algebraic model: work in any field of fractions of $\mathbb{C}[s,t]$, lift coordinate
partials via $\Omega_{K/\mathbb{C}}\simeq K\otimes\Omega_{\mathbb{C}[s,t]/\mathbb{C}}$, and take
chart current $q_t=-t^5/5$ with constant moments $(0,0,1)$.
-/

abbrev Rst : Type := MvPolynomial (Fin 2) ℂ

namespace FlatMomentSectionE3

variable (K : Type*) [Field K] [CharZero K]
variable [Algebra Rst K] [IsFractionRing Rst K]
variable [Algebra ℂ K] [IsScalarTower ℂ Rst K]

private abbrev ι : Rst →+* K := algebraMap Rst K

private lemma ι_injective : Function.Injective (ι K : Rst → K) :=
  IsFractionRing.injective Rst K

/-- `mapBaseChange` is bijective for a fraction field of a polynomial algebra. -/
private lemma mapBaseChange_bijective :
    Function.Bijective (mapBaseChange ℂ Rst K) := by
  refine ⟨?inj, ?surj⟩
  case inj =>
    have : Algebra.FormallyEtale Rst K :=
      Algebra.FormallyEtale.of_isLocalization (nonZeroDivisors Rst)
    have : Algebra.FormallySmooth Rst K := inferInstance
    have hexact := Algebra.H1Cotangent.exact_δ_mapBaseChange ℂ Rst K
    intro x y hxy
    have hx : mapBaseChange ℂ Rst K (x - y) = 0 := by
      simpa [map_sub, sub_eq_zero] using hxy
    have : x - y ∈ Set.range (Algebra.H1Cotangent.δ ℂ Rst K) :=
      (hexact (x - y)).1 hx
    obtain ⟨z, hz⟩ := this
    have hz0 : Algebra.H1Cotangent.δ ℂ Rst K z = 0 := by
      have : Subsingleton (Algebra.H1Cotangent Rst K) :=
        Algebra.FormallySmooth.subsingleton_h1Cotangent
      simp [Subsingleton.elim z 0]
    exact sub_eq_zero.mp (by simpa [hz0] using hz.symm)
  case surj =>
    have : Algebra.FormallyUnramified Rst K :=
      Algebra.FormallyUnramified.of_isLocalization (nonZeroDivisors Rst)
    have hrange : LinearMap.range (mapBaseChange ℂ Rst K) = ⊤ := by
      rw [range_mapBaseChange]
      exact top_unique fun x _ =>
        (LinearMap.mem_ker).2 (Subsingleton.elim _ _)
    intro y
    have : y ∈ LinearMap.range (mapBaseChange ℂ Rst K) := by simp [hrange]
    exact this

/-- Equivalence `K ⊗[R] Ω[R/ℂ] ≃ Ω[K/ℂ]`. -/
private def omegaFracEquiv : K ⊗[Rst] Ω[Rst⁄ℂ] ≃ₗ[K] Ω[K⁄ℂ] :=
  LinearEquiv.ofBijective (mapBaseChange ℂ Rst K) (mapBaseChange_bijective K)

private lemma omegaFracEquiv_tmul_D (p : Rst) :
    omegaFracEquiv K (1 ⊗ₜ D ℂ Rst p) = D ℂ K (ι K p) := by
  change mapBaseChange ℂ Rst K (1 ⊗ₜ D ℂ Rst p) = D ℂ K (algebraMap Rst K p)
  simp [mapBaseChange_tmul, map_D]

private lemma omegaFracEquiv_symm_D_algebraMap (p : Rst) :
    (omegaFracEquiv K).symm (D ℂ K (ι K p)) = 1 ⊗ₜ D ℂ Rst p := by
  apply (omegaFracEquiv K).symm_apply_eq.2
  exact (omegaFracEquiv_tmul_D K p).symm

/-- Lift of `pderiv i` to a `ℂ`-derivation on a fraction field of `Rst`. -/
private def liftPDerivℂ (i : Fin 2) : Derivation ℂ K K :=
  let dR : Derivation ℂ Rst K := (Algebra.linearMap Rst K).compDer (pderiv i)
  let φ : Ω[Rst⁄ℂ] →ₗ[Rst] K := dR.liftKaehlerDifferential
  let φK : K ⊗[Rst] Ω[Rst⁄ℂ] →ₗ[K] K := φ.liftBaseChange K
  let ψ : Ω[K⁄ℂ] →ₗ[K] K := φK ∘ₗ (omegaFracEquiv K).symm.toLinearMap
  linearMapEquivDerivation ℂ K ψ

/-- Integer-scalar restriction of the lifted partial. -/
private def liftPDeriv (i : Fin 2) : Derivation ℤ K K :=
  (liftPDerivℂ K i).restrictScalars ℤ

private lemma liftPDeriv_algebraMap (i : Fin 2) (p : Rst) :
    liftPDeriv K i (ι K p) = ι K (pderiv i p) := by
  change liftPDerivℂ K i (ι K p) = ι K (pderiv i p)
  have hψ :
      liftPDerivℂ K i (ι K p) =
        ((Algebra.linearMap Rst K).compDer (pderiv i)).liftKaehlerDifferential
          (D ℂ Rst p) := by
    unfold liftPDerivℂ
    simp only [linearMapEquivDerivation_apply_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
      omegaFracEquiv_symm_D_algebraMap, LinearMap.liftBaseChange_one_tmul]
  rw [hψ, Derivation.liftKaehlerDifferential_comp_D]
  rfl

private lemma liftPDeriv_X (i j : Fin 2) :
    liftPDeriv K i (ι K (X j)) = if j = i then (1 : K) else 0 := by
  rw [liftPDeriv_algebraMap]
  classical
  simp [pderiv_X, Pi.single_apply, apply_ite (ι K : Rst → K), map_one, map_zero]

/-- The required existential package, specialized to a fixed fraction field. -/
private theorem exists_in_fraction_field :
    ∃ (Dr Ds Dt : Derivation ℤ K K) (a s t P : K)
      (n : ℕ) (c : Fin n → K) (T0 T2 T4 : Fin n → K)
      (qr qs qt : K),
      n ≠ 0 ∧
        a ≠ 0 ∧ t ≠ 0 ∧
        Dr a = 0 ∧ Ds a = 0 ∧ Dt a = 0 ∧
        Dr t = 0 ∧ Ds t = 0 ∧ Dt t = 1 ∧
        Ds s = 1 ∧
        (∑ j : Fin n, c j * T0 j = 0) ∧
        (∑ j : Fin n, c j * T2 j = 0) ∧
        (∑ j : Fin n, c j * T4 j = 1) ∧
        (-(P * (Dr qr + Ds qs + Dt qt) -
            (2 / 3 : K) * (qr * Dr P + qs * Ds P + qt * Dt P)) =
          (∑ j : Fin n, c j * T0 j) +
            (∑ j : Fin n, c j * T2 j) * t ^ 2 +
              (∑ j : Fin n, c j * T4 j) * t ^ 4) := by
  refine ⟨0, liftPDeriv K 0, liftPDeriv K 1,
    1, ι K (X 0), ι K (X 1), 1, 1, fun _ => (1 : K),
    fun _ => 0, fun _ => 0, fun _ => 1,
    0, 0, -(ι K (X 1)) ^ 5 / 5, ?_⟩
  have hs : liftPDeriv K 0 (ι K (X 0)) = 1 := by simp [liftPDeriv_X]
  have ht0 : liftPDeriv K 0 (ι K (X 1)) = 0 := by simp [liftPDeriv_X]
  have ht1 : liftPDeriv K 1 (ι K (X 1)) = 1 := by simp [liftPDeriv_X]
  have hX1_ne : (X 1 : Rst) ≠ 0 := by
    intro h
    simpa using congrArg (coeff (Finsupp.single (1 : Fin 2) 1)) h
  have ht_ne : ι K (X 1) ≠ 0 := fun h =>
    hX1_ne ((ι_injective K) (by simpa using h))
  have hDt_pow : liftPDeriv K 1 ((ι K (X 1)) ^ 5) = 5 * (ι K (X 1)) ^ 4 := by
    have h := (liftPDeriv K 1).leibniz_pow (ι K (X 1)) 5
    simpa [ht1, nsmul_eq_mul, smul_eq_mul, Nat.cast_ofNat] using h
  have h5 : (5 : K) ≠ 0 := by
    exact_mod_cast (Nat.succ_ne_zero 4 : (5 : ℕ) ≠ 0)
  have hDt_qt : liftPDeriv K 1 (-(ι K (X 1)) ^ 5 / 5) = -(ι K (X 1)) ^ 4 := by
    have hconst : liftPDeriv K 1 (5 : K) = 0 := (liftPDeriv K 1).map_natCast 5
    have hinv : liftPDeriv K 1 ((5 : K)⁻¹) = 0 := by
      simpa [hconst] using (liftPDeriv K 1).leibniz_inv (5 : K)
    -- Rewrite `-t^5 / 5` as `(-(1/5)) * t^5` and apply Leibniz.
    have hx : -(ι K (X 1)) ^ 5 / 5 = (-(1 : K) / 5) * (ι K (X 1)) ^ 5 := by
      field_simp [h5]
    have hneg5 : liftPDeriv K 1 (-(1 : K) / 5) = 0 := by
      have h1 : liftPDeriv K 1 (1 : K) = 0 := (liftPDeriv K 1).map_one_eq_zero
      have hn : liftPDeriv K 1 (-(1 : K)) = 0 := by simp [h1]
      rw [div_eq_mul_inv, Derivation.leibniz, smul_eq_mul, hn, hinv]
      simp
    rw [hx, Derivation.leibniz, smul_eq_mul, hneg5, hDt_pow]
    ring
  refine ⟨by decide, one_ne_zero, ht_ne, by simp, (liftPDeriv K 0).map_one_eq_zero,
    (liftPDeriv K 1).map_one_eq_zero, by simp, ht0, ht1, hs, by simp, by simp, by simp, ?_⟩
  -- With P=1, qr=qs=0: LHS = -Dt qt = t^4 = RHS.
  simp [hDt_qt]

end FlatMomentSectionE3

theorem solution :
    ∃ (K : Type) (_ : Field K) (_ : CharZero K)
      (Dr Ds Dt : Derivation ℤ K K) (a s t P : K)
      (n : ℕ) (c : Fin n → K) (T0 T2 T4 : Fin n → K)
      (qr qs qt : K),
      n ≠ 0 ∧
        a ≠ 0 ∧ t ≠ 0 ∧
        Dr a = 0 ∧ Ds a = 0 ∧ Dt a = 0 ∧
        Dr t = 0 ∧ Ds t = 0 ∧ Dt t = 1 ∧
        Ds s = 1 ∧
        (∑ j : Fin n, c j * T0 j = 0) ∧
        (∑ j : Fin n, c j * T2 j = 0) ∧
        (∑ j : Fin n, c j * T4 j = 1) ∧
        (-(P * (Dr qr + Ds qs + Dt qt) -
            (2 / 3 : K) * (qr * Dr P + qs * Ds P + qt * Dt P)) =
          (∑ j : Fin n, c j * T0 j) +
            (∑ j : Fin n, c j * T2 j) * t ^ 2 +
              (∑ j : Fin n, c j * T4 j) * t ^ 4) := by
  let K := FractionRing Rst
  refine ⟨K, inferInstance, inferInstance, ?_⟩
  exact FlatMomentSectionE3.exists_in_fraction_field K
