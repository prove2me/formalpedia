-- Prove2me | solution 1 for HodgeComputer.FourPlusTwoResidual.core_rational_of_homogenized_chart_source_a6t3
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-25T13:39:14.654905+00:00
-- url     : https://prove2.me/submissions/ebb53dcb-63d5-451f-8643-ba4a10dcf2b3
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_HodgeComputer_FourPlusTwoResidual_exists_core_rational_vector_field
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
Wormhole proof of `core_rational_of_homogenized_chart_source_a6t3`: ignore the
abstract chart witness `h` and build a fresh model on
`K = FractionRing (MvPolynomial (Fin 4) ℂ)`. Coordinate partials lift through the
Kähler isomorphism `Ω_{K/ℂ} ≃ K ⊗ Ω_{R/ℂ}`; the rational vector field is supplied
by `exists_core_rational_vector_field`.
-/

abbrev R4 : Type := MvPolynomial (Fin 4) ℂ

namespace CoreRationalHomogenizedA6T3

variable (K : Type) [Field K] [CharZero K]
variable [Algebra R4 K] [IsFractionRing R4 K]
variable [Algebra ℂ K] [IsScalarTower ℂ R4 K]

private abbrev ι : R4 →+* K := algebraMap R4 K

/-- `mapBaseChange` is bijective for a fraction field of a polynomial algebra. -/
private lemma mapBaseChange_bijective :
    Function.Bijective (mapBaseChange ℂ R4 K) := by
  refine ⟨?inj, ?surj⟩
  case inj =>
    have : Algebra.FormallyEtale R4 K :=
      Algebra.FormallyEtale.of_isLocalization (nonZeroDivisors R4)
    have : Algebra.FormallySmooth R4 K := inferInstance
    have hexact := Algebra.H1Cotangent.exact_δ_mapBaseChange ℂ R4 K
    intro x y hxy
    have hx : mapBaseChange ℂ R4 K (x - y) = 0 := by
      simpa [map_sub, sub_eq_zero] using hxy
    have : x - y ∈ Set.range (Algebra.H1Cotangent.δ ℂ R4 K) :=
      (hexact (x - y)).1 hx
    obtain ⟨z, hz⟩ := this
    have hz0 : Algebra.H1Cotangent.δ ℂ R4 K z = 0 := by
      have : Subsingleton (Algebra.H1Cotangent R4 K) :=
        Algebra.FormallySmooth.subsingleton_h1Cotangent
      simp [Subsingleton.elim z 0]
    exact sub_eq_zero.mp (by simpa [hz0] using hz.symm)
  case surj =>
    have : Algebra.FormallyUnramified R4 K :=
      Algebra.FormallyUnramified.of_isLocalization (nonZeroDivisors R4)
    have hrange : LinearMap.range (mapBaseChange ℂ R4 K) = ⊤ := by
      rw [range_mapBaseChange]
      exact top_unique fun x _ =>
        (LinearMap.mem_ker).2 (Subsingleton.elim _ _)
    intro y
    have : y ∈ LinearMap.range (mapBaseChange ℂ R4 K) := by simp [hrange]
    exact this

private def omegaFracEquiv : K ⊗[R4] Ω[R4⁄ℂ] ≃ₗ[K] Ω[K⁄ℂ] :=
  LinearEquiv.ofBijective (mapBaseChange ℂ R4 K) (mapBaseChange_bijective K)

private lemma omegaFracEquiv_tmul_D (p : R4) :
    omegaFracEquiv K (1 ⊗ₜ D ℂ R4 p) = D ℂ K (ι K p) := by
  change mapBaseChange ℂ R4 K (1 ⊗ₜ D ℂ R4 p) = D ℂ K (algebraMap R4 K p)
  simp [mapBaseChange_tmul, map_D]

private lemma omegaFracEquiv_symm_D_algebraMap (p : R4) :
    (omegaFracEquiv K).symm (D ℂ K (ι K p)) = 1 ⊗ₜ D ℂ R4 p := by
  apply (omegaFracEquiv K).symm_apply_eq.2
  exact (omegaFracEquiv_tmul_D K p).symm

private def liftPDerivℂ (i : Fin 4) : Derivation ℂ K K :=
  let dR : Derivation ℂ R4 K := (Algebra.linearMap R4 K).compDer (pderiv i)
  let φ : Ω[R4⁄ℂ] →ₗ[R4] K := dR.liftKaehlerDifferential
  let φK : K ⊗[R4] Ω[R4⁄ℂ] →ₗ[K] K := φ.liftBaseChange K
  let ψ : Ω[K⁄ℂ] →ₗ[K] K := φK ∘ₗ (omegaFracEquiv K).symm.toLinearMap
  linearMapEquivDerivation ℂ K ψ

private def liftPDeriv (i : Fin 4) : Derivation ℤ K K :=
  (liftPDerivℂ K i).restrictScalars ℤ

private lemma liftPDeriv_algebraMap (i : Fin 4) (p : R4) :
    liftPDeriv K i (ι K p) = ι K (pderiv i p) := by
  change liftPDerivℂ K i (ι K p) = ι K (pderiv i p)
  have hψ :
      liftPDerivℂ K i (ι K p) =
        ((Algebra.linearMap R4 K).compDer (pderiv i)).liftKaehlerDifferential
          (D ℂ R4 p) := by
    unfold liftPDerivℂ
    simp only [linearMapEquivDerivation_apply_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
      omegaFracEquiv_symm_D_algebraMap, LinearMap.liftBaseChange_one_tmul]
  rw [hψ, Derivation.liftKaehlerDifferential_comp_D]
  rfl

/-- Package of lifted coordinate derivations on a fixed fraction field. -/
private theorem exists_in_fraction_field :
    ∃ (δ : Fin 4 → Derivation ℤ K K),
      (∀ (i : Fin 4) (p : R4),
          δ i (ι K p) = ι K (pderiv i p)) ∧
        ∃ v : Fin 4 → K, CoreRationalEquation δ v := by
  let δ : Fin 4 → Derivation ℤ K K := fun i => liftPDeriv K i
  have hδ : ∀ (i : Fin 4) (p : R4), δ i (ι K p) = ι K (pderiv i p) :=
    fun i p => liftPDeriv_algebraMap K i p
  obtain ⟨v, hv⟩ := exists_core_rational_vector_field (K := K) δ hδ
  exact ⟨δ, hδ, v, hv⟩

end CoreRationalHomogenizedA6T3

theorem solution
    (h : ∃ (K : Type) (_ : Field K) (_ : CharZero K)
      (Dr Ds Dt : Derivation ℤ K K) (a s t P qr qs qt : K),
      a ≠ 0 ∧ t ≠ 0 ∧
        Dr a = 0 ∧ Ds a = 0 ∧ Dt a = 0 ∧
        Dr t = 0 ∧ Ds t = 0 ∧ Dt t = 1 ∧
        Ds s = 1 ∧
        (let H := a ^ 6 * P
          let db := fun z : K => Dr z / a
          let dc := fun z : K => (Dt z - s / t * Ds z) / a
          let dd := fun z : K => Ds z / (a * t)
          let pb := (2 : K) * a * qr / (3 * t)
          let pc := (2 : K) * a * qt / (3 * t)
          let pd := (2 : K) * a * (s * qt + t * qs) / (3 * t)
          pb * db H + pc * dc H + pd * dd H -
            (3 / 2 : K) * H * (db pb + dc pc + dd pd) = a ^ 6 * t ^ 3)) :
    ∃ (K : Type) (_ : Field K) (_ : CharZero K)
      (_ : Algebra (MvPolynomial (Fin 4) ℂ) K)
      (_ : IsFractionRing (MvPolynomial (Fin 4) ℂ) K)
      (δ : Fin 4 → Derivation ℤ K K) (v : Fin 4 → K),
      (∀ (i : Fin 4) (p : MvPolynomial (Fin 4) ℂ),
          δ i (algebraMap (MvPolynomial (Fin 4) ℂ) K p) =
            algebraMap (MvPolynomial (Fin 4) ℂ) K (MvPolynomial.pderiv i p)) ∧
        HodgeComputer.FourPlusTwoResidual.CoreRationalEquation δ v := by
  -- Ignore the abstract chart witness `h`; build a fresh fraction-field model.
  let _ := h
  let K := FractionRing R4
  refine ⟨K, inferInstance, inferInstance, inferInstance, inferInstance, ?_⟩
  obtain ⟨δ, hδ, v, hv⟩ := CoreRationalHomogenizedA6T3.exists_in_fraction_field K
  exact ⟨δ, v, hδ, hv⟩
