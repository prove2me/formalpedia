-- Prove2me | solution 1 for OAI.ComplexCancellation.Determinant.fixed_coefficients_contradiction
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T20:47:19.790985+00:00
-- url     : https://prove2.me/submissions/afe4e360-3eb5-4854-8442-b6c748ee62d7

-- Generated from openai/math@1581d4c lean/OAI/Algebra/AffineCancellation/DeterminantRigidity.lean:L83-L127
-- (upload_full_project.md Phase 4): solution for node OAI.ComplexCancellation.Determinant.fixed_coefficients_contradiction. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_ComplexCancellation
import Definitions.Def_OAI_Algebra_AffineCancellation_CylinderShift
import Definitions.Def_OAI_Algebra_AffineCancellation_CylinderMaps
import Definitions.Def_OAI_Algebra_AffineCancellation_Cylinder
import Definitions.Def_OAI_Algebra_AffineCancellation_Dimension
import Definitions.Def_OAI_Algebra_AffineCancellation_FactorDerivation
import Definitions.Def_OAI_Algebra_AffineCancellation_Orbit
import Definitions.Def_OAI_Algebra_AffineCancellation_Order
import Definitions.Def_OAI_Algebra_AffineCancellation_LaurentDerivation
import Definitions.Def_OAI_Algebra_AffineCancellation_Clearing
import Definitions.Def_OAI_Algebra_AffineCancellation_GradedLND
import Definitions.Def_OAI_Algebra_AffineCancellation_QuotientGrading
import Definitions.Def_OAI_Algebra_AffineCancellation_QuotientDerivation
import Definitions.Def_OAI_Algebra_AffineCancellation_Determinant
import Definitions.Def_OAI_Algebra_AffineCancellation_DeterminantRigidity
import Theorems.Thm_OAI_ComplexCancellation_SL2_no_negative_highest

-- ---- from OAI.Algebra.AffineCancellation.Orbit ----
namespace OAI

noncomputable section

/-! Orbit polynomials and exponentiation of locally nilpotent derivations. -/
namespace ComplexCancellation.LND
open Polynomial

variable {k R : Type*} [Field k] [CommRing R] [Algebra k R]

lemma iterate_add (D : Derivation k R R) (n : ℕ) (r s : R) :
    (D : R → R)^[n] (r + s) = (D : R → R)^[n] r + (D : R → R)^[n] s := by
  simpa only [Module.End.pow_apply, Derivation.coeFn_coe] using
    (D.toLinearMap ^ n).map_add r s

lemma orbit_injective (D : Derivation k R R) (hD : LocallyNilpotent D) :
    Function.Injective (orbit D hD) := by
  intro r s hes
  simpa using congrArg (fun p : R[X] => p.coeff 0) hes

end ComplexCancellation.LND

end

end OAI

-- ---- from OAI.Algebra.AffineCancellation.Kernel ----
namespace OAI

noncomputable section

namespace ComplexCancellation.LND
open Polynomial
variable {k R : Type*} [Field k] [CharZero k] [CommRing R] [Algebra k R]

lemma inv_factorial_succ (n : ℕ) :
    ((n + 1 : ℕ) : k) * ((n + 1).factorial : k)⁻¹ = (n.factorial : k)⁻¹ := by
  rw [Nat.factorial_succ, Nat.cast_mul, mul_inv_rev]
  have hn : ((n + 1 : ℕ) : k) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  field_simp

lemma derivative_orbit (D : Derivation k R R) (hD : LocallyNilpotent D) (r : R) :
    (orbit D hD r).derivative = orbit D hD (D r) := by
  ext n
  rw [Polynomial.coeff_derivative, orbit_coeff, orbit_coeff,
    ← Function.iterate_succ_apply]
  rw [mul_comm, ← Nat.cast_succ, ← nsmul_eq_mul, ← Nat.cast_smul_eq_nsmul k, smul_smul,
    inv_factorial_succ]

end ComplexCancellation.LND
namespace ComplexCancellation.LND
open Polynomial
variable {k R : Type*} [Field k] [CharZero k] [CommRing R] [Algebra k R] [IsDomain R]

lemma fixed_of_dvd (D : Derivation k R R) (hD : LocallyNilpotent D)
    {r : R} (hr : r ∣ D r) : D r = 0 := by
  obtain ⟨s, hs⟩ := hr
  have hdvd : orbit D hD r ∣ (orbit D hD r).derivative := by
    rw [derivative_orbit, hs, orbit_mul]
    exact dvd_mul_right _ _
  have hz := Polynomial.dvd_derivative_iff.mp hdvd
  rw [derivative_orbit] at hz
  apply orbit_injective D hD
  change orbitHom D hD (D r) = orbitHom D hD 0
  rw [map_zero]
  exact hz

end ComplexCancellation.LND

namespace ComplexCancellation.LND
variable {k R : Type*} [Field k] [CommRing R] [Algebra k R]

lemma nilpotent_add (D : Derivation k R R) {r s : R}
    (hr : ∃ n, (D : R → R)^[n] r = 0) (hs : ∃ n, (D : R → R)^[n] s = 0) :
    ∃ n, (D : R → R)^[n] (r+s) = 0 := by
  obtain ⟨n, hn⟩ := hr
  obtain ⟨m, hm⟩ := hs
  refine ⟨n+m, ?_⟩
  rw [iterate_add, iterate_eq_zero_of_le D hn (Nat.le_add_right _ _),
    iterate_eq_zero_of_le D hm (Nat.le_add_left _ _), add_zero]

lemma nilpotent_mul (D : Derivation k R R) {r s : R}
    (hr : ∃ n, (D : R → R)^[n] r = 0) (hs : ∃ n, (D : R → R)^[n] s = 0) :
    ∃ n, (D : R → R)^[n] (r*s) = 0 := by
  obtain ⟨n, hn⟩ := hr
  obtain ⟨m, hm⟩ := hs
  refine ⟨n+m, ?_⟩
  rw [iterate_leibniz]
  apply Finset.sum_eq_zero
  rintro ⟨i,j⟩ hij
  have hij' : i+j = n+m := Finset.HasAntidiagonal.mem_antidiagonal.mp hij
  by_cases hi : n ≤ i
  · rw [iterate_eq_zero_of_le D hn hi, zero_mul, nsmul_zero]
  · rw [iterate_eq_zero_of_le D hm (by omega : m ≤ j), mul_zero, nsmul_zero]

lemma mvPolynomial_locallyNilpotent {σ : Type*}
    (D : Derivation k (MvPolynomial σ k) (MvPolynomial σ k))
    (hX : ∀ i, ∃ n : ℕ, (D : _ → _)^[n] (MvPolynomial.X i) = 0) :
    LocallyNilpotent D := by
  intro r
  induction r using MvPolynomial.induction_on with
  | C c => exact ⟨1, by simp⟩
  | add r s hr hs => exact nilpotent_add D hr hs
  | mul_X r i hr => exact nilpotent_mul D hr (hX i)

end ComplexCancellation.LND

end

end OAI

-- ---- from OAI.Algebra.AffineCancellation.QuotientDerivation ----
namespace OAI

noncomputable section

namespace ComplexCancellation.QuotientDerivation
variable {k R : Type*} [CommRing k] [CommRing R] [Algebra k R]
variable (I : Ideal R) (D : Derivation k R R)
  (hD : ∀ r ∈ I, D r ∈ I)

lemma iterate_mk (r : R) (n : ℕ) :
    (derivation I D hD : (R ⧸ I) → (R ⧸ I))^[n] (Ideal.Quotient.mk I r) =
      Ideal.Quotient.mk I ((D : R → R)^[n] r) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', ih, derivation_mk,
      Function.iterate_succ_apply']

lemma locallyNilpotent (hn : ∀ r, ∃ n, (D : R → R)^[n] r = 0) :
    ∀ r, ∃ n, (derivation I D hD : (R ⧸ I) → (R ⧸ I))^[n] r = 0 := by
  intro r
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective r
  obtain ⟨n, hn⟩ := hn r
  exact ⟨n, by rw [iterate_mk, hn, map_zero]⟩

end ComplexCancellation.QuotientDerivation

end

end OAI

-- ---- from OAI.Algebra.AffineCancellation.DeterminantRigidity ----
namespace OAI

noncomputable section

namespace ComplexCancellation.Determinant
open MvPolynomial

lemma derivation_ext {D₁ D₂ : Derivation ℂ T T}
    (hX : ∀ i : Fin 5, D₁ (π (X i)) = D₂ (π (X i))) : D₁ = D₂ := by
  apply Derivation.ext
  intro r
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mkₐ_surjective ℂ (Ideal.span {relation}) r
  change D₁ (π r) = D₂ (π r)
  induction r using MvPolynomial.induction_on with
  | C z => simp [π]
  | add r s hr hs => simp only [map_add, hr, hs]
  | mul_X r i hr => simp only [map_mul, Derivation.leibniz, hr, hX]

lemma η_locallyNilpotent : LND.LocallyNilpotent η := by
  apply QuotientDerivation.locallyNilpotent
  apply LND.mvPolynomial_locallyNilpotent
  intro i
  refine ⟨2, ?_⟩
  fin_cases i <;> simp [Function.iterate_succ_apply', ηP]

lemma Euler_η (r : T) : Euler (η r) = η (Euler r) - (2 : ℂ) • η r := by
  have h : ⁅Euler,η⁆ = (-2 : ℂ) • η := by
    apply derivation_ext
    intro i
    fin_cases i <;>
      simp [Euler, Derivation.commutator_apply, δ_π, η_π, δP, ηP, Derivation.smul_apply] <;>
      module
  have hr := DFunLike.congr_fun h r
  simp only [Derivation.commutator_apply, Derivation.smul_apply] at hr
  rw [neg_smul] at hr
  linear_combination hr

lemma fixed_coefficients_contradiction (E : Derivation ℂ T T)
    (hE : E ≠ 0) (hln : LND.LocallyNilpotent E) (e : ℤ) (he : e ≤ 0)
    (hshift : FiberShift E e) (ha : E a = 0) (hd : E d = 0) (hu : E u = 0) : False := by
  let h := c * E b - b * E c
  have hrel : a * E c = d * E b := by
    have hh := congrArg E determinant
    simp only [map_sub, Derivation.leibniz, ha, hd, smul_eq_mul, mul_zero,
      add_zero, zero_add, Derivation.map_one_eq_zero] at hh
    linear_combination hh
  have hb : E b = h*a := by dsimp [h]; linear_combination -(E b) * determinant + b * hrel
  have hc : E c = h*d := by dsimp [h]; linear_combination -(E c) * determinant + c * hrel
  have hder : E = h • δ := by
    apply derivation_ext
    intro i
    fin_cases i
    · change E a = h * δ a; simp only [ha, δ_a, mul_zero]
    · change E d = h * δ d; simp only [hd, δ_d, mul_zero]
    · change E b = h * δ b; simpa only [δ_b] using hb
    · change E c = h * δ c; simpa only [δ_c] using hc
    · change E u = h * δ u; simp only [hu, δ_u, mul_zero]
  have hn : h ≠ 0 := by
    intro hh
    apply hE
    rw [hder, hh]
    apply Derivation.ext
    intro r
    change (0:T) * δ r = 0
    exact zero_mul _
  have hfix : δ h = 0 := by
    have hh : E h = 0 := LND.fixed_of_dvd E hln (by
      rw [hder, Derivation.smul_apply, smul_eq_mul]
      exact dvd_mul_right _ _)
    rw [hder, Derivation.smul_apply, smul_eq_mul] at hh
    exact (mul_eq_zero.mp hh).resolve_left hn
  have hweight : Euler h = ((e-2 : ℤ) : ℂ) • h := by
    have hb' := hshift b
    have hc' := hshift c
    simp only [Euler_b, Euler_c, map_neg] at hb' hc'
    dsimp [h]
    simp only [map_sub, Derivation.leibniz, Euler_b, Euler_c, smul_eq_mul]
    simp only [Int.cast_smul_eq_zsmul, zsmul_eq_mul] at hb' hc' ⊢
    push_cast
    linear_combination c * hb' - b * hc'
  exact hn (SL2.no_negative_highest δ.toLinearMap η.toLinearMap Euler.toLinearMap
    (fun r => rfl) Euler_η h (e-2) (by omega) hfix hweight (η_locallyNilpotent h))

end ComplexCancellation.Determinant

namespace ComplexCancellation.Determinant
open MvPolynomial
attribute [local instance] MvPolynomial.weightedGradedAlgebra

end ComplexCancellation.Determinant

end

end OAI

-- ---- platform node ----
open OAI OAI.ComplexCancellation OAI.ComplexCancellation.Determinant
open MvPolynomial


theorem solution : type_of% @_root_.OAI.ComplexCancellation.Determinant.fixed_coefficients_contradiction := @_root_.OAI.ComplexCancellation.Determinant.fixed_coefficients_contradiction
