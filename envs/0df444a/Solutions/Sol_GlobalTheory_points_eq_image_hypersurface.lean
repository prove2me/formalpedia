-- Prove2me | solution 1 for GlobalTheory.points_eq_image_hypersurface
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:29:15.19981+00:00
-- url     : https://prove2.me/submissions/d0c0f07b-cee8-467d-aac4-03be013584cc

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Change
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsIsConnectedPrincipalOpen
import Theorems.Thm_GlobalTheory_evalPair_eq
import Theorems.Thm_GlobalTheory_evalPair_C
import Theorems.Thm_GlobalTheory_evalPair_X
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.evalPair_C
attribute [local simp] GlobalTheory.evalPair_X

set_option autoImplicit false
open ReciprocityTheory.PTheta Complex Matrix Filter Topology
open scoped BigOperators Real
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {A : Type} [CommRing A] [Algebra ℂ A] {d : ℕ}
    (j : MvPolynomial (Fin d) ℂ →ₐ[ℂ] A) (a : A) (p : Polynomial (MvPolynomial (Fin d) ℂ))
    (q q' : MvPolynomial (Fin d) ℂ)
    (hp : ∀ r : Polynomial (MvPolynomial (Fin d) ℂ), r.eval₂ j.toRingHom a = 0 ↔ p ∣ r)
    (r : A → Polynomial (MvPolynomial (Fin d) ℂ))
    (hr : ∀ b, j q * b = (r b).eval₂ j.toRingHom a) :
    {x : A → ℂ | ∃ φ : A →ₐ[ℂ] ℂ, ⇑φ = x ∧ x (j (q * q')) ≠ 0} =
      (fun (z : (Fin d → ℂ) × ℂ) (b : A) => evalPair z (r b) / MvPolynomial.eval z.1 q) ''
        {z : (Fin d → ℂ) × ℂ | MvPolynomial.eval z.1 (q * q') ≠ 0 ∧
          (p.map (MvPolynomial.eval z.1)).eval z.2 = 0} := by
  set E : Polynomial (MvPolynomial (Fin d) ℂ) →+* A :=
    Polynomial.eval₂RingHom j.toRingHom a with hE
  have hEr : ∀ b, E (r b) = j q * b := fun b => (hr b).symm
  have hEC : ∀ s, E (Polynomial.C s) = j s := fun s => by simp [hE]
  ext x
  constructor
  · rintro ⟨φ, rfl, hφ⟩
    let z : (Fin d → ℂ) × ℂ := (fun i => φ (j (MvPolynomial.X i)), φ a)
    have h1 : ∀ s, φ (j s) = MvPolynomial.eval z.1 s := by
      intro s
      induction s using MvPolynomial.induction_on with
      | C c =>
        have : (MvPolynomial.C c : MvPolynomial (Fin d) ℂ) = algebraMap ℂ _ c := rfl
        rw [MvPolynomial.eval_C, this, AlgHom.commutes, AlgHom.commutes]; rfl
      | add s t hs ht => simp only [map_add, hs, ht]
      | mul_X s i hs => simp only [map_mul, hs, MvPolynomial.eval_X, z]
    have h2 : ∀ s, φ (E s) = evalPair z s := by
      intro s
      induction s using Polynomial.induction_on' with
      | add s t hs ht => simp only [map_add, hs, ht]
      | monomial n s =>
        have hX : E Polynomial.X = a := by simp [hE]
        rw [← Polynomial.C_mul_X_pow_eq_monomial, map_mul, map_mul, map_mul, map_pow, map_pow,
          map_pow, evalPair_C, evalPair_X, hEC, h1, hX]
    have hne : MvPolynomial.eval z.1 (q * q') ≠ 0 := by rwa [← h1]
    have hq : MvPolynomial.eval z.1 q ≠ 0 := by
      rw [map_mul] at hne; exact left_ne_zero_of_mul hne
    refine ⟨z, ⟨hne, ?_⟩, ?_⟩
    · have : E p = 0 := (hp p).2 dvd_rfl
      rw [← evalPair_eq, ← h2, this, map_zero]
    · funext b
      simp only
      rw [← h2, hEr, map_mul, h1]
      field_simp
  · rintro ⟨z, ⟨hne, hz⟩, rfl⟩
    have hq : MvPolynomial.eval z.1 q ≠ 0 := by
      rw [map_mul] at hne; exact left_ne_zero_of_mul hne
    rw [← evalPair_eq] at hz
    have key : ∀ s t, E s = E t → evalPair z s = evalPair z t := by
      intro s t hst
      have h0 : E (s - t) = 0 := by rw [map_sub, hst, sub_self]
      obtain ⟨u, hu⟩ := (hp (s - t)).1 h0
      rw [← sub_eq_zero, ← map_sub, hu, map_mul, hz, zero_mul]
    have hj : ∀ s, evalPair z (r (j s)) / MvPolynomial.eval z.1 q = MvPolynomial.eval z.1 s := by
      intro s
      rw [key (r (j s)) (Polynomial.C (q * s)) (by rw [hEr, hEC, map_mul]), evalPair_C, map_mul]
      field_simp
    let φ : A →ₐ[ℂ] ℂ :=
      { toFun := fun b => evalPair z (r b) / MvPolynomial.eval z.1 q
        map_one' := by simpa using hj 1
        map_zero' := by simpa using hj 0
        map_mul' := by
          intro b c
          have := key (r (b * c) * Polynomial.C q) (r b * r c)
            (by simp only [map_mul, hEr, hEC]; ring)
          simp only [map_mul, evalPair_C] at this
          field_simp
          exact this
        map_add' := by
          intro b c
          have := key (r (b + c)) (r b + r c) (by simp only [map_add, hEr]; ring)
          rw [this, map_add, add_div]
        commutes' := by
          intro c
          have := hj (algebraMap ℂ _ c)
          rw [AlgHom.commutes] at this
          rw [this]
          simp }
    refine ⟨φ, rfl, ?_⟩
    simp only
    rw [hj]
    exact hne
end GlobalTheory
