-- Prove2me | solution 1 for GlobalTheory.exists_isConnected_principalOpen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:36:16.354606+00:00
-- url     : https://prove2.me/submissions/ed85baaa-da66-4cb5-96f8-00f24704647d

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Change
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsIsConnectedPrincipalOpen
import Theorems.Thm_GlobalTheory_evalPair_eq
import Theorems.Thm_GlobalTheory_evalPair_C
import Theorems.Thm_GlobalTheory_evalPair_X
import Theorems.Thm_GlobalTheory_continuous_evalPair
import Theorems.Thm_GlobalTheory_points_eq_image_hypersurface
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
theorem _root_.solution :
    (∀ (A : Type) [CommRing A] [IsDomain A] [Algebra ℂ A] [Algebra.FiniteType ℂ A], ∃ (d : ℕ) (j : MvPolynomial (Fin d) ℂ →ₐ[ℂ] A) (a : A) (p : Polynomial (MvPolynomial (Fin d) ℂ)) (q : MvPolynomial (Fin d) ℂ), ringKrullDim A = d ∧ Function.Injective j ∧ j.toRingHom.Finite ∧ p.Monic ∧ Irreducible p ∧ (∀ r : Polynomial (MvPolynomial (Fin d) ℂ), r.eval₂ j.toRingHom a = 0 ↔ p ∣ r) ∧ q ≠ 0 ∧ Polynomial.C q ∈ Ideal.span {p, p.derivative} ∧ ∀ b : A, ∃ r : Polynomial (MvPolynomial (Fin d) ℂ), j q * b = r.eval₂ j.toRingHom a) → (∀ (d : ℕ) (p : Polynomial (MvPolynomial (Fin d) ℂ)) (q : MvPolynomial (Fin d) ℂ), p.Monic → Irreducible p → q ≠ 0 → (∀ x y, MvPolynomial.eval x q ≠ 0 → (p.map (MvPolynomial.eval x)).eval y = 0 → (p.map (MvPolynomial.eval x)).derivative.eval y ≠ 0) → IsConnected {z : (Fin d → ℂ) × ℂ | MvPolynomial.eval z.1 q ≠ 0 ∧ (p.map (MvPolynomial.eval z.1)).eval z.2 = 0}) → (∀ (A : Type) [CommRing A] [IsDomain A] [Algebra ℂ A] [Algebra.FiniteType ℂ A] (f : A), f ≠ 0 → ∃ h : A, h ≠ 0 ∧ IsConnected {x : A → ℂ | ∃ φ : A →ₐ[ℂ] ℂ, ⇑φ = x ∧ x (h * f) ≠ 0}) := by
  intro H1 H2 A _ _ _ _ f hf
  obtain ⟨d, j, a, p, q, -, hinj, hfin, hmon, hirr, hp, hq, hspan, hr⟩ := H1 A
  choose r hr using hr
  obtain ⟨q', hq', f', hf'⟩ : ∃ q' : MvPolynomial (Fin d) ℂ, q' ≠ 0 ∧ f ∣ j q' := by
    letI : Algebra (MvPolynomial (Fin d) ℂ) A := j.toRingHom.toAlgebra
    haveI : Module.Finite (MvPolynomial (Fin d) ℂ) A := hfin
    have hint : IsIntegral (MvPolynomial (Fin d) ℂ) f := Algebra.IsIntegral.isIntegral f
    exact hint.isAlgebraic.exists_nonzero_dvd (mem_nonZeroDivisors_of_ne_zero hf)
  have hmul : j q * f' * f = j (q * q') := by rw [map_mul, hf']; ring
  have hqq : q * q' ≠ 0 := mul_ne_zero hq hq'
  refine ⟨j q * f', ?_, ?_⟩
  · intro h0
    rw [h0, zero_mul] at hmul
    exact hqq (hinj (by rw [← hmul, map_zero]))
  · rw [hmul, points_eq_image_hypersurface j a p q q' hp r hr]
    refine (H2 d p (q * q') hmon hirr hqq ?_).image _ ?_
    · intro x y hx hy hd
      obtain ⟨u, v, huv⟩ := Ideal.mem_span_pair.1 hspan
      have h := congrArg (evalPair (x, y)) huv
      rw [Polynomial.derivative_map] at hd
      simp only [map_add, map_mul, evalPair_C] at h
      rw [evalPair_eq _ p, evalPair_eq _ p.derivative, hy, hd, mul_zero, mul_zero, add_zero] at h
      rw [map_mul, ← h, zero_mul] at hx
      exact hx rfl
    · refine continuousOn_pi.2 fun b => ContinuousOn.div (continuous_evalPair _).continuousOn
        ((MvPolynomial.continuous_eval q).comp continuous_fst).continuousOn ?_
      intro z hz
      have := hz.1
      rw [map_mul] at this
      exact left_ne_zero_of_mul this
end GlobalTheory
