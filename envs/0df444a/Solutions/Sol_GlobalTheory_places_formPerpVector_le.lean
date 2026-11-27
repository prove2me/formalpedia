-- Prove2me | solution 1 for GlobalTheory.places_formPerpVector_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:42:02.514493+00:00
-- url     : https://prove2.me/submissions/2cf92230-761f-4156-a39a-df36c37f97d8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_FormPerpVectorMemOfIntegral
import Theorems.Thm_GlobalTheory_pairingMatrix_apply
import Theorems.Thm_GlobalTheory_formPairMatrix_apply
import Theorems.Thm_GlobalTheory_seminorm_formPerpVector_le
import Theorems.Thm_GlobalTheory_seminorm_det_formPairMatrix_le
import Theorems.Thm_GlobalTheory_innerFormLeft_apply
import Theorems.Thm_GlobalTheory_normSq_place_form_le
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.pairingMatrix_apply
attribute [local simp] GlobalTheory.formPairMatrix_apply
attribute [local simp] GlobalTheory.innerFormLeft_apply

set_option autoImplicit false
open scoped BigOperators Nat
open GlobalTheory
variable {R M T : Type*} [CommRing R] [StarRing R] [AddCommGroup M] [Module R M]
namespace GlobalTheory
theorem _root_.solution [Fintype T] {p : ℕ} (h : M →ₗ[R] M →ₗ⋆[R] R)
    (hh : ∀ u v, h u v = star (h v u)) (τ : T → R →+* ℂ)
    (hτ : ∀ t x, τ t (star x) = starRingEnd ℂ (τ t x)) (hpos : ∀ t v, 0 ≤ (τ t (h v v)).re)
    (e e' : Fin p → M) (g : M) {r : ℝ}
    (he : ∀ a, √(∑ t, (τ t (h (e a) (e a))).re) ≤ r)
    (he' : ∀ a, √(∑ t, (τ t (h (e' a) (e' a))).re) ≤ r)
    (hg : √(∑ t, (τ t (h g g)).re) ≤ r) :
    (∀ t, ‖τ t (formPairMatrix h e e').det‖ ≤ p ! * r ^ (2 * p)) ∧
      √(∑ t, (τ t (h (formPerpVector h e e' g) (formPerpVector h e e' g))).re)
        ≤ (p + 1)! * r ^ (2 * p + 1) := by
  have hsum : ∀ v, 0 ≤ ∑ t, (τ t (h v v)).re := fun v => Finset.sum_nonneg fun t _ => hpos t v
  have hcs1 : ∀ t u v, ‖τ t (h u v)‖ ≤ √(τ t (h u u)).re * √(τ t (h v v)).re := by
    intro t u v
    rw [← Real.sqrt_mul (hpos t u)]
    exact Real.le_sqrt_of_sq_le (normSq_place_form_le h hh (τ t) (hτ t) (hpos t) u v)
  have hsm : ∀ t (x : R) v, (τ t (h (x • v) (x • v))).re = ‖τ t x‖ ^ 2 * (τ t (h v v)).re := by
    intro t x v
    simp only [map_smul, LinearMap.smul_apply, LinearMap.map_smulₛₗ, smul_eq_mul, map_mul,
      starRingEnd_apply, hτ]
    rw [← mul_assoc, ← starRingEnd_apply, Complex.conj_mul', ← Complex.ofReal_pow,
      Complex.re_ofReal_mul]
  let π : R →+* (T → ℂ) := RingHom.pi τ
  let ν : RingSeminorm R :=
    { toFun := fun x => ‖π x‖
      map_zero' := by simp
      add_le' := fun x y => by rw [map_add]; exact norm_add_le _ _
      neg' := fun x => by rw [map_neg, norm_neg]
      mul_le' := fun x y => by rw [map_mul]; exact norm_mul_le _ _ }
  have hν : ∀ t x, ‖τ t x‖ ≤ ν x := fun t x => norm_le_pi_norm (π x) t
  have hν1 : ν 1 ≤ 1 := (pi_norm_le_iff_of_nonneg zero_le_one).2 fun t => by simp [π]
  let μ : AddGroupSeminorm M :=
    { toFun := fun v => √(∑ t, (τ t (h v v)).re)
      map_zero' := by simp
      add_le' := fun u v => by
        refine Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩
        have h1 : ∑ t, √(τ t (h u u)).re * √(τ t (h v v)).re
            ≤ √(∑ t, (τ t (h u u)).re) * √(∑ t, (τ t (h v v)).re) :=
          Real.sum_sqrt_mul_sqrt_le _ (fun t => hpos t u) fun t => hpos t v
        have h2 : ∑ t, (τ t (h (u + v) (u + v))).re
            ≤ ∑ t, ((τ t (h u u)).re + 2 * (√(τ t (h u u)).re * √(τ t (h v v)).re)
              + (τ t (h v v)).re) := by
          refine Finset.sum_le_sum fun t _ => ?_
          have a1 := (Complex.re_le_norm _).trans (hcs1 t u v)
          have a2 := (Complex.re_le_norm _).trans (hcs1 t v u)
          simp only [map_add, LinearMap.add_apply, Complex.add_re]
          nlinarith
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum] at h2
        rw [add_sq, Real.sq_sqrt (hsum u), Real.sq_sqrt (hsum v)]
        linarith
      neg' := fun v => by simp }
  have hμ : ∀ t v, √(τ t (h v v)).re ≤ μ v := fun t v =>
    Real.sqrt_le_sqrt (Finset.single_le_sum (fun s _ => hpos s v) (Finset.mem_univ t))
  have hcs : ∀ u v, ν (h u v) ≤ μ u * μ v := fun u v =>
    (pi_norm_le_iff_of_nonneg (mul_nonneg (apply_nonneg μ u) (apply_nonneg μ v))).2 fun t =>
      (hcs1 t u v).trans
        (mul_le_mul (hμ t u) (hμ t v) (Real.sqrt_nonneg _) (apply_nonneg μ u))
  have hsmul : ∀ (x : R) (v : M), μ (x • v) ≤ ν x * μ v := by
    intro x v
    refine Real.sqrt_le_iff.2 ⟨mul_nonneg (apply_nonneg ν x) (apply_nonneg μ v), ?_⟩
    have : μ v ^ 2 = ∑ t, (τ t (h v v)).re := Real.sq_sqrt (hsum v)
    rw [mul_pow, this, Finset.mul_sum]
    refine Finset.sum_le_sum fun t _ => ?_
    rw [hsm]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hν t x) 2) (hpos t v)
  exact ⟨fun t => (hν t _).trans (seminorm_det_formPairMatrix_le ν hν1 μ h hcs e e' he he'),
    seminorm_formPerpVector_le ν hν1 μ hsmul h hcs e e' g he he' hg⟩
end GlobalTheory
