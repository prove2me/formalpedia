-- Prove2me | solution 1 for GlobalTheory.ThetaTangent.exists_unit_of_three_term
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:48:21.985152+00:00
-- url     : https://prove2.me/submissions/66f53310-b51e-4c14-9a7d-08c7acc19a9d

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Change
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_LevelThreeSeparatesTangentVectors
import Theorems.Thm_GlobalTheory_ThetaTangent_dense_ne_zero
import Theorems.Thm_GlobalTheory_ThetaTangent_exists_entire_quotient
import Theorems.Thm_GlobalTheory_SCV_differentiableOn_fderiv_apply


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.PTheta Complex Matrix Filter Topology
open scoped BigOperators Real
open GlobalTheory GlobalTheory.ThetaTangent
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace GlobalTheory.ThetaTangent
theorem _root_.solution [FiniteDimensional ℂ E] {θ : E → ℂ} (hθ : Differentiable ℂ θ)
    (h0 : θ ≠ 0) (ξ s : E) (γ : ℂ) (m : ℕ)
    (hrel : ∀ a b : E,
      fderiv ℂ θ a ξ * θ b ^ (m + 1) * θ (s - a - ((m : ℂ) + 1) • b)
        + θ a * (((m : ℂ) + 1) * θ b ^ m * fderiv ℂ θ b ξ) * θ (s - a - ((m : ℂ) + 1) • b)
        + θ a * θ b ^ (m + 1) * fderiv ℂ θ (s - a - ((m : ℂ) + 1) • b) ξ
      = γ * (θ a * θ b ^ (m + 1) * θ (s - a - ((m : ℂ) + 1) • b))) (t : ℂ) :
    ∃ h : E → ℂ, Differentiable ℂ h ∧ (∀ y, h y ≠ 0) ∧ ∀ y, θ (y + t • ξ) = h y * θ y := by
  set k : ℂ := (m : ℂ) + 1 with hk
  have hk0 : k ≠ 0 := Nat.cast_add_one_ne_zero m
  set D : E → ℂ := fun x => fderiv ℂ θ x ξ with hD
  have hDd : Differentiable ℂ D := by
    rw [← differentiableOn_univ]
    exact GlobalTheory.SCV.differentiableOn_fderiv_apply isOpen_univ hθ.differentiableOn ξ
  have hU := dense_ne_zero hθ h0
  have hUo : IsOpen {x | θ x ≠ 0} := isOpen_ne_fun hθ.continuous continuous_const
  obtain ⟨x₀, hx₀⟩ : ∃ x, θ x ≠ 0 := hU.nonempty
  have hU' : ∀ (p : E) (c : ℂ), c ≠ 0 → Dense {x | θ (p - c • x) ≠ 0} := by
    intro p c hc
    refine dense_ne_zero (f := fun x => θ (p - c • x)) (hθ.comp (by fun_prop)) fun h => hx₀ ?_
    have := congrFun h (c⁻¹ • (p - x₀))
    simpa [smul_smul, hc] using this
  obtain ⟨ψ, hψ, hDψ⟩ := exists_entire_quotient (D := D) hU (by
    intro a
    obtain ⟨b, hb1, hb2⟩ := ((hU' (s - a) k hk0).inter_of_isOpen_right hU hUo).nonempty
    simp only [Set.mem_setOf_eq] at hb1 hb2
    refine ⟨fun x => γ - k * D b / θ b - D (s - x - k • b) / θ (s - x - k • b), ?_⟩
    have hc : ContinuousAt (fun x => θ (s - x - k • b)) a :=
      (hθ.continuous.comp (by fun_prop)).continuousAt
    filter_upwards [hc.eventually_ne hb1] with x hx
    refine ⟨?_, ?_⟩
    · have d1 : DifferentiableAt ℂ (fun x => D (s - x - k • b)) x :=
        (hDd.comp (f := fun x => s - x - k • b) (by fun_prop)) x
      have d2 : DifferentiableAt ℂ (fun x => θ (s - x - k • b)) x :=
        (hθ.comp (f := fun x => s - x - k • b) (by fun_prop)) x
      simp only [div_eq_mul_inv]
      exact (differentiableAt_const _).sub (d1.mul (d2.inv hx))
    · have := hrel x b
      have hp : θ b ^ m ≠ 0 := pow_ne_zero _ hb2
      field_simp
      apply mul_left_cancel₀ hp
      simp only [hD]
      linear_combination this)
  have hψc := hψ.continuous
  have hfun : ∀ a b : E, ψ a + k * ψ b + ψ (s - a - k • b) = γ := by
    have h1 : ∀ b, θ b ≠ 0 → ∀ a, ψ a + k * ψ b + ψ (s - a - k • b) = γ := by
      intro b hb a
      have hd := (hU' (s - k • b) 1 one_ne_zero).inter_of_isOpen_right hU hUo
      refine congrFun (Continuous.ext_on hd
        (f := fun a => ψ a + k * ψ b + ψ (s - a - k • b)) (g := fun _ => γ)
        (by fun_prop) continuous_const ?_) a
      rintro x ⟨hx1, hx2⟩
      simp only [Set.mem_setOf_eq, one_smul] at hx1 hx2
      rw [sub_right_comm] at hx1
      have := hrel x b
      have e1 := hDψ x
      have e2 := hDψ b
      have e3 := hDψ (s - x - k • b)
      simp only [hD] at e1 e2 e3
      rw [e1, e2, e3] at this
      apply mul_right_cancel₀ (mul_ne_zero (mul_ne_zero hx2 (pow_ne_zero (m + 1) hb)) hx1)
      linear_combination this
    intro a b
    exact congrFun (Continuous.ext_on hU
        (f := fun b => ψ a + k * ψ b + ψ (s - a - k • b)) (g := fun _ => γ)
        (by fun_prop) continuous_const fun x hx => h1 x hx a) b
  have hdiff : ∀ y w : E, ψ (y + w) = ψ y + (ψ w - ψ 0) := by
    intro y w
    have e1 := hfun (y + w) (k⁻¹ • (s - y - w))
    have e2 := hfun y (k⁻¹ • (s - y - w))
    rw [smul_inv_smul₀ hk0] at e1 e2
    rw [show s - (y + w) - (s - y - w) = 0 by abel] at e1
    rw [show s - y - (s - y - w) = w by abel] at e2
    linear_combination e1 - e2
  have hκ : Differentiable ℂ (fun r : ℂ => ψ (r • ξ) - ψ 0) := by fun_prop
  obtain ⟨K, hK⟩ := hκ.isExactOn_univ
  refine ⟨fun y => Complex.exp (t * ψ y + (K t - K 0)), by fun_prop,
    fun y => Complex.exp_ne_zero _, fun y => ?_⟩
  have hF : ∀ r : ℂ, HasDerivAt
      (fun r : ℂ => θ (y + r • ξ) * Complex.exp (-(r * ψ y + K r))) 0 r := by
    intro r
    have hl : HasDerivAt (fun r : ℂ => y + r • ξ) ξ r := by
      simpa using ((hasDerivAt_id r).smul_const ξ).const_add y
    have h1 : HasDerivAt (fun r : ℂ => θ (y + r • ξ)) (D (y + r • ξ)) r :=
      (hθ (y + r • ξ)).hasFDerivAt.comp_hasDerivAt r hl
    have h2 : HasDerivAt (fun r : ℂ => -(r * ψ y + K r)) (-(1 * ψ y + (ψ (r • ξ) - ψ 0))) r :=
      (((hasDerivAt_id r).mul_const (ψ y)).add (hK r (Set.mem_univ r))).neg
    refine (h1.mul h2.cexp).congr_deriv ?_
    rw [hDψ, hdiff]
    ring
  have hc := is_const_of_deriv_eq_zero (fun r => (hF r).differentiableAt)
    (fun r => (hF r).deriv) t 0
  simp only [zero_smul, add_zero, zero_mul, zero_add] at hc
  have e : θ (y + t • ξ) = (θ (y + t • ξ) * Complex.exp (-(t * ψ y + K t)))
      * Complex.exp (t * ψ y + K t) := by
    rw [mul_assoc, ← Complex.exp_add]; simp
  rw [e, hc, mul_assoc, ← Complex.exp_add, mul_comm]
  congr 2
  ring
end GlobalTheory.ThetaTangent
