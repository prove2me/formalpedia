-- Prove2me | solution 1 for GlobalTheory.LowestWeight.eq_zero_lower
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:35:53.921846+00:00
-- url     : https://prove2.me/submissions/c5916e7f-02ff-4866-9f86-f726aff9132c

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainPointBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_OrthogonalFrameDomain
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FourierCoefficientDomain
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExhaustFStatementPfB
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_LowestWeightFunctionMulEq
import Theorems.Thm_GlobalTheory_LowestWeight_contract_mem_dom
import Theorems.Thm_GlobalTheory_LowestWeight_diagonal_mem_bor
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_OrthogonalFrameDomain_rmul_mem_dom


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open NumberField ReciprocityTheory.ChartRestriction.G.FD Matrix Filter Topology
open scoped ComplexConjugate ComplexOrder
open GlobalTheory.LowestWeight
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
namespace GlobalTheory.LowestWeight
theorem _root_.solution (la : Wt X.Ψ r) (x₀ : Frame X.Ψ r)
    (hx₀ : ∀ τ : X.Ψ, gram τ.1 X.Gm (mat x₀ τ) =
      Matrix.diagonal fun a : Fin r => ((sgn X.p0 (a : ℕ) : ℝ) : ℂ))
    (hx₀' : x₀ ∈ X.dom) (m : Frame X.Ψ r → ℂ) (hm : DifferentiableOn ℂ m X.dom)
    (hB : ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, m (rmul x b) = bchar la b * m x)
    (hT : ∀ t : X.Ψ → Fin r → ℂ, (∀ τ i, ‖t τ i‖ = 1) → ∀ x ∈ X.dom,
      m (X.lmulC (fun τ => mat x₀ τ * Matrix.diagonal (t τ) * (mat x₀ τ)⁻¹) x) =
        (∏ τ, ∏ i, t τ i ^ la τ i) * m x)
    (h0 : m x₀ = 0) {L : Frame X.Ψ r} (hL : ∀ τ a c, a < c → L τ a c = 0)
    (hLd : rmul x₀ L ∈ X.dom) : m (rmul x₀ L) = 0 := by
  set F : ℂ → Frame X.Ψ r := fun ζ => rmul x₀ fun τ a c => ζ ^ ((a : ℕ) - c) * L τ a c with hF
  have hFd : Differentiable ℂ F := by
    refine differentiable_pi.2 fun τ => differentiable_pi.2 fun a => differentiable_pi.2 fun c => ?_
    simp only [hF, rmul, mat, Matrix.mul_apply, Matrix.of_apply]
    fun_prop
  have hdiag : ∀ τ a, L τ a a ≠ 0 := by
    intro τ a
    have h : (mat x₀ τ * mat L τ).det ≠ 0 := (hLd τ).1
    rw [det_mul] at h
    have h' := right_ne_zero_of_mul h
    rw [det_of_lowerTriangular (mat L τ) (fun a c hac => hL τ a c (by simpa using hac))] at h'
    exact Finset.prod_ne_zero_iff.1 h' a (Finset.mem_univ _)
  have hF0 : F 0 = rmul x₀ fun τ => (diagonal fun a => L τ a a : Matrix (Fin r) (Fin r) ℂ) := by
    simp only [hF]
    congr 1
    funext τ a c
    rcases lt_trichotomy a c with h | rfl | h
    · rw [hL τ a c h, mul_zero, diagonal_apply_ne _ h.ne]
    · simp
    · rw [zero_pow (Nat.sub_ne_zero_of_lt h), zero_mul, diagonal_apply_ne _ h.ne']
  have hb0 := diagonal_mem_bor X _ hdiag
  have hFne : ∀ ζ : ℂ, ζ ≠ 0 → F ζ = rmul (rmul x₀ fun τ =>
      (diagonal (fun a : Fin r => ζ ^ (a : ℕ)) * mat L τ : Matrix (Fin r) (Fin r) ℂ))
      (fun _ => (diagonal fun a : Fin r => (ζ ^ (a : ℕ))⁻¹ : Matrix (Fin r) (Fin r) ℂ)) := by
    intro ζ hζ
    funext τ
    change mat x₀ τ * Matrix.of (fun a c : Fin r => ζ ^ ((a : ℕ) - c) * L τ a c) =
      mat x₀ τ * (diagonal (fun a : Fin r => ζ ^ (a : ℕ)) * mat L τ) *
        diagonal fun a : Fin r => (ζ ^ (a : ℕ))⁻¹
    rw [Matrix.mul_assoc]
    congr 1
    ext a c
    simp only [Matrix.mul_diagonal, Matrix.diagonal_mul, mat, Matrix.of_apply]
    rcases lt_or_ge a c with h | h
    · simp [hL τ a c h]
    · rw [pow_sub₀ _ hζ h]
      ring
  have hbζ : ∀ ζ : ℂ, ζ ≠ 0 → (fun _ : X.Ψ =>
      (diagonal fun a : Fin r => (ζ ^ (a : ℕ))⁻¹ : Matrix (Fin r) (Fin r) ℂ)) ∈ Bor X.Ψ r :=
    fun ζ hζ => diagonal_mem_bor X (fun _ a => (ζ ^ (a : ℕ))⁻¹)
      fun _ a => inv_ne_zero (pow_ne_zero _ hζ)
  have hctr : ∀ ζ : ℂ, ζ ≠ 0 → ‖ζ‖ ≤ 1 → (rmul x₀ fun τ =>
      (diagonal (fun a : Fin r => ζ ^ (a : ℕ)) * mat L τ : Matrix (Fin r) (Fin r) ℂ)) ∈ X.dom := by
    intro ζ hζ hζ1
    refine contract_mem_dom X hx₀ hLd _ (fun a => pow_ne_zero _ hζ) (ρ := ‖ζ‖ ^ X.p0)
      (pow_pos (norm_pos_iff.2 hζ) _) (fun a ha => ?_) (fun a ha => ?_)
    · rw [norm_pow]; exact pow_le_pow_of_le_one (norm_nonneg _) hζ1 ha.le
    · rw [norm_pow]; exact pow_le_pow_of_le_one (norm_nonneg _) hζ1 ha
  have hFmem : ∀ ζ ∈ Metric.closedBall (0 : ℂ) 1, F ζ ∈ X.dom := by
    intro ζ hζ
    rcases eq_or_ne ζ 0 with rfl | h
    · rw [hF0]; exact OrthogonalFrameDomain.rmul_mem_dom X hx₀' hb0
    · rw [hFne ζ h]
      exact OrthogonalFrameDomain.rmul_mem_dom X (hctr ζ h (mem_closedBall_zero_iff.1 hζ)) (hbζ ζ h)
  have hg : DiffContOnCl ℂ (m ∘ F) (Metric.ball 0 1) := by
    refine DifferentiableOn.diffContOnCl ?_
    rw [closure_ball _ one_ne_zero]
    exact hm.comp hFd.differentiableOn hFmem
  have hsph : Set.EqOn (m ∘ F) (fun _ => m (rmul x₀ L)) (frontier (Metric.ball (0 : ℂ) 1)) := by
    intro ζ hζ
    rw [frontier_ball _ one_ne_zero, mem_sphere_zero_iff_norm] at hζ
    have hζ0 : ζ ≠ 0 := norm_ne_zero_iff.1 (by rw [hζ]; exact one_ne_zero)
    have h1 := hT (fun _ a => ζ ^ (a : ℕ)) (fun _ a => by rw [norm_pow, hζ, one_pow]) _ hLd
    have e : X.lmulC (fun τ => mat x₀ τ * Matrix.diagonal (fun a : Fin r => ζ ^ (a : ℕ)) *
        (mat x₀ τ)⁻¹) (rmul x₀ L) = rmul x₀ fun τ =>
      (diagonal (fun a : Fin r => ζ ^ (a : ℕ)) * mat L τ : Matrix (Fin r) (Fin r) ℂ) := by
      funext τ
      change mat x₀ τ * Matrix.diagonal (fun a : Fin r => ζ ^ (a : ℕ)) * (mat x₀ τ)⁻¹ *
        (mat x₀ τ * mat L τ) = mat x₀ τ * (diagonal (fun a : Fin r => ζ ^ (a : ℕ)) * mat L τ)
      rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _
        (isUnit_iff_ne_zero.2 (hx₀' τ).1), Matrix.mul_assoc]
    rw [e] at h1
    change m (F ζ) = m (rmul x₀ L)
    rw [hFne ζ hζ0, hB _ (hctr ζ hζ0 hζ.le) _ (hbζ ζ hζ0), h1, ← mul_assoc]
    change (∏ τ, ∏ a : Fin r, diagonal (fun a : Fin r => (ζ ^ (a : ℕ))⁻¹) a a ^ la τ a) * _ * _ = _
    rw [← Finset.prod_mul_distrib, Finset.prod_eq_one, one_mul]
    intro τ _
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_eq_one fun a _ => ?_
    rw [diagonal_apply_eq, ← mul_zpow, inv_mul_cancel₀ (pow_ne_zero _ hζ0), _root_.one_zpow]
  have key := Complex.eqOn_of_eqOn_frontier Metric.isBounded_ball hg diffContOnCl_const hsph
    (Metric.mem_ball_self one_pos)
  change m (F 0) = m (rmul x₀ L) at key
  rw [← key, hF0, hB _ hx₀' _ hb0, h0, mul_zero]
end GlobalTheory.LowestWeight
