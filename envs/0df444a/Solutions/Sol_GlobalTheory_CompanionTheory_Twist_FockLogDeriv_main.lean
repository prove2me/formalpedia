-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Twist.FockLogDeriv.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T18:29:51.763474+00:00
-- url     : https://prove2.me/submissions/1af38800-4a61-405b-b1fa-36fbffb857dd

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_TwistedProofs_EqZeroOfForallNhds
import Theorems.Thm_GlobalTheory_CompanionTheory_Twist_FockLogDeriv_eq_zero_of_forall_nhds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Twist GlobalTheory.CompanionTheory.Twist.FockLogDeriv
namespace GlobalTheory.CompanionTheory.Twist.FockLogDeriv
theorem _root_.solution {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (T : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (hT : ∀ b, (∀ y, T y b = 0) → b = 0)
    (Jm : V × V →ₗ[ℝ] V × V) (f₀ : SchwartzMap V ℂ) (hf : f₀ ≠ 0)
    (hE : ∀ (p : V × V) (y : V), fderiv ℝ f₀ y (Jm p).1
        + (-(2 * Real.pi * Complex.I)) * ((T y (Jm p).2 : ℝ) : ℂ) * f₀ y
      = Complex.I * (fderiv ℝ f₀ y p.1
        + (-(2 * Real.pi * Complex.I)) * ((T y p.2 : ℝ) : ℂ) * f₀ y)) :
    ∃ m : V →ₗ[ℝ] V →ₗ[ℝ] ℂ, ∀ a y, fderiv ℝ f₀ y a = m a y * f₀ y := by
  let Φ : V × V →ₗ[ℝ] (V → ℂ) :=
    { toFun := fun p y => fderiv ℝ f₀ y p.1 + (-(2 * Real.pi * Complex.I)) * ((T y p.2 : ℝ) : ℂ) * f₀ y
      map_add' := by
        intro p q
        funext y
        simp only [Prod.fst_add, Prod.snd_add, map_add, Complex.ofReal_add, Pi.add_apply]
        ring
      map_smul' := by
        intro s p
        funext y
        simp only [Prod.smul_fst, Prod.smul_snd, map_smul, smul_eq_mul, Complex.ofReal_mul, RingHom.id_apply,
          Pi.smul_apply, Complex.real_smul]
        ring }
  have hΦ : ∀ p y, Φ p y = fderiv ℝ f₀ y p.1 + (-(2 * Real.pi * Complex.I)) * ((T y p.2 : ℝ) : ℂ) * f₀ y :=
    fun p y => rfl
  have hEΦ : ∀ p y, Φ (Jm p) y = Complex.I * Φ p y := fun p y => by rw [hΦ, hΦ]; exact hE p y
  have hΦ0 : ∀ w y, Φ (0, w) y = (-(2 * Real.pi * Complex.I)) * ((T y w : ℝ) : ℂ) * f₀ y := by
    intro w y
    rw [hΦ]
    simp only [map_zero, zero_add]
  let Q : V × V →ₗ[ℝ] V × V :=
    (LinearMap.inr ℝ V V) ∘ₗ (LinearMap.fst ℝ V V) + Jm ∘ₗ (LinearMap.inr ℝ V V) ∘ₗ (LinearMap.snd ℝ V V)
  let Θ : V × V →ₗ[ℝ] (V → ℂ) := Φ ∘ₗ Q
  have hΘ : ∀ w₁ w₂ y, Θ (w₁, w₂) y = (-(2 * Real.pi * Complex.I)) * ((T y w₁ : ℝ) : ℂ) * f₀ y +
      Complex.I * ((-(2 * Real.pi * Complex.I)) * ((T y w₂ : ℝ) : ℂ) * f₀ y) := by
    intro w₁ w₂ y
    have e : Θ (w₁, w₂) = Φ (0, w₁) + Φ (Jm (0, w₂)) := map_add Φ _ _
    rw [e, Pi.add_apply, hEΦ, hΦ0, hΦ0]
  obtain ⟨y₀, hy₀⟩ : ∃ y₀, f₀ y₀ ≠ 0 := by
    by_contra h
    push Not at h
    exact hf (SchwartzMap.ext fun y => by simp [h y])
  have hU : {y | f₀ y ≠ 0} ∈ 𝓝 y₀ := (isOpen_compl_singleton.preimage f₀.continuous).mem_nhds hy₀
  have hc : (-(2 * Real.pi * Complex.I) : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, Complex.I_ne_zero]
  have hinj : Function.Injective Θ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    rintro ⟨w₁, w₂⟩ h
    have hsplit : ∀ y ∈ {y | f₀ y ≠ 0}, T y w₁ = 0 ∧ T y w₂ = 0 := by
      intro y hy
      have h0 : Θ (w₁, w₂) y = 0 := by rw [h]; rfl
      rw [hΘ] at h0
      have h3 : ((T y w₁ : ℝ) : ℂ) + Complex.I * ((T y w₂ : ℝ) : ℂ) = 0 := by
        have h4 : (-(2 * Real.pi * Complex.I)) * f₀ y *
            (((T y w₁ : ℝ) : ℂ) + Complex.I * ((T y w₂ : ℝ) : ℂ)) = 0 := by
          rw [← h0]; ring
        rcases mul_eq_zero.mp h4 with h5 | h5
        · rcases mul_eq_zero.mp h5 with h6 | h6
          · exact absurd h6 hc
          · exact absurd h6 hy
        · exact h5
      have hre := congrArg Complex.re h3
      have him := congrArg Complex.im h3
      simp at hre him
      exact ⟨hre, him⟩
    have e1 := eq_zero_of_forall_nhds T hT y₀ _ hU w₁ fun y hy => (hsplit y hy).1
    have e2 := eq_zero_of_forall_nhds T hT y₀ _ hU w₂ fun y hy => (hsplit y hy).2
    rw [e1, e2]; rfl
  have hle : LinearMap.range Θ ≤ LinearMap.range Φ := LinearMap.range_comp_le_range Q Φ
  have hrange : LinearMap.range Θ = LinearMap.range Φ := by
    apply Submodule.eq_of_le_of_finrank_le hle
    rw [LinearMap.finrank_range_of_inj hinj]
    exact LinearMap.finrank_range_le Φ
  have hmem : ∀ a, (Φ ∘ₗ LinearMap.inl ℝ V V) a ∈ LinearMap.range Θ := fun a => by
    rw [hrange]; exact LinearMap.mem_range_self Φ _
  let e := LinearEquiv.ofInjective Θ hinj
  let W : V →ₗ[ℝ] V × V :=
    e.symm.toLinearMap ∘ₗ LinearMap.codRestrict (LinearMap.range Θ) (Φ ∘ₗ LinearMap.inl ℝ V V) hmem
  have hW : ∀ a, Θ (W a) = Φ (a, 0) := by
    intro a
    have h := congrArg Subtype.val (e.apply_symm_apply ⟨Φ (a, 0), hmem a⟩)
    exact h
  let m : V →ₗ[ℝ] V →ₗ[ℝ] ℂ := LinearMap.mk₂ ℝ
    (fun a y => (-(2 * Real.pi * Complex.I)) * ((T y (W a).1 : ℝ) : ℂ) +
      Complex.I * ((-(2 * Real.pi * Complex.I)) * ((T y (W a).2 : ℝ) : ℂ)))
    (by intro a₁ a₂ y; simp only [map_add, Prod.fst_add, Prod.snd_add, Complex.ofReal_add]; ring)
    (by intro s a y; simp only [map_smul, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, Complex.ofReal_mul,
      Complex.real_smul]; ring)
    (by intro a y₁ y₂; simp only [map_add, LinearMap.add_apply, Complex.ofReal_add]; ring)
    (by intro s a y; simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, Complex.ofReal_mul,
      Complex.real_smul]; ring)
  refine ⟨m, fun a y => ?_⟩
  have h1 : Φ (a, 0) y = fderiv ℝ f₀ y a := by
    rw [hΦ]; simp only [map_zero, Complex.ofReal_zero, mul_zero, zero_mul, add_zero]
  have h2 := hΘ (W a).1 (W a).2 y
  rw [Prod.mk.eta, hW, h1] at h2
  rw [h2]
  show _ = ((-(2 * Real.pi * Complex.I)) * ((T y (W a).1 : ℝ) : ℂ) +
      Complex.I * ((-(2 * Real.pi * Complex.I)) * ((T y (W a).2 : ℝ) : ℂ))) * f₀ y
  ring
end GlobalTheory.CompanionTheory.Twist.FockLogDeriv
