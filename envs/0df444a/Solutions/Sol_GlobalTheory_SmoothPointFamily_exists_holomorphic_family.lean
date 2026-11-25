-- Prove2me | solution 1 for GlobalTheory.SmoothPointFamily.exists_holomorphic_family
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:42:33.27009+00:00
-- url     : https://prove2.me/submissions/efb877d2-b8fc-4f94-bc54-49effccca0e8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ChainRuleAndJacobianCriterion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsHolomorphicSections
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_ExistsHolomorphicFamily
import Theorems.Thm_GlobalTheory_SmoothPointFamily_exists_etale_away
import Theorems.Thm_GlobalTheory_SmoothPointFamily_exists_finset_of_mem_nhds
import Theorems.Thm_GlobalTheory_EtaleFamily_exists_holomorphic_sections


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Topology
open GlobalTheory GlobalTheory.SmoothPointFamily
open KaehlerDifferential
namespace GlobalTheory.SmoothPointFamily
theorem _root_.solution : ∀ (K A : Type) [Field K] [CharZero K] [CommRing A] [Algebra K A] [Algebra.Smooth K A] (σ : K →+* ℂ) (φ₀ : A →+* ℂ), φ₀.comp (algebraMap K A) = σ → ∃ (m : ℕ) (s : Fin m → A) (B : Set (Fin m → ℂ)) (φ : (Fin m → ℂ) → (A →+* ℂ)) (S : Finset A) (ε : ℝ), IsOpen B ∧ 0 < ε ∧ (∀ b ∈ B, (φ b).comp (algebraMap K A) = σ ∧ ∀ i, φ b (s i) = b i) ∧ (∀ a : A, DifferentiableOn ℂ (fun b => φ b a) B) ∧ ∀ ψ : A →+* ℂ, ψ.comp (algebraMap K A) = σ → (∀ a ∈ S, ‖ψ a - φ₀ a‖ < ε) → (fun i => ψ (s i)) ∈ B ∧ φ (fun i => ψ (s i)) = ψ := by
  intro K A _ _ _ _ _ σ φ₀ h₀
  haveI : (RingHom.ker φ₀).IsPrime := RingHom.ker_isPrime φ₀
  obtain ⟨g, m, s, hg, het⟩ := exists_etale_away (R := K) (RingHom.ker φ₀)
  have hg₀ : φ₀ g ≠ 0 := hg
  let R := Localization.Away g
  let ι : A →+* R := algebraMap A R
  let L : (ψ : A →+* ℂ) → ψ g ≠ 0 → (R →+* ℂ) := fun ψ h =>
    IsLocalization.Away.lift g (g := ψ) (isUnit_iff_ne_zero.2 h)
  have hL : ∀ ψ h a, L ψ h (ι a) = ψ a := fun ψ h a => IsLocalization.Away.lift_eq g _ a
  let P : MvPolynomial (Fin m) K →+* R := MvPolynomial.eval₂Hom (algebraMap K R) fun i => ι (s i)
  have hPC : ∀ k, P (MvPolynomial.C k) = ι (algebraMap K A k) := fun k => by
    simp only [P, MvPolynomial.eval₂Hom_C]
    exact IsScalarTower.algebraMap_apply K A R k
  have hPX : ∀ i, P (MvPolynomial.X i) = ι (s i) := fun i => by simp [P]
  have hLC : ∀ (ψ : A →+* ℂ) h, ψ.comp (algebraMap K A) = σ →
      ∀ k, L ψ h (P (MvPolynomial.C k)) = σ k := fun ψ h hψ k => by
    rw [hPC, hL ψ h, ← hψ]; rfl
  obtain ⟨N, τ, n, f, O, hN, hO, hO₀, hd, hτ, hrec⟩ :=
    GlobalTheory.EtaleFamily.exists_holomorphic_sections 0 m K R P Set.univ (fun _ => σ) 0 (L φ₀ hg₀) het
      isOpen_univ trivial (fun a => differentiableOn_const _) (hLC φ₀ hg₀ h₀)
  choose k c hc using fun j => IsLocalization.Away.surj g (f j)
  have hval : ∀ ψ h j, L ψ h (f j) = ψ (c j) / ψ g ^ k j := fun ψ h j => by
    have := congrArg (L ψ h) (hc j)
    rw [map_mul, map_pow, hL ψ h, hL ψ h] at this
    rw [← this, mul_div_cancel_right₀ _ (pow_ne_zero _ h)]
  have hcont : ContinuousAt
      (fun y : A → ℂ => ((0 : Fin 0 → ℂ), fun j => y (c j) / y g ^ k j)) φ₀ :=
    continuousAt_const.prodMk (continuousAt_pi.2 fun j =>
      (continuous_apply (c j)).continuousAt.div ((continuous_apply g).pow _).continuousAt
        (pow_ne_zero _ hg₀))
  have hU : {y : A → ℂ | y g ≠ 0 ∧ ((0 : Fin 0 → ℂ), fun j => y (c j) / y g ^ k j) ∈ O} ∈
      𝓝 (φ₀ : A → ℂ) := by
    refine Filter.Eventually.and ((continuous_apply g).continuousAt.eventually_ne hg₀)
      (hcont (hO.mem_nhds ?_))
    simpa only [hval] using hO₀
  obtain ⟨S, ε, hε, hS⟩ := exists_finset_of_mem_nhds hU
  have hin : Differentiable ℂ fun b : Fin m → ℂ => ((0 : Fin 0 → ℂ), b) :=
    (differentiable_const _).prodMk differentiable_id
  refine ⟨m, s, (fun b => ((0 : Fin 0 → ℂ), b)) ⁻¹' N, fun b => (τ (0, b)).comp ι, S, ε,
    hN.preimage hin.continuous, hε, fun b hb => ⟨RingHom.ext fun a => ?_, fun i => ?_⟩,
    fun a => (hd (ι a)).comp hin.differentiableOn fun _ h => h, fun ψ hψ hψS => ?_⟩
  · rw [RingHom.comp_apply, RingHom.comp_apply, ← hPC]
    exact (hτ _ hb).2.1 a
  · rw [RingHom.comp_apply, ← hPX]
    exact (hτ _ hb).2.2 i
  · obtain ⟨h1, h2⟩ := hS ψ hψS
    obtain ⟨h3, h4⟩ := hrec 0 (L ψ h1) (hLC ψ h1 hψ) (by simpa only [hval] using h2)
    simp only [hPX, hL ψ h1] at h3 h4
    refine ⟨h3, RingHom.ext fun a => ?_⟩
    rw [RingHom.comp_apply, h4, hL ψ h1]
end GlobalTheory.SmoothPointFamily
