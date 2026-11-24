-- Prove2me | solution 1 for GlobalTheory.GaussTransport.transport
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T20:32:54.981552+00:00
-- url     : https://prove2.me/submissions/580c06bc-d41f-4eb0-840f-a6a589a82eb8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzDensityTransportLinearEquivChirp
import Theorems.Thm_GlobalTheory_GaussTransport_hasTemperateGrowth_chirp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open FourierTransform MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.GaussTransport
open LineDeriv
namespace GlobalTheory.GaussTransport
theorem _root_.solution : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (A : V ≃L[ℝ] E) (Q : V →L[ℝ] V →L[ℝ] ℂ) (N : Submodule ℂ (SchwartzMap V ℂ)),
    (∀ x, Real.pi * ‖A x‖ ^ 2 = (Q x x).re) →
    (∀ (v : V) (f f₁ : SchwartzMap V ℂ), f ∈ N → (∀ x, f₁ x = fderiv ℝ (⇑f) x v) → f₁ ∈ N) →
    (∀ (ℓ : V →L[ℝ] ℝ) (f f₁ : SchwartzMap V ℂ), f ∈ N → (∀ x, f₁ x = (ℓ x : ℂ) * f x) → f₁ ∈ N) →
    ∃ N₂ : Submodule ℂ (SchwartzMap E ℂ),
      (∀ (v : E) (f f₁ : SchwartzMap E ℂ), f ∈ N₂ → (∀ x, f₁ x = fderiv ℝ (⇑f) x v) → f₁ ∈ N₂) ∧
      (∀ (ℓ : E →L[ℝ] ℝ) (f f₁ : SchwartzMap E ℂ), f ∈ N₂ → (∀ x, f₁ x = (ℓ x : ℂ) * f x) → f₁ ∈ N₂) ∧
      (∀ (g : SchwartzMap V ℂ) (G : SchwartzMap E ℂ), (∀ x, g x = Complex.exp (-(Q x x))) → g ∈ N →
        (∀ y, G y = Complex.exp (-((Real.pi * ‖y‖ ^ 2 : ℝ) : ℂ))) → G ∈ N₂) ∧
      (Dense (N₂ : Set (SchwartzMap E ℂ)) → Dense (N : Set (SchwartzMap V ℂ))) := by
  intro V _ _ _ E _ _ _ A Q N hQ hD hL
  set χ : V → ℂ := fun x => Complex.exp (Complex.I * ((-1 * (Q x x).im : ℝ) : ℂ)) with hχdef
  set χi : V → ℂ := fun x => Complex.exp (Complex.I * ((1 * (Q x x).im : ℝ) : ℂ)) with hχidef
  have hχ : χ.HasTemperateGrowth := hasTemperateGrowth_chirp Q (-1)
  have hχi : χi.HasTemperateGrowth := hasTemperateGrowth_chirp Q 1
  have hχχi : ∀ x, χ x * χi x = 1 := by
    intro x
    simp only [hχdef, hχidef, ← Complex.exp_add]
    rw [← Complex.exp_zero]; congr 1; push_cast; ring
  let Ψ : SchwartzMap E ℂ →L[ℂ] SchwartzMap V ℂ :=
    (SchwartzMap.smulLeftCLM ℂ χ).comp (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ A)
  have hΨ : ∀ f x, Ψ f x = χ x * f (A x) := by
    intro f x
    simp [Ψ, SchwartzMap.smulLeftCLM_apply_apply hχ]
  refine ⟨N.comap (Ψ : SchwartzMap E ℂ →ₗ[ℂ] SchwartzMap V ℂ), ?_, ?_, ?_, ?_⟩
  · intro w f f₁ hf hf₁
    rw [Submodule.mem_comap] at hf ⊢
    simp only [ContinuousLinearMap.coe_coe] at hf ⊢
    set v : V := A.symm w with hv
    let lam : V →L[ℝ] ℝ := Complex.imCLM.comp (Q.flip v + Q v)
    have hlam : ∀ x, lam x = (Q x v).im + (Q v x).im := by intro x; simp [lam]
    have hlamT : (fun x : V => ((lam x : ℝ) : ℂ)).HasTemperateGrowth :=
      (Complex.ofRealCLM.comp lam).hasTemperateGrowth
    have h1N : ∂_{v} (Ψ f) ∈ N := hD v (Ψ f) _ hf (fun x => SchwartzMap.lineDerivOp_apply_eq_fderiv v (Ψ f) x)
    have h2N : SchwartzMap.smulLeftCLM ℂ (fun x : V => ((lam x : ℝ) : ℂ)) (Ψ f) ∈ N :=
      hL lam (Ψ f) _ hf (fun x => by rw [SchwartzMap.smulLeftCLM_apply_apply hlamT, smul_eq_mul])
    have hder : ∀ x, fderiv ℝ (⇑(Ψ f)) x v =
        χ x * fderiv ℝ (⇑f) (A x) w - Complex.I * ((lam x : ℂ) * (χ x * f (A x))) := by
      intro x
      have hfun : (⇑(Ψ f)) = χ * (fun y => f (A y)) := funext (hΨ f)
      let L : ℂ →L[ℝ] ℂ := Complex.ofRealCLM.comp ((-1 : ℝ) • Complex.imCLM)
      have hq := Q.hasFDerivAt_of_bilinear (hasFDerivAt_id x) (hasFDerivAt_id x)
      have hu := ((L.hasFDerivAt).comp x hq).const_mul Complex.I
      have hχd : HasFDerivAt χ (Complex.exp (Complex.I * L (Q x x)) • (Complex.I • (L.comp
          (((ContinuousLinearMap.precompR V Q) (id x)) (ContinuousLinearMap.id ℝ V) +
            ((ContinuousLinearMap.precompL V Q) (ContinuousLinearMap.id ℝ V)) (id x))))) x := by
        refine hu.cexp.congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => ?_)
        simp [χ, L]
      have hfA : HasFDerivAt (fun y => f (A y)) ((fderiv ℝ (⇑f) (A x)).comp (A : V →L[ℝ] E)) x :=
        (f.differentiableAt.hasFDerivAt).comp x A.hasFDerivAt
      rw [hfun, (hχd.mul hfA).fderiv]
      have hχx : χ x = Complex.exp (-(Complex.I * ((Q x x).im : ℂ))) := by simp [χ]
      simp [L, v, hlam]
      rw [hχx]
      ring
    have hsum : Ψ f₁ = ∂_{v} (Ψ f) + Complex.I • SchwartzMap.smulLeftCLM ℂ (fun x : V => ((lam x : ℝ) : ℂ)) (Ψ f) := by
      ext x
      rw [SchwartzMap.add_apply, SchwartzMap.smul_apply, SchwartzMap.smulLeftCLM_apply_apply hlamT,
        SchwartzMap.lineDerivOp_apply_eq_fderiv, hder, hΨ, hΨ, hf₁, smul_eq_mul, smul_eq_mul]
      ring
    rw [hsum]
    exact N.add_mem h1N (N.smul_mem _ h2N)
  · intro ℓ f f₁ hf hf₁
    rw [Submodule.mem_comap] at hf ⊢
    simp only [ContinuousLinearMap.coe_coe] at hf ⊢
    refine hL (ℓ.comp (A : V →L[ℝ] E)) (Ψ f) (Ψ f₁) hf (fun x => ?_)
    rw [hΨ, hΨ, hf₁]
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe]
    ring
  · intro g G hg hgN hG
    rw [Submodule.mem_comap]
    simp only [ContinuousLinearMap.coe_coe]
    have hΨG : Ψ G = g := by
      ext x
      rw [hΨ, hG, hg, hχdef]
      simp only
      rw [← Complex.exp_add]
      congr 1
      conv_rhs => rw [← Complex.re_add_im (Q x x)]
      rw [← hQ x]
      push_cast
      ring
    rw [hΨG]; exact hgN
  · intro hd
    have hsurj : Function.Surjective Ψ := by
      intro k
      refine ⟨SchwartzMap.compCLMOfContinuousLinearEquiv ℂ A.symm (SchwartzMap.smulLeftCLM ℂ χi k), ?_⟩
      ext x
      rw [hΨ]
      simp only [SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply,
        ContinuousLinearEquiv.symm_apply_apply, SchwartzMap.smulLeftCLM_apply_apply hχi, smul_eq_mul]
      rw [← mul_assoc, hχχi, one_mul]
    refine (hsurj.denseRange.dense_image Ψ.continuous hd).mono ?_
    rintro _ ⟨f, hf, rfl⟩
    exact hf
end GlobalTheory.GaussTransport
