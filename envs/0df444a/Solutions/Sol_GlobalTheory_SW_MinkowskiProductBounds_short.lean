-- Prove2me | solution 1 for GlobalTheory.SW.MinkowskiProductBounds.short
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T01:01:48.263836+00:00
-- url     : https://prove2.me/submissions/2292f2ef-e4fa-44e5-a204-7ed4dacf29fa

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsNeZeroNormSqLeMulCovolumeRpow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsShortIso
import Theorems.Thm_GlobalTheory_SW_MinkowskiProductBounds_mink
import Theorems.Thm_GlobalTheory_SW_MinkowskiProductBounds_basis_many
import Theorems.Thm_GlobalTheory_SW_MinkowskiProductBounds_fac
import Theorems.Thm_GlobalTheory_SW_MinkowskiProductBounds_hval_eq
import Theorems.Thm_GlobalTheory_spanCovol_bot
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.spanCovol_bot



set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.MinkowskiProductBounds
open Module Submodule
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Ψ : Finset (E →+* ℂ)}
namespace GlobalTheory.SW.MinkowskiProductBounds
theorem _root_.solution (h : IsType Ψ) (m : ℕ) (Δ ε : ℝ) (hε : 0 < ε) : ∃ (n : ℕ) (C : ℝ),
    ∀ H : CM Ψ m m, (∀ τ, (H τ).PosDef) → ∏ τ, ‖(H τ).det‖ ≤ Δ →
    (∀ v : Fin m → E, v ≠ 0 → (∀ a, IsIntegral ℤ (v a)) → ε ≤ ∑ τ, hval Ψ H τ v) →
    ∃ V : Matrix (Fin n) (Fin m) E, IntM V ∧ (∃ S : Matrix (Fin m) (Fin n) E, S * V = 1) ∧
      ∀ i τ, hval Ψ H τ (V i) ≤ C := by
  classical
  obtain ⟨b, hb⟩ := basis_many h m
  let e : (Ψ → Fin m → ℂ) ≃ₗ[ℝ] PiLp 2 (fun _ : Ψ => EuclideanSpace ℂ (Fin m)) :=
    (LinearEquiv.piCongrRight fun _ => (WithLp.linearEquiv 2 ℝ (Fin m → ℂ)).symm).trans
      (WithLp.linearEquiv 2 ℝ _).symm
  have he : ∀ x, ‖e x‖ ^ 2 = ∑ τ, ‖WithLp.toLp 2 (x τ)‖ ^ 2 := fun x =>
    PiLp.norm_sq_eq_of_L2 _ _
  obtain ⟨C, hC⟩ := mink b e Δ (√ε) (Real.sqrt_pos.2 hε)
  refine ⟨finrank ℝ (PiLp 2 fun _ : Ψ => EuclideanSpace ℂ (Fin m)), C ^ 2,
    fun H hH hΔ hmin => ?_⟩
  choose B hB1 hB2 hB3 using fun τ => fac (hH τ)
  let T : (Ψ → Fin m → ℂ) →ₗ[ℝ] (Ψ → Fin m → ℂ) := LinearMap.pi fun τ =>
    ((Matrix.toLin' (B τ)ᵀ).restrictScalars ℝ).comp (LinearMap.proj τ)
  have hT : ∀ x τ, T x τ = x τ ᵥ* B τ := fun x τ => by simp [T, mulVec_transpose]
  have hdet : LinearMap.det T = ∏ τ, ‖(H τ).det‖ := by
    rw [LinearMap.det_pi]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [LinearMap.det_restrictScalars, Algebra.norm_complex_apply, LinearMap.det_toLin',
      det_transpose, hB1 τ, det_mul, det_conjTranspose, norm_mul, norm_star, Complex.normSq_eq_norm_sq,
      sq]
  have hq : ∀ v : Fin m → E, ‖e (T fun τ a => τ.1 (v a))‖ ^ 2 = ∑ τ, hval Ψ H τ v := by
    intro v
    rw [he]
    exact Finset.sum_congr rfl fun τ _ => by rw [hT, hval_eq, hB3]
  obtain ⟨v, hv⟩ := hC T
    (by rw [hdet]; exact Finset.prod_ne_zero_iff.2 fun τ _ => norm_ne_zero_iff.2 (hH τ).det_pos.ne')
    (by rwa [hdet, abs_of_nonneg (Finset.prod_nonneg fun _ _ => norm_nonneg _)])
    (by
      intro x hx h0
      obtain ⟨w, hw, rfl⟩ := (hb x).1 hx
      rw [Real.sqrt_le_left (norm_nonneg _), hq]
      exact hmin w (by rintro rfl; exact h0 (by ext; simp)) hw)
  choose w hw hvw using fun i => (hb _).1 (hv i).1
  refine ⟨Matrix.of w, fun i a => hw i a, ?_, fun i τ => ?_⟩
  · have hinj : LinearMap.ker (Matrix.toLin' (Matrix.of w)) = ⊥ := by
      rw [LinearMap.ker_eq_bot']
      intro c hc
      obtain ⟨σ⟩ : Nonempty (E →+* ℂ) := inferInstance
      obtain ⟨τ⟩ : Nonempty Ψ := by
        by_cases hσ : σ ∈ Ψ
        · exact ⟨⟨σ, hσ⟩⟩
        · exact ⟨⟨ComplexEmbedding.conjugate σ, by have := h σ; tauto⟩⟩
      let l : (Ψ → Fin m → ℂ) →ₗ[ℝ] ℂ :=
        { toFun := fun x => ∑ a, x τ a * τ.1 (c a)
          map_add' := fun x y => by simp [add_mul, Finset.sum_add_distrib]
          map_smul' := fun r x => by simp [Finset.mul_sum, mul_assoc] }
      have hl : l = 0 := v.ext fun i => by
        have := congrArg τ.1 (congrFun hc i)
        rw [hvw i]
        simpa [l, mulVec, dotProduct] using this
      ext a
      have := LinearMap.congr_fun hl fun _ => Pi.single a 1
      simpa [l, Pi.single_apply] using this
    obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective _ hinj
    refine ⟨LinearMap.toMatrix' g, ?_⟩
    have := congrArg LinearMap.toMatrix' hg
    rwa [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_toLin', LinearMap.toMatrix'_id] at this
  · have h1 := (hv i).2
    rw [hvw i] at h1
    have h2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    rw [hq] at h2
    refine le_trans ?_ h2
    exact Finset.single_le_sum (f := fun τ => hval Ψ H τ (w i))
      (fun τ _ => by rw [hval_eq, hB3]; positivity) (Finset.mem_univ τ)
end GlobalTheory.SW.MinkowskiProductBounds
