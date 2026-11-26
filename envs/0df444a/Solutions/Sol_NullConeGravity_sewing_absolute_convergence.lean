-- Prove2me | solution 1 for NullConeGravity.sewing_absolute_convergence
-- status  : ACCEPTED   (prove)
-- author  : @scuba8684
-- created : 2026-11-26T19:28:28.717398+00:00
-- url     : https://prove2.me/submissions/31f62f09-65b2-49b9-85cf-3ab4e53fd5de

import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Tactic.NormNum

private theorem basisSewing {ι E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] (b : HilbertBasis ι ℂ E) (x y : E) :
    Summable (fun i => ‖inner ℂ x (b i) * inner ℂ (b i) y‖) ∧
    (∑' i, inner ℂ x (b i) * inner ℂ (b i) y) = inner ℂ x y ∧
    (∑' i, ‖inner ℂ x (b i) * inner ℂ (b i) y‖) ≤ ‖x‖ * ‖y‖ := by
  have h := lp.tsum_mul_le_mul_norm (by rw [Real.holderConjugate_iff]; norm_num)
    (b.repr x) (b.repr y)
  have hnorm (i : ι) : ‖inner ℂ x (b i) * inner ℂ (b i) y‖ =
      ‖b.repr x i‖ * ‖b.repr y i‖ := by
    rw [norm_mul, b.repr_apply_apply, b.repr_apply_apply, norm_inner_symm (𝕜 := ℂ) x (b i)]
  refine ⟨?_, b.tsum_inner_mul_inner x y, ?_⟩
  · simpa only [hnorm] using h.1
  · simpa only [hnorm, LinearIsometryEquiv.norm_map] using h.2

theorem solution {ι : Type*} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] (e : ι → E) (he : Orthonormal ℂ e)
    (htotal : (Submodule.span ℂ (Set.range e)).topologicalClosure = ⊤)
    (U₁ U₂ : E ≃ₗᵢ[ℂ] E) (φ ψ : E) :
    Summable (fun i : ι => ‖inner ℂ φ (U₂ (e i)) * inner ℂ (e i) (U₁ ψ)‖) ∧
    (∑' i : ι, inner ℂ φ (U₂ (e i)) * inner ℂ (e i) (U₁ ψ)) = inner ℂ φ (U₂ (U₁ ψ)) ∧
    (∑' i : ι, ‖inner ℂ φ (U₂ (e i)) * inner ℂ (e i) (U₁ ψ)‖) ≤ ‖φ‖ * ‖ψ‖ := by
  let b := HilbertBasis.mk he htotal.ge
  have hb : (b : ι → E) = e := HilbertBasis.coe_mk _ _
  have move (z : E) : inner ℂ φ (U₂ z) = inner ℂ (U₂.symm φ) z := by
    simpa only [LinearIsometryEquiv.symm_apply_apply] using (U₂.symm.inner_map_map φ (U₂ z)).symm
  simpa only [hb, ← move, LinearIsometryEquiv.norm_map] using basisSewing b (U₂.symm φ) (U₁ ψ)
