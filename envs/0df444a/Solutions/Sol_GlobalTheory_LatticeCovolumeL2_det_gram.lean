-- Prove2me | solution 1 for GlobalTheory.LatticeCovolumeL2.det_gram
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:02:17.15391+00:00
-- url     : https://prove2.me/submissions/430b42f8-3ea1-41a2-8794-a4f8c9c302a4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsLineBasis

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.LatticeCovolumeL2
open NumberField Matrix
variable {E : Type} [Field E] [NumberField E]
namespace GlobalTheory.LatticeCovolumeL2
theorem _root_.solution {ι : Type} [Fintype ι] [DecidableEq ι] (hι : Fintype.card ι = Module.finrank ℚ E)
    (Ψ : Finset (E →+* ℂ)) (hΨ : ∀ τ : E →+* ℂ, τ ∈ Ψ ↔ ComplexEmbedding.conjugate τ ∉ Ψ)
    (a : ι → E) (s : Ψ → ℝ) (G : Matrix ι ι ℝ)
    (hG : ∀ k l, G k l = ∑ τ : Ψ, (τ.1 (a k) * (starRingEnd ℂ) (τ.1 (a l))).re * s τ) :
    G.det = |((Algebra.discr ℚ a : ℚ) : ℝ)| * (∏ τ, (s τ / 2)) ^ 2 := by
  let κ := Ψ ⊕ Ψ
  let e1 : κ ≃ (E →+* ℂ) := cmEquiv Ψ hΨ
  have hcard : Fintype.card ι = Fintype.card κ := by
    rw [hι, Fintype.card_congr e1, NumberField.Embeddings.card]
  let f : ι ≃ κ := Fintype.equivOfCardEq hcard
  let e2 : ι ≃ (E →ₐ[ℚ] ℂ) := (f.trans e1).trans (RingHom.equivRatAlgHom E ℂ)
  let B : Matrix ι ι ℂ := Algebra.embeddingsMatrixReindex ℚ ℂ a e2
  have hB : ∀ k j, B k j = e1 (f j) (a k) := fun k j => rfl
  let d : κ → ℂ := fun σ => Sum.elim (fun τ => ((s τ : ℂ) / 2)) (fun τ => ((s τ : ℂ) / 2)) σ
  let Dm : Matrix ι ι ℂ := Matrix.diagonal (fun j => d (f j))
  let Cm : Matrix ι ι ℂ := (B.map (starRingEnd ℂ))ᵀ
  have hGm : G.map (fun x : ℝ => (x : ℂ)) = B * Dm * Cm := by
    ext k l
    rw [Matrix.map_apply, hG k l, Matrix.mul_apply]
    simp only [Dm, Cm, Matrix.mul_diagonal, Matrix.transpose_apply, Matrix.map_apply, hB]
    rw [Equiv.sum_comp f (fun σ => e1 σ (a k) * d σ * (starRingEnd ℂ) (e1 σ (a l))),
      Fintype.sum_sum_type]
    push_cast
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun τ _ => ?_
    have he1l : e1 (Sum.inl τ) = τ.1 := rfl
    have he1r : e1 (Sum.inr τ) = ComplexEmbedding.conjugate τ.1 := rfl
    simp only [he1l, he1r, d, Sum.elim_inl, Sum.elim_inr, ComplexEmbedding.conjugate_coe_eq,
      Complex.conj_conj]
    rw [Complex.re_eq_add_conj, map_mul, Complex.conj_conj]
    ring
  have hdisc : algebraMap ℚ ℂ (Algebra.discr ℚ a) = B.det ^ 2 :=
    Algebra.discr_eq_det_embeddingsMatrixReindex_pow_two ℚ ℂ a e2
  have hdetG : ((G.det : ℝ) : ℂ) = B.det * (starRingEnd ℂ) B.det * (∏ τ, ((s τ : ℂ) / 2)) ^ 2 := by
    have h1 : ((G.det : ℝ) : ℂ) = (G.map (fun x : ℝ => (x : ℂ))).det :=
      RingHom.map_det Complex.ofRealHom G
    have h2 : (B.map (starRingEnd ℂ)).det = (starRingEnd ℂ) B.det := (RingHom.map_det _ B).symm
    rw [h1, hGm, det_mul, det_mul, det_diagonal, det_transpose, h2,
      Equiv.prod_comp f d, Fintype.prod_sum_type]
    simp only [d, Sum.elim_inl, Sum.elim_inr]
    ring
  have hn : ((|((Algebra.discr ℚ a : ℚ) : ℝ)| : ℝ) : ℂ) = B.det * (starRingEnd ℂ) B.det := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, ← norm_pow, ← hdisc]
    congr 1
    rw [eq_ratCast, Complex.norm_ratCast]
  apply Complex.ofReal_injective
  rw [hdetG, Complex.ofReal_mul, hn, Complex.ofReal_pow, Complex.ofReal_prod]
  simp only [Complex.ofReal_div, Complex.ofReal_ofNat]
end GlobalTheory.LatticeCovolumeL2
