-- Prove2me | solution 1 for GlobalTheory.Published.Landherr.congr_of_signature
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:55:15.538414+00:00
-- url     : https://prove2.me/submissions/d6e07195-a3ba-4a4b-b868-820101892d72

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_AdelicLattices__AlgebraMapNormOfBasisOneSqrt_07cf76d090f2548e
import Theorems.Thm_GlobalTheory_Published_Landherr_congr_of_gram_eq
import Theorems.Thm_GlobalTheory_Published_Landherr_congr_conjugate

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
open scoped Matrix TensorProduct ComplexConjugate
open ReciprocityTheory.ChartRestriction.G.FD
open GlobalTheory GlobalTheory.Published
open GlobalTheory.Published.Landherr
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
  {G G' : Matrix (Fin r) (Fin r) E}
omit [NumberField E] [IsCMField E]
namespace GlobalTheory.Published.Landherr
theorem _root_.solution (Ψ : Set (E →+* ℂ))
    (hΨ : ∀ τ : E →+* ℂ, τ ∈ Ψ ∨ ComplexEmbedding.conjugate τ ∈ Ψ)
    (hs : ∀ τ ∈ Ψ, ∃ p : ℕ,
      (∃ Q : Matrix (Fin r) (Fin r) ℂ, Q.det ≠ 0 ∧
        gram τ G Q = Matrix.diagonal fun a : Fin r => ((sgn p (a : ℕ) : ℝ) : ℂ)) ∧
      ∃ Q : Matrix (Fin r) (Fin r) ℂ, Q.det ≠ 0 ∧
        gram τ G' Q = Matrix.diagonal fun a : Fin r => ((sgn p (a : ℕ) : ℝ) : ℂ))
    (τ : E →+* ℂ) :
    ∃ Q : Matrix (Fin r) (Fin r) ℂ, Q.det ≠ 0 ∧ G'.map τ = Qᵀ * G.map τ * Q.map conj := by
  have key : ∀ σ ∈ Ψ, ∃ Q : Matrix (Fin r) (Fin r) ℂ, Q.det ≠ 0 ∧
      G'.map σ = Qᵀ * G.map σ * Q.map conj := by
    intro σ hσ
    obtain ⟨p, ⟨Q, hQ, h⟩, Q', hQ', h'⟩ := hs σ hσ
    exact congr_of_gram_eq σ hQ hQ' (h.trans h'.symm)
  rcases hΨ τ with h | h
  · exact key τ h
  · have := congr_conjugate _ (key _ h)
    rwa [show ComplexEmbedding.conjugate (ComplexEmbedding.conjugate τ) = τ from star_star τ] at this
end GlobalTheory.Published.Landherr
