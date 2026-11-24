-- Prove2me | solution 1 for GlobalTheory.Published.Landherr.congr_conjugate
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T19:39:57.027206+00:00
-- url     : https://prove2.me/submissions/bd61da7e-af97-4c32-b47b-e1da54f71440

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_AdelicLattices__AlgebraMapNormOfBasisOneSqrt_07cf76d090f2548e

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
theorem _root_.solution (τ : E →+* ℂ)
    (h : ∃ Q : Matrix (Fin r) (Fin r) ℂ, Q.det ≠ 0 ∧ G'.map τ = Qᵀ * G.map τ * Q.map conj) :
    ∃ Q : Matrix (Fin r) (Fin r) ℂ, Q.det ≠ 0 ∧ G'.map (ComplexEmbedding.conjugate τ) =
      Qᵀ * G.map (ComplexEmbedding.conjugate τ) * Q.map conj := by
  obtain ⟨Q, hQ, h⟩ := h
  refine ⟨Q.map conj, ?_, ?_⟩
  · have : (Q.map conj).det = conj Q.det := (RingHom.map_det (starRingEnd ℂ) Q).symm
    rw [this]
    exact (map_ne_zero _).mpr hQ
  · have e : ∀ M : Matrix (Fin r) (Fin r) E,
        M.map (ComplexEmbedding.conjugate τ) = (M.map τ).map conj := fun M => rfl
    rw [e, e, h, Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map]
end GlobalTheory.Published.Landherr
