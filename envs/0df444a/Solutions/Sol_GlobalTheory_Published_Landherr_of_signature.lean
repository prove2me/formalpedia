-- Prove2me | solution 1 for GlobalTheory.Published.Landherr.of_signature
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T20:14:10.449921+00:00
-- url     : https://prove2.me/submissions/253fc79a-555e-4eef-a83a-ded14fbc1b10

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_AdelicLattices__AlgebraMapNormOfBasisOneSqrt_07cf76d090f2548e
import Theorems.Thm_GlobalTheory_Published_Landherr_congr_of_signature

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
namespace GlobalTheory.Published.Landherr
theorem _root_.solution (H : Landherr) (hG : ∀ a b, cc (G a b) = G b a)
    (hG' : ∀ a b, cc (G' a b) = G' b a) (hd : G.det ≠ 0) (hd' : G'.det ≠ 0)
    (Ψ : Set (E →+* ℂ)) (hΨ : ∀ τ : E →+* ℂ, τ ∈ Ψ ∨ ComplexEmbedding.conjugate τ ∈ Ψ)
    (hs : ∀ τ ∈ Ψ, ∃ p : ℕ,
      (∃ Q : Matrix (Fin r) (Fin r) ℂ, Q.det ≠ 0 ∧
        gram τ G Q = Matrix.diagonal fun a : Fin r => ((sgn p (a : ℕ) : ℝ) : ℂ)) ∧
      ∃ Q : Matrix (Fin r) (Fin r) ℂ, Q.det ≠ 0 ∧
        gram τ G' Q = Matrix.diagonal fun a : Fin r => ((sgn p (a : ℕ) : ℝ) : ℂ))
    (hn : ∃ x : E, G.det / G'.det = x * cc x) :
    ∃ P : Matrix (Fin r) (Fin r) E, P.det ≠ 0 ∧ G' = Pᵀ * G * P.map cc :=
  H E r G G' hG hG' hd hd' (congr_of_signature Ψ hΨ hs) hn
end GlobalTheory.Published.Landherr
