-- Prove2me | solution 1 for GlobalTheory.metaplectic_euclidean_gaussian
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:17:56.647445+00:00
-- url     : https://prove2.me/submissions/5efd554b-7b2b-4966-b55f-4f872f02941a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_MetaplecticRepresentation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IteratedLineDerivMemWeylAlg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsEqTransposeMulDiagonalMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MetaplecticGaussianNormalisedStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousMetaplecticSchwartzActionProdStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzEqGaussianOfFderivEqMulVecStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SymplecticHolPartDetNeZeroAndIsSymmStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FderivEqMulVecOfSchrodingerAnnihilatedStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MetaplecticCoverWeilRepresentation
import Theorems.Thm_CompanionTheory_ThKF_E_Impl_continuous
import Theorems.Thm_CompanionTheory_ThKF_E_Impl_dRho
import Theorems.Thm_CompanionTheory_ThKR_Mp_omS_dRho
import Theorems.Thm_GlobalTheory_RealWeil_omS_dRho
import Theorems.Thm_GlobalTheory_T_continuous_metaplectic_schwartz_action_prod
import Theorems.Thm_GlobalTheory_T_fderiv_eq_mulVec_of_schrodinger_annihilated
import Theorems.Thm_GlobalTheory_T_metaplecticGaussianNormalisedAlt
import Theorems.Thm_GlobalTheory_T_schwartz_eq_gaussian_of_fderiv_eq_mulVec_of_isSymm
import Theorems.Thm_GlobalTheory_T_symplectic_holPart_det_ne_zero_and_isSymm


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix Complex GlobalTheory.RealWeil
open scoped Real SchwartzMap ComplexConjugate
namespace GlobalTheory
theorem _root_.solution : ∀ (l : Type) [Fintype l] [DecidableEq l], ∃ (G : Type) (_ : Group G) (_ : TopologicalSpace G) (_ : IsTopologicalGroup G) (pr : G →* Matrix.symplecticGroup l ℝ) (om : G →* (L2 l ≃ₗᵢ[ℂ] L2 l)) (omS : G →* (Sch l →L[ℂ] Sch l)) (φ : Sch l), IsCoveringMap pr ∧ Function.Surjective pr ∧ (∃ ε : G, ε ≠ 1 ∧ (∀ g, pr g = 1 ↔ g = 1 ∨ g = ε) ∧ ∀ f, om ε f = -f) ∧ (∀ f : L2 l, Continuous fun g => om g f) ∧ (∀ (g : G) (w : l ⊕ l → ℝ) (f : L2 l), om g (rho w f) = rho ((pr g : Matrix (l ⊕ l) (l ⊕ l) ℝ) *ᵥ w) (om g f)) ∧ (∀ (g : G) (f : Sch l), om g (f.toLp 2) = (omS g f).toLp 2) ∧ (∀ x : EuclideanSpace ℝ l, φ x = cexp (-π * ((x.ofLp ⬝ᵥ x.ofLp : ℝ) : ℂ))) ∧ (Continuous fun x : G × Sch l => omS x.1 x.2) ∧ ∀ (g : G) (P Q : Matrix l l ℂ), (∀ a b, P a b = ((pr g).1 (.inl a) (.inl b) : ℂ) - I * ((pr g).1 (.inl a) (.inr b) : ℂ)) → (∀ a b, Q a b = ((pr g).1 (.inr a) (.inl b) : ℂ) - I * ((pr g).1 (.inr a) (.inr b) : ℂ)) → ∃ c : ℂ, c ^ 2 * P.det = 1 ∧ ∀ x : EuclideanSpace ℝ l, omS g φ x = c * cexp (π * I * ((fun i => (x i : ℂ)) ⬝ᵥ (-(Q * P⁻¹)) *ᵥ fun i => (x i : ℂ))) := by
  intro l _ _
  obtain ⟨G, iG, tG, hG, pr, om, omS, φ, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := GlobalTheory.T.metaplecticGaussianNormalisedAlt l
  refine ⟨G, iG, tG, hG, pr, om, omS, φ, h1, h2, h3, h4, h5, h6, h7,
    GlobalTheory.T.continuous_metaplectic_schwartz_action_prod l G pr om omS h1.continuous h4 h5 h6, ?_⟩
  intro g P Q hP hQ
  refine ⟨omS g φ 0, h9 g P hP, ?_⟩
  obtain ⟨hdet, hS⟩ := GlobalTheory.T.symplectic_holPart_det_ne_zero_and_isSymm l (pr g).1 P Q hP hQ (pr g).2
  have hann : ∀ j : l, dRho ((pr g).1 *ᵥ Pi.single (.inl j) 1) (omS g φ) =
      I • dRho ((pr g).1 *ᵥ Pi.single (.inr j) 1) (omS g φ) := fun j => by
    rw [← omS_dRho h5 h6, ← omS_dRho h5 h6, h8 j, map_smul]
  have hd := GlobalTheory.T.fderiv_eq_mulVec_of_schrodinger_annihilated l (pr g).1 P Q hP hQ hdet (omS g φ) hann
  rw [hS.eq] at hd
  exact GlobalTheory.T.schwartz_eq_gaussian_of_fderiv_eq_mulVec_of_isSymm l (-(Q * P⁻¹)) (omS g φ) hS hd
end GlobalTheory
