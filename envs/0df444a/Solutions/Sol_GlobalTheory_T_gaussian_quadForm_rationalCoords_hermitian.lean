-- Prove2me | solution 1 for GlobalTheory.T.gaussian_quadForm_rationalCoords_hermitian
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T18:23:40.34134+00:00
-- url     : https://prove2.me/submissions/4733aff3-dd84-4838-9f19-deb7d11ee7f7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_GaussianQuadFormRationalCoordsHermitian
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_GaussianQuadFormRationalCoordsHermitianStatement
import Theorems.Thm_GlobalTheory_SW_gauss_form_dictionary


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Finset (E →+* ℂ)), IsType Ψ → ∀ (n N : ℕ), ∀ Z ∈ Hn Ψ N, ∀ (z z' : CM Ψ n N) (k : Fin n), zetaOf Ψ z z' k ⬝ᵥ ((tauOf Ψ Z).map fun t => (t.im : ℂ))⁻¹ *ᵥ zetaOf Ψ z z' k = 2 * ∑ τ : Ψ, z' τ k ⬝ᵥ (imH (Z τ))⁻¹ *ᵥ z τ k := by
  first | exact @GlobalTheory.SW.gauss_form_dictionary | exact GlobalTheory.SW.gauss_form_dictionary | (intros; apply GlobalTheory.SW.gauss_form_dictionary <;> assumption)
end _root_.GlobalTheory.T
