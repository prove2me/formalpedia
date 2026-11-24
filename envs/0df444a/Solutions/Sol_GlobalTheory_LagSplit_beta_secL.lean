-- Prove2me | solution 1 for GlobalTheory.LagSplit.beta_secL
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T18:35:12.884229+00:00
-- url     : https://prove2.me/submissions/b2fab900-ebbc-4308-a249-9d71c963417a

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Clauses
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_SubConjTransposeOfSymm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_BetaEqZeroOfCharacter
import Theorems.Thm_GlobalTheory_LagSplit_omegaCx_eq_dot
import Theorems.Thm_GlobalTheory_LagSplit_secL_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Complex Matrix ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Key.Chi
open GlobalTheory GlobalTheory.LagSplit
variable {g : ℕ}
namespace GlobalTheory.LagSplit
theorem _root_.solution (σ : (Fin g → ℂ) →ₗ[ℂ] (Fin g ⊕ Fin g → ℂ)) (z w : Fin g → ℂ) :
    beta (omegaCx g) σ (secL g) z w = -((σ z ∘ Sum.inr) ⬝ᵥ w) := by
  simp [omegaCx_eq_dot, secL_apply]
end GlobalTheory.LagSplit
