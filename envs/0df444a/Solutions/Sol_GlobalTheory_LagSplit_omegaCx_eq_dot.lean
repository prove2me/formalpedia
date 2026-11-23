-- Prove2me | solution 1 for GlobalTheory.LagSplit.omegaCx_eq_dot
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:52:59.0857+00:00
-- url     : https://prove2.me/submissions/582a1f16-a12e-4fad-af28-d5a0fe99b7f3

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Clauses
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_SubConjTransposeOfSymm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_BetaEqZeroOfCharacter
import Theorems.Thm_GlobalTheory_LagSplit_omegaCx_apply

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
theorem _root_.solution (a b : Fin g ⊕ Fin g → ℂ) :
    omegaCx g a b = (a ∘ Sum.inl) ⬝ᵥ (b ∘ Sum.inr) - (a ∘ Sum.inr) ⬝ᵥ (b ∘ Sum.inl) := by
  simp [omegaCx_apply, dotProduct, Finset.sum_sub_distrib]
end GlobalTheory.LagSplit
