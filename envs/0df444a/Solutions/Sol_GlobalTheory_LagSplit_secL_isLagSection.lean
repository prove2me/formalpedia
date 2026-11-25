-- Prove2me | solution 1 for GlobalTheory.LagSplit.secL_isLagSection
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:59:02.471365+00:00
-- url     : https://prove2.me/submissions/f2b45225-746c-4bba-82c6-4f0c1ef8d888

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Clauses
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_SubConjTransposeOfSymm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_BetaEqZeroOfCharacter
import Theorems.Thm_GlobalTheory_LagSplit_omegaCx_elim
import Theorems.Thm_GlobalTheory_LagSplit_perProj_elim
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
theorem _root_.solution (τ : Matrix (Fin g) (Fin g) ℂ) :
    IsLagSection (omegaCx g) (perProj τ) (secL g) :=
  ⟨fun z => by simp [secL_apply, perProj_elim], fun z w => by simp [secL_apply, omegaCx_elim]⟩
end GlobalTheory.LagSplit
