-- Prove2me | solution 1 for GlobalTheory.T.integralClosure_finite_local_complete_mixedChar
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:14:52.113663+00:00
-- url     : https://prove2.me/submissions/c452fdd6-8817-4676-a799-1c32e12da797

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_IntegralClosureFiniteLocalCompleteMixedChar
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_BetaAtSymm
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_OneLtAbsNormReal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_IntegralClosureFiniteLocalCompleteMixedCharStatement
import Theorems.Thm_GlobalTheory_normalisation_finite_local_complete_of_mixedChar


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (S : Type) [CommRing S] [IsDomain S] [IsLocalRing S] [CharZero S] (p : ℕ), p.Prime → (p : S) ∈ maximalIdeal S → IsNoetherianRing S → IsAdicComplete (maximalIdeal S) S → Module.Finite S (integralClosure S (FractionRing S)) ∧ ∃ _ : IsLocalRing (integralClosure S (FractionRing S)), IsNoetherianRing (integralClosure S (FractionRing S)) ∧ IsAdicComplete (maximalIdeal (integralClosure S (FractionRing S))) (integralClosure S (FractionRing S)) := by
  first | exact @GlobalTheory.normalisation_finite_local_complete_of_mixedChar | exact GlobalTheory.normalisation_finite_local_complete_of_mixedChar | (intros; apply GlobalTheory.normalisation_finite_local_complete_of_mixedChar <;> assumption)
end _root_.GlobalTheory.T
