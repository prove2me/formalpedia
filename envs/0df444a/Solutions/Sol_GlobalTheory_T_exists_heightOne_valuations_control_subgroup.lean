-- Prove2me | solution 1 for GlobalTheory.T.exists_heightOne_valuations_control_subgroup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T18:19:33.075124+00:00
-- url     : https://prove2.me/submissions/345255f6-f66e-4a02-b922-8f8b4cde3f35

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsHeightOneValuationsControlSubgroup
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsHeightOneValuationsControlSubgroupStatement
import Theorems.Thm_GlobalTheory_HtVal_exists_vals


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] (J : Type) [Finite J] (g : J → (FractionRing R)ˣ), ∃ (s : ℕ) (v : Fin s → ((FractionRing R)ˣ →* Multiplicative ℤ)), (∀ i (x : (FractionRing R)ˣ) (r : R), (x : FractionRing R) = algebraMap R _ r → 0 ≤ Multiplicative.toAdd (v i x)) ∧ (∀ x ∈ Subgroup.closure (Set.range g), (∀ i, 0 ≤ Multiplicative.toAdd (v i x)) → ∃ r : R, (x : FractionRing R) = algebraMap R _ r) := by
  first | exact @GlobalTheory.HtVal.exists_vals | exact GlobalTheory.HtVal.exists_vals | (intros; apply GlobalTheory.HtVal.exists_vals <;> assumption)
end _root_.GlobalTheory.T
