-- Prove2me | solution 1 for GroundTheory.GroupCoh.infResShortComplex_mono_exact
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:36:03.240937+00:00
-- url     : https://prove2.me/submissions/c0cf167f-8aac-4b00-a1df-3bda890f8a70

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_DeltaMap
import Definitions.Def_GroundTheory_TateCohomology_CoindOne
import Definitions.Def_GroundTheory_TateCohomology_InfRes
import Theorems.Thm_GroundTheory_GroupCoh_infRes_step

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.GroupCoh
open CategoryTheory Limits groupCohomology Rep
universe u
variable {k G : Type u} [CommRing k] [Group G]
variable (A : Rep k G) (S : Subgroup G) [S.Normal]
namespace GroundTheory.GroupCoh
theorem _root_.solution (n : ℕ) :
    ∀ A : Rep k G, (∀ i, 0 < i → i < n + 1 → IsZero (groupCohomology (res S.subtype A) i)) →
      Mono (infResShortComplex A S n).f ∧ (infResShortComplex A S n).Exact := by
  induction n with
  | zero => exact fun A _ => ⟨inferInstanceAs (Mono (H1InfRes A S).f), H1InfRes_exact A S⟩
  | succ n ih => exact fun A hA => infRes_step A S n ih hA
end GroundTheory.GroupCoh
