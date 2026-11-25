-- Prove2me | solution 1 for GroundTheory.GroupCoh.inflation_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:45:15.086239+00:00
-- url     : https://prove2.me/submissions/bc356b83-ebd6-48cd-a246-11a54a7b64d6

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_DeltaMap
import Definitions.Def_GroundTheory_TateCohomology_CoindOne
import Definitions.Def_GroundTheory_TateCohomology_InfRes
import Theorems.Thm_GroundTheory_GroupCoh_infResShortComplex_mono_exact

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
variable {A S}
namespace GroundTheory.GroupCoh
theorem _root_.solution {q : ℕ} (hq : q ≠ 0)
    (hA : ∀ i, 0 < i → i < q → IsZero (groupCohomology (res S.subtype A) i)) :
    Function.Injective (inflation A S q).hom := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hq
  exact (ModuleCat.mono_iff_injective _).1 (infResShortComplex_mono_exact S n A hA).1
end GroundTheory.GroupCoh
