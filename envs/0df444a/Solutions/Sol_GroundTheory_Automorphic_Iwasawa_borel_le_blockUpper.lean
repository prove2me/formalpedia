-- Prove2me | solution 1 for GroundTheory.Automorphic.Iwasawa.borel_le_blockUpper
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:52:15.629804+00:00
-- url     : https://prove2.me/submissions/f589df75-fd8f-4ad0-8d07-122ff55abe20

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GLnLattice
import Definitions.Def_GroundTheory_AutomorphicForms_Iwasawa

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Automorphic
open ValuativeRel Matrix Filter
open scoped Pointwise
open GroundTheory.Automorphic.Iwasawa
open GLnLocal
variable (F : Type*) [Field F] (n : ℕ)
namespace GroundTheory.Automorphic.Iwasawa
theorem _root_.solution {α : Type*} [LinearOrder α] {β : Fin n → α} (hβ : Monotone β) :
    borel F n ≤ blockUpper F n β :=
  fun _ hg _ _ hij => hg (hβ.reflect_lt hij)
end GroundTheory.Automorphic.Iwasawa
