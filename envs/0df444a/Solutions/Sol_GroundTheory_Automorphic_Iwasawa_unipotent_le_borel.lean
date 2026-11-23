-- Prove2me | solution 1 for GroundTheory.Automorphic.Iwasawa.unipotent_le_borel
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:42:36.214837+00:00
-- url     : https://prove2.me/submissions/f631ed38-b282-4024-83ff-8a41d9ff568b

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
theorem _root_.solution : unipotent F n ≤ borel F n := fun _ hg => hg.1
end GroundTheory.Automorphic.Iwasawa
