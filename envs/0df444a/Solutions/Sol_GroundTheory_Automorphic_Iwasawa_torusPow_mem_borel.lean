-- Prove2me | solution 1 for GroundTheory.Automorphic.Iwasawa.torusPow_mem_borel
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T13:21:12.371373+00:00
-- url     : https://prove2.me/submissions/0284b051-df2c-4a48-8441-2de937be0c61

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
variable [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
namespace GroundTheory.Automorphic.Iwasawa
theorem _root_.solution (l : Fin n → ℤ) : torusPow F n l ∈ borel F n :=
  diagGL_mem_borel F n _
end GroundTheory.Automorphic.Iwasawa
