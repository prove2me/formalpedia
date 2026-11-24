-- Prove2me | solution 2 for GlobalTheory.CubeColim.nonempty_of_card
-- status  : ACCEPTED   (prove)
-- author  : @grencez
-- created : 2026-11-23T22:51:10.431553+00:00
-- url     : https://prove2.me/submissions/78fffeb8-0af7-4fdb-9190-4ccc1cb995cc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsIsoTermComparisonRestrictScalars
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CechComplexDirectLimit
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits Filter
open GlobalTheory
open GlobalTheory.CubeColim
variable {ι : Type} [LinearOrder ι] [Fintype ι]

theorem solution {m : ℕ} (hm : 0 < m) (s : {s : Finset ι // s.card = m}) :
    s.1.Nonempty := by
  apply Finset.card_pos.mp
  exact s.property.symm ▸ hm
