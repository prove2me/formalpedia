-- Prove2me | solution 1 for GlobalTheory.T.blockTriangular_row_lattice_triangular_basis
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:04:20.578068+00:00
-- url     : https://prove2.me/submissions/ab7e9192-2fc3-4da3-9261-0c5a8afc1ddc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_BlockTriangularRowLatticeTriangularBasis
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_BlockTriangularRowLatticeTriangularBasisStatement
import Theorems.Thm_GlobalTheory_InertZeta_RowSpan_spanEq_holds


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.InertZeta
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : SpanEq := by
  first | exact @GlobalTheory.InertZeta.RowSpan.spanEq_holds | exact GlobalTheory.InertZeta.RowSpan.spanEq_holds | (intros; apply GlobalTheory.InertZeta.RowSpan.spanEq_holds <;> assumption)
end _root_.GlobalTheory.T
