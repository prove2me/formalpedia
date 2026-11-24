-- Prove2me | solution 1 for GlobalTheory.compactSpace_UpqT_definite
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:17:21.795913+00:00
-- url     : https://prove2.me/submissions/3503b139-3db8-4728-bec6-25392bab9f03

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_DataCD
import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_UpqDefiniteCompact
import Theorems.Thm_GlobalTheory_isCompact_Upq_zero_left
import Theorems.Thm_Formalism_UG_Final_KpqSubgroupCompact
import Theorems.Thm_Formalism_UG_P_indefinite_unitary_compact


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.BasicNotions MeasureTheory Filter Topology Matrix
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ N : ℕ, CompactSpace (UpqT N 0) ∧ CompactSpace (UpqT 0 N) := fun N =>
  ⟨(isCompact_iff_compactSpace.1 (Formalism.UG.P.indefinite_unitary_compact N) :
      CompactSpace (Formalism.UG.Upq N 0 : Set (GL (Fin N ⊕ Fin 0) ℂ))),
    (isCompact_iff_compactSpace.1 (isCompact_Upq_zero_left N) :
      CompactSpace (Formalism.UG.Upq 0 N : Set (GL (Fin 0 ⊕ Fin N) ℂ)))⟩
end GlobalTheory
