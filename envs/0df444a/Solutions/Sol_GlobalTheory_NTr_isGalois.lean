-- Prove2me | solution 1 for GlobalTheory.NTr.isGalois
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T19:02:47.675365+00:00
-- url     : https://prove2.me/submissions/49ac415c-32a8-42b7-8218-46515db2245b

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnramifiedQuadraticIntegralTraceFormPerfect
import Theorems.Thm_GlobalTheory_NTr_findim
import Theorems.Thm_GlobalTheory_NTr_conj_ne_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.NTr
variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [hU : Unram F E]
include hU
namespace GlobalTheory.NTr
theorem _root_.solution : IsGalois F E := by
  haveI := findim (F := F) (E := E)
  apply IsGalois.of_card_aut_eq_finrank
  rw [hU.finrank_eq]
  apply le_antisymm
  · have := (AlgEquiv.card_le (F := F) (K := E))
    rw [hU.finrank_eq] at this
    rw [Nat.card_eq_fintype_card]
    convert this
  · have h2 : ({1, conj F E} : Set (E ≃ₐ[F] E)).ncard = 2 := by
      rw [Set.ncard_pair (Ne.symm conj_ne_one)]
    rw [← h2]
    exact Set.ncard_le_card _
end GlobalTheory.NTr
