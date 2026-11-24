-- Prove2me | solution 1 for GlobalTheory.UnitLemma.TorusPts.tt_swap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T15:40:41.542813+00:00
-- url     : https://prove2.me/submissions/23a99a1a-02d0-48aa-b636-7096888a50fd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_DltEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CharpolyDvdPowOfAevalEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsInjectiveTorusClassesOfIdempotentDecomposi

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc Polynomial
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.TorusPts
variable {A : Type} [CommRing A] {I : Type} [Fintype I]
namespace GlobalTheory.UnitLemma.TorusPts
theorem _root_.solution (f h c d : I → A) : tt f h c d = tt h f d c := by
  unfold tt
  congr 1
  exact Finset.sum_congr rfl fun i _ => add_comm _ _
end GlobalTheory.UnitLemma.TorusPts
