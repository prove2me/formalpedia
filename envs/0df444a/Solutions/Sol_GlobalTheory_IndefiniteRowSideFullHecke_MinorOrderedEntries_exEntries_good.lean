-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries.exEntries_good
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:58:57.864177+00:00
-- url     : https://prove2.me/submissions/7a829567-fdf4-4e52-a787-bd06d3cbffa0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_MinorOrderedEntries

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Matrix
open scoped TensorProduct Kronecker
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries
variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {S : Sizes} (P : ι → Entries S)
namespace GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries
theorem _root_.solution : exEntries.Good where
  a_half l := by
    fin_cases l
    exacts [⟨11, by norm_num [exEntries]⟩, ⟨6, by norm_num [exEntries]⟩, ⟨2, by norm_num [exEntries]⟩]
  u_half i := by
    fin_cases i
    exact ⟨0, by norm_num [exEntries]⟩
  order := by decide +kernel
end GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries
