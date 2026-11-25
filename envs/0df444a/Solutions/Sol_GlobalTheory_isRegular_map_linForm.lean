-- Prove2me | solution 1 for GlobalTheory.isRegular_map_linForm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:55:28.321333+00:00
-- url     : https://prove2.me/submissions/2bee9baf-37d8-4ec6-b1a2-91d4ca9d20df

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsWeaklyRegularMapCAppendMapLinForm
import Theorems.Thm_GlobalTheory_quotientSpanLinFormEquiv_mk
import Theorems.Thm_GlobalTheory_quotientMapCSupSpanLinFormEquiv_mk
import Theorems.Thm_GlobalTheory_isRegular_map_C_append_map_linForm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.quotientSpanLinFormEquiv_mk
attribute [local simp] GlobalTheory.quotientMapCSupSpanLinFormEquiv_mk

set_option autoImplicit false
open MvPolynomial RingTheory.Sequence
noncomputable section
open GlobalTheory
variable {R : Type*} [CommRing R] {ι J : Type*} [Fintype J]
variable (u : J → R) {j₀ : J} (hu : IsUnit (u j₀))
include hu
namespace GlobalTheory
theorem _root_.solution [Nontrivial R] {l : List ι} (hl : l.Nodup) :
    RingTheory.Sequence.IsRegular (MvPolynomial (ι × J) R) (l.map (linForm u)) := by
  simpa using isRegular_map_C_append_map_linForm u hu (RingTheory.Sequence.IsRegular.nil R R) hl
end GlobalTheory
