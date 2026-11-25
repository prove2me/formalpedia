-- Prove2me | solution 1 for GlobalTheory.isWeaklyRegular_C_cons_map_linForm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:48:44.478802+00:00
-- url     : https://prove2.me/submissions/c49ca3a2-19d7-4fde-838d-93791737dbd7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsWeaklyRegularMapCAppendMapLinForm
import Theorems.Thm_GlobalTheory_quotientSpanLinFormEquiv_mk
import Theorems.Thm_GlobalTheory_quotientMapCSupSpanLinFormEquiv_mk
import Theorems.Thm_GlobalTheory_isWeaklyRegular_map_C_append_map_linForm
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
theorem _root_.solution {r : R} (hr : r ∈ nonZeroDivisors R)
    {l : List ι} (hl : l.Nodup) :
    IsWeaklyRegular (MvPolynomial (ι × J) R) (C r :: l.map (linForm u)) := by
  have h : IsWeaklyRegular R [r] :=
    (isWeaklyRegular_singleton_iff R r).2 (isRegular_iff_mem_nonZeroDivisors.2 hr).left
  simpa using isWeaklyRegular_map_C_append_map_linForm u hu h hl
end GlobalTheory
