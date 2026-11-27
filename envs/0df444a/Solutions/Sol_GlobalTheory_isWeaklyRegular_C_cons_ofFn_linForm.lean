-- Prove2me | solution 1 for GlobalTheory.isWeaklyRegular_C_cons_ofFn_linForm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:39:05.94891+00:00
-- url     : https://prove2.me/submissions/71fbce47-55ce-4034-9c16-1b82f9d635c2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsWeaklyRegularMapCAppendMapLinForm
import Theorems.Thm_GlobalTheory_isWeaklyRegular_C_cons_map_linForm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial RingTheory.Sequence
noncomputable section
open GlobalTheory
variable {R : Type*} [CommRing R] {ι J : Type*} [Fintype J]
variable (u : J → R) {j₀ : J} (hu : IsUnit (u j₀))
include hu
namespace GlobalTheory
theorem _root_.solution {r : R} (hr : r ∈ nonZeroDivisors R)
    {n : ℕ} {e : Fin n → ι} (he : Function.Injective e) :
    IsWeaklyRegular (MvPolynomial (ι × J) R) (C r :: List.ofFn fun k => linForm u (e k)) := by
  have := isWeaklyRegular_C_cons_map_linForm u hu hr (List.nodup_ofFn.2 he)
  rwa [List.map_ofFn] at this
end GlobalTheory
