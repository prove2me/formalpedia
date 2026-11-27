-- Prove2me | solution 1 for GlobalTheory.isWeaklyRegular_ofFn_linForm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:39:13.72967+00:00
-- url     : https://prove2.me/submissions/ec53f1ac-f139-4705-8683-1897be754aa7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsWeaklyRegularMapCAppendMapLinForm
import Theorems.Thm_GlobalTheory_isWeaklyRegular_map_linForm

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
theorem _root_.solution {n : ℕ} {e : Fin n → ι} (he : Function.Injective e) :
    IsWeaklyRegular (MvPolynomial (ι × J) R) (List.ofFn fun k => linForm u (e k)) := by
  have := isWeaklyRegular_map_linForm u hu (List.nodup_ofFn.2 he)
  rwa [List.map_ofFn] at this
end GlobalTheory
