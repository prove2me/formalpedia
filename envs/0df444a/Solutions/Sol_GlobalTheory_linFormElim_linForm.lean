-- Prove2me | solution 1 for GlobalTheory.linFormElim_linForm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:39:58.167682+00:00
-- url     : https://prove2.me/submissions/fa743616-2d5f-4396-ba0a-c44eeb6867bd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsWeaklyRegularMapCAppendMapLinForm
import Theorems.Thm_GlobalTheory_linFormEquiv_symm_linForm

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
namespace GlobalTheory
theorem _root_.solution {S : Set ι} {i : ι} (hi : i ∈ S) :
    linFormElim u hu S (linForm u i) = 0 := by
  rw [linFormElim_apply, linFormEquiv_symm_linForm u hu hi, killVars_X_of_mem (by exact ⟨hi, rfl⟩)]
end GlobalTheory
