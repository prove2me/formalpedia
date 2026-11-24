-- Prove2me | solution 1 for GlobalTheory.OppRad.un_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:17:05.696718+00:00
-- url     : https://prove2.me/submissions/d93fc62c-faa6-4a18-b230-6178cf157863

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MatrixRegular
import Theorems.Thm_GlobalTheory_OppRad_mem_U
import Theorems.Thm_GlobalTheory_OppRad_un_val
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.OppRad.un_val

set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.OppRad
open scoped Classical
variable {R : Type} [Ring R]
namespace GlobalTheory.OppRad
theorem _root_.solution {p q x : R} (h : x * x = 0) (h1 : p * x = x) (h2 : x * q = x) : un x h ∈ U p q := by
  simpa [mem_U] using ⟨h1, h2⟩
end GlobalTheory.OppRad
