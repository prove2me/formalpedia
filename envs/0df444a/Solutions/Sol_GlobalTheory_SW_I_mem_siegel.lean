-- Prove2me | solution 1 for GlobalTheory.SW.I_mem_siegel
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T19:57:48.706972+00:00
-- url     : https://prove2.me/submissions/552fd3c9-fbea-49a4-9d9b-7f6ca51ff174

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IMemSiegel

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex
open scoped ComplexConjugate
open GlobalTheory GlobalTheory.SW
noncomputable section
variable {κ ι : Type} [Fintype κ] [Fintype ι] [DecidableEq ι]
namespace GlobalTheory.SW
theorem _root_.solution : (I • (1 : Matrix ι ι ℂ)) ∈ Siegel ι := by
  refine ⟨?_, ?_⟩
  · simp [Matrix.IsSymm]
  · have him : (I • (1 : Matrix ι ι ℂ)).map Complex.im = 1 := by
      ext i j
      by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
    rw [him]
    exact Matrix.PosDef.one
end GlobalTheory.SW
