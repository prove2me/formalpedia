-- Prove2me | solution 1 for GlobalTheory.T.rat_mem_span_of_real_mem_span_fin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:33:43.600587+00:00
-- url     : https://prove2.me/submissions/aa80a2ff-b152-47c0-8417-8e08d536fd6b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_RatMemSpanOfRealMemSpanFin
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_RatMemSpanOfRealMemSpanFinStatement
import Theorems.Thm_GlobalTheory_rat_mem_span_of_real_mem_span


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (k r : ℕ) (w : Fin k → Fin r → ℚ) (v : Fin r → ℚ), (fun j => ((v j : ℚ) : ℝ)) ∈ Submodule.span ℝ (Set.range fun i j => ((w i j : ℚ) : ℝ)) → v ∈ Submodule.span ℚ (Set.range w) := by
  first | exact @GlobalTheory.rat_mem_span_of_real_mem_span | exact GlobalTheory.rat_mem_span_of_real_mem_span | (intros; apply GlobalTheory.rat_mem_span_of_real_mem_span <;> assumption)
end _root_.GlobalTheory.T
