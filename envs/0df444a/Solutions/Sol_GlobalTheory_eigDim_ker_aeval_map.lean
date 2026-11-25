-- Prove2me | solution 1 for GlobalTheory.eigDim_ker_aeval_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T02:43:37.411079+00:00
-- url     : https://prove2.me/submissions/962bdfaf-2507-4f00-81b3-a3529336a766

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FinrankKerAevalEqNatDegreeMulFinrankEigenspaceAl
import Theorems.Thm_GlobalTheory_eigDim_ker_map
import Theorems.Thm_P2M_GlobalTheory_eigDim_aeval_toLin__0786b496869e
import Theorems.Thm_GlobalTheory_eigDim_aeval_map

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {K L : Type} [Field K] [Field L] (φ : K →+* L) {n : Type}
    [Fintype n] [DecidableEq n] (M : Matrix n n K) (f : K[X]) :
    Module.finrank L (LinearMap.ker (aeval (Matrix.toLin' (M.map φ)) (f.map φ))) =
      Module.finrank K (LinearMap.ker (aeval (Matrix.toLin' M) f)) := by
  rw [eigDim_aeval_toLin', eigDim_aeval_toLin', ← eigDim_aeval_map, eigDim_ker_map]
end GlobalTheory
