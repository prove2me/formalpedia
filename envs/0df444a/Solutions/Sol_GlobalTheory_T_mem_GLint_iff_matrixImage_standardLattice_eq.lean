-- Prove2me | solution 1 for GlobalTheory.T.mem_GLint_iff_matrixImage_standardLattice_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:18:23.190476+00:00
-- url     : https://prove2.me/submissions/800d2fee-31b9-4184-83e3-0a5ac673ec94

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemGLintIffMatrixImageStandardLatticeEq
import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemMatLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemGLintIffMatrixImageStandardLatticeEqStatement
import Theorems.Thm_GlobalTheory_LatOrb_mem_GLint_iff_matLat_std


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial Matrix GlobalTheory.LatOrb
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ {K : Type} [Field K] (V : ValuationSubring K) (n : ℕ) (k : GL (Fin n) K),
    k ∈ Formalism.UG.GLint (Fin n) V.toSubring ↔ matLat V k.val (stdLat V n) = stdLat V n := by
  first | exact @GlobalTheory.LatOrb.mem_GLint_iff_matLat_std | exact GlobalTheory.LatOrb.mem_GLint_iff_matLat_std | (intros; apply GlobalTheory.LatOrb.mem_GLint_iff_matLat_std <;> assumption)
end _root_.GlobalTheory.T
