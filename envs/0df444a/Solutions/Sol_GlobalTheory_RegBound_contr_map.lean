-- Prove2me | solution 1 for GlobalTheory.RegBound.contr_map
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:01:43.39084+00:00
-- url     : https://prove2.me/submissions/d75a8cae-57d0-4230-8b75-8b0a8fd281a9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsUniformRegularityBound
import Theorems.Thm_GlobalTheory_RegBound_contr_smul_map

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Module MvPolynomial
open GlobalTheory GlobalTheory.RegBound
variable {σ K : Type} [Field K]
variable {L : Type} [Field L] [Algebra K L]
namespace GlobalTheory.RegBound
theorem _root_.solution (φ : L →ₗ[K] K) (F : MvPolynomial σ K) :
    contr φ (map (algebraMap K L) F) = φ 1 • F := by
  rw [← contr_smul_map, one_smul]
end GlobalTheory.RegBound
