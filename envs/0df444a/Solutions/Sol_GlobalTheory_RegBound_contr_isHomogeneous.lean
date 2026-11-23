-- Prove2me | solution 1 for GlobalTheory.RegBound.contr_isHomogeneous
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:55:05.892903+00:00
-- url     : https://prove2.me/submissions/562c1e8e-36d0-4efc-b76d-38ffcf70b294

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsUniformRegularityBound
import Theorems.Thm_GlobalTheory_RegBound_contr_comp

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
theorem _root_.solution (φ : L →ₗ[K] K) {e : ℕ} {F : MvPolynomial σ L}
    (hF : F.IsHomogeneous e) : (contr φ F).IsHomogeneous e := by
  rw [← homogeneousComponent_eq_self hF, contr_comp]
  exact homogeneousComponent_isHomogeneous _ _
end GlobalTheory.RegBound
