-- Prove2me | solution 1 for GlobalTheory.unitary_transitive_of_norm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:39:45.967533+00:00
-- url     : https://prove2.me/submissions/da58c0b3-2991-4793-a5a3-341369d43fec

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ConjTransposeVecMulVecSelf
import Theorems.Thm_GlobalTheory_UnitWitt_exists_unitary_mulVec

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
namespace GlobalTheory
theorem _root_.solution : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E]
    [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (u v : Fin r → E), star u ⬝ᵥ u = star v ⬝ᵥ v →
    star u ⬝ᵥ u ≠ 0 → ∃ g : Matrix.unitaryGroup (Fin r) E, g.1 *ᵥ u = v := by
  intro F E _ _ _ _ hU r u v hc h0
  haveI : CharZero F := hU.charZero
  have h2 : (2 : E) ≠ 0 := by
    intro h
    apply (two_ne_zero : (2 : F) ≠ 0)
    apply (algebraMap F E).injective
    rw [map_ofNat, map_zero]; exact h
  exact GlobalTheory.UnitWitt.exists_unitary_mulVec h2 u v hc h0
end GlobalTheory
