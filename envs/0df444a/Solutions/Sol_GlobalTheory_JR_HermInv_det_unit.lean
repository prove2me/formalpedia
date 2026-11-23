-- Prove2me | solution 1 for GlobalTheory.JR.HermInv.det_unit
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:39:48.216226+00:00
-- url     : https://prove2.me/submissions/6da0a00c-bcb5-4b94-9e8c-f864acd82b34

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnitaryActionHermitianInvariantsTransitive

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.HermInv
variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
variable {r : ℕ}
namespace GlobalTheory.JR.HermInv
theorem _root_.solution (a : Inv r F) (hΔ : Delta a ≠ 0) (h : Matrix (Fin r) (Fin r) E)
    (hh : hᴴ * h = (hankel a).map (algebraMap F E)) : IsUnit h.det := by
  have : (hᴴ * h).det ≠ 0 := by
    rw [hh, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (map_ne_zero _).2 hΔ
  rw [det_mul] at this
  exact isUnit_iff_ne_zero.2 (right_ne_zero_of_mul this)
end GlobalTheory.JR.HermInv
