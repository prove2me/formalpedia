-- Prove2me | solution 1 for GroundTheory.Global.sup_mul_sup_eq_of_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:54:04.627335+00:00
-- url     : https://prove2.me/submissions/0248b787-57ec-4cf7-88b0-8f74a333e753

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_HeckeLFunction
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_NonvanishingDivisorSum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Ideal Complex Filter Topology
open GroundTheory GroundTheory.Global
noncomputable section
variable {K : Type*} [Field K] [NumberField K]
namespace GroundTheory.Global
theorem _root_.solution {R : Type*} [CommRing R] {I J D : Ideal R} (hIJ : I ⊔ J = ⊤)
    (hD : I * J ≤ D) : (D ⊔ I) * (D ⊔ J) = D := by
  refine le_antisymm ?_ ?_
  · rw [Ideal.sup_mul, Ideal.mul_sup, Ideal.mul_sup]
    exact sup_le (sup_le Ideal.mul_le_left Ideal.mul_le_left) (sup_le Ideal.mul_le_right hD)
  · calc D = D * (I ⊔ J) := by rw [hIJ, Ideal.mul_top]
      _ = D * I ⊔ D * J := Ideal.mul_sup _ _ _
      _ ≤ (D ⊔ I) * (D ⊔ J) := sup_le (by
          rw [mul_comm]
          exact Ideal.mul_mono le_sup_right le_sup_left)
          (Ideal.mul_mono le_sup_left le_sup_right)
end GroundTheory.Global
