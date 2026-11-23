-- Prove2me | solution 1 for GlobalTheory.GramCount.map_ip
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:35:59.290628+00:00
-- url     : https://prove2.me/submissions/73819904-d43c-4a13-af91-a4a7b8a92a92

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_PrimOfIsUnitDet

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.GramCount
variable {A : Type} [CommRing A]
variable (c : A →+* A) {n : ℕ}
namespace GlobalTheory.GramCount
theorem _root_.solution {B : Type} [CommRing B] (c' : B →+* B) (φ : A →+* B)
    (hφ : ∀ u, φ (c u) = c' (φ u)) (x y : Fin n → A) :
    φ (ip c x y) = ip c' (fun i => φ (x i)) (fun i => φ (y i)) := by
  unfold ip
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, hφ]
end GlobalTheory.GramCount
