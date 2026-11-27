-- Prove2me | solution 1 for GroundTheory.PAdicHodge.compound_mulVec_map_maxMinor_of_mul_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:50:30.651032+00:00
-- url     : https://prove2.me/submissions/3e7b7c5c-0063-4b1e-8ae4-1cf2abef22ff

import Mathlib
import Definitions.Def_GroundTheory_PowerSubgroups_CountableNeighbourhoods_ExistsMaxMinorNeZeroOfLinearIndependentAlt
import Definitions.Def_GroundTheory_PAdicHodge_SlopeCauchyBinet
import Theorems.Thm_GroundTheory_PAdicHodge_maxMinor_map
import Theorems.Thm_GroundTheory_PAdicHodge_compound_mulVec_maxMinor_of_mul_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.PAdicHodge
open Matrix Finset Equiv
variable {R : Type*} [CommRing R]
variable {m n k : ℕ}
namespace GroundTheory.PAdicHodge
theorem _root_.solution (φ : R →+* R) (A : Matrix (Fin n) (Fin n) R)
    (B : Matrix (Fin n) (Fin k) R) (C : Matrix (Fin k) (Fin k) R) (h : A * B.map φ = B * C) :
    compound k A *ᵥ (fun s => φ (maxMinor B s)) = C.det • maxMinor B := by
  rw [← compound_mulVec_maxMinor_of_mul_eq A B (B.map φ) C h]
  congr 1
  funext s
  rw [maxMinor_map]
end GroundTheory.PAdicHodge
