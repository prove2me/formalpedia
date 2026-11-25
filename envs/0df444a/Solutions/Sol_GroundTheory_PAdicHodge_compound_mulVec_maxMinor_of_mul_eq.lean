-- Prove2me | solution 1 for GroundTheory.PAdicHodge.compound_mulVec_maxMinor_of_mul_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T01:28:09.827887+00:00
-- url     : https://prove2.me/submissions/3f457f74-4ae2-4594-b33e-8049026474bd

import Mathlib
import Definitions.Def_GroundTheory_PowerSubgroups_CountableNeighbourhoods_ExistsMaxMinorNeZeroOfLinearIndependentAlt
import Definitions.Def_GroundTheory_PAdicHodge_SlopeCauchyBinet
import Theorems.Thm_GroundTheory_PAdicHodge_maxMinor_mul_right
import Theorems.Thm_GroundTheory_PAdicHodge_maxMinor_mul_left_eq_mulVec

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
theorem _root_.solution (A : Matrix (Fin n) (Fin n) R)
    (B B' : Matrix (Fin n) (Fin k) R) (C : Matrix (Fin k) (Fin k) R) (h : A * B' = B * C) :
    compound k A *ᵥ maxMinor B' = C.det • maxMinor B := by
  rw [← maxMinor_mul_left_eq_mulVec, h]
  funext s
  rw [maxMinor_mul_right, Pi.smul_apply, smul_eq_mul, mul_comm]
end GroundTheory.PAdicHodge
