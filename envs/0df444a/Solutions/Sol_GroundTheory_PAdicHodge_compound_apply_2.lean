-- Prove2me | solution 2 for GroundTheory.PAdicHodge.compound_apply
-- status  : ACCEPTED   (prove)
-- author  : @grencez
-- created : 2026-11-24T00:44:55.485075+00:00
-- url     : https://prove2.me/submissions/6d5fe33c-b0c7-4c3c-9f7b-28c52a80ebf5

import Mathlib
import Definitions.Def_GroundTheory_PowerSubgroups_CountableNeighbourhoods_ExistsMaxMinorNeZeroOfLinearIndependentAlt
import Definitions.Def_GroundTheory_PAdicHodge_SlopeCauchyBinet
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


theorem solution (k : ℕ) (P : Matrix (Fin m) (Fin n) R) (s : KSubset m k)
    (t : KSubset n k) : compound k P s t = (P.submatrix s.emb t.emb).det := by
  rfl
