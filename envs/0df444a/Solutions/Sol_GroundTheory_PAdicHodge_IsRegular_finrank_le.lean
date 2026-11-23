-- Prove2me | solution 1 for GroundTheory.PAdicHodge.IsRegular.finrank_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:27:32.928168+00:00
-- url     : https://prove2.me/submissions/ad910786-ec27-407f-9b60-b71be3b1ba59

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_Admissible

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
open TensorProduct Module
open GroundTheory.PAdicHodge.IsRegular
variable {G F B : Type*} [Group G] [Field F] [CommRing B] [IsDomain B] [Algebra F B]
  [MulSemiringAction G B] [SMulCommClass G F B] (h : IsRegular G F B)
include h
variable {V : Type*} [AddCommGroup V] [Module F V] (ρ : Representation F G V)
namespace GroundTheory.PAdicHodge.IsRegular
theorem _root_.solution [FiniteDimensional F V] :
    finrank (invariantRing G F B) (DB B ρ) ≤ finrank F V :=
  (h.finite_and_finrank_le ρ).2
end GroundTheory.PAdicHodge.IsRegular
