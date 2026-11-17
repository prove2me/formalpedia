-- Prove2me | solution 1 for N25.Endgame.canonicalF3_point_count25
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T19:13:56.765813+00:00
-- url     : https://prove2.me/submissions/8d6f6909-2630-4207-bb7a-70ce8022950f

import Definitions.Def_N25_CanonicalPointPlaces
import Definitions.Def_N25_CanonicalNormalizedPoints
import Definitions.Def_N25_NormalizedPointPivot

/-! Cardinality transport from full normalized canonical points to degree-one places. -/
namespace N25.Endgame

open N25

/-- A direct kernel count on the forty normalized projective candidates over the ternary prime field. -/
theorem _root_.solution : Nat.card (CanonicalPoint25 (ZMod 3)) = 5 := by
  let : DecidablePred (@IsCanonicalNormalized25 (ZMod 3) _) := fun P => by
    unfold IsCanonicalNormalized25
    infer_instance
  rw [Nat.card_eq_fintype_card]
  decide +kernel

end N25.Endgame

namespace N25

end N25
