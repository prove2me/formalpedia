-- Prove2me | solution 1 for N25.Endgame.canonicalF2_point_count25
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T19:13:55.824275+00:00
-- url     : https://prove2.me/submissions/c6da8fba-a5a1-47b1-b915-ee2e547584bd

import Definitions.Def_N25_CanonicalPointPlaces
import Definitions.Def_N25_CanonicalNormalizedPoints
import Definitions.Def_N25_NormalizedPointPivot

/-! Cardinality transport from full normalized canonical points to degree-one places. -/
namespace N25.Endgame

open N25

/-- A direct kernel count on the fifteen normalized projective candidates over the binary prime field. -/
theorem _root_.solution : Nat.card (CanonicalPoint25 (ZMod 2)) = 5 := by
  let : DecidablePred (@IsCanonicalNormalized25 (ZMod 2) _) := fun P => by
    unfold IsCanonicalNormalized25
    infer_instance
  rw [Nat.card_eq_fintype_card]
  decide +kernel

end N25.Endgame

namespace N25

end N25
