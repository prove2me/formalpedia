-- Prove2me | solution 1 for N25.Endgame.canonicalF2_degreeOnePlace_count25
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T19:13:58.624093+00:00
-- url     : https://prove2.me/submissions/b37ac7fa-ad6e-4ec6-8879-a23ca48ace3d

import Definitions.Def_N25_CanonicalPointPlaces
import Definitions.Def_N25_CanonicalNormalizedPoints
import Definitions.Def_N25_NormalizedPointPivot
import Theorems.Thm_N25_Endgame_canonical_degreeOnePlace_card_eq_points25
import Theorems.Thm_N25_Endgame_canonicalF2_point_count25
import Theorems.Thm_N25_canonicalOpenChartRing_isDomain_good25

/-! Cardinality transport from full normalized canonical points to degree-one places. -/
namespace N25.Endgame

open N25

/-- There are five degree-one places over the literal field with two elements. -/
theorem _root_.solution :
    letI : IsDomain (CanonicalOpenChartRing25 (ZMod 2)) :=
      canonicalOpenChartRing_isDomain_good25 2 (Or.inl rfl) (ZMod 2)
    Nat.card {P : AlgebraicCurve.Place (ZMod 2) (CanonicalFF25 (ZMod 2)) //
      P.deg = 1} = 5 := by
  rw [canonical_degreeOnePlace_card_eq_points25 2 (Or.inl rfl)]
  exact canonicalF2_point_count25

end N25.Endgame

namespace N25

end N25
