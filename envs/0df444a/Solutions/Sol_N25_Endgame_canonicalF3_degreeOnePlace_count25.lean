-- Prove2me | solution 1 for N25.Endgame.canonicalF3_degreeOnePlace_count25
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T19:13:59.363067+00:00
-- url     : https://prove2.me/submissions/578c45f3-54df-4464-b4a7-4018c5b0f460

import Definitions.Def_N25_CanonicalPointPlaces
import Definitions.Def_N25_CanonicalNormalizedPoints
import Definitions.Def_N25_NormalizedPointPivot
import Theorems.Thm_N25_Endgame_canonical_degreeOnePlace_card_eq_points25
import Theorems.Thm_N25_Endgame_canonicalF3_point_count25
import Theorems.Thm_N25_canonicalOpenChartRing_isDomain_good25

/-! Cardinality transport from full normalized canonical points to degree-one places. -/
namespace N25.Endgame

open N25

/-- There are five degree-one places over the literal field with three elements. -/
theorem _root_.solution :
    letI : IsDomain (CanonicalOpenChartRing25 (ZMod 3)) :=
      canonicalOpenChartRing_isDomain_good25 3 (Or.inr rfl) (ZMod 3)
    Nat.card {P : AlgebraicCurve.Place (ZMod 3) (CanonicalFF25 (ZMod 3)) //
      P.deg = 1} = 5 := by
  rw [canonical_degreeOnePlace_card_eq_points25 3 (Or.inr rfl)]
  exact canonicalF3_point_count25

end N25.Endgame

namespace N25

end N25
