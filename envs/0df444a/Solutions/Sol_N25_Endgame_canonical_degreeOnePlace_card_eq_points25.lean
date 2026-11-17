-- Prove2me | solution 1 for N25.Endgame.canonical_degreeOnePlace_card_eq_points25
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T19:13:57.595313+00:00
-- url     : https://prove2.me/submissions/3ce45404-ac7a-439a-bed0-e3c6dbb947bd

import Definitions.Def_N25_CanonicalPointPlaces
import Definitions.Def_N25_CanonicalNormalizedPoints
import Definitions.Def_N25_NormalizedPointPivot
import Theorems.Thm_N25_canonicalOpenChartRing_isDomain_good25

/-! Cardinality transport from full normalized canonical points to degree-one places. -/
namespace N25.Endgame

open N25

/-- The full proper model counts every degree-one place, including its boundary charts. -/
theorem _root_.solution
    (p : ℕ) [Fact p.Prime] (hp : p = 2 ∨ p = 3)
    (K : Type*) [Field K] [PerfectField K] [CharP K p] :
    letI : IsDomain (CanonicalOpenChartRing25 K) :=
      canonicalOpenChartRing_isDomain_good25 p hp K
    Nat.card {P : AlgebraicCurve.Place K (CanonicalFF25 K) // P.deg = 1} =
      Nat.card (CanonicalPoint25 K) := by
  let : IsDomain (CanonicalOpenChartRing25 K) :=
    canonicalOpenChartRing_isDomain_good25 p hp K
  exact Nat.card_congr (canonicalPointPlaceEquivGood25 p hp K).symm

end N25.Endgame

namespace N25

end N25
