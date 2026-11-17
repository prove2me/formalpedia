-- Prove2me | solution 1 for N25.Endgame.unitPlaneToXHGood25_coordinates
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T19:12:42.731978+00:00
-- url     : https://prove2.me/submissions/45eeb4df-747a-4933-aad2-671bcdf7b923

import Definitions.Def_N25_UnitPlaneModularMapGoodCharacteristic
import Theorems.Thm_N25_unitPlaneFieldPointLift25C_coordinates
import Definitions.Def_N25_UnitPlaneFieldPointLiftOverField
import Theorems.Thm_N25_unitRelation25_qExpansion_certificate
import Theorems.Thm_N25_U25C_zero_transcendental

/-! Coordinate formulas for the good-characteristic plane-to-modular map. -/
namespace N25.Endgame

/-- The plane-to-modular map sends the two plane coordinates to the prescribed modular units. -/
theorem _root_.solution
    (p : ℕ) [Fact p.Prime] (hp : p = 2 ∨ p = 3)
    (K : Type*) [Field K] [CharP K p] :
    unitPlaneToXHGood25 p hp K
        (algebraMap (N25.UnitPlaneRing25C K)
          (N25.UnitPlaneFF25C K) (N25.unitPlaneU25C K)) =
      N25.U25C K 0 ∧
    unitPlaneToXHGood25 p hp K
        (algebraMap (N25.UnitPlaneRing25C K)
          (N25.UnitPlaneFF25C K) (N25.unitPlaneV25C K)) =
      N25.U25C K 0 / N25.U25C K 1 := by
  cases hp <;>
    exact N25.unitPlaneFieldPointLift25C_coordinates
      (N25.U25C K 0) (N25.U25C K 0 / N25.U25C K 1)
      (N25.unitRelation25_qExpansion_certificate K)
      (N25.U25C_zero_transcendental K)

end N25.Endgame
