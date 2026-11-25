-- Prove2me | solution 1 for GlobalTheory.MulEtaleDvr.flat_pullback_mulN
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:28:34.450803+00:00
-- url     : https://prove2.me/submissions/8e93a917-e4b0-4df9-86d0-76bfe283318b

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FormallyUnramifiedMulN
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FlatOfFormallyUnramifiedGrpEnd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_RingHomFlatCodescendsAlongFaithfullyFlat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FlatOfFlatFibresDvr
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_IsUnitNatCastSections
import Theorems.Thm_GlobalTheory_MulEtaleDvr_pullback_map_mulN
import Theorems.Thm_GlobalTheory_MulEtaleDvr_flat_mulN_field

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory
open GlobalTheory.MulEtaleDvr
variable {S : Scheme.{0}}
namespace GlobalTheory.MulEtaleDvr
theorem _root_.solution {T k : Type} [CommRing T] [Field k] (σ : T →+* k) (G : Over (Sp T))
    [GrpObj G] [IsCommMonObj G] (n : ℕ) (hn : IsUnit (n : T)) (hG : LocallyOfFiniteType G.hom) :
    Flat ((Over.pullback (spMap σ)).map (mulN G n)).left := by
  rw [pullback_map_mulN]
  refine flat_mulN_field k _ n (by simpa using hn.map σ) ?_
  exact inferInstanceAs (LocallyOfFiniteType (pullback.snd G.hom _))
end GlobalTheory.MulEtaleDvr
