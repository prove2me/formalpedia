-- Prove2me | solution 1 for GlobalTheory.MulEtaleDvr.isPullback_torsion
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T18:59:28.445333+00:00
-- url     : https://prove2.me/submissions/cc96e5a6-a1cc-4944-a7c0-48d8345a29c1

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FormallyUnramifiedMulN
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FlatOfFormallyUnramifiedGrpEnd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_RingHomFlatCodescendsAlongFaithfullyFlat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FlatOfFlatFibresDvr
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_IsUnitNatCastSections

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
theorem _root_.solution (G : Over S) [GrpObj G] (n : ℕ) :
    IsPullback (torsion.ι G n).left (torsion G n).hom (mulN G n).left η[G].left := by
  have h := (IsPullback.of_hasPullback (mulN G n) (η : 𝟙_ (Over S) ⟶ G)).map (Over.forget S)
  have e : (pullback.snd (mulN G n) (η : 𝟙_ (Over S) ⟶ G)).left = (torsion G n).hom :=
    (Category.comp_id _).symm.trans (Over.w (pullback.snd (mulN G n) (η : 𝟙_ (Over S) ⟶ G)))
  exact e ▸ h
end GlobalTheory.MulEtaleDvr
