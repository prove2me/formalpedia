-- Prove2me | solution 1 for GlobalTheory.MulEtaleDvr.flat_mulN_field
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:17:25.128104+00:00
-- url     : https://prove2.me/submissions/4b7fdffb-e541-4b26-8c7e-4929592f8c9c

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FormallyUnramifiedMulN
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FlatOfFormallyUnramifiedGrpEnd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_RingHomFlatCodescendsAlongFaithfullyFlat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FlatOfFlatFibresDvr
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_IsUnitNatCastSections
import Theorems.Thm_GlobalTheory_MulEtaleDvr_isMonHom_mulN
import Theorems.Thm_GlobalTheory_MulEtaleDvr_pullback_map_mulN
import Theorems.Thm_GlobalTheory_MulEtaleDvr_isUnit_natCast_sections
import Theorems.Thm_GlobalTheory_flat_of_flat_fieldBaseChange
import Theorems.Thm_GlobalTheory_flat_of_formallyUnramified_grpEnd
import Theorems.Thm_GlobalTheory_formallyUnramified_mulN


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
theorem _root_.solution (k : Type) [Field k] (G : Over (Sp k)) [GrpObj G] [IsCommMonObj G] (n : ℕ)
    (hn : IsUnit (n : k)) (hG : LocallyOfFiniteType G.hom) : Flat (mulN G n).left := by
  refine flat_of_flat_fieldBaseChange k (AlgebraicClosure k) (algebraMap _ _) G G _ ?_
  rw [pullback_map_mulN]
  refine flat_of_formallyUnramified_grpEnd _ _ _ ?_ (isMonHom_mulN _ n)
    (formallyUnramified_mulN _ _ n (isUnit_natCast_sections ?_))
  · exact inferInstanceAs (LocallyOfFiniteType (pullback.snd G.hom _))
  · simpa using hn.map (algebraMap k (AlgebraicClosure k))
end GlobalTheory.MulEtaleDvr
