-- Prove2me | solution 1 for GlobalTheory.MulEtaleDvr.isMonHom_mulN
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T18:59:27.784811+00:00
-- url     : https://prove2.me/submissions/aed302c8-fae5-4005-aa4e-f5775833ef83

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FormallyUnramifiedMulN
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FlatOfFormallyUnramifiedGrpEnd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_RingHomFlatCodescendsAlongFaithfullyFlat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FlatOfFlatFibresDvr
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_IsUnitNatCastSections
import Theorems.Thm_GlobalTheory_MulUnramified_comp_mulN


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
theorem _root_.solution (G : Over S) [GrpObj G] [IsCommMonObj G] (n : ℕ) : IsMonHom (mulN G n) where
  one_hom := by rw [MulUnramified.comp_mulN, one_eq_one, one_pow]
  mul_hom := by
    rw [MulUnramified.comp_mulN, mul_eq_mul, comp_mul, mul_pow]
    congr 1 <;> simp [MulUnramified.comp_mulN]
end GlobalTheory.MulEtaleDvr
