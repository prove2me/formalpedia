-- Prove2me | solution 1 for GlobalTheory.MulPullSec.powGen_isGen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T18:59:28.4408+00:00
-- url     : https://prove2.me/submissions/4f8678e5-5918-49db-80ff-bbe06762643f

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaFamilyOrigin_ExistsMulPullSec

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.MulPullSec
variable {X Y Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K]
namespace GlobalTheory.MulPullSec
theorem _root_.solution {φ : K → (Y ⟶ X)} {ε : K → ℤ} {t : LB.Gen (LB.LinComb L φ ε)} (ht : t.IsGen) (N : ℕ) :
    (powGen t N).IsGen := by
  intro i j
  have e := congrArg (· ^ N) (ht i j)
  simp only [mul_pow] at e
  refine (map_pow _ _ _).trans (e.trans (congrArg₂ (· * ·) ?_ (map_pow _ _ _).symm))
  refine (Finset.prod_pow _ _ _).symm.trans (Finset.prod_congr rfl fun k _ => ?_)
  rw [zpow_mul, zpow_natCast]
  rfl
end GlobalTheory.MulPullSec
