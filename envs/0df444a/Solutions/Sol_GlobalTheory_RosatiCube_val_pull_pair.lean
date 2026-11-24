-- Prove2me | solution 1 for GlobalTheory.RosatiCube.val_pull_pair
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T20:07:12.330667+00:00
-- url     : https://prove2.me/submissions/fce1ec0b-2fe2-4ad6-bc71-6ccc632a65ca

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RosVal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_RosatiCubicalAdditive
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_pull


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (rosatiφ rosatiε zero2)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.RosatiCube
open ReciprocityTheory.ChartRestriction.G.DVR
variable {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A]
variable {L : LB A.left}
omit [IsCommMonObj A]
namespace GlobalTheory.RosatiCube
theorem _root_.solution {K : Type} [Fintype K] {φ : K → ((A ⊗ A).left ⟶ A.left)} {ε : K → ℤ}
    (u : LB.Gen (LB.LinComb L φ ε)) {T T' : Over S} (ρ : T' ⟶ T) {z : T'.left} {J} (hJ : Good L z J) (a b : T ⟶ A) :
    val (LB.pullGen L _ _ u (lift a b).left) ρ.left z J = val₂ u z J (ρ ≫ a) (ρ ≫ b) := by
  rw [val_pull hJ, ← Over.comp_left, comp_lift]; rfl
end GlobalTheory.RosatiCube
