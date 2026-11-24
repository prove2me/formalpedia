-- Prove2me | solution 1 for GlobalTheory.RosatiCube.IsNormGen.val_origin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T20:07:11.536347+00:00
-- url     : https://prove2.me/submissions/4f64fa11-336d-43e4-a798-5d59769b7e30

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RosVal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_RosatiCubicalAdditive
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_corr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_one
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
namespace GlobalTheory.RosatiCube
namespace IsNormGen
theorem _root_.solution {f g : A ⟶ A} {u : LB.Gen (LB.LinComb L (rosatiφ A f g) rosatiε)} (hu : IsNormGen L f g u)
    {y : (𝟙_ (Over S)).left} {J} (hJ : Good L y J) : val₂ u y J (1 : 𝟙_ (Over S) ⟶ A) 1 = 1 := by
  have e : lift (1 : 𝟙_ (Over S) ⟶ A) (1 : 𝟙_ (Over S) ⟶ A) = lift η[A] η[A] := by simp [Hom.one_def]
  have := val_corr hJ hu.2 (𝟙 _)
  rw [val_pull hJ, Category.id_comp, val_one] at this
  rw [val₂, e]; exact this
end IsNormGen
end GlobalTheory.RosatiCube
