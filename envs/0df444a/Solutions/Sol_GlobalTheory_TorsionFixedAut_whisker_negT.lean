-- Prove2me | solution 1 for GlobalTheory.TorsionFixedAut.whisker_negT
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:32:54.072483+00:00
-- url     : https://prove2.me/submissions/1337697a-e235-41a3-80ad-f531b30fc902

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_EqIdOfFixesTorsion

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory GlobalTheory.TorsionFixedAut
open ReciprocityTheory.ChartRestriction.G.Geo.Tor TopologicalSpace
variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} {T : Over S}
variable (σ : A ⟶ A) (c : LB.Gen (LB.LinComb L (K := Fin 2) ![σ.left, 𝟙 A.left] ![1, -1]))
variable [IsMonHom σ]
namespace GlobalTheory.TorsionFixedAut
theorem _root_.solution : negT A T ≫ T ◁ σ = T ◁ σ ≫ negT A T := by
  apply CartesianMonoidalCategory.hom_ext
  · simp [negT]
  · simp [negT]
end GlobalTheory.TorsionFixedAut
