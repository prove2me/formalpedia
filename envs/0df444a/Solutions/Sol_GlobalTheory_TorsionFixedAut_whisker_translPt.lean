-- Prove2me | solution 1 for GlobalTheory.TorsionFixedAut.whisker_translPt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:50:23.412524+00:00
-- url     : https://prove2.me/submissions/0945dbd9-87e8-4890-83ec-d7e285f178b6

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
theorem _root_.solution {x : T ⟶ A} (hx : x ≫ σ = x) : T ◁ σ ≫ translPt A x = translPt A x ≫ σ := by
  show T ◁ σ ≫ ((fst T A ≫ x) * snd T A) = ((fst T A ≫ x) * snd T A) ≫ σ
  rw [MonObj.comp_mul, MonObj.mul_comp, whiskerLeft_snd, whiskerLeft_fst_assoc, Category.assoc, hx]
end GlobalTheory.TorsionFixedAut
