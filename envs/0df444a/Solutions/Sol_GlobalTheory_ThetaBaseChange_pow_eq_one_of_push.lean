-- Prove2me | solution 1 for GlobalTheory.ThetaBaseChange.pow_eq_one_of_push
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:08:33.186054+00:00
-- url     : https://prove2.me/submissions/4d4ff6a3-276d-4bdf-af21-301bf94b3dca

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsSecOfLocal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_TorsionEqOneOfTranslationKeepsRatios
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_PowEqOneOfPush
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.ThetaBaseChange
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.FieldBaseChange GlobalTheory.ThetaScalar
variable {S S' W : Scheme.{0}} {g : S' ⟶ S} {t : W ⟶ S} {t' : W ⟶ S'}
variable {A : Over S} {A' : Over S'} [GrpObj A] [GrpObj A'] {Φ : A'.left ⟶ A.left}
namespace GlobalTheory.ThetaBaseChange
theorem _root_.solution (ht : t' ≫ g = t) (hp : IsGrpPullback A' A g Φ) {x : Over.mk t ⟶ A} {x' : Over.mk t' ⟶ A'}
    (hx : x'.left ≫ Φ = x.left) {k : ℕ} (h : x ^ k = 1) : x' ^ k = 1 := by
  subst ht
  have hψ : ∀ y : Over.mk t' ⟶ A', (y.left ≫ Φ) ≫ A.hom = (Over.mk t').hom ≫ g := fun y => by
    rw [Category.assoc, hp.1.w, ← Category.assoc, Over.w]
  let ψ : (Over.mk t' ⟶ A') → (Over.mk (t' ≫ g) ⟶ A) := fun y => Over.homMk (y.left ≫ Φ) (hψ y)
  have hmul : ∀ y z, ψ (y * z) = ψ y * ψ z := fun y z =>
    Over.OverMorphism.ext (hp.2 (Over.mk t') y z (ψ y) (ψ z) rfl rfl).symm
  let Ψ : (Over.mk t' ⟶ A') →* (Over.mk (t' ≫ g) ⟶ A) := MonoidHom.mk' ψ hmul
  have hinj : Function.Injective ψ := fun y z e => by
    have e' : y.left ≫ Φ = z.left ≫ Φ := congrArg (fun f => f.left) e
    exact Over.OverMorphism.ext (hp.1.hom_ext e' (by rw [Over.w, Over.w]))
  have hx' : ψ x' = x := Over.OverMorphism.ext hx
  apply hinj
  change Ψ (x' ^ k) = Ψ 1
  rw [map_pow, map_one]
  show ψ x' ^ k = 1
  rw [hx', h]
end GlobalTheory.ThetaBaseChange
