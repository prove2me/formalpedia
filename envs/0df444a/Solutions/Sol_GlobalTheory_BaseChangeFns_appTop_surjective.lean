-- Prove2me | solution 1 for GlobalTheory.BaseChangeFns.appTop_surjective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:01:28.501033+00:00
-- url     : https://prove2.me/submissions/55b9e4dd-b9fe-4df1-8b32-3a1e338dcea9

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_AppTopSurjective
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
namespace GlobalTheory.BaseChangeFns
private theorem surjective_appTop_of_iso {X Y : Scheme.{0}} (e : X ≅ Y) : Function.Surjective e.hom.appTop.hom := by
  first
  | exact (ConcreteCategory.bijective_of_isIso e.hom.appTop).2
  | exact (ConcreteCategory.bijective_of_isIso (e.hom.app ⊤)).2
  | exact fun a => ⟨e.inv.appTop.hom a, by
      rw [← CommRingCat.comp_apply, ← Scheme.comp_appTop, e.inv_hom_id, Scheme.id_appTop]; rfl⟩
private theorem surjective_appTop_comp {X Y Z : Scheme.{0}} (p : X ⟶ Y) (q : Y ⟶ Z)
    (hp : Function.Surjective p.appTop.hom) (hq : Function.Surjective q.appTop.hom) :
    Function.Surjective (p ≫ q).appTop.hom := by
  first
  | exact hp.comp hq
  | (rw [Scheme.comp_appTop, CommRingCat.hom_comp, RingHom.coe_comp]; exact hp.comp hq)
  | exact surj_comp hp hq
private theorem isAbelianScheme_pullback' {S₀ S : Scheme.{0}} {B : Over S₀} [GrpObj B] (t : S ⟶ S₀)
    (hB : IsAbelianScheme B) : IsAbelianScheme ((Over.pullback t).obj B) := by
  have h1 := hB.smooth
  have h2 := hB.proper
  have h3 := hB.geomConnected
  have h4 := hB.comm
  constructor
  case comm =>
    first
    | infer_instance
    | exact Functor.obj.instIsCommMonObj _
  case smooth =>
    show Smooth (pullback.snd B.hom t)
    first
    | infer_instance
    | exact MorphismProperty.pullback_snd _ _ h1
  case proper =>
    show IsProper (pullback.snd B.hom t)
    first
    | infer_instance
    | exact MorphismProperty.pullback_snd _ _ h2
  case geomConnected =>
    show GeometricallyConnected (pullback.snd B.hom t)
    first
    | infer_instance
    | exact MorphismProperty.pullback_snd _ _ h3
end GlobalTheory.BaseChangeFns
end
end

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory GlobalTheory.BaseChangeFns
namespace GlobalTheory.BaseChangeFns
theorem _root_.solution (hG : Out.GlobalFnsSt) {S₀ : Scheme.{0}} {B : Over S₀} [GrpObj B]
    (hB : IsAbelianScheme B) {S X : Scheme.{0}} {t : S ⟶ S₀} {π : X ⟶ B.left} {f : X ⟶ S}
    (h : IsPullback π f B.hom t) : Function.Surjective f.appTop.hom := by
  have key : Function.Surjective (pullback.snd B.hom t).appTop.hom :=
    (hG S ((Over.pullback t).obj B) (isAbelianScheme_pullback' t hB)).2
  rw [← h.isoPullback_hom_snd]
  exact surjective_appTop_comp _ _ (surjective_appTop_of_iso _) key
end GlobalTheory.BaseChangeFns
