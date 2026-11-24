-- Prove2me | solution 1 for GlobalTheory.IsoLimit.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:18:35.388232+00:00
-- url     : https://prove2.me/submissions/19000e10-ac62-4c0b-a323-dc08cddbfd61

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsIsoOfIsClosedImmersionOfThickenings
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_IsIsoOfIsClosedImmersion
import Theorems.Thm_GlobalTheory_IsoLimit_isIso_of_isClosedImmersion

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.IsoLimit
open ThickeningClosed
namespace GlobalTheory.IsoLimit
theorem _root_.solution : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] [IsNoetherianRing V] (Γ₁ Y : Over (Spec (CommRingCat.of V))) (p : Γ₁ ⟶ Y) [IsProper Y.hom] [IsProper p.left], (∀ e, IsIso ((Over.pullback (thick V (IsLocalRing.maximalIdeal V) e)).map p)) → IsIso p := by
  intro V _ _ _ _ Γ₁ Y p _ _ h
  have hw : p.left ≫ Y.hom = Γ₁.hom := Over.w p
  let q (e : ℕ) : pullback Γ₁.hom (thick V (IsLocalRing.maximalIdeal V) e) ⟶
      pullback Y.hom (thick V (IsLocalRing.maximalIdeal V) e) :=
    ((Over.pullback (thick V (IsLocalRing.maximalIdeal V) e)).map p).left
  have hq (e : ℕ) : IsIso (q e) := by
    haveI := h e
    exact inferInstanceAs (IsIso ((Over.forget _).map
      ((Over.pullback (thick V (IsLocalRing.maximalIdeal V) e)).map p)))
  have q1 (e : ℕ) : q e ≫ pullback.fst _ _ = pullback.fst _ _ ≫ p.left := pullback.lift_fst _ _ _
  have q2 (e : ℕ) : q e ≫ pullback.snd _ _ = pullback.snd _ _ := pullback.lift_snd _ _ _
  have hd : IsIso (pullback.diagonal p.left) := by
    refine isIso_of_isClosedImmersion (pullback.fst p.left p.left ≫ p.left ≫ Y.hom) _ fun n ↦ ?_
    have c := pullback.condition (f := pullback.fst p.left p.left ≫ p.left ≫ Y.hom)
      (g := thick V (IsLocalRing.maximalIdeal V) n)
    have c' := pullback.condition (f := p.left) (g := p.left)
    set u := pullback.fst (pullback.fst p.left p.left ≫ p.left ≫ Y.hom)
      (thick V (IsLocalRing.maximalIdeal V) n)
    set v := pullback.snd (pullback.fst p.left p.left ≫ p.left ≫ Y.hom)
      (thick V (IsLocalRing.maximalIdeal V) n)
    have e : pullback.lift (f := Γ₁.hom) (u ≫ pullback.fst _ _) v
          (by rw [← c, ← hw, Category.assoc]) =
        pullback.lift (f := Γ₁.hom) (u ≫ pullback.snd _ _) v
          (by rw [← c, ← hw, Category.assoc, ← reassoc_of% c']) := by
      haveI := hq n
      rw [← cancel_mono (q n)]
      apply pullback.hom_ext
      · simp only [Category.assoc, q1, pullback.lift_fst_assoc, c']
      · simp only [Category.assoc, q2, pullback.lift_snd]
    have e' := congrArg (· ≫ pullback.fst _ _) e
    simp only [pullback.lift_fst] at e'
    refine ⟨u ≫ pullback.fst _ _, ?_⟩
    apply pullback.hom_ext
    · simp
    · simp [e']
  have hm : Mono p.left := (pullback.isIso_diagonal_iff p.left).1 hd
  have hc : IsClosedImmersion p.left :=
    (IsClosedImmersion.iff_isProper_and_mono p.left).2 ⟨‹_›, hm⟩
  have hi : IsIso p.left := by
    refine isIso_of_isClosedImmersion Y.hom _ fun n ↦ ?_
    haveI := hq n
    exact ⟨inv (q n) ≫ pullback.fst _ _, by rw [Category.assoc, ← q1, IsIso.inv_hom_id_assoc]⟩
  have : IsIso ((Over.forget _).map p) := hi
  exact isIso_of_reflects_iso p (Over.forget _)
end GlobalTheory.IsoLimit
