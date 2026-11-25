-- Prove2me | solution 1 for GlobalTheory.IsoLimitIdeal.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T18:03:49.092023+00:00
-- url     : https://prove2.me/submissions/a9597351-3699-4b8e-a8af-3cbec6ef33f5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsIsoOfIsClosedImmersionOfThickenings
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_IsIsoOfIsClosedImmersion
import Theorems.Thm_GlobalTheory_IsoLimitIdeal_isIso_of_isClosedImmersion
import Theorems.Thm_GlobalTheory_Descent_freeIso_hom
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Descent.freeIso_hom



set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.IsoLimitIdeal
open ThickeningClosed
namespace GlobalTheory.IsoLimitIdeal
theorem _root_.solution : ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (I : Ideal R), I ≠ ⊤ → ∀ (Γ₁ Y : Over (Spec (CommRingCat.of R))) (p : Γ₁ ⟶ Y) [IsProper Y.hom] [IsProper p.left], (∀ e, IsIso ((Over.pullback (thick R I e)).map p)) → IsIso p := by
  intro V _ _ _ I hI Γ₁ Y p _ _ h
  have hw : p.left ≫ Y.hom = Γ₁.hom := Over.w p
  let q (e : ℕ) : pullback Γ₁.hom (thick V I e) ⟶
      pullback Y.hom (thick V I e) :=
    ((Over.pullback (thick V I e)).map p).left
  have hq (e : ℕ) : IsIso (q e) := by
    haveI := h e
    exact inferInstanceAs (IsIso ((Over.forget _).map
      ((Over.pullback (thick V I e)).map p)))
  have q1 (e : ℕ) : q e ≫ pullback.fst _ _ = pullback.fst _ _ ≫ p.left := pullback.lift_fst _ _ _
  have q2 (e : ℕ) : q e ≫ pullback.snd _ _ = pullback.snd _ _ := pullback.lift_snd _ _ _
  have hd : IsIso (pullback.diagonal p.left) := by
    refine isIso_of_isClosedImmersion I hI (pullback.fst p.left p.left ≫ p.left ≫ Y.hom) _ fun n ↦ ?_
    have c := pullback.condition (f := pullback.fst p.left p.left ≫ p.left ≫ Y.hom)
      (g := thick V I n)
    have c' := pullback.condition (f := p.left) (g := p.left)
    set u := pullback.fst (pullback.fst p.left p.left ≫ p.left ≫ Y.hom)
      (thick V I n)
    set v := pullback.snd (pullback.fst p.left p.left ≫ p.left ≫ Y.hom)
      (thick V I n)
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
    refine isIso_of_isClosedImmersion I hI Y.hom _ fun n ↦ ?_
    haveI := hq n
    exact ⟨inv (q n) ≫ pullback.fst _ _, by rw [Category.assoc, ← q1, IsIso.inv_hom_id_assoc]⟩
  have : IsIso ((Over.forget _).map p) := hi
  exact isIso_of_reflects_iso p (Over.forget _)
end GlobalTheory.IsoLimitIdeal
