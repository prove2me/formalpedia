-- Prove2me | solution 1 for GlobalTheory.Models.isFinite_lift_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T18:58:12.141968+00:00
-- url     : https://prove2.me/submissions/cbc9df6c-93e2-424b-aae9-8b481ee121a7

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigidSys
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Splits
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GtBaseChangeSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabComp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_PullCub
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_AuxiliaryInertOddPrime
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_IsFiniteLiftComp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models
open GlobalTheory GlobalTheory.Models
namespace GlobalTheory.Models
theorem _root_.solution {X X' X'' S S' S'' : Scheme.{0}} {s : X ⟶ S} {s' : X' ⟶ S'} {s'' : X'' ⟶ S''}
    {g : S' ⟶ S} {g' : S'' ⟶ S'} {g'' : S'' ⟶ S} (hg : g'' = g' ≫ g) {p : X' ⟶ X} {p' : X'' ⟶ X'}
    (w : p ≫ s = s' ≫ g) (w' : p' ≫ s' = s'' ≫ g') (w'' : (p' ≫ p) ≫ s = s'' ≫ g'')
    (h : IsFinite (pullback.lift p s' w)) (h' : IsFinite (pullback.lift p' s'' w')) :
    IsFinite (pullback.lift (p' ≫ p) s'' w'') := by
  subst hg
  obtain ⟨θ, hθ1, hθ2⟩ : ∃ θ : pullback s' g' ⟶ pullback s (g' ≫ g),
      θ ≫ pullback.fst s (g' ≫ g) = pullback.fst s' g' ≫ p ∧ θ ≫ pullback.snd s (g' ≫ g) = pullback.snd s' g' :=
    ⟨pullback.lift (pullback.fst s' g' ≫ p) (pullback.snd s' g')
      (by rw [Category.assoc, w, pullback.condition_assoc]), pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  obtain ⟨κ, hκ1, hκ2⟩ : ∃ κ : pullback s (g' ≫ g) ⟶ pullback s g,
      κ ≫ pullback.fst s g = pullback.fst s (g' ≫ g) ∧ κ ≫ pullback.snd s g = pullback.snd s (g' ≫ g) ≫ g' :=
    ⟨pullback.lift (pullback.fst s (g' ≫ g)) (pullback.snd s (g' ≫ g) ≫ g')
      (by rw [Category.assoc]; exact pullback.condition), pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩

  have hfac : pullback.lift (p' ≫ p) s'' w'' = pullback.lift p' s'' w' ≫ θ := by
    apply pullback.hom_ext
    · simp only [Category.assoc, hθ1, pullback.lift_fst, pullback.lift_fst_assoc]
    · simp only [Category.assoc, hθ2, pullback.lift_snd]

  have hright : IsPullback (pullback.snd s (g' ≫ g)) κ g' (pullback.snd s g) := by
    refine IsPullback.of_bot ?_ hκ2.symm (IsPullback.of_hasPullback s g).flip
    rw [hκ1]
    exact (IsPullback.of_hasPullback s (g' ≫ g)).flip

  have hsq : IsPullback θ (pullback.fst s' g') κ (pullback.lift p s' w) := by
    refine IsPullback.of_right ?_ ?_ hright
    · rw [hθ2, pullback.lift_snd]
      exact (IsPullback.of_hasPullback s' g').flip
    · apply pullback.hom_ext
      · simp only [Category.assoc, hκ1, hθ1, pullback.lift_fst]
      · simp only [Category.assoc, hκ2, reassoc_of% hθ2, pullback.lift_snd, pullback.condition]
  have hfin : IsFinite θ := MorphismProperty.of_isPullback (P := @IsFinite) hsq.flip h
  rw [hfac]
  infer_instance
end GlobalTheory.Models
