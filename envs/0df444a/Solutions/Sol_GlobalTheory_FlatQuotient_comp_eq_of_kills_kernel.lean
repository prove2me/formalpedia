-- Prove2me | solution 1 for GlobalTheory.FlatQuotient.comp_eq_of_kills_kernel
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T15:15:56.941799+00:00
-- url     : https://prove2.me/submissions/4aaacf8a-d74e-4ed0-b743-51fc0ccd080f

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegExp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_FlatQuotientIsoOfSameKernel

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
open GlobalTheory.FlatQuotient
variable {S : Scheme.{0}}
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
variable {S : Scheme.{0}}
namespace GlobalTheory.FlatQuotient
namespace _root_.GlobalTheory.FlatQuotient
theorem _root_.solution {G B B' T : Over S} [GrpObj G] [GrpObj B] [GrpObj B']
    (q : G ⟶ B) (i : T ⟶ G) (f : G ⟶ B') [IsMonHom q] [IsMonHom f]
    (hker : IsPullback i (toUnit _) q (η[B])) (hf : i ≫ f = toUnit _ ≫ η[B'])
    {Z : Over S} (g g' : Z ⟶ G) (h : g ≫ q = g' ≫ q) : g ≫ f = g' ≫ f := by
  have hk : (g * g'⁻¹) ≫ q = toUnit Z ≫ η[B] := by
    rw [mul_comp, GrpObj.inv_comp, h, mul_inv_cancel, Hom.one_def]
  have hl : hker.lift (g * g'⁻¹) (toUnit Z) hk ≫ i = g * g'⁻¹ := hker.lift_fst _ _ _
  have hone : (g * g'⁻¹) ≫ f = 1 := by
    rw [← hl, Category.assoc, hf, Hom.one_def, ← Category.assoc, toUnit_unique
      (hker.lift (g * g'⁻¹) (toUnit Z) hk ≫ toUnit T) (toUnit Z)]
  rw [mul_comp, GrpObj.inv_comp, mul_inv_eq_one] at hone
  exact hone
end _root_.GlobalTheory.FlatQuotient
end GlobalTheory.FlatQuotient
