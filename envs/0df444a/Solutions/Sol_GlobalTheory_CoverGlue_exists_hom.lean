-- Prove2me | solution 1 for GlobalTheory.CoverGlue.exists_hom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T14:31:47.759019+00:00
-- url     : https://prove2.me/submissions/b73e4c6b-49bc-4272-859c-65ff333fac27

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_FiniteHomogeneousInf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsUniqueHom
import Theorems.Thm_GlobalTheory_CoverGlue_existsUnique_hom

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
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
open GlobalTheory GlobalTheory.CoverGlue
namespace GlobalTheory.CoverGlue
theorem _root_.solution {X Y : Scheme.{0}} {I : Type} {Z : I → Scheme.{0}} (ψ : ∀ i, Z i ⟶ X)
    (hψ : ∀ i, IsOpenImmersion (ψ i)) (hc : ∀ x : X, ∃ i, x ∈ Set.range (ψ i)) (f : ∀ i, Z i ⟶ Y)
    {B : I → I → Scheme.{0}} {a : ∀ i j, B i j ⟶ Z i} {b : ∀ i j, B i j ⟶ Z j}
    (hB : ∀ i j, IsPullback (a i j) (b i j) (ψ i) (ψ j)) (hf : ∀ i j, a i j ≫ f i = b i j ≫ f j) :
    ∃ F : X ⟶ Y, ∀ i, ψ i ≫ F = f i :=
  (existsUnique_hom ψ hψ hc f fun i j _ x y e => by
    rw [← (hB i j).lift_fst x y e, Category.assoc, hf, ← Category.assoc, (hB i j).lift_snd]).exists
end GlobalTheory.CoverGlue
