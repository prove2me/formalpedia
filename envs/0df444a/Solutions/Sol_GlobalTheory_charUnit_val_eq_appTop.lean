-- Prove2me | solution 1 for GlobalTheory.charUnit_val_eq_appTop
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:16:41.380662+00:00
-- url     : https://prove2.me/submissions/704f8e04-d5c5-4af8-9209-d88bc3845466

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegExp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsPullbackCompIsoMonHom

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
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (S : Scheme.{0}) (X : Type) [AddCommGroup X] (χ : X) :
    (charUnit S X χ).val = (pullback.fst (splitTorusAff ZU X).hom (toZ S)).appTop.hom
      ((Scheme.ΓSpecIso (torusRing ZU X)).inv.hom (AddMonoidAlgebra.single χ 1)) := by
  have h : ∀ (Y : Scheme.{0}) (i : (⊤ : Y.Opens) ⟶ ⊤) (a : Γ(Y, ⊤)),
      (Y.presheaf.map i.op).hom a = a := fun Y i a => by
    rw [Subsingleton.elim i (𝟙 _), op_id, Y.presheaf.map_id]
    rfl
  exact h _ _ _
end GlobalTheory
