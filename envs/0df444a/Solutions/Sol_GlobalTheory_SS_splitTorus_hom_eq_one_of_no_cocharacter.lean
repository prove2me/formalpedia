-- Prove2me | solution 1 for GlobalTheory.SS.splitTorus_hom_eq_one_of_no_cocharacter
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T20:24:18.025893+00:00
-- url     : https://prove2.me/submissions/09b6cb53-fa2a-45f1-b9b3-7d07cdb9ff3a

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_HomBaseChangeBijectiveOfLeNilradical
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_SplitTorusHomEqOneOfNoCocharacter
import Theorems.Thm_GlobalTheory_SplitTorus_torusMap_add
import Theorems.Thm_GlobalTheory_SplitTorus_torusMap_comp
import Theorems.Thm_GlobalTheory_SplitTorus_torusMap_id
import Theorems.Thm_GlobalTheory_SplitTorus_torusMap_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
open GlobalTheory GlobalTheory.SS
namespace GlobalTheory.SS
theorem _root_.solution :
    ∀ (S : Scheme.{0}) (B : Over S) [GrpObj B] (X : Type) [AddCommGroup X] [Module.Free ℤ X]
      [Module.Finite ℤ X], (∀ f : Gm S ⟶ B, IsMonHom f → f = 1) →
      ∀ u : splitTorus S X ⟶ B, IsMonHom u → u = 1 := by
  intro S B _ X _ _ _ h u hu
  classical
  let b := Module.Free.chooseBasis ℤ X
  let l : _ → (X →+ ULift.{0} ℤ) := fun i =>
    (AddEquiv.ulift : ULift.{0} ℤ ≃+ ℤ).symm.toAddMonoidHom.comp (b.coord i).toAddMonoidHom
  let c : _ → (ULift.{0} ℤ →+ X) := fun i => SplitTorus.uliftMultiples X (b i)
  have h1 : ∀ i, SplitTorus.torusMap S ((c i).comp (l i)) ≫ u = 1 := fun i => by
    have e : SplitTorus.torusMap S (l i) ≫ u = 1 := h _ (inferInstanceAs
      (IsMonHom (SplitTorus.torusMap S (l i) ≫ u)))
    rw [SplitTorus.torusMap_comp, Category.assoc, e, MonObj.comp_one]
  have h2 : ∀ s : Finset (Module.Free.ChooseBasisIndex ℤ X),
      SplitTorus.torusMap S (∑ i ∈ s, (c i).comp (l i)) ≫ u = 1 := fun s => by
    induction s using Finset.induction_on with
    | empty => rw [Finset.sum_empty, SplitTorus.torusMap_zero, MonObj.one_comp]
    | insert i s hi ih =>
      rw [Finset.sum_insert hi, SplitTorus.torusMap_add, MonObj.mul_comp, h1, ih, _root_.mul_one]
  have h3 : (∑ i, (c i).comp (l i)) = AddMonoidHom.id X := by
    ext x
    rw [AddMonoidHom.finset_sum_apply]
    exact b.sum_repr x
  have := h2 Finset.univ
  rwa [h3, SplitTorus.torusMap_id, Category.id_comp] at this
end GlobalTheory.SS
