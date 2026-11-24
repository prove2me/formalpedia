-- Prove2me | solution 1 for GlobalTheory.splitTorus_hom_proper_trivial_field
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:01:57.463228+00:00
-- url     : https://prove2.me/submissions/f0109827-e004-423f-8dbb-20cda0786dc1

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegExp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_Torus2GammaBijective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_SplitTorusHomProperTrivialField
import Theorems.Thm_GlobalTheory_TorusToProper_point_ext
import Theorems.Thm_GlobalTheory_TorusToProper_units_family_trivial
import Theorems.Thm_GlobalTheory_TorusToProper_pt_nat
import Theorems.Thm_GlobalTheory_TorusToProper_pt_univ
import Theorems.Thm_GlobalTheory_TorusToProper_char_eq_prod

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
open TorusToProper
namespace GlobalTheory
theorem _root_.solution (K : Type) [Field K] (X : Type) [AddCommGroup X]
    [Module.Free ℤ X] [Module.Finite ℤ X] (B : Over (Spec (CommRingCat.of K))) [GrpObj B]
    [IsProper B.hom] (f : splitTorus (Spec (CommRingCat.of K)) X ⟶ B) (hf : IsMonHom f) :
    f = toUnit _ ≫ η[B] := by
  let Ψ : ∀ (R : Type) [CommRing R] [Algebra K R], (Multiplicative X →* Rˣ) →* (sp K R ⟶ B) :=
    fun R _ _ => (MonoidHom.mk' (fun t => t ≫ f) (fun s t => MonObj.mul_comp s t f)).comp (pt K X R)
  have hΨ : ∀ (R : Type) [CommRing R] [Algebra K R] φ, Ψ R φ = pt K X R φ ≫ f := fun _ _ _ _ => rfl
  have h1 : ∀ (l : X →+ ℤ) (L : Type) [Field L] [Algebra K L] (x : Lˣ), Ψ L (coch l Lˣ x) = 1 := by
    intro l L _ _ x
    refine units_family_trivial (fun R _ _ => (Ψ R).comp (coch l Rˣ)) ?_ L x
    intro R R' _ _ _ _ g y
    simp only [MonoidHom.comp_apply, hΨ]
    rw [← Category.assoc, ← pt_nat]
    congr 2
    refine MonoidHom.ext fun a => ?_
    exact (map_zpow (Units.map (g : R →* R')) y _).symm
  have h2 : ∀ (L : Type) [Field L] [Algebra K L] φ, Ψ L φ = 1 := by
    intro L _ _ φ
    rw [char_eq_prod X (Module.Free.chooseBasis ℤ X) _ φ, ← MonoidHom.mem_ker]
    exact Subgroup.prod_mem _ fun i _ => h1 _ L _
  have : IsDomain (AddMonoidAlgebra K X) := NoZeroDivisors.to_isDomain _
  let R := AddMonoidAlgebra K X
  let F := FractionRing R
  have h3 : pt K X R (univ K X) ≫ f = pt K X R (univ K X) ≫ toUnit _ ≫ η[B] := by
    apply point_ext (IsScalarTower.toAlgHom K R F) (IsFractionRing.injective R F)
    rw [← Category.assoc, ← pt_nat, ← hΨ, h2, ← Category.assoc, ← Category.assoc, Hom.one_def]
    congr 1
    exact toUnit_unique _ _
  have h4 : (pt K X R (univ K X)).left ≫ f.left =
      (pt K X R (univ K X)).left ≫ (toUnit _ ≫ η[B]).left := congrArg CommaMorphism.left h3
  rw [pt_univ] at h4
  ext1
  exact (cancel_epi _).1 h4
end GlobalTheory
