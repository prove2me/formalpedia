-- Prove2me | solution 1 for GlobalTheory.TorusConst.eq_const
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:23:17.312893+00:00
-- url     : https://prove2.me/submissions/3be58c57-c71c-490f-8fd6-702a86be5686

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_SplitTorusHomProperTrivialField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_SplitTorusToAbelianVarietyConst
import Theorems.Thm_GlobalTheory_TorusConst_ev_comp_cst
import Theorems.Thm_GlobalTheory_TorusConst_ev_tU
import Theorems.Thm_GlobalTheory_TorusConst_ev_eq
import Theorems.Thm_GlobalTheory_TorusToProper_char_eq_prod
import Theorems.Thm_GlobalTheory_TorusToProper_point_ext
import Theorems.Thm_GlobalTheory_TorusToProper_pt_nat
import Theorems.Thm_GlobalTheory_TorusToProper_pt_univ


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
open GlobalTheory
open GlobalTheory.TorusConst
open Polynomial TorusToProper
variable {K : Type} [Field K] {B : Over (Spec (CommRingCat.of K))}
namespace GlobalTheory.TorusConst
theorem _root_.solution (Y : Type) [AddCommGroup Y] [Module.Free ℤ Y] [Module.Finite ℤ Y] [GrpObj B]
    [IsProper B.hom] (f : splitTorus (Spec (CommRingCat.of K)) Y ⟶ B) :
    f = toUnit _ ≫ η ≫ f := by
  have h1 : ∀ (L : Type) [Field L] [Algebra K L] (φ : Multiplicative Y →* Lˣ) (l : Y →+ ℤ) (x : Lˣ),
      pt K Y L (coch l Lˣ x * φ) ≫ f = pt K Y L φ ≫ f := by
    intro L _ _ φ l x
    let ψ : Multiplicative Y →* (LaurentPolynomial L)ˣ :=
      coch l _ (tU L) * (Units.map (cst K L : L →* LaurentPolynomial L)).comp φ
    have h2 : ∀ x : Lˣ, spm (ev (AlgHom.id K L) x) ≫ pt K Y _ ψ = pt K Y L (coch l Lˣ x * φ) := by
      intro x
      rw [← pt_nat]
      congr 1
      refine MonoidHom.ext fun a => ?_
      have e1 : Units.map (ev (AlgHom.id K L) x : LaurentPolynomial L →* L) (tU L) = x :=
        Units.ext (ev_tU _ _)
      have e2 : Units.map (ev (AlgHom.id K L) x : LaurentPolynomial L →* L)
          (Units.map (cst K L : L →* LaurentPolynomial L) (φ a)) = φ a :=
        Units.ext (AlgHom.congr_fun (ev_comp_cst (AlgHom.id K L) x) _)
      change Units.map (ev (AlgHom.id K L) x : LaurentPolynomial L →* L)
        (tU L ^ l a.toAdd * Units.map (cst K L : L →* LaurentPolynomial L) (φ a)) =
        x ^ l a.toAdd * φ a
      rw [map_mul, map_zpow, e1, e2]
    have h3 := ev_eq (pt K Y _ ψ ≫ f) x 1
    rwa [← Category.assoc, ← Category.assoc, h2, h2, map_one, _root_.one_mul] at h3
  have h2 : ∀ (L : Type) [Field L] [Algebra K L] (φ : Multiplicative Y →* Lˣ),
      pt K Y L φ ≫ f = pt K Y L 1 ≫ f := by
    intro L _ _ φ
    rw [char_eq_prod Y (Module.Free.chooseBasis ℤ Y) _ φ]
    generalize (Finset.univ : Finset (Module.Free.ChooseBasisIndex ℤ Y)) = s
    classical
    induction s using Finset.induction_on with
    | empty => rw [Finset.prod_empty]
    | insert i s hi ih => rw [Finset.prod_insert hi, h1, ih]
  have : IsDomain (AddMonoidAlgebra K Y) := NoZeroDivisors.to_isDomain _
  let R := AddMonoidAlgebra K Y
  let F := FractionRing R
  have h3 : pt K Y R (univ K Y) ≫ f = pt K Y R (univ K Y) ≫ toUnit _ ≫ η ≫ f := by
    apply point_ext (IsScalarTower.toAlgHom K R F) (IsFractionRing.injective R F)
    rw [← Category.assoc, ← pt_nat, h2, map_one, Hom.one_def, Category.assoc, ← Category.assoc,
      ← Category.assoc (spm _), ← Category.assoc (spm _ ≫ _), Category.assoc (toUnit _)]
    congr 1
    exact toUnit_unique _ _
  have h4 : (pt K Y R (univ K Y)).left ≫ f.left =
      (pt K Y R (univ K Y)).left ≫ (toUnit _ ≫ η ≫ f).left := congrArg CommaMorphism.left h3
  rw [pt_univ] at h4
  ext1
  exact (cancel_epi _).1 h4
end GlobalTheory.TorusConst
