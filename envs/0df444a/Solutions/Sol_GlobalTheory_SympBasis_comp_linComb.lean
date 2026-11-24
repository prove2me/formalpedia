-- Prove2me | solution 1 for GlobalTheory.SympBasis.comp_linComb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:00:02.854014+00:00
-- url     : https://prove2.me/submissions/145589d2-6f51-4dbf-b339-c06a916d145d

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_SymplecticTorsionSystemIsGeometricBasis
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
namespace GlobalTheory.SympBasis
private theorem comp_list_prod_eq_prod_map_comp_over {S : Scheme.{0}} {A T T' : Over S} [GrpObj A] (f : T' ⟶ T)
    (l : List (T ⟶ A)) : f ≫ l.prod = (l.map (f ≫ ·)).prod := by
  induction l with
  | nil => simp [MonObj.comp_one]
  | cons x l ih => simp [List.prod_cons, MonObj.comp_mul, ih]
end GlobalTheory.SympBasis
namespace GlobalTheory
end GlobalTheory
end

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory GlobalTheory.SympBasis
namespace GlobalTheory.SympBasis
theorem _root_.solution {S : Scheme.{0}} {A T T' : Over S} [GrpObj A] (f : T' ⟶ T) {n : ℕ} (y : Fin n → (T ⟶ A))
    (a : Fin n → ℕ) : f ≫ Out.linComb y a = Out.linComb (fun i => f ≫ y i) a := by
  unfold Out.linComb
  rw [comp_list_prod_eq_prod_map_comp_over, List.map_ofFn]
  simp [Function.comp_def, MonObj.comp_pow]
end GlobalTheory.SympBasis
