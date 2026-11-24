-- Prove2me | solution 1 for GlobalTheory.ZM.SymmCommutant.entry_of_commute
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:19:09.472455+00:00
-- url     : https://prove2.me/submissions/4c252286-dc5f-49d5-afe6-bf0ac081c188

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsGaloisCover
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_FinrankSymmCommutantKroneckerLe

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
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZM.SymmCommutant
open Matrix
namespace GlobalTheory.ZM.SymmCommutant
theorem _root_.solution {K : Type} [Field K] {h : ℕ}
    (Ψ : Matrix (Fin 8 × Fin h) (Fin 8 × Fin h) K)
    (H : ∀ v : Fin 8, Matrix.kronecker (Matrix.single (0 : Fin 8) v (1 : K))
        (1 : Matrix (Fin h) (Fin h) K) * Ψ =
      Ψ * Matrix.kronecker (Matrix.single (0 : Fin 8) v (1 : K)) (1 : Matrix (Fin h) (Fin h) K))
    (v b : Fin 8) (i j : Fin h) :
    Ψ (v, i) (b, j) = if v = b then Ψ (0, i) (0, j) else 0 := by
  have := congrFun (congrFun (H v) (0, i)) (b, j)
  simpa [Matrix.mul_apply, Fintype.sum_prod_type, Matrix.kronecker, Matrix.kroneckerMap_apply,
    Matrix.single_apply, Matrix.one_apply, ite_and] using this
end GlobalTheory.ZM.SymmCommutant
