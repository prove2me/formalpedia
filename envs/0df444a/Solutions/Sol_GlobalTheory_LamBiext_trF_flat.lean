-- Prove2me | solution 1 for GlobalTheory.LamBiext.trF_flat
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:43:24.447428+00:00
-- url     : https://prove2.me/submissions/a74bf6d1-12c4-4f3b-9257-78f9d14daee1

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_Biextensions_CubicalExtendsSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_AbelianLawCounterexamples_MulGenNegRight
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsLaws

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.LamBiext
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
variable {X W Y Z : Scheme.{0}} (L : LB X) {I K : Type} [Fintype I] [Fintype K]
  (φ : I → (W ⟶ X)) (δ : I → ℤ) (ψ : K → (Y ⟶ W)) (ε : K → ℤ)
namespace GlobalTheory.LamBiext
theorem _root_.solution (r : Z ⟶ Y) (z : Z) (j j' : K → I → L.ι) :
    trF (L := L) (flatφ φ ψ) (flatε δ ε) r z (fun p => j p.1 p.2) (fun p => j' p.1 p.2) =
      ∏ k, trF (L := L) φ δ (r ≫ ψ k) z (j k) (j' k) ^ ε k := by
  rw [trF, Fintype.prod_prod_type]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [trF, ← Finset.prod_zpow]
  refine Finset.prod_congr rfl fun i _ => ?_
  show gm (r ≫ ψ k ≫ φ i) z _ (L.g (j k i) (j' k i)) ^ (ε k * δ i) = _
  rw [mul_comm (ε k), zpow_mul, Category.assoc]
end GlobalTheory.LamBiext
