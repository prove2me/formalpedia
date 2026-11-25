-- Prove2me | solution 1 for GlobalTheory.KeyKa.KosBasis.phi_mulVec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T15:24:29.126201+00:00
-- url     : https://prove2.me/submissions/525690c4-9e95-4367-ac34-64ad64c05d66

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_KoszulExactOfGradedRegularStatement
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_IsSquareDeterminantComparison
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_IsPluriharmonicSiegel
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_MapsAtLeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OneEqSpTranslZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_KoszulExactOfRegular
import Theorems.Thm_GlobalTheory_Descent_freeIso_hom
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Descent.freeIso_hom



set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa
open GlobalTheory
noncomputable section
open GlobalTheory GlobalTheory.KeyKa GlobalTheory.KeyKa.KosBasis
variable {K : Type} [CommRing K]
namespace GlobalTheory.KeyKa.KosBasis
theorem _root_.solution (x : KeyIn K) {n l : ℕ} {s : Fin x.P.g → RR x n}
    {b : ∀ j, Fin ((l - j * n) ^ x.P.g) → RR x (l - j * n)} {m} (hm : IsMul x l s b m)
    (i : Fin x.P.g) {j : ℕ} (hj : j < x.P.g) (v) (c) :
    phi x (b j) ((m i j (j + 1)).mulVec v) c = lf x (s i) c * phi x (b (j + 1)) v c := by
  have h : ∀ k, lf x (s i) c * lf x (b (j + 1) k) c =
      ∑ k', cst x.P.A.hom (x.P.L.U c) (m i j (j + 1) k' k) * lf x (b j k') c :=
    fun k => hm i j hj k c
  calc phi x (b j) ((m i j (j + 1)).mulVec v) c
      = ∑ k', ∑ k, cst x.P.A.hom (x.P.L.U c) (v k) *
          (cst x.P.A.hom (x.P.L.U c) (m i j (j + 1) k' k) * lf x (b j k') c) := by
        simp only [phi, Matrix.mulVec, dotProduct, map_sum, map_mul, Finset.sum_mul]
        exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
    _ = ∑ k, cst x.P.A.hom (x.P.L.U c) (v k) * (lf x (s i) c * lf x (b (j + 1) k) c) := by
        rw [Finset.sum_comm]
        simp only [h, Finset.mul_sum]
    _ = _ := by
        simp only [phi, Finset.mul_sum]
        exact Finset.sum_congr rfl fun _ _ => by ring
end GlobalTheory.KeyKa.KosBasis
