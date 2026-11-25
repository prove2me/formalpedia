-- Prove2me | solution 1 for GlobalTheory.KeyPBScale.lie_baseChange
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:09:09.963906+00:00
-- url     : https://prove2.me/submissions/9a7f3a38-b66d-4b8d-9c02-4321406cadb5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_IsSquareDeterminantComparison
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_PwIsoIsGen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_DualNumberRingHomExt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GenericRegularity_LieCombBaseChange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_LieBaseChange
import Theorems.Thm_GlobalTheory_lieComb_baseChange


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.KeyKa
noncomputable section
open GlobalTheory GlobalTheory.KeyPBScale
namespace GlobalTheory.KeyPBScale
theorem _root_.solution {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') {G : Over (Sp R)} [GrpObj G]
    {G' : Over (Sp R')} [GrpObj G'] {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G (spMap f) φ) {n m : ℕ}
    (e : m = n) (M : Matrix (Fin n) (Fin n) R) (v v' : Fin n → (epsR R ⟶ G)) (u u' : Fin m → (epsR R' ⟶ G'))
    (hv : ∀ i, IsLieComb (M i) v (v' i))
    (hu : ∀ i : Fin m, IsLieComb (fun j : Fin m => f (M (i.cast e) (j.cast e))) u (u' i))
    (huv : ∀ i, (u i).left ≫ φ = spMap (Chart.dualMapR f) ≫ (v (i.cast e)).left) (i : Fin m) :
    (u' i).left ≫ φ = spMap (Chart.dualMapR f) ≫ (v' (i.cast e)).left := by
  subst e
  exact (lieComb_baseChange R R' f G G' φ h m v (v' i) (M i) u (u' i) huv (hv i)).2 (hu i)
end GlobalTheory.KeyPBScale
