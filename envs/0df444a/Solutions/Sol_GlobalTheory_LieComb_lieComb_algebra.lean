-- Prove2me | solution 1 for GlobalTheory.LieComb.lieComb_algebra
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:05:43.451801+00:00
-- url     : https://prove2.me/submissions/318fba7a-4674-4f7d-9ba8-8a049093316e

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_MapsAtLeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OneEqSpTranslZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_AwayToAwayRightEqOfComp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_IsLieBasisIffIsUnitDet
import Theorems.Thm_GlobalTheory_LieComb_isLieComb_iff_tanExp
import Theorems.Thm_GlobalTheory_LieComb_isTangent_tanExp
import Theorems.Thm_GlobalTheory_LieComb_tanExp_tanExp
import Theorems.Thm_GlobalTheory_LieComb_tanExp_single
import Theorems.Thm_GlobalTheory_LieComb_isLieBasis_iff_isUnit_det
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_isTan_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_spMap_id


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap spMap_id isTan_iff)
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp epsR IsTangent IsLieComb IsLieBasis)
open TrivSqZeroExt (inl inr)
open GlobalTheory GlobalTheory.LieComb
open GlobalTheory.SqZero
attribute [local instance] Over.cartesianMonoidalCategory
variable {R : Type} [CommRing R] {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]
  {n : ℕ} {v : Fin n → (epsR R ⟶ G)}
namespace GlobalTheory.LieComb
theorem _root_.solution (R : Type) [CommRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G]
    (n : ℕ) (v : Fin n → (epsR R ⟶ G)) (hv : ∀ i, IsTangent (v i)) :
    (∀ c, ∃! w, IsLieComb c v w) ∧ (∀ c w, IsLieComb c v w → IsTangent w) ∧
    (∀ (m : ℕ) (M : Fin m → Fin n → R) (v' : Fin m → (epsR R ⟶ G)) (c : Fin m → R) (w),
      (∀ i, IsLieComb (M i) v (v' i)) → IsLieComb c v' w → IsLieComb (∑ i, c i • M i) v w) ∧
    (∀ i, IsLieComb (Pi.single i 1) v (v i)) ∧
    ∀ (M : Matrix (Fin n) (Fin n) R) (v' : Fin n → (epsR R ⟶ G)), IsLieBasis v →
      (∀ i, IsLieComb (M i) v (v' i)) → (IsLieBasis v' ↔ IsUnit M.det) := by
  refine ⟨fun c => ⟨tanExp v c, (isLieComb_iff_tanExp _ _).2 rfl,
    fun w hw => (isLieComb_iff_tanExp _ _).1 hw⟩, fun c w hw => ?_, fun m M v' c w hM hw => ?_,
    fun i => (isLieComb_iff_tanExp _ _).2 (tanExp_single hv i).symm, fun M v' hb hM => ?_⟩
  · rw [(isLieComb_iff_tanExp _ _).1 hw]
    exact isTangent_tanExp hv c
  · obtain rfl : v' = fun i => tanExp v (M i) :=
      funext fun i => (isLieComb_iff_tanExp _ _).1 (hM i)
    rw [isLieComb_iff_tanExp] at hw ⊢
    rw [hw, tanExp_tanExp hv]
  · obtain rfl : v' = fun i => tanExp v (M i) :=
      funext fun i => (isLieComb_iff_tanExp _ _).1 (hM i)
    exact isLieBasis_iff_isUnit_det hb M
end GlobalTheory.LieComb
