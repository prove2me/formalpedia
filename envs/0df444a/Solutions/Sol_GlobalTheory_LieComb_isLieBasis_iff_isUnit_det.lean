-- Prove2me | solution 1 for GlobalTheory.LieComb.isLieBasis_iff_isUnit_det
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:51:38.529026+00:00
-- url     : https://prove2.me/submissions/2c81cca6-4e29-4338-86be-81fc3f769479

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
import Theorems.Thm_GlobalTheory_SqZero_isLieBasisOver_self
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
theorem _root_.solution (hv : IsLieBasis v) (M : Matrix (Fin n) (Fin n) R) :
    IsLieBasis (fun i => tanExp v (M i)) ↔ IsUnit M.det := by
  have key : ∀ c : Fin n → R,
      tanExp (fun i => tanExp v (M i)) c = tanExp v (Matrix.vecMul c M) := fun c => by
    rw [Matrix.vecMul_eq_sum]
    exact tanExp_tanExp hv.1 (fun i => M i) c
  obtain ⟨hinj, -⟩ := isLieBasisOver_self hv
  rw [← Matrix.isUnit_iff_isUnit_det]
  constructor
  · intro h
    refine Matrix.vecMul_surjective_iff_isUnit.1 fun d => ?_
    obtain ⟨c, hc, -⟩ := h.2 _ (isTangent_tanExp hv.1 d)
    rw [isLieComb_iff_tanExp, key] at hc
    exact ⟨c, (hinj _ _ hc).symm⟩
  · intro h
    refine ⟨fun i => isTangent_tanExp hv.1 _, fun w hw => ?_⟩
    obtain ⟨d, hd, -⟩ := hv.2 w hw
    obtain ⟨c, hc⟩ := Matrix.vecMul_surjective_iff_isUnit.2 h d
    have hc' : Matrix.vecMul c M = d := hc
    rw [isLieComb_iff_tanExp] at hd
    refine ⟨c, ?_, fun c' h' => ?_⟩
    · change IsLieComb _ _ _
      rw [isLieComb_iff_tanExp, key, hc', hd]
    · change IsLieComb _ _ _ at h'
      rw [isLieComb_iff_tanExp, key, hd, ← hc'] at h'
      exact Matrix.vecMul_injective_of_isUnit h (hinj _ _ h').symm
end GlobalTheory.LieComb
