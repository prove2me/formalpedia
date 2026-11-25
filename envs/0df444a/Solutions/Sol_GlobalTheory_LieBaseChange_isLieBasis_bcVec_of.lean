-- Prove2me | solution 1 for GlobalTheory.LieBaseChange.isLieBasis_bcVec_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T15:43:33.459002+00:00
-- url     : https://prove2.me/submissions/87c2bcac-1935-43d5-980a-7bd9e07b9481

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_FlagBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabComp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_EigLatBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_Biextensions_CubicalExtendsSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasisBaseChange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_AwayToAwayRightEqOfComp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsIsLieBasisBaseChange
import Theorems.Thm_GlobalTheory_LieBaseChange_isTan_iff_mem
import Theorems.Thm_GlobalTheory_LieBaseChange_pushR_bcVec
import Theorems.Thm_GlobalTheory_LieBaseChange_pushR_prodPts
import Theorems.Thm_GlobalTheory_SqZero_mem_redKer_of_section
import Theorems.Thm_GlobalTheory_SqZero_ptsMap_apply
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_Chart_comp_one__39cc6a6ed057
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_dualMapA_inr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_isLieComb_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_isTan_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_pushR_inj
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_spMap_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_spMap_comp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.SqZero.ptsMap_apply



set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Chart
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding spMap spMap_comp IsTan
open TrivSqZeroExt (inl inr)
open GlobalTheory GlobalTheory.LieBaseChange
open GlobalTheory.SqZero
variable {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R']
  (G : Over (Spec (CommRingCat.of R))) [GrpObj G]
variable {G} {n : ℕ}
namespace GlobalTheory.LieBaseChange
theorem _root_.solution [IsCommMonObj G] {v : Fin n → (epsR R ⟶ G)} (hv : ∀ i, IsTangent (v i))
    (inj : ∀ c c' : Fin n → R',
      lieExp v (fun i => (inr (c i) : DualNumber R')) (fun _ => TrivSqZeroExt.inr_mul_inr _ _ _) =
      lieExp v (fun i => (inr (c' i) : DualNumber R')) (fun _ => TrivSqZeroExt.inr_mul_inr _ _ _) →
        c = c')
    (surj : ∀ y ∈ redKer G (RingHom.ker ((fstD R').restrictScalars R)), ∃ c : Fin n → R', y =
      lieExp v (fun i => (inr (c i) : DualNumber R')) (fun _ => TrivSqZeroExt.inr_mul_inr _ _ _)) :
    IsLieBasis (bcVec R' v) := by
  refine ⟨fun i => (isTan_iff _).1 ((isTan_iff_mem G _).2 ?_), fun w hw => ?_⟩
  · rw [pushR_bcVec]
    refine mem_redKer_of_section ((fstD R').restrictScalars R)
      ((Algebra.ofId R' (DualNumber R')).restrictScalars R) (fun a => rfl) ?_
    have : ((fstD R').restrictScalars R).comp (dualMapA R R') = (Algebra.ofId R R').comp (fstD R) := by
      refine DualNumber.algHom_ext ?_
      change (dualMapA R R' (inr 1)).fst = algebraMap R R' 0
      rw [dualMapA_inr]; simp
    rw [← Category.assoc, spMap_comp, this, ← spMap_comp, Category.assoc, (isTan_iff _).2 (hv i),
      comp_one']
  · obtain ⟨c, hc⟩ := surj _ ((isTan_iff_mem G _).1 ((isTan_iff _).2 hw))
    refine ⟨c, (isLieComb_iff _ _ _).2 (pushR_inj G (by rw [hc, pushR_prodPts])), fun c' hc' => ?_⟩
    refine inj _ _ ?_
    rw [← hc, (isLieComb_iff _ _ _).1 hc', pushR_prodPts]
end GlobalTheory.LieBaseChange
