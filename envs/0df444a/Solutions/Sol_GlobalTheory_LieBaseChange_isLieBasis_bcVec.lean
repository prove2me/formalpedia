-- Prove2me | solution 1 for GlobalTheory.LieBaseChange.isLieBasis_bcVec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:04:52.784575+00:00
-- url     : https://prove2.me/submissions/a9834dd9-464b-4528-9c1d-7b2c40444285

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
import Theorems.Thm_GlobalTheory_LieBaseChange_isLieBasis_bcVec_of
import Theorems.Thm_GlobalTheory_SqZero_IsAway_ext
import Theorems.Thm_GlobalTheory_SqZero_expBij
import Theorems.Thm_GlobalTheory_SqZero_ker_fst_sq
import Theorems.Thm_GlobalTheory_SqZero_lieExp_congr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_spMap_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_spMap_comp


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
theorem _root_.solution [IsCommMonObj G] [Smooth G.hom] {v : Fin n → (epsR R ⟶ G)}
    (hv : IsLieBasis v) : IsLieBasis (bcVec R' v) := by
  obtain ⟨h₁, h₂⟩ := expBij (DualNumber R') hv (RingHom.ker ((fstD R').restrictScalars R))
    (ker_fst_sq (R := R) (S := R') R')
  refine isLieBasis_bcVec_of hv.1 (fun c c' h => funext fun i => ?_) fun y hy => ?_
  · exact congrArg TrivSqZeroExt.snd
      (congrFun (h₁ _ _ (fun i => inr_mem_kerD (c i)) (fun i => inr_mem_kerD (c' i)) _ _ h) i)
  · obtain ⟨c, hc, hcJ, e⟩ := h₂ y hy
    have hc' : ∀ i, c i = inr (c i).snd := fun i =>
      have h0 : (c i).fst = 0 := hcJ i
      TrivSqZeroExt.ext h0 rfl
    exact ⟨fun i => (c i).snd, e.trans (lieExp_congr v hc' _ _)⟩
end GlobalTheory.LieBaseChange
