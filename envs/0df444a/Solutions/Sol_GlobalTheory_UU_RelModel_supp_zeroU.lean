-- Prove2me | solution 1 for GlobalTheory.UU.RelModel.supp_zeroU
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:35:27.017716+00:00
-- url     : https://prove2.me/submissions/0820f7c7-c63d-45c5-8b4c-ffab885cbb2d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueSamePt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_SecEqOfSecConst
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsCompleteDvrFiniteSubalgebra
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueSamePtRight
import Theorems.Thm_GlobalTheory_UU_RelModel_expF_one
import Theorems.Thm_GlobalTheory_UnifZero_resTop_inj
import Theorems.Thm_GlobalTheory_UnifZero_scal_bijective
import Theorems.Thm_GlobalTheory_UnifZero_scal_zero
import Theorems.Thm_P2M_UpperTheory_Reformulated_B_Qk17_isPrecomplete_finite_module__f12f74bf6019
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory GlobalTheory.UU GlobalTheory.UU.RelModel
open GlobalTheory.UnifZero ReciprocityTheory.ChartRestriction.G.Out.Inh
variable {X Y Z : Scheme.{0}} {K : Type} [Fintype K]
variable (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ)
namespace GlobalTheory.UU.RelModel
theorem _root_.solution : (zeroU R I).Supp F k PUnit.unit := by
  refine ⟨_, _, expF_one R I F k, fun _ => PUnit.unit, fun h => ?_⟩
  have : IsIso (fst (TF (R := R) F) (zeroData R I).toPre.P.A).left :=
    (inferInstance : IsIso (pullback.fst (TF (R := R) F).hom (𝟙 _)))
  have e := resTop_inj (GlobalTheory.ToricData.wchart_triv _ _) (h.trans (map_zero _).symm)
  refine one_ne_zero ((scal_bijective (fst (TF (R := R) F) (zeroData R I).toPre.P.A).left).1 (?_ : _ = scal _ (0 : F)))
  rw [scal_zero]
  exact (show scal _ (1 : F) = 1 by simp only [scal, map_one]).trans e
end GlobalTheory.UU.RelModel
