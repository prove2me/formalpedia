-- Prove2me | solution 1 for GlobalTheory.BundleNormalise.gm_iso
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T14:10:54.763352+00:00
-- url     : https://prove2.me/submissions/f776eb00-9350-4926-b52a-3f39f1e06ea9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsGenOfRigid
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsUniqueHom
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_FiniteHomogeneousInf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsPartialBundleIsoNormalised
import Theorems.Thm_GlobalTheory_BundleNormalise_gm_div
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_rp__e27165827f88
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_Geo_Tor_pullU_res__268497da66fb
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_div
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_id_pull

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
open GlobalTheory.ZM
noncomputable section
namespace GlobalTheory.BundleNormalise
open GlobalTheory.RigidTriv
variable {X Y : Scheme.{0}}
private theorem gm_res_eq_gm (f : Y ⟶ X) (y : Y) {U V : X.Opens} (h : V ≤ U) (hy : f y ∈ V) (u : Γ(X, U)ˣ) :
    gm f y V (res h u) = gm f y U u := by
  rw [← gm_id_pull f y V hy, pullU_res₂ f h u]
  exact gm_rp₁ f y U (f ⁻¹ᵁ V) (f.preimage_mono h) hy u
end GlobalTheory.BundleNormalise
end
end

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
noncomputable section
open GlobalTheory GlobalTheory.BundleNormalise
open GlobalTheory.RigidTriv
variable {X Y : Scheme.{0}}
namespace GlobalTheory.BundleNormalise
theorem _root_.solution {M M' : LB X} {w : LB.Iso M' M} (hw : w.IsGen) (f : Y ⟶ X) (y : Y) (a a' : M.ι) (b b' : M'.ι)
    (hm : f y ∈ M.U a ⊓ M'.U b ⊓ (M.U a' ⊓ M'.U b')) :
    gm f y (M.U a ⊓ M'.U b) (w.s (a, b)) =
      gm f y _ (M.g a a') * (gm f y _ (M'.g b b'))⁻¹ * gm f y (M.U a' ⊓ M'.U b') (w.s (a', b')) := by
  have hl : M.U a ⊓ M'.U b ⊓ (M.U a' ⊓ M'.U b') ≤ M.U a ⊓ M'.U b := inf_le_left
  have hr : M.U a ⊓ M'.U b ⊓ (M.U a' ⊓ M'.U b') ≤ M.U a' ⊓ M'.U b' := inf_le_right
  refine (gm_res_eq_gm f y hl hm (w.s (a, b))).symm.trans ?_
  refine (congrArg (gm f y (M.U a ⊓ M'.U b ⊓ (M.U a' ⊓ M'.U b'))) (hw (a, b) (a', b'))).trans ?_
  refine (map_mul (gm f y (M.U a ⊓ M'.U b ⊓ (M.U a' ⊓ M'.U b'))) _ _).trans ?_
  exact congrArg₂ (· * ·) (gm_div f y a a' b b' hm) (gm_res_eq_gm f y hr hm (w.s (a', b')))
end GlobalTheory.BundleNormalise
