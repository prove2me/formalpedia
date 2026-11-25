-- Prove2me | solution 1 for GlobalTheory.ZV.FormSec.formSec_eq_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T15:09:07.690497+00:00
-- url     : https://prove2.me/submissions/d4b6702e-33eb-4211-87b8-74dca9f162eb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_SectionsHaveFiniteDimension
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_FiniteHomogeneousInf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsSegreCoordinates
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_SecCoordBcScaleUnique
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_IsRegularFnIffOfIsAffineOpen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_HomogeneousIdealSectionsOfLineBundlePower
import Theorems.Thm_GlobalTheory_ZV_FormSec_mem_idealOf
import Theorems.Thm_GlobalTheory_ZV_FormSec_gs_formSec
import Theorems.Thm_GlobalTheory_SegreCoord_ev_eq
import Theorems.Thm_GlobalTheory_SegreCoord_ev_ext
import Theorems.Thm_GlobalTheory_SegreCoord_ev_stalkMap
import Theorems.Thm_GlobalTheory_SegreCoord_exists_secCoord
import Theorems.Thm_GlobalTheory_SegreCoord_gs_stalkMap
import Theorems.Thm_GlobalTheory_SegreCoord_loc_of_secCoord
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_chart


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
open GlobalTheory.ZV
noncomputable section
open GlobalTheory GlobalTheory.ZV GlobalTheory.ZV.FormSec
open GlobalTheory.SegreCoord (ev ev_eq ev_ext ev_stalkMap Loc loc_of_secCoord exists_secCoord)
variable {R σ : Type} [CommRing R] {X : Scheme.{0}} {p : X ⟶ Sp R} {M : LB X} {th : σ → M.Sec}
namespace GlobalTheory.ZV.FormSec
theorem _root_.solution (hM : M.IsLB) {d : ℕ} {F : MvPolynomial σ R} (hF : F.IsHomogeneous d) :
    (∀ j, (formSec p th hF).f j = 0) ↔ F ∈ idealOf p M th (𝟙 X) := by
  constructor
  · intro h0
    refine mem_idealOf.2 fun T _ β x v hx h => ev_ext fun y => ?_
    obtain ⟨k, hk⟩ := exists_chart hM (x y)
    have hy : x y ∈ (lbPow M d).U (fun _ => k) := (Cartier.lbPow_U M d _).ge hk
    obtain ⟨u, hu⟩ := gs_formSec hF hx h y _ hy
    have h1 : gs x y _ (0 : Γ(X, (lbPow M d).U (fun _ => k))) = 0 := by rw [gs_eq x y _ hy, map_zero, map_zero]
    rw [map_zero]
    exact u.mul_right_eq_zero.1 (hu.symm.trans ((congrArg (gs x y _) (h0 fun _ => k)).trans h1))
  · intro hI j
    refine fn_ext fun z hz => ?_
    obtain ⟨V, hV, hzV, hle⟩ := exists_isAffineOpen_mem_and_subset hz
    let x : Sp Γ(X, V) ⟶ X := hV.fromSpec
    haveI : IsOpenImmersion x := inferInstanceAs (IsOpenImmersion hV.fromSpec)
    have hr : Set.range x = V := hV.range_fromSpec
    obtain ⟨y, rfl⟩ : z ∈ Set.range x := hr.ge hzV
    obtain ⟨v, hv⟩ := exists_secCoord (th := th) hM (x := x) (k := j ⟨⟩)
      fun y => (Cartier.lbPow_U M d j).le (hle (hr.le ⟨y, rfl⟩))
    have hx : x ≫ p = spMap (Spec.preimage (x ≫ p)).hom := (Spec.map_preimage _).symm
    obtain ⟨u, hu⟩ := gs_formSec hF hx hv y j hz
    rw [mem_idealOf.1 hI _ _ x v hx hv, map_zero, mul_zero, ← Category.comp_id x,
      GlobalTheory.SegreCoord.gs_stalkMap x (𝟙 X) y _ hz] at hu
    rw [gs_eq (𝟙 X) (x y) _ hz 0, map_zero, map_zero]
    exact (asIso (x.stalkMap y)).commRingCatIsoToRingEquiv.injective (hu.trans (map_zero _).symm)
end GlobalTheory.ZV.FormSec
