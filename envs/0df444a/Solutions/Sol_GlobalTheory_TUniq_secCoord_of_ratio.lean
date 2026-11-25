-- Prove2me | solution 1 for GlobalTheory.TUniq.secCoord_of_ratio
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:03:40.502544+00:00
-- url     : https://prove2.me/submissions/07accb88-d192-4f90-8a36-294c4ac38a98

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_FiniteHomogeneousInf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsCompatOfLocal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsSegreCoordinates
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaFamilyOrigin_IsThetaPtOverMove
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaFamilyOrigin_IsThetaPtOverOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_SecCoordOfRatio
import Theorems.Thm_GlobalTheory_SegreCoord_ev_ext
import Theorems.Thm_GlobalTheory_SegreCoord_exists_secCoord
import Theorems.Thm_GlobalTheory_SegreCoord_loc_of_secCoord
import Theorems.Thm_GlobalTheory_SegreCoord_secCoord_of_loc
import Theorems.Thm_GlobalTheory_TUniq_GeoGood_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm


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
noncomputable section
open GlobalTheory GlobalTheory.TUniq
open GlobalTheory.SegreCoord ReciprocityTheory.ChartRestriction.G.Out
namespace GlobalTheory.TUniq
theorem _root_.solution {X X' : Scheme.{0}} {M : LB X} {M' : LB X'} (hM' : M'.IsLB) {σ : Type} {th : σ → M.Sec}
    {th' : σ → M'.Sec} {B : Type} [Field B] {x : Sp B ⟶ X} {x' : Sp B ⟶ X'} (p : Sp B) {j : M.ι} {j' : M'.ι}
    (hj : x p ∈ M.U j) (hj' : x' p ∈ M'.U j') (c : ((Sp B).presheaf.stalk p)ˣ)
    (h : ∀ i, gs x' p _ ((th' i).f j') = c * gs x p _ ((th i).f j)) {v : σ → B} (H : SecCoord M th x v) :
    SecCoord M' th' x' v := by
  have hs : ∀ y : Sp B, y = p := fun y => Subsingleton.elim (α := PrimeSpectrum B) _ _
  obtain ⟨u, hu⟩ := loc_of_secCoord H p j hj
  by_cases hv : Ideal.span (Set.range v) = ⊤
  · refine secCoord_of_loc hv fun y l hl => ?_
    obtain rfl := hs y
    refine ⟨gm x' y _ (M'.g l j') * (c * u), fun i => ?_⟩
    rw [gs_sec (th' i) x' y hl hj', h, hu, Units.val_mul, Units.val_mul]
    ring
  · have h0 : ∀ i, v i = 0 := fun i => by
      by_contra hi
      exact hv (Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span ⟨i, rfl⟩) (IsUnit.mk0 _ hi))
    obtain ⟨w, hw⟩ := exists_secCoord (th := th') hM' (x := x') (k := j') fun y => by rw [hs y]; exact hj'
    obtain ⟨u', hu'⟩ := loc_of_secCoord hw p j' hj'
    have : w = v := funext fun i => ev_ext fun y => by
      obtain rfl := hs y
      have := hu' i
      rw [h, hu, h0, map_zero, zero_mul, mul_zero] at this
      rw [h0, map_zero]
      exact (Units.mul_left_eq_zero _).1 this.symm
    exact this ▸ hw
end GlobalTheory.TUniq
