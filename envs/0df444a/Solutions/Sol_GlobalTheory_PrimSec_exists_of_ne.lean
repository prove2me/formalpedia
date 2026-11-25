-- Prove2me | solution 1 for GlobalTheory.PrimSec.exists_of_ne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:26:58.526881+00:00
-- url     : https://prove2.me/submissions/5a85ce18-13c0-4e16-943a-bd6de78e1d2d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ValuationRingExistsAssociatedOfSumEqZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Clauses
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_AlWellDefSt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsSmulSecNonzeroOnSpecialFibre
import Theorems.Thm_GlobalTheory_PrimSec_app_rs
import Theorems.Thm_GlobalTheory_PrimSec_app_cst
import Theorems.Thm_GlobalTheory_PrimSec_mem_basicOpen_cst
import Theorems.Thm_GlobalTheory_PrimSec_exists_numerator
import Theorems.Thm_GlobalTheory_PrimSec_rs_loc
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Pdiv GlobalTheory.AbLaw
open scoped CategoryTheory.Obj TensorProduct
noncomputable section
open GlobalTheory GlobalTheory.PrimSec
variable {O K : Type} [CommRing O] [IsDomain O] [ValuationRing O] [Field K] [Algebra O K] [IsFractionRing O K]
  {X XK : Scheme.{0}} {f : X ⟶ Sp O} {j : XK ⟶ X} {fK : XK ⟶ Sp K}
  (H : IsPullback j fK f (spMap (algebraMap O K))) {M : LB X} (σ : LB.Sec (M.pull j))
include H
namespace GlobalTheory.PrimSec
theorem _root_.solution [Ring.DimensionLEOne O] (c : K) (i : M.ι) {x : X} (hx : x ∈ M.U i)
    (hfx : f x ≠ IsLocalRing.closedPoint O) :
    ∃ (V : X.Opens) (hV : V ≤ M.U i) (b : Γ(X, V)), x ∈ V ∧
      (j.app V).hom b = AbLaw.cst fK (j ⁻¹ᵁ V) c * loc σ i hV := by
  obtain ⟨_, ⟨W, hW, rfl⟩, hxW, hWU⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open hx (M.U i).isOpen
  have hWU : W ≤ M.U i := hWU
  obtain ⟨π, b, hπ, hb⟩ := exists_numerator H hW (AbLaw.cst fK (j ⁻¹ᵁ W) c * loc σ i hWU)
  have h0 : (f x).asIdeal = ⊥ := by
    by_contra h
    exact hfx (PrimeSpectrum.ext (IsLocalRing.eq_maximalIdeal ((f x).isPrime.isMaximal h)))
  have hxπ : x ∈ X.basicOpen (AbLaw.cst f W π) := (mem_basicOpen_cst f W π hxW).2 (by rw [h0]; exact hπ)
  have hle := X.basicOpen_le (AbLaw.cst f W π)
  obtain ⟨u, hu⟩ : IsUnit (AbLaw.cst f (X.basicOpen (AbLaw.cst f W π)) π) := by
    rw [← rs_cst f hle]
    exact X.toRingedSpace.isUnit_res_basicOpen _
  refine ⟨_, hle.trans hWU, u⁻¹.val * rs X hle b, hxπ, ?_⟩
  rw [map_mul, app_rs, hb, map_mul, map_mul, rs_cst, rs_cst, rs_loc σ _ _ hle, ← app_cst H.w, ← hu, ← _root_.mul_assoc, ← map_mul,
    Units.inv_mul, map_one, _root_.one_mul]
end GlobalTheory.PrimSec
