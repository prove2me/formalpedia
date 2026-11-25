-- Prove2me | solution 1 for GlobalTheory.PrimSec.loc_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:28:10.333458+00:00
-- url     : https://prove2.me/submissions/cbd519c9-5631-41e4-86c7-aebecfa747e6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ValuationRingExistsAssociatedOfSumEqZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Clauses
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_AlWellDefSt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsSmulSecNonzeroOnSpecialFibre
import Theorems.Thm_GlobalTheory_PrimSec_rs_injective
import Theorems.Thm_GlobalTheory_PrimSec_nonempty_of_ne_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsCub_compat
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
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Pdiv GlobalTheory.AbLaw
open scoped CategoryTheory.Obj TensorProduct
noncomputable section
open GlobalTheory GlobalTheory.PrimSec
variable {X XK : Scheme.{0}} {j : XK ⟶ X} {M : LB X}
namespace GlobalTheory.PrimSec
theorem _root_.solution [IsIntegral XK] (σ : LB.Sec (M.pull j)) (hσ : ∃ i, σ.f i ≠ 0) (i : M.ι) {V : X.Opens}
    (hV : V ≤ M.U i) (hne : Nonempty (j ⁻¹ᵁ V)) : loc σ i hV ≠ 0 := by
  obtain ⟨k, hk⟩ := hσ
  intro h
  have h1 : σ.f (fun _ => i) = 0 := rs_injective (le_pull M j hV) hne (h.trans (map_zero _).symm)
  have h2 := σ.compat k (fun _ => i)
  rw [h1, map_zero, mul_zero] at h2
  obtain ⟨⟨y, hy⟩⟩ := hne
  obtain ⟨⟨z, hz⟩⟩ := nonempty_of_ne_zero hk
  obtain ⟨w, hw⟩ := nonempty_preirreducible_inter ((M.pull j).U k).isOpen ((M.pull j).U (fun _ => i)).isOpen
    ⟨z, hz⟩ ⟨y, le_pull M j hV hy⟩
  exact hk (rs_injective inf_le_left ⟨⟨w, hw⟩⟩ (h2.trans (map_zero _).symm))
end GlobalTheory.PrimSec
