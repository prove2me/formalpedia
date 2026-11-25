-- Prove2me | solution 1 for GlobalTheory.ZV.FormSec.eval_eq_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T15:21:10.584907+00:00
-- url     : https://prove2.me/submissions/dd25dd09-070e-4c3f-b181-ada2c5461a87

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
import Theorems.Thm_GlobalTheory_ZV_FormSec_isUnit_gs_iff
import Theorems.Thm_GlobalTheory_ZV_FormSec_gs_formSec
import Theorems.Thm_GlobalTheory_Cartier_IsRegularFn_mul
import Theorems.Thm_GlobalTheory_SegreCoord_RankOne_map
import Theorems.Thm_GlobalTheory_SegreCoord_ev_eq
import Theorems.Thm_GlobalTheory_SegreCoord_ev_ext
import Theorems.Thm_GlobalTheory_SegreCoord_ev_stalkMap
import Theorems.Thm_GlobalTheory_SegreCoord_exists_secCoord
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
theorem _root_.solution {K : Type} [Field K] {p : X ⟶ Sp K} (hM : M.IsLB) {d : ℕ} {F : MvPolynomial σ K}
    (hF : F.IsHomogeneous d) {y : Sp K ⟶ X} {v : σ → K} (hy : y ≫ p = 𝟙 _) (h : SecCoord M th y v) :
    MvPolynomial.eval v F = 0 ↔ ¬ ⊤ ≤ y ⁻¹ᵁ Out.nonzeroLocus (formSec p th hF) := by
  have hy' : y ≫ p = spMap (RingHom.id K) := hy.trans (Spec.map_id (CommRingCat.of K)).symm
  rw [← not_iff_not, not_not]
  constructor
  · intro h0 z _
    obtain ⟨k, hk⟩ := exists_chart hM (y z)
    have hz : y z ∈ (lbPow M d).U (fun _ => k) := (Cartier.lbPow_U M d _).ge hk
    obtain ⟨u, hu⟩ := gs_formSec hF hy' h z _ hz
    refine TopologicalSpace.Opens.mem_iSup.2 ⟨fun _ => k, (isUnit_gs_iff y z hz _).1 ?_⟩
    rw [hu]
    exact u.isUnit.mul ((Ne.isUnit h0).map (ev z))
  · intro hle h0
    let z : Sp K := (⊥ : PrimeSpectrum K)
    obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1
      (show y z ∈ Out.nonzeroLocus (formSec p th hF) from hle (Set.mem_univ z))
    have hz : y z ∈ (lbPow M d).U j := X.basicOpen_le _ hj
    obtain ⟨u, hu⟩ := gs_formSec hF hy' h z j hz
    have hun := (isUnit_gs_iff y z hz _).2 hj
    rw [hu, show MvPolynomial.eval₂ (RingHom.id K) v F = 0 from h0, map_zero, mul_zero] at hun
    exact not_isUnit_zero hun
end GlobalTheory.ZV.FormSec
