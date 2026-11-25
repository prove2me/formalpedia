-- Prove2me | solution 1 for GlobalTheory.ZV.FormSec.span_eq_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:01:51.097806+00:00
-- url     : https://prove2.me/submissions/acd47581-67dc-4814-ab3d-03293e969393

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
import Theorems.Thm_GlobalTheory_ZV_FormSec_not_mem_of_isUnit_ev
import Theorems.Thm_GlobalTheory_SegreCoord_ev_eq
import Theorems.Thm_GlobalTheory_SegreCoord_ev_ext
import Theorems.Thm_GlobalTheory_SegreCoord_ev_stalkMap
import Theorems.Thm_GlobalTheory_SegreCoord_exists_secCoord
import Theorems.Thm_GlobalTheory_SegreCoord_loc_of_secCoord


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
theorem _root_.solution (hc : ⨆ i, Out.nonzeroLocus (th i) = ⊤) {T : Type} [CommRing T] {x : Sp T ⟶ X} {v : σ → T}
    (h : SecCoord M th x v) : Ideal.span (Set.range v) = ⊤ := by
  by_contra hJ
  obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hJ
  let y : Sp T := (⟨m, hm.isPrime⟩ : PrimeSpectrum T)
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 (hc.ge (Set.mem_univ (x y)))
  obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 hi
  have hk' : x y ∈ M.U k := X.basicOpen_le _ hk
  obtain ⟨u, hu⟩ := loc_of_secCoord h y k hk'
  have := (isUnit_gs_iff x y hk' _).2 hk
  rw [hu] at this
  exact not_mem_of_isUnit_ev y (isUnit_of_mul_isUnit_left this) (hle (Ideal.subset_span ⟨i, rfl⟩))
end GlobalTheory.ZV.FormSec
