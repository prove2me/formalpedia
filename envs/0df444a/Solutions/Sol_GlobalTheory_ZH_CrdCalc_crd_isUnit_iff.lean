-- Prove2me | solution 1 for GlobalTheory.ZH.CrdCalc.crd_isUnit_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:24:52.599563+00:00
-- url     : https://prove2.me/submissions/6b91e764-f063-4802-bd5b-8cf154abe27b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PullChartIsLB
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsUnitCharts
import Theorems.Thm_GlobalTheory_ZH_CrdCalc_isUnit_valR_iff
import Theorems.Thm_GlobalTheory_ZH_CrdCalc_top_le_iff
import Theorems.Thm_GlobalTheory_ZH_CrdCalc_exists_unit_charts

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra
noncomputable section
open GlobalTheory GlobalTheory.ZH GlobalTheory.ZH.CrdCalc
variable {R : Type} [CommRing R] {X : Scheme.{0}}
variable {H : LB X} {J : Type} {s : J → H.Sec}
namespace GlobalTheory.ZH.CrdCalc
theorem _root_.solution [IsLocalRing R] {x : Sp R ⟶ X} {v : J → R} (j : J) (h : Crd H s x v) :
    IsUnit (v j) ↔ ⊤ ≤ x ⁻¹ᵁ Out.nonzeroLocus (s j) := by
  obtain ⟨l, c, hl, hv⟩ := h
  rw [hv, Units.isUnit_units_mul]
  constructor
  · intro hu
    exact ((isUnit_valR_iff x _ hl _).1 hu).trans
      (x.preimage_mono (le_iSup (fun k => X.basicOpen ((s j).f k)) l))
  · intro hu
    obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 ((top_le_iff x _).1 hu)
    have hk' := (top_le_iff x _).2 hk
    have hU : ⊤ ≤ x ⁻¹ᵁ H.U k := hk'.trans (x.preimage_mono (X.basicOpen_le _))
    obtain ⟨u, hu⟩ := exists_unit_charts H x l k hl hU
    rw [hu, Units.isUnit_units_mul]
    exact (isUnit_valR_iff x _ hU _).2 hk'
end GlobalTheory.ZH.CrdCalc
