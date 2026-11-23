-- Prove2me | solution 1 for GlobalTheory.ZH.CrdCalc.crd_map
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:15:45.539376+00:00
-- url     : https://prove2.me/submissions/c868c5df-5b14-453b-9536-32be543e8ac3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PullChartIsLB
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsUnitCharts
import Theorems.Thm_GlobalTheory_ZH_CrdCalc_valR_spMap

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
theorem _root_.solution {R' : Type} [CommRing R'] (φ : R →+* R') {x : Sp R ⟶ X} {v : J → R} (h : Crd H s x v) :
    Crd H s (spMap φ ≫ x) (fun j => φ (v j)) := by
  obtain ⟨l, c, hl, hv⟩ := h
  obtain ⟨h₁, h₂⟩ := valR_spMap φ x _ hl
  refine ⟨l, Units.map φ.toMonoidHom c, h₁, fun j => ?_⟩
  beta_reduce
  rw [h₂, hv, map_mul]
  rfl
end GlobalTheory.ZH.CrdCalc
