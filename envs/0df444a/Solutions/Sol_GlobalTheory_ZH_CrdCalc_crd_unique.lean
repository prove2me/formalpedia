-- Prove2me | solution 1 for GlobalTheory.ZH.CrdCalc.crd_unique
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:24:52.66716+00:00
-- url     : https://prove2.me/submissions/4eac9b37-88af-4374-aabd-481e767ae379

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PullChartIsLB
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsUnitCharts
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
theorem _root_.solution {x : Sp R ⟶ X} {v v' : J → R} (h : Crd H s x v) (h' : Crd H s x v') :
    ∃ c : Rˣ, ∀ j, v' j = (c : R) * v j := by
  obtain ⟨l, c, hl, hv⟩ := h
  obtain ⟨l', c', hl', hv'⟩ := h'
  obtain ⟨u, hu⟩ := exists_unit_charts H x l' l hl' hl
  refine ⟨c' * u * c⁻¹, fun j => ?_⟩
  rw [hv, hv', hu, Units.val_mul, Units.val_mul, _root_.mul_assoc, Units.inv_mul_cancel_left, _root_.mul_assoc]
end GlobalTheory.ZH.CrdCalc
