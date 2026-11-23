-- Prove2me | solution 1 for GlobalTheory.ZH.CrdCalc.crd_smul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:08:10.943449+00:00
-- url     : https://prove2.me/submissions/76eae1a0-aba5-4021-a6cc-897349ac25d0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PullChartIsLB
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsUnitCharts

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
theorem _root_.solution {x : Sp R ⟶ X} {v : J → R} (c : Rˣ) (h : Crd H s x v) :
    Crd H s x (fun j => (c : R) * v j) := by
  obtain ⟨l, c', hl, hv⟩ := h
  exact ⟨l, c * c', hl, fun j => by beta_reduce; rw [hv, Units.val_mul, _root_.mul_assoc]⟩
end GlobalTheory.ZH.CrdCalc
