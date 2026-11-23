-- Prove2me | solution 1 for GlobalTheory.ZH.CrdCalc.crd_ratio
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:16:42.667805+00:00
-- url     : https://prove2.me/submissions/deb5db56-0e8d-4951-8b6b-cb4c9f6363cd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PullChartIsLB
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsUnitCharts
import Theorems.Thm_GlobalTheory_ZH_CrdCalc_valR_mul
import Theorems.Thm_GlobalTheory_ZH_CrdCalc_valR_res

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
theorem _root_.solution {x : Sp R ⟶ X} {v : J → R} {i j : J} {W : X.Opens} {r : Γ(X, W)} (h : Crd H s x v)
    (hr : IsRatio (s j) (s i) W r) (hW : ⊤ ≤ x ⁻¹ᵁ W) : v j = valR x W r * v i := by
  obtain ⟨l, c, hl, hv⟩ := h
  have hh : ⊤ ≤ x ⁻¹ᵁ (W ⊓ H.U l) := fun y hy => ⟨hW hy, hl hy⟩
  have := congrArg (valR x (W ⊓ H.U l)) (hr l)
  rw [valR_mul x _ hh, valR_res x _ hh, valR_res x _ hh, valR_res x _ hh] at this
  rw [hv, hv, this, mul_left_comm]
end GlobalTheory.ZH.CrdCalc
