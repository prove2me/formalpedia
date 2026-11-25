-- Prove2me | solution 1 for GlobalTheory.Jet.polyDeriv_comp_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:02:40.24483+00:00
-- url     : https://prove2.me/submissions/39aac4df-174b-4db6-927c-37906a37e059

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchy
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_PolyDerivMonomialOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_CardToMultisetEqDegree
import Theorems.Thm_GlobalTheory_Jet_polyDeriv_comp_smul_at

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex ReciprocityTheory.ChartRestriction.G.I2
open GlobalTheory
open GlobalTheory.Jet
variable {σ W W' : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W]
  [NormedAddCommGroup W'] [NormedSpace ℂ W']
namespace GlobalTheory.Jet
theorem _root_.solution [FiniteDimensional ℂ W] {P : MvPolynomial σ ℂ} {a : ℕ}
    (hP : P.IsHomogeneous a) (c : ℂ) (u : σ → W) {F : W → ℂ} (hF : Differentiable ℂ F) :
    polyDeriv P u (fun v => F (c • v)) 0 = c ^ a * polyDeriv P u F 0 := by
  rw [polyDeriv_comp_smul_at hP c u hF, smul_zero]
end GlobalTheory.Jet
