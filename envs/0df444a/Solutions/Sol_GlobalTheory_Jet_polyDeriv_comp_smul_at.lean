-- Prove2me | solution 1 for GlobalTheory.Jet.polyDeriv_comp_smul_at
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:57:08.917266+00:00
-- url     : https://prove2.me/submissions/a3d983d4-db37-4062-bd64-50bbbeb92d55

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchy
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_PolyDerivMonomialOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_CardToMultisetEqDegree
import Theorems.Thm_GlobalTheory_Jet_polyDeriv_comp_clm
import Theorems.Thm_GlobalTheory_Jet_polyDeriv_smul_dir

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
    (hP : P.IsHomogeneous a) (c : ℂ) (u : σ → W) {F : W → ℂ} (hF : Differentiable ℂ F) (x : W) :
    polyDeriv P u (fun v => F (c • v)) x = c ^ a * polyDeriv P u F (c • x) := by
  rw [← polyDeriv_smul_dir hP]
  exact polyDeriv_comp_clm P u hF (c • ContinuousLinearMap.id ℂ W) x
end GlobalTheory.Jet
