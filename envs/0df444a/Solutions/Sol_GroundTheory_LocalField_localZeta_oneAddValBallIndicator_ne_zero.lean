-- Prove2me | solution 1 for GroundTheory.LocalField.localZeta_oneAddValBallIndicator_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:01:52.796912+00:00
-- url     : https://prove2.me/submissions/56797f78-ded8-4f2e-b680-873cf3097eff

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_LocalZetaTate
import Definitions.Def_GroundTheory_LocalFields_PadicLogHom
import Definitions.Def_GroundTheory_LocalFields_LocalZetaEpsilon
import Theorems.Thm_GroundTheory_LocalField_localZeta_oneAddValBallIndicator
import Theorems.Thm_GroundTheory_LocalField_haarIntegers_valBall
import Theorems.Thm_GroundTheory_LocalField_one_lt_residueCard_nnreal


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.LocalField
open ValuativeRel MeasureTheory Measure Topology Filter
open scoped WithZero NNReal ENNReal Pointwise
variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable [MeasurableSpace K] [BorelSpace K]
variable {χ : Kˣ →* ℂˣ} {ψ : AddChar K Circle}
namespace GroundTheory.LocalField
theorem _root_.solution {c : ℕ} (hc : 1 ≤ c)
    (hker : unitFiltrationUnits K c ≤ χ.ker) (s : ℂ) :
    localZeta (oneAddValBallIndicator c) χ s ≠ 0 := by
  rw [localZeta_oneAddValBallIndicator hc hker]
  have h1 : (multHaarConst K).toReal ≠ 0 :=
    ENNReal.toReal_ne_zero.mpr ⟨multHaarConst_ne_zero, multHaarConst_ne_top⟩
  have h2 : (haarIntegers K).real (valBall K c) ≠ 0 := by
    rw [measureReal_def, haarIntegers_valBall, ENNReal.coe_toReal]
    exact_mod_cast (zpow_pos (zero_lt_one.trans one_lt_residueCard_nnreal) _).ne'
  exact_mod_cast mul_ne_zero h1 h2
end GroundTheory.LocalField
