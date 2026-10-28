-- Prove2me | solution 1 for OAI.GammaFPP.CrossingBridge.gamma_direction_nat_limit
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-25T03:56:18.694988+00:00
-- url     : https://prove2.me/submissions/b521fcac-d5aa-46a4-b00b-af817b5818bf

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_GammaPassage
import Definitions.Def_OAIW2GF000
import Theorems.Thm_OAI_GammaFPP_GammaEnvironment_isTimeConstant

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_ActualNoCorner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP.CrossingBridge
open PlanarFPP GammaFPP.RealDirectionBridge GammaFPP.BK
open MeasureTheory Filter
open scoped Topology
variable {shape rate : ℝ}
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {τ : Edge → Ω → ℝ}

/-- The actual time constant along the manuscript's rounded direction sequence. -/
lemma gamma_direction_nat_limit_oai (henv : GammaEnvironment shape rate P τ)
    (hshape : 0 < shape) (hrate : 0 < rate) (b : ℝ) :
    ∀ᵐ ω ∂P, Tendsto
      (fun n : ℕ => passageTime (fun e => τ e ω) 0 ((n : ℤ),⌊b*(n : ℝ)⌋)/(n : ℝ))
      atTop (𝓝 ((gammaMeanNorm henv hshape hrate) (direction b))) := by
  filter_upwards [henv.isTimeConstant hshape hrate (direction b)] with ω hω
  have hh := hω.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have he (n : ℕ) : latticeFloor ((n : ℝ) • direction b)=((n : ℤ),⌊b*(n : ℝ)⌋) := by
    simp [latticeFloor,direction,PiLp.smul_apply,mul_comm]
  simpa only [Function.comp_def,he,show (0 : Vertex)=(0,0) from rfl] using hh

end GammaFPP.CrossingBridge

end OAI
end

theorem solution.{u_1} : type_of% @OAI.GammaFPP.CrossingBridge.gamma_direction_nat_limit_oai.{u_1} := @OAI.GammaFPP.CrossingBridge.gamma_direction_nat_limit_oai.{u_1}
