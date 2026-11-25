-- Prove2me | solution 1 for GlobalTheory.T.exists_thetaRunParameters_uniform_torus
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:13:52.693423+00:00
-- url     : https://prove2.me/submissions/577d26dd-18cd-44a7-83da-a0d1bee66a53

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsThetaRunParametersUniformTorus
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TorusAtData
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainPointBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ModerateCoefficientPositivity
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsThetaRunParametersUniformTorusStatement
import Theorems.Thm_GlobalTheory_ThetaRunParameters_exists_par


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.I2
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r m : ℕ), 2 ≤ PT.f E * r → 1 ≤ m → m ^ 4 ≤ PT.f E → (PT.f E : ℝ) ≤ PT.rd E → (PT.f E : ℝ) ^ 2 ≤ PT.rd E → 16 ≤ PT.rd E → ∃ (q : ℕ) (R0 : ℝ), 0 < th (E := E) q R0 ∧ ∀ X : PT E, X.r = r → (∃ τ, X.dim τ ≤ m) → ∃ P : Par X 1, P.q = q ∧ P.R0 = R0 ∧ P.m = m := by
  first | exact @GlobalTheory.ThetaRunParameters.exists_par | exact GlobalTheory.ThetaRunParameters.exists_par | (intros; apply GlobalTheory.ThetaRunParameters.exists_par <;> assumption)
end _root_.GlobalTheory.T
