-- Prove2me | solution 1 for GlobalTheory.Phase.VacShape.isMu_ex
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:57:07.452114+00:00
-- url     : https://prove2.me/submissions/dc46491a-b1e3-4ac0-958a-48d1ff59f543

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IntMIffInt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsExOfPow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SelfDualVacuumGaussianShapeRootOfUnityPhases

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex GlobalTheory.SW GlobalTheory.Phase
open scoped ComplexConjugate Real
open GlobalTheory GlobalTheory.Phase GlobalTheory.Phase.VacShape
open GlobalTheory.SW.Vac
namespace GlobalTheory.Phase.VacShape
theorem _root_.solution (q : ℚ) : IsMu (ex q) := by
  refine ⟨2 * q.den, Nat.mul_pos two_pos q.den_pos, ?_⟩
  rw [ex, ← Complex.exp_nat_mul, Complex.exp_eq_one_iff]
  refine ⟨q.num, ?_⟩
  have : (q.den : ℂ) * (q : ℂ) = q.num := by exact_mod_cast Rat.den_mul_eq_num q
  rw [← this]; push_cast; ring
end GlobalTheory.Phase.VacShape
