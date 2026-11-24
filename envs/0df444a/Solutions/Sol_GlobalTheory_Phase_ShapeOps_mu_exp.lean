-- Prove2me | solution 1 for GlobalTheory.Phase.ShapeOps.mu_exp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T19:25:57.470054+00:00
-- url     : https://prove2.me/submissions/416e4279-2d19-4db9-b51b-d54e3de6e4a1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IntMIffInt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_RationalSchwartzBruhatAlgebraIntegralLinear
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_IsCosetQuadraticPhaseTestFunctionConjCharacterMu

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
open GlobalTheory GlobalTheory.Phase GlobalTheory.Phase.ShapeOps
variable {κ ι : Type} [Fintype κ] [Fintype ι]
namespace GlobalTheory.Phase.ShapeOps
theorem _root_.solution (q : ℚ) : IsMu (cexp (2 * Real.pi * I * (q : ℂ))) := by
  refine ⟨q.den, q.den_pos, ?_⟩
  rw [← Complex.exp_nat_mul]
  have h : ((q.den : ℚ) * q) = q.num := Rat.den_mul_eq_num q
  have h' : ((q.den : ℂ) * q) = q.num := by exact_mod_cast congrArg (fun t : ℚ => (t : ℂ)) h
  rw [show (q.den : ℂ) * (2 * Real.pi * I * (q : ℂ)) = ((q.den : ℂ) * q) * (2 * Real.pi * I) by ring, h']
  exact Complex.exp_int_mul_two_pi_mul_I _
end GlobalTheory.Phase.ShapeOps
