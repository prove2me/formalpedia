-- Prove2me | solution 1 for GlobalTheory.Phase.ShapeOps.exists_den
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T19:25:55.306798+00:00
-- url     : https://prove2.me/submissions/2833ec93-0495-414c-b389-e5bebf8170c0

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
theorem _root_.solution (y : Matrix κ ι ℚ) : ∃ N : ℕ, 0 < N ∧ IntM ((N : ℚ) • y) := by
  classical
  refine ⟨∏ p : κ × ι, (y p.1 p.2).den, Finset.prod_pos fun p _ => Rat.den_pos _, fun k i => ?_⟩
  obtain ⟨c, hc⟩ : (y k i).den ∣ ∏ p : κ × ι, (y p.1 p.2).den :=
    Finset.dvd_prod_of_mem (fun p : κ × ι => (y p.1 p.2).den) (Finset.mem_univ (k, i))
  rw [hc, Matrix.smul_apply, smul_eq_mul]
  have : (((y k i).den * c : ℕ) : ℚ) * y k i = algebraMap ℤ ℚ (c * (y k i).num) := by
    have h := Rat.den_mul_eq_num (y k i)
    simp only [eq_intCast]
    push_cast
    rw [← h]; ring
  rw [this]
  exact isIntegral_algebraMap
end GlobalTheory.Phase.ShapeOps
