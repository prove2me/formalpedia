-- Prove2me | solution 1 for GlobalTheory.SW.Parab.par_exists_den
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T18:07:49.860077+00:00
-- url     : https://prove2.me/submissions/05abefdf-c0b6-44c3-a7c6-1ac75ca65e66

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IMemSiegel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_RationalSchwartzBruhatAlgebraIntegralLinearStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SchwartzBruhatInvariantIntegralMatrixMulStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SiegelThetaTransformationSiegelParabolic

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex GlobalTheory.SW
open scoped ComplexConjugate Real
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.Parab
namespace GlobalTheory.SW.Parab
theorem _root_.solution {ι : Type} [Fintype ι] (S : Matrix ι ι ℚ) :
    ∃ N : ℕ, 0 < N ∧ ∀ i j, IsIntegral ℤ (((N : ℚ) • S) i j) := by
  classical
  refine ⟨∏ p : ι × ι, (S p.1 p.2).den, Finset.prod_pos fun p _ => (S p.1 p.2).den_pos, ?_⟩
  intro i j
  obtain ⟨c, hc⟩ : (S i j).den ∣ ∏ p : ι × ι, (S p.1 p.2).den :=
    Finset.dvd_prod_of_mem (fun p : ι × ι => (S p.1 p.2).den) (Finset.mem_univ (i, j))
  rw [hc, Matrix.smul_apply, smul_eq_mul]
  have : (((S i j).den * c : ℕ) : ℚ) * S i j = algebraMap ℤ ℚ (c * (S i j).num) := by
    simp only [eq_intCast, Int.cast_mul, Int.cast_natCast, Nat.cast_mul]
    rw [← Rat.mul_den_eq_num (S i j)]
    ring
  rw [this]
  exact isIntegral_algebraMap
end GlobalTheory.SW.Parab
