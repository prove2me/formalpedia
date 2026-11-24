-- Prove2me | solution 1 for GlobalTheory.SW.heisS_exists_den
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T20:31:12.083188+00:00
-- url     : https://prove2.me/submissions/73b929b1-94bd-4f1d-9541-64e674a48fa6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IMemSiegel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_RationalSchwartzBruhatAlgebraIntegralLinearStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HeisenbergOperatorRationalPointLaws

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
open GlobalTheory GlobalTheory.SW
namespace GlobalTheory.SW
theorem _root_.solution {κ ι : Type} [Fintype κ] [Fintype ι] (a : Matrix κ ι ℚ) :
    ∃ D : ℕ, 0 < D ∧ ∀ k i, IsIntegral ℤ ((D : ℚ) * a k i) := by
  classical
  refine ⟨∏ p : κ × ι, (a p.1 p.2).den, Finset.prod_pos fun p _ => (a p.1 p.2).den_pos, ?_⟩
  intro k i
  obtain ⟨c, hc⟩ : (a k i).den ∣ ∏ p : κ × ι, (a p.1 p.2).den :=
    Finset.dvd_prod_of_mem (fun p : κ × ι => (a p.1 p.2).den) (Finset.mem_univ (k, i))
  have : ((∏ p : κ × ι, (a p.1 p.2).den : ℕ) : ℚ) * a k i
      = algebraMap ℤ ℚ ((c : ℤ) * (a k i).num) := by
    rw [hc]
    have h := Rat.mul_den_eq_num (a k i)
    simp only [eq_intCast, Int.cast_mul, Int.cast_natCast, Nat.cast_mul]
    rw [← h]; ring
  rw [this]
  exact isIntegral_algebraMap
end GlobalTheory.SW
