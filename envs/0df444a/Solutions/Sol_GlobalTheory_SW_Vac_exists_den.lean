-- Prove2me | solution 1 for GlobalTheory.SW.Vac.exists_den
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:44:55.344634+00:00
-- url     : https://prove2.me/submissions/f3b9563f-f191-4375-bde9-866e648edbc5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IMemSiegel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SchwartzBruhatInnerProductSelfNonnegBoundsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsExOfPow

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
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.Vac
noncomputable section
variable {κ ι : Type} [Fintype κ] [Fintype ι]
namespace GlobalTheory.SW.Vac
theorem _root_.solution (x : Matrix κ ι ℚ) : ∃ N : ℕ, 0 < N ∧ IntM ((N : ℚ) • x) := by
  classical
  refine ⟨∏ p : κ × ι, (x p.1 p.2).den, Finset.prod_pos fun p _ => (x p.1 p.2).den_pos, ?_⟩
  intro k i
  obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem (fun p : κ × ι => (x p.1 p.2).den)
    (Finset.mem_univ (k, i))
  rw [hc]
  have : (((x k i).den * c : ℕ) : ℚ) * x k i = ((c * (x k i).num : ℤ) : ℚ) := by
    push_cast; rw [← Rat.den_mul_eq_num]; ring
  simp only [Matrix.smul_apply, smul_eq_mul, this]
  exact isIntegral_algebraMap (R := ℤ)
end GlobalTheory.SW.Vac
