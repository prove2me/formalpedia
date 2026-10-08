-- Prove2me | solution 1 for OAI.Erdos3.selectedCombined_coprime_outside
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-08T10:23:47.422755+00:00
-- url     : https://prove2.me/submissions/1634ed01-2252-4145-af0e-e8a1044dc56b

import Mathlib
import Definitions.Def_ErdosReciprocal

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.StableReferenceMean
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem selectedCombined_coprime_outside {ι : Type*} [DecidableEq ι]
    (q : ι → ℕ) (hpair : Pairwise (fun i j => (q i).Coprime (q j))) (M : ℕ) (K : Finset ι)
    (hcop : ∀ i ∉ K, M.Coprime (q i)) (j : ι) (hj : j ∉ K) :
    (M.lcm (∏ i ∈ K, q i)).Coprime (q j) := by
  have hK : (∏ i ∈ K, q i).Coprime (q j) := by
    apply Nat.coprime_prod_left_iff.mpr
    intro i hi
    exact hpair (fun heq => hj (heq ▸ hi))
  exact Nat.Coprime.of_dvd_left (Nat.lcm_dvd_mul M _)
    (Nat.coprime_mul_iff_left.mpr ⟨hcop j hj, hK⟩)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

end OAI

end

theorem solution.{u_1} : type_of% @OAI.Erdos3.selectedCombined_coprime_outside.{u_1} := @OAI.Erdos3.selectedCombined_coprime_outside.{u_1}
