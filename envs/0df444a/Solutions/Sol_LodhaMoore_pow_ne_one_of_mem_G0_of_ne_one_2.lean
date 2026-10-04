-- Prove2me | solution 2 for LodhaMoore.pow_ne_one_of_mem_G0_of_ne_one
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-03T11:34:28.639309+00:00
-- url     : https://prove2.me/submissions/f244c767-3953-4073-a606-e658d8432c29

import Mathlib
import Definitions.Def_LodhaMoore
import Theorems.Thm_LodhaMoore_G0_le_Hpp_and_noFreeSubgroupOfRankTwo
import Theorems.Thm_Monod_Hpp_orientation_leftOrderable_torsionFree

section
namespace LodhaMoore

end LodhaMoore
end

section
open LodhaMoore
theorem solution : ∀ g ∈ G0, g ≠ 1 → ∀ n : ℕ, 0 < n → g ^ n ≠ 1 := by
  intro g hg hne n hn hpow
  refine Monod.Hpp_orientation_leftOrderable_torsionFree.2.2 ⟨g, G0_le_Hpp_and_noFreeSubgroupOfRankTwo.1 hg⟩
    (fun h => hne (congrArg Subtype.val h)) n hn ?_
  ext1
  simpa using hpow
end
