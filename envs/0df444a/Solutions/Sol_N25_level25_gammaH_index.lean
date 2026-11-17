-- Prove2me | solution 1 for N25.level25_gammaH_index
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:42:41.760876+00:00
-- url     : https://prove2.me/submissions/16b9c11b-4258-4560-b363-2b48ddd22759

import Mathlib
import Definitions.Def_N25
import Theorems.Thm_N25_level25_row_lift

set_option autoImplicit false

open scoped MatrixGroups

namespace N25

/-- Reduction of the lower-right entry maps the integral Borel onto all residue units. -/
private theorem level25_gamma0Units_surjective : Function.Surjective (CohCarrier.gamma0Units 25) := by
  intro u
  obtain ⟨A, hc, hd⟩ := level25_row_lift 0 (u : ZMod 25) (Or.inr u.isUnit)
  have hA : A ∈ CongruenceSubgroup.Gamma0 25 := CongruenceSubgroup.Gamma0_mem.mpr hc
  refine ⟨⟨A, hA⟩, ?_⟩
  apply Units.ext
  exact hd

/-- The level-H index is the product of the Borel index and the unit-group index. -/
theorem _root_.solution (H : Subgroup (ZMod 25)ˣ) :
    (CohCarrier.GammaH 25 H).index = H.index * (CongruenceSubgroup.Gamma0 25).index := by
  rw [CohCarrier.GammaH, Subgroup.index_map_subtype,
    Subgroup.index_comap_of_surjective H level25_gamma0Units_surjective]

end N25
