-- Prove2me | solution 1 for GroundTheory.Global.mem_maximalIdeal_iff_valued_lt_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:00:04.319833+00:00
-- url     : https://prove2.me/submissions/49416f4c-072b-4e6f-938a-3e5d84b1d5b9

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_CompletionAtPlace
import Definitions.Def_GroundTheory_GlobalFields_CompletionAtPlace_Integers
import Theorems.Thm_GroundTheory_Global_integers_valued

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField ValuativeRel
open scoped WithZero
open GroundTheory GroundTheory.Global
variable {F : Type*} [Field F] [NumberField F] (u : HeightOneSpectrum (𝓞 F))
namespace GroundTheory.Global
theorem _root_.solution (y : 𝒪[u.adicCompletion F]) :
    y ∈ 𝓂[u.adicCompletion F] ↔ Valued.v (y : u.adicCompletion F) < 1 := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
    (integers_valued u).isUnit_iff_valuation_eq_one]
  exact ⟨fun h ↦ lt_of_le_of_ne ((integers_valued u).map_le_one y) h, ne_of_lt⟩
end GroundTheory.Global
