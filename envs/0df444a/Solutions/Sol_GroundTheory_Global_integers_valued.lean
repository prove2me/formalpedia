-- Prove2me | solution 1 for GroundTheory.Global.integers_valued
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:48:31.498398+00:00
-- url     : https://prove2.me/submissions/231f15fc-b19d-4219-ac9b-b7966f399996

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_CompletionAtPlace
import Definitions.Def_GroundTheory_GlobalFields_CompletionAtPlace_Integers
import Theorems.Thm_GroundTheory_Global_mem_valuationInteger_iff


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
theorem _root_.solution :
    (Valued.v : Valuation (u.adicCompletion F) ℤᵐ⁰).Integers 𝒪[u.adicCompletion F] where
  hom_inj a b h := Subtype.ext h
  map_le_one y := by
    have h : (y : u.adicCompletion F) ∈ u.adicCompletionIntegers F :=
      (mem_valuationInteger_iff u (y : u.adicCompletion F)).1 y.2
    exact h
  exists_of_le_one x hx := ⟨⟨x, (mem_valuationInteger_iff u x).2 hx⟩, rfl⟩
end GroundTheory.Global
