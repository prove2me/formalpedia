-- Prove2me | solution 1 for OAI.UniversalFInfinity.Milnor.contractible
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T19:54:55.798347+00:00
-- url     : https://prove2.me/submissions/76b01fa5-d7f9-4ede-a65c-3f50a4894d0d

import Mathlib
import Definitions.Def_OAIQWUFI006
import Theorems.Thm_OAI_UniversalFInfinity_Cellular_contractible_of_sphereFillable

section
-- module Solutions.OAIQW_UniversalFInfinity.MilnorControl
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Topology BigOperators
open Set Metric Topology

namespace UniversalFInfinity.Milnor

section
open Set Metric Topology BigOperators UniversalFInfinity.Simplicial
open scoped Classical unitInterval
universe u v
variable {G : Type u}

local instance (priority := 2000) instDecidableEqProdNat_solutions_r461751_1 (α : Type*) : DecidableEq (ℕ × α) := Classical.decEq (ℕ × α)
lemma contractible_oai [Nonempty G] : ContractibleSpace (Space G) := by
  let g : G := Classical.choice ‹Nonempty G›
  let : Nonempty (Space G) := ⟨vertex (0,g)⟩
  exact Cellular.contractible_of_sphereFillable (sphereFillable g)

end

open Set Metric Topology BigOperators UniversalFInfinity.Simplicial
open scoped Classical unitInterval
universe u v
end UniversalFInfinity.Milnor

end

end OAI
end

theorem solution.{u} : type_of% @OAI.UniversalFInfinity.Milnor.contractible_oai.{u} := @OAI.UniversalFInfinity.Milnor.contractible_oai.{u}
