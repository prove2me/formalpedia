-- Prove2me | solution 1 for GroundTheory.LocalField.quotient_mk_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T01:18:49.188076+00:00
-- url     : https://prove2.me/submissions/4bd92345-3211-4bab-85cd-a001b28ed200

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_CompleteTrivial
import Definitions.Def_GroundTheory_LocalFields_NormalLattice
import Definitions.Def_GroundTheory_LocalFields_CompleteTrivialLocal

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
open GroundTheory GroundTheory.LocalField
open ValuativeRel Finset
variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]
omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] [ValuativeRel L] [ValuativeExtension K L]
  [FiniteDimensional K L]
namespace GroundTheory.LocalField
theorem _root_.solution {N : AddSubgroup L} {ι : Type*} [Fintype ι] (g : ι → L) :
    ∑ i, (g i : L ⧸ N) = ((∑ i, g i : L) : L ⧸ N) :=
  (map_sum (QuotientAddGroup.mk' N) g univ).symm
end GroundTheory.LocalField
