-- Prove2me | solution 1 for GroundTheory.Global.IsTranscendenceBasis.extendScalars_of_isAlgebraic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:07:19.336093+00:00
-- url     : https://prove2.me/submissions/f66f0e1c-0003-4c3f-b9cb-7a4e21e565bf

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_ExistsRingEquivExtendOfIsTranscendenceBasis
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_AutCFixed

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Global
open Polynomial IntermediateField
variable {Ω : Type*} [Field Ω] [IsAlgClosed Ω] {F : Type*} [Field F] [Algebra F Ω]
omit [IsAlgClosed Ω]
namespace GroundTheory.Global
namespace IsTranscendenceBasis
theorem _root_.solution {E : Type*} [Field E] [Algebra F E]
    [Algebra E Ω] [IsScalarTower F E Ω] [Algebra.IsAlgebraic F E] {ι : Type*} {v : ι → Ω}
    (hv : IsTranscendenceBasis F v) : IsTranscendenceBasis E v := by
  refine (hv.1.extendScalars E).isTranscendenceBasis_iff_isAlgebraic.mpr ⟨fun z => ?_⟩
  have le : Algebra.adjoin F (Set.range v) ≤ (Algebra.adjoin E (Set.range v)).restrictScalars F :=
    Algebra.adjoin_le fun z hz => (Subalgebra.mem_restrictScalars _).mpr (Algebra.subset_adjoin hz)
  exact (hv.isAlgebraic.isAlgebraic z).tower_top_of_subalgebra_le le
end IsTranscendenceBasis
end GroundTheory.Global
