-- Prove2me | solution 1 for MassDataIdxCore.secondSplit_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:07:16.845906+00:00
-- url     : https://prove2.me/submissions/33b9fbc8-f536-4d85-a6c3-f74f47cf0cd2

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeIndices_StRedCore

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MassDataIdxCore
open Matrix
variable {K T : Type} [Field K] [CommRing T] [Algebra K T] (θ : T ≃ₐ[K] K × K)
namespace MassDataIdxCore
theorem _root_.solution (t : T) : t2 θ t = (θ t).2 := rfl
end MassDataIdxCore
