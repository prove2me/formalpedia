-- Prove2me | solution 1 for MassDataIdxRed.glRed_coe
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:01:09.762619+00:00
-- url     : https://prove2.me/submissions/e8257d78-2dc9-4bd9-a7be-ed307e0b2fb1

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeIndices_GlRedEqOneIff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MassDataIdxRed
open Matrix
namespace MassDataIdxRed
theorem _root_.solution {ι R S : Type} [Fintype ι] [DecidableEq ι] [CommRing R] [CommRing S] (π : R →+* S)
    (A : GL ι R) : ((glRed π A : GL ι S) : Matrix ι ι S) = (A : Matrix ι ι R).map π := rfl
end MassDataIdxRed
