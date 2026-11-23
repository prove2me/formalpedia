-- Prove2me | solution 1 for GlobalTheory.PrescribedRank.tup_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:22:46.315528+00:00
-- url     : https://prove2.me/submissions/34dd4341-eba2-43ed-8386-93a8f0bc99e5

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_DataG
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ConstMapInjective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.MainNotions.G MvPolynomial
noncomputable section
open GlobalTheory GlobalTheory.PrescribedRank
variable (p : ℕ) (O Kf : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
namespace GlobalTheory.PrescribedRank
theorem _root_.solution (L L' : (noPlaces p O Kf).Tup) : L = L' := funext fun v => isEmptyElim v
end GlobalTheory.PrescribedRank
