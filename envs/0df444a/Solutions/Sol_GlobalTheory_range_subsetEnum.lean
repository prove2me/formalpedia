-- Prove2me | solution 1 for GlobalTheory.range_subsetEnum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:13:56.514317+00:00
-- url     : https://prove2.me/submissions/c9a1dfbe-dd54-4680-b414-9f5590834944

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_MulConjTransposeEqOneOfOrthonormal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open GlobalTheory
variable {R : Type*} [CommRing R]
namespace GlobalTheory
theorem _root_.solution {n : Type*} [LinearOrder n] {i : ℕ} (S : Set.powersetCard n i) :
    Set.range (subsetEnum S) = (S.1 : Set n) :=
  Finset.range_orderEmbOfFin _ _
end GlobalTheory
