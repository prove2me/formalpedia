-- Prove2me | solution 1 for GlobalTheory.mem_powSaturation
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:21:30.627804+00:00
-- url     : https://prove2.me/submissions/c8af6716-ab74-4f61-98d6-c5dee02a7a94

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_HasRationalTorsionIffMemRange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsIntegralModelOfForms

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open WeierstrassCurve Polynomial
variable {K : Type*} [Field K]
namespace GlobalTheory
theorem _root_.solution {S : Subring K} {p : ℕ} {x y : K} (n : ℕ) (hy : y ∈ S)
    (h : (p : K) ^ n * x = y) : x ∈ powSaturation S p :=
  ⟨n, h ▸ hy⟩
end GlobalTheory
