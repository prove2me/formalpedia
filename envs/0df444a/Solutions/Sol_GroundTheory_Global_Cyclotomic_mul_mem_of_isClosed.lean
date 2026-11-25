-- Prove2me | solution 1 for GroundTheory.Global.Cyclotomic.mul_mem_of_isClosed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:05:16.218956+00:00
-- url     : https://prove2.me/submissions/85bca251-82ec-4c0d-a435-72da5f026883

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_CyclotomicCharacters_ProfinitePadic
import Definitions.Def_GroundTheory_GlobalFields_CyclotomicCharacters_ClosedSubgroups

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology
open scoped GroundTheory.LocalField.Abstract
open GroundTheory GroundTheory.Global
open GroundTheory.Global.Cyclotomic
open GroundTheory.LocalField.Abstract
variable {ℓ : ℕ} [hℓ : Fact ℓ.Prime]
namespace GroundTheory.Global.Cyclotomic
theorem _root_.solution (H : AddSubgroup ℤ_[ℓ]) (hH : IsClosed (H : Set ℤ_[ℓ])) {x : ℤ_[ℓ]}
    (hx : x ∈ H) (t : ℤ_[ℓ]) : x * t ∈ H :=
  PadicInt.denseRange_natCast.induction_on t (hH.preimage (continuous_const.mul continuous_id))
    fun k => by
      show x * (k : ℤ_[ℓ]) ∈ H
      rw [mul_comm, ← nsmul_eq_mul]
      exact H.nsmul_mem hx k
end GroundTheory.Global.Cyclotomic
