-- Prove2me | solution 1 for GroundTheory.Arith.SchemeCoh.eq_of_supported
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:34:27.348678+00:00
-- url     : https://prove2.me/submissions/5c39ed65-f5f3-460d-aef0-25cae77b4421

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ConsCompSuccAboveZero
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_CechNaturality_Chains

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Arith GroundTheory.Arith.SchemeCoh
open CategoryTheory
universe w
variable {ι : Type w}
namespace GroundTheory.Arith.SchemeCoh
theorem _root_.solution {m : ℕ} {M : Type*} [AddCommGroup M] (L L' : Chain ι m →+ M)
    {S : Set (Fin (m + 1) → ι)} (h : ∀ j ∈ S, ∀ z : ℤ, L (Finsupp.single j z) = L' (Finsupp.single j z))
    {c : Chain ι m} (hc : c ∈ Finsupp.supported ℤ ℤ S) : L c = L' c := by
  rw [← Finsupp.sum_single c, Finsupp.sum, map_sum, map_sum]
  exact Finset.sum_congr rfl fun j hj => h j ((Finsupp.mem_supported ℤ c).1 hc hj) _
end GroundTheory.Arith.SchemeCoh
