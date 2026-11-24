-- Prove2me | solution 1 for GroundTheory.Arith.SchemeCoh.map_mem_supported
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:34:03.050531+00:00
-- url     : https://prove2.me/submissions/40600a23-bc97-4e3a-8d01-38e05a944c9b

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
theorem _root_.solution {m n : ℕ} (L : Chain ι m →+ Chain ι n) {S : Set (Fin (m + 1) → ι)}
    {T : Set (Fin (n + 1) → ι)}
    (h : ∀ j ∈ S, ∀ z : ℤ, L (Finsupp.single j z) ∈ Finsupp.supported ℤ ℤ T) {c : Chain ι m}
    (hc : c ∈ Finsupp.supported ℤ ℤ S) : L c ∈ Finsupp.supported ℤ ℤ T := by
  rw [← Finsupp.sum_single c, Finsupp.sum, map_sum]
  exact Submodule.sum_mem _ fun j hj => h j ((Finsupp.mem_supported ℤ c).1 hc hj) _
end GroundTheory.Arith.SchemeCoh
