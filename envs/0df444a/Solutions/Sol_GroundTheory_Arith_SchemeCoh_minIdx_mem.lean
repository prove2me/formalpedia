-- Prove2me | solution 1 for GroundTheory.Arith.SchemeCoh.minIdx_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:47:10.406865+00:00
-- url     : https://prove2.me/submissions/b47d1ba4-1a4a-40da-99e9-8866a4709102

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
variable [LinearOrder ι]
namespace GroundTheory.Arith.SchemeCoh
theorem _root_.solution {n : ℕ} (i : Fin (n + 1) → ι) : minIdx i ∈ Set.range i := by
  obtain ⟨a, -, ha⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty i
  exact ⟨a, ha.symm⟩
end GroundTheory.Arith.SchemeCoh
