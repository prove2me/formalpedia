-- Prove2me | solution 1 for GroundTheory.PAdicHodge.adjoin_sub_one_eq_cycl
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:53:31.529869+00:00
-- url     : https://prove2.me/submissions/563d8f48-dd04-47a2-ba49-8aee5667ffe2

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_NormalizedTrace
import Definitions.Def_GroundTheory_PAdicHodge_CyclotomicField
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_NormNatCastPrime
import Definitions.Def_GroundTheory_PAdicHodge_CyclotomicTower
import Theorems.Thm_GroundTheory_PAdicHodge_cycl_eq_adjoin


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.PAdicHodge
open IntermediateField Polynomial Module
noncomputable section
variable {p : ℕ} [Fact p.Prime]
namespace GroundTheory.PAdicHodge
theorem _root_.solution {ζ : PadicAlgCl p} {n : ℕ} (hζ : IsPrimitiveRoot ζ (p ^ n)) :
    ℚ_[p]⟮ζ - 1⟯ = cycl p n := by
  rw [cycl_eq_adjoin hζ]
  apply le_antisymm
  · rw [adjoin_simple_le_iff]
    exact sub_mem (mem_adjoin_simple_self ℚ_[p] ζ) (one_mem _)
  · rw [adjoin_simple_le_iff]
    have h := add_mem (mem_adjoin_simple_self ℚ_[p] (ζ - 1)) (one_mem ℚ_[p]⟮ζ - 1⟯)
    rwa [sub_add_cancel] at h
end GroundTheory.PAdicHodge
