-- Prove2me | solution 1 for GlobalTheory.T.polarization_module_unit_dual
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T20:17:56.34068+00:00
-- url     : https://prove2.me/submissions/765b9fcb-66ec-4526-b674-e6dd85138a66

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PolarizationModuleUnitDual
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_PolarisationModuleIndex
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PolarizationModuleUnitDualStatement
import Theorems.Thm_GlobalTheory_PolModLattice_polMod_isUnit_mul_eq_dual


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.PolarisationModuleIndex
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (L : Submodule (OF E) E),
    (∃ N : ℕ, 0 < N ∧ (∀ x : 𝓞 E, (N : E) * algebraMap (𝓞 E) E x ∈ L) ∧ ∀ x ∈ L, IsIntegral ℤ ((N : E) * x)) →
    IsUnit (polMod L) ∧ polMod L * L = dualLat L := by
  first | exact @GlobalTheory.PolModLattice.polMod_isUnit_mul_eq_dual | exact GlobalTheory.PolModLattice.polMod_isUnit_mul_eq_dual | (intros; apply GlobalTheory.PolModLattice.polMod_isUnit_mul_eq_dual <;> assumption)
end _root_.GlobalTheory.T
