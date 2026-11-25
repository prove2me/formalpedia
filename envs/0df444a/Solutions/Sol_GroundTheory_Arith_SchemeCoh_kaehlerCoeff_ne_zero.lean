-- Prove2me | solution 1 for GroundTheory.Arith.SchemeCoh.kaehlerCoeff_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T01:24:58.06859+00:00
-- url     : https://prove2.me/submissions/5111c2fd-77b7-4270-aba2-5df210d4ec10

import Mathlib
import Definitions.Def_GroundTheory_FunctionField_PlaceBridge
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_KaehlerPlace
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_kaehlerCoeff_smul_D

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Arith GroundTheory.Arith.SchemeCoh
open GroundTheory.FunctionField KaehlerDifferential IntermediateField
variable {k K : Type*} [Field k] [Field K] [Algebra k K]
variable [IsFunctionField k K]
variable [PerfectField k]
namespace GroundTheory.Arith.SchemeCoh
theorem _root_.solution {t : K} (ht : D k K t ≠ 0) {ω : Ω[K⁄k]} (hω : ω ≠ 0) :
    kaehlerCoeff t ω ≠ 0 := by
  intro h
  have := kaehlerCoeff_smul_D ht ω
  rw [h, zero_smul] at this
  exact hω this.symm
end GroundTheory.Arith.SchemeCoh
