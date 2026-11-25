-- Prove2me | solution 1 for GlobalTheory.ArchMetric.muMax_ne_bot
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:35:06.889532+00:00
-- url     : https://prove2.me/submissions/f90b6bbd-16cc-4a2d-8109-0711c562bbe6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_MemSaturatedOrderIsoSubspaceSpanSymmApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FinrankMulDiscrRpowLeSumSqOfMemTraceDual
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsSmulMemOfMemSpanLattice

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module Matrix
open scoped ComplexOrder ComplexConjugate
open GlobalTheory
open GlobalTheory.ArchMetric
variable {K : Type*} [Field K] [NumberField K] {V V' : Type*} [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [AddCommGroup V'] [Module K V']
  [Module (𝓞 K) V'] [IsScalarTower (𝓞 K) K V'] (h : ArchMetric K V)
variable {A B : Submodule (𝓞 K) V}
namespace GlobalTheory.ArchMetric
theorem _root_.solution (h0 : A ≠ ⊥) : h.muMax A ≠ ⊥ :=
  ((EReal.bot_lt_coe _).trans_le (h.slope_le_muMax le_rfl h0)).ne'
end GlobalTheory.ArchMetric
