-- Prove2me | solution 1 for GlobalTheory.awayFrac_zero_bijective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:46:20.222981+00:00
-- url     : https://prove2.me/submissions/09baa346-4cbc-4fa0-b132-d740c8892fc3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsIsoTermComparisonRestrictScalars
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_CubeComplexAcyclicIffQuasiIsoCechAug
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_CubeComplexExactAtOfIsLocalizedModuleRes
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsGradedMapLinearCombination
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_ExistsAwayFracOfMemHomLoc

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open DirectSum MvPolynomial CategoryTheory
universe u
noncomputable section
open GlobalTheory
open GradedHilbert
variable {A : Type*} [CommRing A] (M : Type*) [AddCommGroup M] [Module A M]
  {N : Type*} [AddCommGroup N] [Module A N] {P : Type*} [AddCommGroup P] [Module A P]
variable {M}
namespace GlobalTheory
theorem _root_.solution {f : A} (h : Function.Bijective fun m : M => f • m) :
    Function.Bijective (awayFrac M f 0) := by
  refine ⟨awayFrac_injective h.1 0, fun z => ?_⟩
  obtain ⟨k, m, rfl⟩ := exists_awayFrac z
  obtain ⟨y, rfl⟩ := (h.2.iterate k) m
  refine ⟨y, ?_⟩
  rw [smul_iterate_apply, ← awayFrac_add_pow_smul f 0 k, zero_add]
end GlobalTheory
