-- Prove2me | solution 1 for Neutral.B1.contCoboundaries1_le_cocycles1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:52:30.507081+00:00
-- url     : https://prove2.me/submissions/898a357c-fcbd-4a02-a881-385428cd0c57

import Mathlib
import Definitions.Def_ReciprocityTheory_NeutralLocalFields_Reciprocity
import Definitions.Def_ReciprocityTheory_NeutralLocalFields_Duality

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Representation
open Neutral Neutral.B1
set_option linter.unusedVariables false
noncomputable section
open Representation
variable {R : Type*} [CommRing R]
variable {G : Type*} [Group G] [TopologicalSpace G]
variable {M : Type*} [AddCommGroup M] [Module R M] [TopologicalSpace M]
  [IsTopologicalAddGroup M] [ContinuousConstSMul R M]
variable (rho : Representation R G M)
namespace Neutral.B1
theorem _root_.solution (h : ContAction rho) : Bd1 rho ≤ Z1 rho := by
  rintro f ⟨m, rfl⟩
  refine ⟨(h.comp (continuous_id.prodMk continuous_const)).sub continuous_const, fun g g' => ?_⟩
  simp only [amitsur_d0_apply, map_mul, Module.End.mul_apply, map_sub]
  abel
end Neutral.B1
