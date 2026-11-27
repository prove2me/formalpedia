-- Prove2me | solution 1 for Neutral.B1.contCoboundaries2_le_cocycles2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:53:29.289654+00:00
-- url     : https://prove2.me/submissions/775ac793-f85a-4623-914c-a36cb81a93e7

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
theorem _root_.solution [ContinuousMul G] (h : ContAction rho) : Bd2 rho ≤ Z2 rho := by
  rintro f ⟨c, hc, rfl⟩
  have hc' : Continuous c := hc
  refine ⟨((h.comp (continuous_fst.prodMk (hc'.comp continuous_snd))).sub
    (hc'.comp continuous_mul)).add (hc'.comp continuous_fst), fun g g' k => ?_⟩
  simp only [d1_apply, map_add, map_sub, map_mul, Module.End.mul_apply, mul_assoc]
  abel
end Neutral.B1
