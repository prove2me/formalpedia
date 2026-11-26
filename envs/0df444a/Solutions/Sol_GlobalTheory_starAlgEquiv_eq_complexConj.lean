-- Prove2me | solution 1 for GlobalTheory.starAlgEquiv_eq_complexConj
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-26T03:22:08.357567+00:00
-- url     : https://prove2.me/submissions/7e8517aa-0d35-4278-98fd-88336d4ea7da

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MemUnitaryGroupIffIsIsometry
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open NumberField
open GlobalTheory
universe u v
attribute [instance] HermModule.addCommGroup HermModule.module
attribute [instance] HermSpace.addCommGroup HermSpace.module HermSpace.finite
attribute [simp] IsStarFixed.star_algebraMap
variable (E : Type*) [Field E] [NumberField E] [IsCMField E]
theorem _root_.solution :
    starAlgEquiv (maximalRealSubfield E) E = IsCMField.complexConj E := by
  first
    | (intros; rfl)
    | exact Iff.rfl
    | (intros; ext; rfl)
    | (intros; exact (Finset.sup_univ_eq_ciSup _))
    | (intros; simp [GlobalTheory.mem_saturation_iff'])
    | (intros; exact (isoTransvection.pow ..))
    | (intros; ext; simp)
    | (intros; exact?)

