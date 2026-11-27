-- Prove2me | solution 2 for Neutral.B1.mem_cocycles2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:51:50.787201+00:00
-- url     : https://prove2.me/submissions/1b30be74-9ea3-44c7-bba1-a7f5dc034ee0

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
theorem _root_.solution (f : G × G → M) :
    f ∈ Z2 rho ↔ Continuous f ∧
      ∀ g h k, rho g (f (h, k)) - f (g * h, k) + f (g, h * k) - f (g, h) = 0 := Iff.rfl
end Neutral.B1
