-- Prove2me | solution 1 for GroundTheory.Automorphic.iwasawa_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:44:21.6919+00:00
-- url     : https://prove2.me/submissions/97fc288d-021e-441f-a679-2a107eeae6ab

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_RealGroupsPolar
import Definitions.Def_GroundTheory_AutomorphicForms_RealGroupsIwasawa
import Theorems.Thm_GroundTheory_Automorphic_coe_iwasawaHomeomorph_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.coe_iwasawaHomeomorph_apply

set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open Matrix
open scoped ComplexOrder
set_option linter.unusedSectionVars false
variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [LinearOrder n]
open scoped Matrix.Norms.L2Operator Topology
open Filter Set
variable [WellFoundedLT n] [LocallyFiniteOrderBot n]
namespace GroundTheory.Automorphic
theorem _root_.solution (g : GL n 𝕜) :
    ∃! x : unitaryGroup n 𝕜 × PosDiag n × UpperUnitriangular n 𝕜,
      (x.1 : Matrix n n 𝕜) * diagonal (fun i => (x.2.1.1 i : 𝕜)) * x.2.2.1 = g := by
  refine ⟨iwasawaHomeomorph.symm g, congrArg Units.val (iwasawaHomeomorph.apply_symm_apply g), ?_⟩
  intro x hx
  apply iwasawaHomeomorph.injective
  rw [Homeomorph.apply_symm_apply]
  exact Units.ext hx
end GroundTheory.Automorphic
