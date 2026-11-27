-- Prove2me | solution 1 for GlobalTheory.linearIndependent_real_coe_basis
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:40:06.723035+00:00
-- url     : https://prove2.me/submissions/58c78639-61f5-4e11-ab27-96c9e90c0449

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsOrthonormalOfLinearIndependent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_LinearIndependentRealOfIntOfDiscrete
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DiscreteTopologySpanOfLinearIndependent
import Theorems.Thm_GlobalTheory_linearIndependent_real_of_int_of_discrete


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped InnerProductSpace
open Module Submodule Matrix
open GlobalTheory
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
variable [FiniteDimensional ℝ V]
namespace GlobalTheory
theorem _root_.solution {ι : Type*} [Fintype ι] {L : Submodule ℤ V}
    [DiscreteTopology L] (b : Basis ι ℤ L) : LinearIndependent ℝ fun i => (b i : V) :=
  linearIndependent_real_of_int_of_discrete L (fun i => (b i).2)
    (b.linearIndependent.map' L.subtype (ker_subtype L))
end GlobalTheory
