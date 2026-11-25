-- Prove2me | solution 1 for GroundTheory.LocalField.repr_mem_of_mem_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:14:24.242826+00:00
-- url     : https://prove2.me/submissions/c9b8c1a3-d875-4923-b59e-0e81db039fb2

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_LubinTateReciprocity_RootEval

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.LocalField
open PowerSeries
variable {B : Type*} [CommRing B] {I : Ideal B} {P : Polynomial B}
namespace GroundTheory.LocalField
theorem _root_.solution (hP : P.Monic) (J : Ideal B) {z : AdjoinRoot P}
    (hz : z ∈ J.map (AdjoinRoot.of P)) (i : Fin (AdjoinRoot.powerBasis' hP).dim) :
    (AdjoinRoot.powerBasis' hP).basis.repr z i ∈ J := by
  have hz' : z ∈ J • (⊤ : Submodule B (AdjoinRoot P)) := by
    rw [Ideal.smul_top_eq_map]
    exact hz
  refine Submodule.smul_induction_on hz' (fun a ha m _ => ?_) (fun x y hx hy => ?_)
  · rw [map_smul, Finsupp.smul_apply, smul_eq_mul]
    exact J.mul_mem_right _ ha
  · rw [map_add, Finsupp.add_apply]
    exact J.add_mem hx hy
end GroundTheory.LocalField
