-- Prove2me | solution 1 for GroundTheory.PAdicHodge.norm_untilt_sum_sub_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:55:33.221806+00:00
-- url     : https://prove2.me/submissions/e90155b9-b182-497c-9e86-66eb6ae9e499

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_PerfectoidField
import Definitions.Def_GroundTheory_PAdicHodge_TiltValuation
import Definitions.Def_GroundTheory_PAdicHodge_TiltField
import Definitions.Def_GroundTheory_PAdicHodge_KerTheta
import Definitions.Def_GroundTheory_PAdicHodge_TiltMap
import Definitions.Def_GroundTheory_PAdicHodge_TiltAlgebra
import Theorems.Thm_GroundTheory_PAdicHodge_tiltMap_algebraMap
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.PAdicHodge.tiltMap_algebraMap



set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.PAdicHodge
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
variable {p : ℕ} [Fact p.Prime] [IsPerfectoidField K p]
namespace GroundTheory.PAdicHodge
theorem _root_.solution {ι : Type*} (s : Finset ι) (x : ι → PreTilt (normInteger K) p) :
    ‖(((∑ i ∈ s, x i).untilt : normInteger K) : K) - ∑ i ∈ s, ((x i).untilt : K)‖ ≤
      ‖(p : K)‖ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    rw [Finset.sum_insert hj, Finset.sum_insert hj]
    have h1 := norm_untilt_add_sub_le (x j) (∑ i ∈ s, x i)
    have e : (((x j + ∑ i ∈ s, x i).untilt : normInteger K) : K) -
        (((x j).untilt : K) + ∑ i ∈ s, ((x i).untilt : K)) =
        ((((x j + ∑ i ∈ s, x i).untilt : normInteger K) : K) -
          (((x j).untilt + (∑ i ∈ s, x i).untilt : normInteger K) : K)) +
        ((((∑ i ∈ s, x i).untilt : normInteger K) : K) - ∑ i ∈ s, ((x i).untilt : K)) := by
      push_cast; ring
    rw [e]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le h1 ih)
end GroundTheory.PAdicHodge
