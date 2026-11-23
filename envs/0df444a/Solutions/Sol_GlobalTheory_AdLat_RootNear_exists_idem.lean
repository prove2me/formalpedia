-- Prove2me | solution 1 for GlobalTheory.AdLat.RootNear.exists_idem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:45:50.05926+00:00
-- url     : https://prove2.me/submissions/24464c5a-186d-4d03-bda7-a168b035e810

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_Hat1
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsIntegralUnitRootNormOneAdeleStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_IsOpenNsmulAdelicCompletionOfVectorSetStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsAdeleRingTensorEquivInfiniteProdFiniteStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsRootNear

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.AdLat
open scoped TensorProduct Topology Matrix
noncomputable section
open GlobalTheory GlobalTheory.AdLat GlobalTheory.AdLat.RootNear
namespace GlobalTheory.AdLat.RootNear
theorem _root_.solution {ι : Type} (O : ι → Type) [∀ v, CommRing (O v)] [∀ v, IsLocalRing (O v)] (n : ℕ) :
    ∃ e f : ∀ v, O v, e * e = e ∧ 1 - e = n * f ∧ ∀ a, IsUnit (1 + e * n * a) := by
  classical
  refine ⟨fun v => if IsUnit (n : O v) then 0 else 1,
    fun v => if IsUnit (n : O v) then Ring.inverse (n : O v) else 0, ?_, ?_, ?_⟩
  · funext v
    by_cases h : IsUnit (n : O v) <;> simp [h]
  · funext v
    by_cases h : IsUnit (n : O v) <;> simp [h, Ring.mul_inverse_cancel]
  · intro a
    rw [Pi.isUnit_iff]
    intro v
    by_cases h : IsUnit (n : O v)
    · simp [h]
    · have h2 : -((n : O v) * a v) ∈ nonunits (O v) := by
        intro h3
        exact h (isUnit_of_mul_isUnit_left ((IsUnit.neg_iff _).1 h3))
      simpa [h] using IsLocalRing.isUnit_one_sub_self_of_mem_nonunits _ h2
end GlobalTheory.AdLat.RootNear
