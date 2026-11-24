-- Prove2me | solution 1 for GlobalTheory.DI.Dtot_Dtot
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:52:38.043437+00:00
-- url     : https://prove2.me/submissions/1c61432c-39e1-4973-a698-de376e6cfda8

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFlatLift
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CechAndTotalDifferentialAdditiveSquareZero
import Theorems.Thm_GlobalTheory_DI_delta_delta

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open GlobalTheory GlobalTheory.DI
variable {ι : Type} [LinearOrder ι] {E : Type} [AddCommGroup E]
namespace GlobalTheory.DI
theorem _root_.solution (d : E →+ E) (hd : ∀ x, d (d x) = 0) (c : Finset ι → E) :
    Dtot d (Dtot d c) = 0 := by
  funext t
  have hDt : ∀ s, Dtot d c s = delta c s + (-1 : ℤ) ^ s.card • d (c s) := fun s => rfl
  have e1 : delta (Dtot d c) t = delta (delta c) t +
      ∑ i ∈ t, cubeSign t i • ((-1 : ℤ) ^ (t.erase i).card • d (c (t.erase i))) := by
    show ∑ i ∈ t, cubeSign t i • Dtot d c (t.erase i) = delta (delta c) t + _
    simp only [hDt, smul_add, Finset.sum_add_distrib]
    rfl
  have e2 : d (delta c t) = ∑ i ∈ t, cubeSign t i • d (c (t.erase i)) := by
    show d (∑ i ∈ t, cubeSign t i • c (t.erase i)) = _
    rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => map_zsmul d _ _
  show delta (Dtot d c) t + (-1 : ℤ) ^ t.card • d (Dtot d c t) = 0
  rw [e1, delta_delta, hDt, map_add, map_zsmul, hd, smul_zero, add_zero, e2, Finset.smul_sum,
    Pi.zero_apply, zero_add, ← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero fun i hi => ?_
  have hc : (-1 : ℤ) ^ (t.erase i).card = -(-1 : ℤ) ^ t.card := by
    rw [← Finset.card_erase_add_one hi, pow_succ]; ring
  rw [hc, neg_smul, smul_neg, smul_comm, neg_add_cancel]
end GlobalTheory.DI
