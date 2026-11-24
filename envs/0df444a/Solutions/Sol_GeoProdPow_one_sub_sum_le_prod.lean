-- Prove2me | solution 1 for GeoProdPow.one_sub_sum_le_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:52:59.381801+00:00
-- url     : https://prove2.me/submissions/3ff4f14f-0ae3-434d-a5ec-ff7617b8057c

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_GeometricProductPowers_GaussianProductPowerBound
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GeometricProductBound_OneSubSumLeProd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GeoProdPow
open Finset
namespace GeoProdPow
theorem _root_.solution (s : Finset ℕ) (u a : ℕ → ℝ) (h0 : ∀ i ∈ s, 0 ≤ u i)
    (h1 : ∀ i ∈ s, u i ≤ 1) (ha : ∀ i ∈ s, 1 - a i ≤ u i) :
    1 - ∑ i ∈ s, a i ≤ ∏ i ∈ s, u i := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    rw [Finset.prod_insert hj, Finset.sum_insert hj]
    have hP1 : ∏ i ∈ s, u i ≤ 1 :=
      Finset.prod_le_one (fun i hi => h0 i (Finset.mem_insert_of_mem hi))
        (fun i hi => h1 i (Finset.mem_insert_of_mem hi))
    have hP := ih (fun i hi => h0 i (Finset.mem_insert_of_mem hi))
      (fun i hi => h1 i (Finset.mem_insert_of_mem hi))
      (fun i hi => ha i (Finset.mem_insert_of_mem hi))
    have hu1 := h1 j (Finset.mem_insert_self j s)
    have hua := ha j (Finset.mem_insert_self j s)
    nlinarith [mul_nonneg (sub_nonneg.2 hu1) (sub_nonneg.2 hP1)]
end GeoProdPow
