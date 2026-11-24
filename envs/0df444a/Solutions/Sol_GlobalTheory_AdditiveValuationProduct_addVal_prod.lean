-- Prove2me | solution 1 for GlobalTheory.AdditiveValuationProduct.addVal_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:55:27.846855+00:00
-- url     : https://prove2.me/submissions/3adee083-650c-4395-abe1-43cbdd96d305

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_Imports

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u_1 u_2
open GlobalTheory GlobalTheory.AdditiveValuationProduct
namespace GlobalTheory.AdditiveValuationProduct
theorem _root_.solution : ∀ {R : Type u_1} [inst : CommRing R] [inst_1 : IsDomain R] [inst_2 : IsDiscreteValuationRing R] {ι : Type u_2} (s : Finset ι) (a : ι → R), (IsDiscreteValuationRing.addVal R : R → ℕ∞) (∏ i ∈ s, a i) = ∑ i ∈ s, (IsDiscreteValuationRing.addVal R : R → ℕ∞) (a i) := by
  intro R _ _ _ ι s a
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j t hj ih =>
    rw [Finset.prod_insert hj, Finset.sum_insert hj, AddValuation.map_mul, ih]
end GlobalTheory.AdditiveValuationProduct
