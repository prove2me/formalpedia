-- Prove2me | solution 1 for GlobalTheory.UltrametricSum.ultra_sum_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:43:34.786454+00:00
-- url     : https://prove2.me/submissions/ac44cd9b-33c8-41b6-8bec-79704247990a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UltraSumLe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.UltrametricSum
namespace GlobalTheory.UltrametricSum
theorem _root_.solution {R : Type} [inst : CommRing R] (a : R → ℝ) (h0 : a (0 : R) = (0 : ℝ))
    (hadd : ∀ (x y : R), a (x + y) ≤ Max.max (a x) (a y)) {ι : Type} (s : Finset ι) (f : ι → R)
    (c : ℝ) (hc : (0 : ℝ) ≤ c) (h : ∀ i ∈ s, a (f i) ≤ c) : a (∑ i ∈ s, f i) ≤ c := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, h0]; exact hc
  | insert j s hj ih =>
    rw [Finset.sum_insert hj]
    exact (hadd _ _).trans (max_le (h j (Finset.mem_insert_self _ _))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi)))
end GlobalTheory.UltrametricSum
