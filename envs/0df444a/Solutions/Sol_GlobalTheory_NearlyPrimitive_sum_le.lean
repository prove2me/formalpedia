-- Prove2me | solution 1 for GlobalTheory.NearlyPrimitive.sum_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T19:03:01.284521+00:00
-- url     : https://prove2.me/submissions/3c2ccae9-0226-4747-8aa7-ebf56e75619d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_NormSmulLeOneOfPrimitiveBoundedPowers

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.NearlyPrimitive
open Finset Filter Topology
namespace GlobalTheory.NearlyPrimitive
theorem _root_.solution {B ι : Type} [AddCommGroup B] (N : B → ℝ) (h0 : N 0 = 0)
    (hadd : ∀ x y, N (x + y) ≤ max (N x) (N y)) {T : ℝ} (hT : 0 ≤ T) (s : Finset ι) (f : ι → B)
    (hf : ∀ i ∈ s, N (f i) ≤ T) : N (∑ i ∈ s, f i) ≤ T := by
  refine Finset.sum_induction f (fun x => N x ≤ T) (fun a b ha hb => ?_) (by rwa [h0]) hf
  exact (hadd a b).trans (max_le ha hb)
end GlobalTheory.NearlyPrimitive
