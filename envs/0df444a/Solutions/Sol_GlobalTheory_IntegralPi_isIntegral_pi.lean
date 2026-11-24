-- Prove2me | solution 1 for GlobalTheory.IntegralPi.isIntegral_pi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T17:52:03.28358+00:00
-- url     : https://prove2.me/submissions/566c3288-bcae-4bb7-851e-e2de85529ead

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsIntegralPi

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.IntegralPi
open Polynomial
namespace GlobalTheory.IntegralPi
theorem _root_.solution {O : Type} [CommRing O] {ι : Type} [Finite ι] {R : ι → Type}
    [∀ i, CommRing (R i)] [∀ i, Algebra O (R i)] (x : ∀ i, R i)
    (hx : ∀ i, IsIntegral O (x i)) : IsIntegral O x := by
  classical
  haveI := Fintype.ofFinite ι
  choose p hpm hp using hx
  refine ⟨∏ i, p i, monic_prod_of_monic _ _ (fun i _ => hpm i), ?_⟩
  rw [← aeval_def]
  funext j
  have key : (aeval x (∏ i, p i)) j = aeval (x j) (∏ i, p i) := by
    have := (aeval_algHom_apply (Pi.evalAlgHom O R j) x (∏ i, p i)).symm
    simpa using this
  rw [key, map_prod, Pi.zero_apply]
  exact Finset.prod_eq_zero (Finset.mem_univ j) (by rw [aeval_def]; exact hp j)
end GlobalTheory.IntegralPi
