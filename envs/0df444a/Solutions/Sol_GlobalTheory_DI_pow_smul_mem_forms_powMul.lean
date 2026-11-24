-- Prove2me | solution 1 for GlobalTheory.DI.pow_smul_mem_forms_powMul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T14:12:37.913791+00:00
-- url     : https://prove2.me/submissions/9895d7fe-4363-4aa9-a998-b88f248c58cb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFlatLift
import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_NadelVanishingPairs_NadelVanishingLemmas_AlternatingProductIntegral
import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_NadelVanishingPairs_NadelVanishingLemmas_SplittingIntegralFormsBound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.DI
open GlobalTheory GlobalTheory.DI
namespace GlobalTheory.DI
theorem _root_.solution {K : Type} [CommRing K] {V : Type} [AddCommGroup V] [Module K V]
    (p : ℕ) (A B : Set K) (L : Set V) (q : ℕ) (b : K) (hb : b ∈ B) (y : ExteriorAlgebra K V)
    (hy : y ∈ forms A L q) : b ^ p • y ∈ forms {z | ∃ c ∈ B, ∃ a ∈ A, z = c ^ p * a} L q := by
  unfold forms at hy ⊢
  induction hy using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨a', ha', v, hv, rfl⟩ := hx
    apply AddSubgroup.subset_closure
    exact ⟨b ^ p * a', ⟨b, hb, a', ha', rfl⟩, v, hv, by rw [smul_smul]⟩
  | zero => rw [smul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | neg x _ hx => rw [smul_neg]; exact neg_mem hx
end GlobalTheory.DI
