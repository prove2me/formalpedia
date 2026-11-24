-- Prove2me | solution 1 for GlobalTheory.LatticeIndicator.exists_eq_sum_ite_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T18:38:55.582638+00:00
-- url     : https://prove2.me/submissions/e3dbe01d-4ab8-476f-9842-4c327b693d01

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsEqSumIndicatorOfRightInvariant

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open GlobalTheory
open GlobalTheory.LatticeIndicator
open Classical
namespace GlobalTheory.LatticeIndicator
theorem _root_.solution {P R : Type*} [PartialOrder P] [Fintype P] [CommRing R]
    (f : P → R) : ∃ c : P → R, ∀ p, f p = ∑ q, c q * (if p ≤ q then 1 else 0) := by
  let v : P → P → R := fun q p => if p ≤ q then 1 else 0
  have hsingle : ∀ q : P, (Pi.single q 1 : P → R) ∈ Submodule.span R (Set.range v) := by
    intro q
    induction q using WellFoundedLT.induction with
    | ind q ih =>
      have : (Pi.single q 1 : P → R) =
          v q - ∑ r ∈ Finset.univ.filter (· < q), (Pi.single r 1 : P → R) := by
        ext p
        simp only [v, Pi.sub_apply, Finset.sum_apply, Pi.single_apply, Finset.sum_ite_eq,
          Finset.mem_filter, Finset.mem_univ, true_and]
        by_cases h : p = q
        · simp [h]
        · simp [h, lt_iff_le_and_ne]
      rw [this]
      exact Submodule.sub_mem _ (Submodule.subset_span ⟨q, rfl⟩)
        (Submodule.sum_mem _ fun r hr => ih r (Finset.mem_filter.1 hr).2)
  have hf : f ∈ Submodule.span R (Set.range v) := by
    rw [pi_eq_sum_univ' f]
    exact Submodule.sum_mem _ fun q _ => Submodule.smul_mem _ _ (hsingle q)
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun R).1 hf
  exact ⟨c, fun p => by rw [← hc]; simp [v, Finset.sum_apply]⟩
end GlobalTheory.LatticeIndicator
