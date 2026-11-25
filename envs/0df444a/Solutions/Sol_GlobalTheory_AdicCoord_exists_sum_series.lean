-- Prove2me | solution 1 for GlobalTheory.AdicCoord.exists_sum_series
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T01:59:48.830599+00:00
-- url     : https://prove2.me/submissions/a073d694-7e75-4920-8e75-d43c7753fd04

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsAdicCoordinatesOfBasisModP

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.AdicCoord
namespace GlobalTheory.AdicCoord
theorem _root_.solution {R : Type} [CommRing R] (x : R)
    [IsPrecomplete (Ideal.span {x}) R] (a : ℕ → R) :
    ∃ L : R, ∀ N : ℕ, x ^ N ∣ (∑ k ∈ Finset.range N, x ^ k * a k) - L := by
  have key : ∀ (N : ℕ) (u v : R), u ≡ v [SMOD ((Ideal.span {x}) ^ N • ⊤ : Submodule R R)] ↔
      x ^ N ∣ u - v := by
    intro N u v
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow,
      Ideal.mem_span_singleton]
  obtain ⟨L, hL⟩ := IsPrecomplete.prec (inferInstance : IsPrecomplete (Ideal.span {x}) R)
    (f := fun N => ∑ k ∈ Finset.range N, x ^ k * a k) (by
      intro m n hmn
      rw [key, ← dvd_neg, neg_sub, ← Finset.sum_Ico_eq_sub _ hmn]
      refine Finset.dvd_sum fun k hk => ?_
      exact Dvd.dvd.mul_right (pow_dvd_pow x (Finset.mem_Ico.1 hk).1) _)
  exact ⟨L, fun N => (key N _ _).1 (hL N)⟩
end GlobalTheory.AdicCoord
