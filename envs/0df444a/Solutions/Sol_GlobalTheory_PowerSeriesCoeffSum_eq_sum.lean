-- Prove2me | solution 1 for GlobalTheory.PowerSeriesCoeffSum.eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:45:06.107812+00:00
-- url     : https://prove2.me/submissions/2f7037ea-d9cf-4a07-809d-d4dabf6f7bf0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_CoeffXMulPart
import Theorems.Thm_GlobalTheory_PowerSeriesCoeffSum_coeff_X_mul_part

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.PowerSeriesCoeffSum
open MvPowerSeries Finsupp
variable {O : Type} [CommRing O] {a : ℕ}
namespace GlobalTheory.PowerSeriesCoeffSum
theorem _root_.solution (f : MvPowerSeries (Fin a) O) (h0 : coeff 0 f = 0) :
    f = ∑ i, X i * part f i := by
  ext m
  rw [map_sum]
  simp only [coeff_X_mul_part]
  by_cases hm : m = 0
  · subst hm; simp [h0]
  · have hne : m.support.Nonempty := Finsupp.support_nonempty_iff.mpr hm
    set i0 := m.support.min' hne with hi0
    have hi0mem : i0 ∈ m.support := Finset.min'_mem _ _
    have key : ∀ i, (1 ≤ m i ∧ ∀ j < i, m j = 0) ↔ i = i0 := by
      intro i
      constructor
      · rintro ⟨h1, h2⟩
        apply le_antisymm
        · by_contra hlt
          push_neg at hlt
          exact (Finsupp.mem_support_iff.mp hi0mem) (h2 _ hlt)
        · exact Finset.min'_le _ _ (Finsupp.mem_support_iff.mpr (by omega))
      · rintro rfl
        refine ⟨Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hi0mem), fun j hj => ?_⟩
        by_contra hj0
        exact absurd (Finset.min'_le _ _ (Finsupp.mem_support_iff.mpr hj0)) (not_le.mpr hj)
    simp only [key]
    simp
end GlobalTheory.PowerSeriesCoeffSum
