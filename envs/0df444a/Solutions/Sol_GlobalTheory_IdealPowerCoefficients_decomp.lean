-- Prove2me | solution 1 for GlobalTheory.IdealPowerCoefficients.decomp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T17:53:53.240513+00:00
-- url     : https://prove2.me/submissions/95ba955b-7dd1-47e6-ab8c-92a956be9f97

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_MemPowIffCoeffMem
import Theorems.Thm_GlobalTheory_IdealPowerCoefficients_pick_eq
import Theorems.Thm_GlobalTheory_IdealPowerCoefficients_pick_mem
import Theorems.Thm_GlobalTheory_IdealPowerCoefficients_coeff_cof

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u_1 u_2
open GlobalTheory GlobalTheory.IdealPowerCoefficients
open MvPowerSeries Finsupp
variable {R : Type u_1} [CommRing R] {κ : Type u_2}
namespace GlobalTheory.IdealPowerCoefficients
theorem _root_.solution [Fintype κ] [DecidableEq κ] (f : MvPowerSeries κ R) :
    f = C (coeff 0 f) + ∑ k, X k * cof f k := by
  classical
  ext d
  rw [map_add, map_sum, coeff_C]
  simp_rw [X, coeff_monomial_mul, one_mul, coeff_cof]
  by_cases hd : d = 0
  · subst hd
    simp [Finsupp.single_le_iff]
  · rw [if_neg hd, zero_add]
    obtain ⟨k0, -⟩ := Finsupp.support_nonempty_iff.2 hd
    have hterm : ∀ k, (if single k 1 ≤ d then
        (if pick (d - single k 1 + single k 1) k = k then coeff (d - single k 1 + single k 1) f
          else 0) else 0) = if pick d k0 = k then coeff d f else 0 := by
      intro k
      by_cases hk : single k 1 ≤ d
      · rw [if_pos hk, tsub_add_cancel_of_le hk, pick_eq d hd k k0]
      · rw [if_neg hk, if_neg]
        rintro rfl
        apply hk
        rw [Finsupp.single_le_iff]
        have := pick_mem d hd k0
        rw [Finsupp.mem_support_iff] at this
        omega
    rw [Finset.sum_congr rfl (fun k _ => hterm k), Finset.sum_ite_eq]
    simp
end GlobalTheory.IdealPowerCoefficients
