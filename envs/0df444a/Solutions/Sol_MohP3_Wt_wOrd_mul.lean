-- Prove2me | solution 1 for MohP3.Wt.wOrd_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:20:39.204085+00:00
-- url     : https://prove2.me/submissions/467170ed-ddbc-4535-9e70-3913479a2112

module
public import Mathlib
public import Definitions.Def_MohP3_Order
public import Theorems.Thm_MohP3_Wt_wt_add

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open MvPowerSeries
open MohP3 MohP3.Wt
variable {k : Type*} [CommRing k]
namespace MohP3.Wt
theorem _root_.solution {F G : MvPowerSeries (Fin 3) k} {m n : ℕ} (hF : WOrd F m) (hG : WOrd G n) :
    WOrd (F * G) (m + n) := by
  classical
  intro d hd
  rw [MvPowerSeries.coeff_mul]
  refine Finset.sum_eq_zero ?_
  rintro ⟨d1, d2⟩ hp
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
  have hw : wt d1 + wt d2 = wt d := by rw [← wt_add, hp]
  rcases lt_or_ge (wt d1) m with h1 | h1
  · rw [hF d1 h1, zero_mul]
  · have h2 : wt d2 < n := by omega
    rw [hG d2 h2, mul_zero]
end MohP3.Wt
