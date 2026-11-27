-- Prove2me | solution 1 for MohP3.Wt.yOrd_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:20:56.471925+00:00
-- url     : https://prove2.me/submissions/5e559ff2-5403-4a90-9cc8-4828dcbf5008

module
public import Mathlib
public import Definitions.Def_MohP3_Order

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open MvPowerSeries
open MohP3 MohP3.Wt
variable {k : Type*} [CommRing k]
namespace MohP3.Wt
theorem _root_.solution {p q : PowerSeries k} {m n : ℕ} (hp : YOrd p m) (hq : YOrd q n) :
    YOrd (p * q) (m + n) := by
  intro d hd
  rw [PowerSeries.coeff_mul]
  refine Finset.sum_eq_zero ?_
  rintro ⟨d1, d2⟩ hpair
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hpair
  rcases lt_or_ge (8 * d1) m with h1 | h1
  · rw [hp d1 h1, zero_mul]
  · have h2 : 8 * d2 < n := by omega
    rw [hq d2 h2, mul_zero]
end MohP3.Wt
