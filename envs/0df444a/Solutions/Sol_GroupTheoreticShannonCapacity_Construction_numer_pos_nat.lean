-- Prove2me | solution 1 for GroupTheoreticShannonCapacity.Construction.numer_pos_nat
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:47:18.654098+00:00
-- url     : https://prove2.me/submissions/7b150280-f803-4bc8-99b4-49608f3c9455

import Definitions.Def_GroupTheoreticShannonCapacity_P0Matrix
import Definitions.Def_GroupTheoreticShannonCapacity_MAlpha
import Definitions.Def_GroupTheoreticShannonCapacity_Construction

set_option autoImplicit true
open GroupTheoreticShannonCapacity GroupTheoreticShannonCapacity.Construction
open Matrix
namespace GroupTheoreticShannonCapacity.Construction
theorem _root_.solution (n k b r s : ℕ) (hk : 1 ≤ k) (hb : 1 ≤ b) (hs : 1 ≤ s) :
    0 < (s : ℤ) ^ n * (r : ℤ) + (k : ℤ) * (a n (k:ℤ) (b:ℤ) (r:ℤ) (s:ℤ)) ^ n := by
  have hs_pos : 0 < (s : ℤ) := by omega
  have hk_pos : 0 < (k : ℤ) := by omega
  have hb_pos : 0 < (b : ℤ) := by omega
  have h1 : 0 ≤ (s : ℤ) ^ n * (r : ℤ) := by
    apply mul_nonneg
    · exact pow_nonneg (by omega : 0 ≤ (s : ℤ)) n
    · exact Int.natCast_nonneg r
  have ha_pos : 0 < a n (k:ℤ) (b:ℤ) (r:ℤ) (s:ℤ) := by
    simp only [a]
    have hbn_pos : 0 < (b : ℤ) ^ n := pow_pos hb_pos n
    have h_kbn : 0 < (k : ℤ) * (b : ℤ) ^ n := mul_pos hk_pos hbn_pos
    have h_sb : 0 ≤ (s : ℤ) * (b : ℤ) := mul_nonneg (by omega) (by omega)
    have h_r : 0 ≤ (r : ℤ) := Int.natCast_nonneg r
    linarith
  have han_pos : 0 < (a n (k:ℤ) (b:ℤ) (r:ℤ) (s:ℤ)) ^ n := pow_pos ha_pos n
  have h2 : 0 < (k : ℤ) * (a n (k:ℤ) (b:ℤ) (r:ℤ) (s:ℤ)) ^ n := mul_pos hk_pos han_pos
  linarith
end GroupTheoreticShannonCapacity.Construction
