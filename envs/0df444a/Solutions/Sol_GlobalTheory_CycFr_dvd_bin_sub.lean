-- Prove2me | solution 1 for GlobalTheory.CycFr.dvd_bin_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:13:56.647815+00:00
-- url     : https://prove2.me/submissions/39f25d56-02f9-41bf-8c6a-4e5f621eb76d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_OneAddXMulDerivativeBin
import Theorems.Thm_GlobalTheory_CycFr_act_X
import Theorems.Thm_GlobalTheory_CycFr_bin_nat
import Theorems.Thm_GlobalTheory_CycFr_act_bin

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PowerSeries
open GlobalTheory GlobalTheory.CycFr
variable {l : ℕ} [Fact l.Prime] (O : Type) [CommRing O] [Algebra ℤ_[l] O]
variable {O}
variable [IsDomain O] [CharZero O]
open PowerSeries
variable {l : ℕ} [Fact l.Prime] (O : Type) [CommRing O] [Algebra ℤ_[l] O]
variable {O}
variable [IsDomain O] [CharZero O]
namespace GlobalTheory.CycFr
namespace _root_.GlobalTheory.CycFr
theorem _root_.solution (k : ℕ) (c d : ℤ_[l]) (h : (l : ℤ_[l]) ^ k ∣ c - d) :
    (1 + X : O⟦X⟧) ^ l ^ k - 1 ∣ _root_.GlobalTheory.CycFr.bin O c - _root_.GlobalTheory.CycFr.bin O d := by
  obtain ⟨e, he⟩ := h
  have hc : c = d + (l : ℤ_[l]) ^ k * e := by rw [← he]; ring
  have hb : _root_.GlobalTheory.CycFr.bin O ((l : ℤ_[l]) ^ k) = (1 + X) ^ l ^ k := by
    rw [← Nat.cast_pow, _root_.GlobalTheory.CycFr.bin_nat]
  obtain ⟨v, hv⟩ : (X : O⟦X⟧) ∣ _root_.GlobalTheory.CycFr.bin O e - 1 :=
    X_dvd_iff.mpr (by rw [map_sub, binomialSeries_constantCoeff, map_one, sub_self])
  have h1 : _root_.GlobalTheory.CycFr.bin O ((l : ℤ_[l]) ^ k * e) - 1 =
      ((1 + X) ^ l ^ k - 1) * _root_.GlobalTheory.CycFr.act O ((l : ℤ_[l]) ^ k) v := by
    rw [← _root_.GlobalTheory.CycFr.act_bin, ← hb,
      ← _root_.GlobalTheory.CycFr.act_X, ← map_mul, ← hv, map_sub, map_one]
  have h2 : _root_.GlobalTheory.CycFr.bin O c - _root_.GlobalTheory.CycFr.bin O d =
      _root_.GlobalTheory.CycFr.bin O d *
        (_root_.GlobalTheory.CycFr.bin O ((l : ℤ_[l]) ^ k * e) - 1) := by
    rw [hc]
    simp only [_root_.GlobalTheory.CycFr.bin, binomialSeries_add]
    ring
  rw [h2, h1]
  exact Dvd.dvd.mul_left (dvd_mul_right _ _) _
end _root_.GlobalTheory.CycFr
end GlobalTheory.CycFr
