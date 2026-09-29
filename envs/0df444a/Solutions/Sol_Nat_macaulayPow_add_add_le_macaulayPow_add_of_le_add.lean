-- Prove2me | solution 1 for Nat.macaulayPow_add_add_le_macaulayPow_add_of_le_add
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/9a680a1f-4e9c-5657-9739-087f965e3028

import Mathlib
import Definitions.Def_Nat_MacaulayPow
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Nat_macaulayPow_add_add_le_macaulayPow_add_of_le_add

set_option autoImplicit false

namespace GreenNum

def top (d a : ℕ) : ℕ := Nat.findGreatest (fun k => k.choose (d + 1) ≤ a) (a + d + 1)

def rem (d a : ℕ) : ℕ := a - (top d a).choose (d + 1)

theorem macaulayPow_zero (a : ℕ) : Nat.macaulayPow 0 a = 0 := by simp [Nat.macaulayPow]

theorem macaulayPow_succ (d a : ℕ) :
    Nat.macaulayPow (d + 1) a = (top d a + 1).choose (d + 2) + Nat.macaulayPow d (rem d a) := by
  rw [Nat.macaulayPow]; rfl

theorem sub_le_choose (d : ℕ) : ∀ k : ℕ, k - d ≤ k.choose (d + 1)
  | 0 => by simp
  | k + 1 => by
      rw [Nat.choose_succ_succ']
      have ih := sub_le_choose d k
      rcases lt_or_ge k d with h | h
      · have : k + 1 - d = 0 := by omega
        omega
      · have hpos : 1 ≤ k.choose d := Nat.choose_pos h
        omega

theorem choose_top_le (d a : ℕ) : (top d a).choose (d + 1) ≤ a :=
  Nat.findGreatest_spec (P := fun k => k.choose (d + 1) ≤ a) (Nat.zero_le _) (by simp)

theorem lt_choose_of_top_lt (d a : ℕ) {k : ℕ} (hk : top d a < k) : a < k.choose (d + 1) := by
  rcases le_or_gt k (a + d + 1) with h | h
  · have := Nat.findGreatest_is_greatest (P := fun k => k.choose (d + 1) ≤ a) hk h
    simpa using this
  · have := sub_le_choose d k
    omega

theorem lt_choose_top_succ (d a : ℕ) : a < (top d a + 1).choose (d + 1) :=
  lt_choose_of_top_lt d a (Nat.lt_succ_self _)

theorem top_eq_of (d a k : ℕ) (h₁ : k.choose (d + 1) ≤ a) (h₂ : a < (k + 1).choose (d + 1)) :
    top d a = k := by
  apply le_antisymm
  · by_contra h
    push Not at h
    have : (k + 1).choose (d + 1) ≤ (top d a).choose (d + 1) := Nat.choose_le_choose _ h
    have := choose_top_le d a
    omega
  · by_contra h
    push Not at h
    have := lt_choose_of_top_lt d a h
    omega

theorem le_top_of_choose_le (d a k : ℕ) (h : k.choose (d + 1) ≤ a) : k ≤ top d a := by
  by_contra h'
  push Not at h'
  have := lt_choose_of_top_lt d a h'
  omega

theorem top_lt_of_lt_choose (d a k : ℕ) (h : a < k.choose (d + 1)) : top d a < k := by
  by_contra h'
  push Not at h'
  have : k.choose (d + 1) ≤ (top d a).choose (d + 1) := Nat.choose_le_choose _ h'
  have := choose_top_le d a
  omega

theorem d_le_top (d a : ℕ) : d ≤ top d a := le_top_of_choose_le d a d (by simp)

theorem top_zero_right (d : ℕ) : top d 0 = d := top_eq_of d 0 d (by simp) (by simp)

theorem d_lt_top_of_pos (d a : ℕ) (ha : 0 < a) : d < top d a := by
  have := le_top_of_choose_le d a (d + 1) (by simp; omega)
  omega

theorem top_zero_left (a : ℕ) : top 0 a = a := top_eq_of 0 a a (by simp) (by simp)

theorem rem_zero_left (a : ℕ) : rem 0 a = 0 := by simp [rem, top_zero_left]

theorem rem_zero_right (d : ℕ) : rem d 0 = 0 := by simp [rem]

theorem rem_add_choose (d a : ℕ) : rem d a + (top d a).choose (d + 1) = a := by
  unfold rem; have := choose_top_le d a; omega

theorem rem_lt (d a : ℕ) : rem d a < (top d a).choose d := by
  have h := lt_choose_top_succ d a
  rw [Nat.choose_succ_succ'] at h
  unfold rem; have := choose_top_le d a; omega

theorem macaulayPow_lt_choose : ∀ (d m r : ℕ), r < m.choose d →
    Nat.macaulayPow d r < (m + 1).choose (d + 1)
  | 0, m, r, _ => by simp [macaulayPow_zero]
  | d + 1, m, r, h => by
      rw [macaulayPow_succ]
      show _ < (m + 1).choose (d + 2)
      have hK : top d r < m := top_lt_of_lt_choose d r m h
      have hrem : Nat.macaulayPow d (rem d r) < (top d r + 1).choose (d + 1) :=
        macaulayPow_lt_choose d (top d r) (rem d r) (rem_lt d r)
      have h1 : (top d r + 1).choose (d + 2) + (top d r + 1).choose (d + 1) =
          (top d r + 2).choose (d + 2) := by
        rw [Nat.choose_succ_succ' (top d r + 1) (d + 1), add_comm]
      have h2 : (top d r + 2).choose (d + 2) ≤ (m + 1).choose (d + 2) :=
        Nat.choose_le_choose _ (by omega)
      omega

theorem macaulayPow_mono : ∀ (d : ℕ) {a b : ℕ}, a ≤ b → Nat.macaulayPow d a ≤ Nat.macaulayPow d b
  | 0, a, b, _ => by simp [macaulayPow_zero]
  | d + 1, a, b, h => by
      have ht : top d a ≤ top d b := le_top_of_choose_le d b _ ((choose_top_le d a).trans h)
      rcases ht.eq_or_lt with ht | ht
      · rw [macaulayPow_succ, macaulayPow_succ, ht]
        have hr : rem d a ≤ rem d b := by
          have ha := rem_add_choose d a; have hb := rem_add_choose d b; rw [ht] at ha; omega
        have := macaulayPow_mono d hr
        omega
      · have h1 : Nat.macaulayPow (d + 1) a < (top d a + 1 + 1).choose (d + 1 + 1) :=
          macaulayPow_lt_choose (d + 1) (top d a + 1) a (lt_choose_top_succ d a)
        have h2 : (top d a + 1 + 1).choose (d + 1 + 1) ≤ (top d b + 1).choose (d + 1 + 1) :=
          Nat.choose_le_choose _ (by omega)
        have h3 : (top d b + 1).choose (d + 1 + 1) ≤ Nat.macaulayPow (d + 1) b := by
          rw [macaulayPow_succ]; exact Nat.le_add_right _ _
        omega

theorem macaulayPow_one (a : ℕ) : Nat.macaulayPow 1 a = (a + 1).choose 2 := by
  rw [macaulayPow_succ, top_zero_left, rem_zero_left, macaulayPow_zero]; rfl

theorem macaulayPow_zero_right : ∀ d : ℕ, Nat.macaulayPow d 0 = 0
  | 0 => macaulayPow_zero 0
  | d + 1 => by
      rw [macaulayPow_succ, top_zero_right, rem_zero_right, macaulayPow_zero_right d,
        Nat.choose_eq_zero_of_lt (by omega)]

theorem top_succ_of_le (d a : ℕ) (ha : 1 ≤ a) (h : a ≤ d + 2) : top (d + 1) a = d + 2 :=
  top_eq_of (d + 1) a (d + 2) (by rw [Nat.choose_self]; exact ha)
    (by have : (d + 2 + 1).choose (d + 1 + 1) = d + 2 + 1 := Nat.choose_succ_self_right (d + 2); omega)

theorem macaulayPow_eq_self : ∀ (d a : ℕ), a ≤ d + 1 → Nat.macaulayPow (d + 1) a = a
  | d, 0, _ => macaulayPow_zero_right (d + 1)
  | 0, a + 1, h => by
      obtain rfl : a = 0 := by omega
      rw [macaulayPow_one]; rfl
  | d + 1, a + 1, h => by
      have ht : top (d + 1) (a + 1) = d + 2 := top_succ_of_le d (a + 1) (by omega) (by omega)
      have hr : rem (d + 1) (a + 1) = a := by simp [rem, ht]
      rw [macaulayPow_succ, ht, hr, macaulayPow_eq_self d a (by omega)]
      have : (d + 2 + 1).choose (d + 1 + 2) = 1 := by
        rw [show d + 1 + 2 = d + 2 + 1 by omega, Nat.choose_self]
      omega

def low : ℕ → ℕ → ℕ
  | 0, _ => 0
  | d + 1, a => (top d a - 1).choose (d + 1) + low d (rem d a)

theorem low_zero (a : ℕ) : low 0 a = 0 := rfl

theorem low_succ (d a : ℕ) : low (d + 1) a = (top d a - 1).choose (d + 1) + low d (rem d a) := rfl

theorem low_zero_right : ∀ d : ℕ, low d 0 = 0
  | 0 => rfl
  | d + 1 => by
      rw [low_succ, top_zero_right, rem_zero_right, low_zero_right d, Nat.choose_eq_zero_of_lt (by omega)]

theorem low_eq_zero : ∀ (d a : ℕ), a ≤ d + 1 → low (d + 1) a = 0
  | d, 0, _ => low_zero_right _
  | 0, a + 1, h => by
      obtain rfl : a = 0 := by omega
      rw [low_succ, top_zero_left, low_zero]; rfl
  | d + 1, a + 1, h => by
      have ht : top (d + 1) (a + 1) = d + 2 := top_succ_of_le d (a + 1) (by omega) (by omega)
      have hr : rem (d + 1) (a + 1) = a := by simp [rem, ht]
      rw [low_succ, ht, hr, low_eq_zero d a (by omega), Nat.choose_eq_zero_of_lt (by omega)]

theorem low_lt_choose : ∀ (d m r : ℕ), r < (m + 1).choose (d + 1) → d + 1 ≤ m →
    low (d + 1) r < m.choose (d + 1)
  | 0, m, r, h, hm => by
      rw [low_succ, top_zero_left, low_zero]
      simp only [zero_add, Nat.choose_one_right, add_zero] at h ⊢
      omega
  | d + 1, m, r, h, hm => by
      rw [low_succ]
      show (top (d + 1) r - 1).choose (d + 2) + low (d + 1) (rem (d + 1) r) < m.choose (d + 2)
      have hT : top (d + 1) r ≤ m := Nat.lt_succ_iff.1 (top_lt_of_lt_choose (d + 1) r (m + 1) h)
      rcases Nat.eq_zero_or_pos r with hr | hr
      · subst hr
        rw [top_zero_right, rem_zero_right, low_zero_right, Nat.choose_eq_zero_of_lt (by omega),
          zero_add]
        exact Nat.choose_pos (by omega)
      · have hT' : d + 1 < top (d + 1) r := d_lt_top_of_pos _ _ hr
        have hRlt : rem (d + 1) r < (top (d + 1) r - 1 + 1).choose (d + 1) := by
          rw [Nat.sub_add_cancel (by omega)]; exact rem_lt (d + 1) r
        have ih := low_lt_choose d (top (d + 1) r - 1) (rem (d + 1) r) hRlt (by omega)
        have h1 : (top (d + 1) r - 1).choose (d + 2) + (top (d + 1) r - 1).choose (d + 1) =
            (top (d + 1) r).choose (d + 2) := by
          have := Nat.choose_succ_succ' (top (d + 1) r - 1) (d + 1)
          rw [Nat.sub_add_cancel (show 1 ≤ top (d + 1) r by omega)] at this
          rw [add_comm]; exact this.symm
        have h2 : (top (d + 1) r).choose (d + 2) ≤ m.choose (d + 2) := Nat.choose_le_choose _ hT
        omega

theorem macaulayPow_low_add : ∀ (d a : ℕ),
    Nat.macaulayPow (d + 1) (low (d + 1) a) + a = Nat.macaulayPow (d + 1) a
  | 0, a => by
      rw [low_succ, top_zero_left, low_zero, add_zero, macaulayPow_one, macaulayPow_one,
        Nat.choose_one_right]
      rcases Nat.eq_zero_or_pos a with rfl | ha
      · rfl
      · have h2 : (a + 1).choose 2 = a + a.choose 2 := by
          have := Nat.choose_succ_succ' a 1; rw [Nat.choose_one_right] at this; exact this
        rw [Nat.sub_add_cancel ha]; omega
  | d + 1, a => by
      rcases Nat.eq_zero_or_pos a with rfl | ha
      · rw [low_zero_right, add_zero]
      · set T := top (d + 1) a with hT
        set R := rem (d + 1) a with hR
        have hTd : d + 1 < T := d_lt_top_of_pos _ _ ha
        have hRa : R + T.choose (d + 2) = a := rem_add_choose (d + 1) a
        have hRlt : R < T.choose (d + 1) := rem_lt (d + 1) a
        have ih := macaulayPow_low_add d R
        rw [low_succ, macaulayPow_succ (d + 1) a]
        show Nat.macaulayPow (d + 2) ((T - 1).choose (d + 2) + low (d + 1) R) + a =
          (T + 1).choose (d + 3) + Nat.macaulayPow (d + 1) R
        rcases (show T = d + 2 ∨ d + 3 ≤ T by omega) with hT2 | hT3
        ·
          have hC : (d + 2).choose (d + 1) = d + 2 := Nat.choose_succ_self_right (d + 1)
          have hR1 : R ≤ d + 1 := by rw [hT2] at hRlt; omega
          rw [hT2, show d + 2 - 1 = d + 1 from rfl, Nat.choose_succ_self, zero_add, low_eq_zero d R hR1,
            macaulayPow_zero_right, macaulayPow_eq_self d R hR1, Nat.choose_self]
          rw [hT2, Nat.choose_self] at hRa
          omega
        ·
          have hlow : low (d + 1) R < (T - 1).choose (d + 1) :=
            low_lt_choose d (T - 1) R (by rw [Nat.sub_add_cancel (by omega)]; exact hRlt) (by omega)
          have hpasc : (T - 1).choose (d + 2) + (T - 1).choose (d + 1) = T.choose (d + 2) := by
            have := Nat.choose_succ_succ' (T - 1) (d + 1)
            rw [Nat.sub_add_cancel (show 1 ≤ T by omega)] at this
            rw [add_comm]; exact this.symm
          have hpasc' : T.choose (d + 3) + T.choose (d + 2) = (T + 1).choose (d + 3) := by
            rw [Nat.choose_succ_succ' T (d + 2), add_comm]
          have htop : top (d + 1) ((T - 1).choose (d + 2) + low (d + 1) R) = T - 1 :=
            top_eq_of (d + 1) _ (T - 1) (Nat.le_add_right _ _)
              (by rw [Nat.sub_add_cancel (show 1 ≤ T by omega)]; show _ < T.choose (d + 2); omega)
          have hrem : rem (d + 1) ((T - 1).choose (d + 2) + low (d + 1) R) = low (d + 1) R := by
            simp [rem, htop]
          rw [macaulayPow_succ, htop, hrem, Nat.sub_add_cancel (show 1 ≤ T by omega)]
          show T.choose (d + 3) + Nat.macaulayPow (d + 1) (low (d + 1) R) + a = _
          omega

theorem le_choose_add_low : ∀ (d m r : ℕ), r < (m + 1).choose (d + 1) → r ≤ m.choose d + low (d + 1) r
  | 0, m, r, _ => by
      rw [low_succ, top_zero_left, low_zero, Nat.choose_zero_right, Nat.choose_one_right]; omega
  | d + 1, m, r, h => by
      rw [low_succ]
      show r ≤ m.choose (d + 1) + ((top (d + 1) r - 1).choose (d + 2) + low (d + 1) (rem (d + 1) r))
      have hT : top (d + 1) r ≤ m := Nat.lt_succ_iff.1 (top_lt_of_lt_choose (d + 1) r (m + 1) h)
      have hT1 : 1 ≤ top (d + 1) r := by have := d_le_top (d + 1) r; omega
      have hRa : rem (d + 1) r + (top (d + 1) r).choose (d + 2) = r := rem_add_choose (d + 1) r
      have hRlt : rem (d + 1) r < (top (d + 1) r - 1 + 1).choose (d + 1) := by
        rw [Nat.sub_add_cancel hT1]; exact rem_lt (d + 1) r
      have ih := le_choose_add_low d (top (d + 1) r - 1) (rem (d + 1) r) hRlt
      have h1 : (top (d + 1) r - 1).choose (d + 2) + (top (d + 1) r - 1).choose (d + 1) =
          (top (d + 1) r).choose (d + 2) := by
        have := Nat.choose_succ_succ' (top (d + 1) r - 1) (d + 1)
        rw [Nat.sub_add_cancel hT1] at this
        rw [add_comm]; exact this.symm
      have h2 : (top (d + 1) r - 1).choose (d + 1) + (top (d + 1) r - 1).choose d =
          (top (d + 1) r).choose (d + 1) := by
        have := Nat.choose_succ_succ' (top (d + 1) r - 1) d
        rw [Nat.sub_add_cancel hT1] at this
        rw [add_comm]; exact this.symm
      have h3 : (top (d + 1) r).choose (d + 1) ≤ m.choose (d + 1) := Nat.choose_le_choose _ hT
      omega

theorem le_add_low : ∀ (d a s : ℕ), a ≤ Nat.macaulayPow d s → a ≤ s + low (d + 1) a
  | 0, a, s, h => by rw [macaulayPow_zero] at h; omega
  | d + 1, a, s, h => by
      rcases Nat.eq_zero_or_pos a with rfl | ha
      · exact Nat.zero_le _
      set T := top (d + 1) a with hT
      set R := rem (d + 1) a with hR
      have hTd : d + 1 < T := d_lt_top_of_pos _ _ ha
      have hRa : R + T.choose (d + 2) = a := rem_add_choose (d + 1) a
      have hRlt : R < T.choose (d + 1) := rem_lt (d + 1) a
      set T' := top d s with hT'
      have hs : rem d s + T'.choose (d + 1) = s := rem_add_choose d s

      have hlt : Nat.macaulayPow (d + 1) s < (T' + 1 + 1).choose (d + 1 + 1) :=
        macaulayPow_lt_choose (d + 1) (T' + 1) s (lt_choose_top_succ d s)
      have hTT' : T ≤ T' + 1 := by
        have := top_lt_of_lt_choose (d + 1) a (T' + 1 + 1) (h.trans_lt hlt); omega
      rw [low_succ]
      show a ≤ s + ((T - 1).choose (d + 2) + low (d + 1) R)
      have hpasc : (T - 1).choose (d + 2) + (T - 1).choose (d + 1) = T.choose (d + 2) := by
        have := Nat.choose_succ_succ' (T - 1) (d + 1)
        rw [Nat.sub_add_cancel (show 1 ≤ T by omega)] at this
        rw [add_comm]; exact this.symm
      rcases (show T ≤ T' ∨ T = T' + 1 by omega) with hle | heq
      ·
        have h1 : T.choose (d + 1) ≤ T'.choose (d + 1) := Nat.choose_le_choose _ hle
        have h2 : R ≤ (T - 1).choose d + low (d + 1) R :=
          le_choose_add_low d (T - 1) R (by rw [Nat.sub_add_cancel (by omega)]; exact hRlt)
        have h3 : (T - 1).choose (d + 1) + (T - 1).choose d = T.choose (d + 1) := by
          have := Nat.choose_succ_succ' (T - 1) d
          rw [Nat.sub_add_cancel (show 1 ≤ T by omega)] at this
          rw [add_comm]; exact this.symm
        omega
      ·
        have hμ : Nat.macaulayPow (d + 1) s = (T' + 1).choose (d + 2) + Nat.macaulayPow d (rem d s) :=
          macaulayPow_succ d s
        rw [← heq] at hμ
        rw [show T' = T - 1 by omega] at hs
        have hR' : R ≤ Nat.macaulayPow d (rem d s) := by omega
        have ih := le_add_low d R (rem d s) hR'
        omega

theorem low_le : ∀ (d a : ℕ), low d a ≤ a
  | 0, _ => Nat.zero_le _
  | d + 1, a => by
      rw [low_succ]
      have h1 : (top d a - 1).choose (d + 1) ≤ (top d a).choose (d + 1) :=
        Nat.choose_le_choose _ (Nat.sub_le _ _)
      have h2 := low_le d (rem d a)
      have h3 := rem_add_choose d a
      omega

theorem macaulayPow_lt_succ : ∀ (d a : ℕ), Nat.macaulayPow (d + 1) a < Nat.macaulayPow (d + 1) (a + 1)
  | 0, a => by
      rw [macaulayPow_one, macaulayPow_one]
      have h2 : (a + 1 + 1).choose 2 = (a + 1) + (a + 1).choose 2 := by
        have h := Nat.choose_succ_succ' (a + 1) 1
        rw [Nat.choose_one_right] at h
        exact h
      omega
  | d + 1, a => by
      have hT : top (d + 1) a ≤ top (d + 1) (a + 1) :=
        le_top_of_choose_le _ _ _ ((choose_top_le (d + 1) a).trans (Nat.le_succ a))
      rcases hT.eq_or_lt with hT | hT
      · rw [macaulayPow_succ (d + 1) a, macaulayPow_succ (d + 1) (a + 1), hT]
        have hr : rem (d + 1) (a + 1) = rem (d + 1) a + 1 := by
          have h1 := rem_add_choose (d + 1) a
          have h2 := rem_add_choose (d + 1) (a + 1)
          rw [hT] at h1
          omega
        rw [hr]
        have := macaulayPow_lt_succ d (rem (d + 1) a)
        omega
      · have h1 : Nat.macaulayPow (d + 1 + 1) a < (top (d + 1) a + 1 + 1).choose (d + 1 + 1 + 1) :=
          macaulayPow_lt_choose (d + 1 + 1) (top (d + 1) a + 1) a (lt_choose_top_succ (d + 1) a)
        have h2 : (top (d + 1) a + 1 + 1).choose (d + 1 + 1 + 1) ≤
            (top (d + 1) (a + 1) + 1).choose (d + 1 + 1 + 1) := Nat.choose_le_choose _ (by omega)
        have h3 : (top (d + 1) (a + 1) + 1).choose (d + 1 + 1 + 1) ≤ Nat.macaulayPow (d + 1 + 1) (a + 1) := by
          rw [macaulayPow_succ]; exact Nat.le_add_right _ _
        omega

theorem macaulayPow_strictMono (d : ℕ) : StrictMono (Nat.macaulayPow (d + 1)) :=
  strictMono_nat_of_lt_succ fun a => macaulayPow_lt_succ d a

theorem le_of_macaulayPow_le (d : ℕ) {a b : ℕ} (h : Nat.macaulayPow (d + 1) a ≤ Nat.macaulayPow (d + 1) b) :
    a ≤ b :=
  (macaulayPow_strictMono d).le_iff_le.mp h

theorem le_macaulayPow_sub_low : ∀ (d a : ℕ), a ≤ Nat.macaulayPow (d + 1) (a - low (d + 2) a)
  | d, a => by
      set T := top (d + 1) a with hT
      set R := rem (d + 1) a with hR
      have hTd : d + 1 ≤ T := d_le_top (d + 1) a
      have hRa : R + T.choose (d + 2) = a := rem_add_choose (d + 1) a
      have hRlt : R < T.choose (d + 1) := rem_lt (d + 1) a
      have hlowR : low (d + 1) R ≤ R := low_le (d + 1) R
      have hpasc : (T - 1).choose (d + 2) + (T - 1).choose (d + 1) = T.choose (d + 2) := by
        have := Nat.choose_succ_succ' (T - 1) (d + 1)
        rw [Nat.sub_add_cancel (show 1 ≤ T by omega)] at this
        rw [add_comm]; exact this.symm
      have hpasc' : (T - 1).choose (d + 1) + (T - 1).choose d = T.choose (d + 1) := by
        have := Nat.choose_succ_succ' (T - 1) d
        rw [Nat.sub_add_cancel (show 1 ≤ T by omega)] at this
        rw [add_comm]; exact this.symm
      have hle1 : (T - 1).choose (d + 2) ≤ T.choose (d + 2) := Nat.choose_le_choose _ (Nat.sub_le _ _)
      have hτ : a - low (d + 2) a = (T - 1).choose (d + 1) + (R - low (d + 1) R) := by
        rw [low_succ (d + 1) a]
        show a - ((T - 1).choose (d + 1 + 1) + low (d + 1) R) = _
        show a - ((T - 1).choose (d + 2) + low (d + 1) R) = _
        omega
      rw [hτ]
      set z := (T - 1).choose (d + 1) + (R - low (d + 1) R) with hz
      rcases lt_or_ge (R - low (d + 1) R) ((T - 1).choose d) with hsmall | hbig
      ·
        have hz1 : (T - 1).choose (d + 1) ≤ z := Nat.le_add_right _ _
        have hz2 : z < (T - 1 + 1).choose (d + 1) := by
          rw [Nat.sub_add_cancel (show 1 ≤ T by omega)]; omega
        have htop : top d z = T - 1 := top_eq_of d z (T - 1) hz1 hz2
        have hrem : rem d z = R - low (d + 1) R := by
          have := rem_add_choose d z; rw [htop] at this; omega
        rw [macaulayPow_succ, htop, hrem, Nat.sub_add_cancel (show 1 ≤ T by omega)]

        have hkey : R ≤ Nat.macaulayPow d (R - low (d + 1) R) := by
          cases d with
          | zero =>
              have hl : low 1 R = R - 1 := by
                rw [low_succ, top_zero_left, low_zero, Nat.choose_one_right, Nat.add_zero]
              have h0 : (T - 1).choose 0 = 1 := Nat.choose_zero_right _
              rw [h0, hl] at hsmall
              have : R = 0 := by omega
              rw [this]; exact Nat.zero_le _
          | succ d => exact le_macaulayPow_sub_low d R
        omega
      ·
        have hz1 : T.choose (d + 1) ≤ z := by omega
        have h1 : T ≤ top d z := le_top_of_choose_le d z T hz1
        have h2 : (T + 1).choose (d + 2) ≤ (top d z + 1).choose (d + 2) := Nat.choose_le_choose _ (by omega)
        have h3 : (top d z + 1).choose (d + 2) ≤ Nat.macaulayPow (d + 1) z := by
          rw [macaulayPow_succ]; exact Nat.le_add_right _ _
        have h4 : a < (T + 1).choose (d + 2) := lt_choose_top_succ (d + 1) a
        omega

end GreenNum

open GreenNum in

theorem solution (d x y u v : ℕ) (hd : 1 ≤ d) (hx : x ≤ u + v)
    (hu : Nat.macaulayPow d u + y ≤ Nat.macaulayPow d y)
    (hv : Nat.macaulayPow (d + 1) v + x ≤ Nat.macaulayPow (d + 1) x) :
    Nat.macaulayPow (d + 1) x + (x + y) ≤ Nat.macaulayPow (d + 1) (x + y) := by
  obtain ⟨e, rfl⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩

  have h1 : v ≤ low (e + 1 + 1) x := by
    have hg := macaulayPow_low_add (e + 1) x
    exact le_of_macaulayPow_le (e + 1) (by omega)
  have h2 : u ≤ low (e + 1) y := by
    have hg := macaulayPow_low_add e y
    exact le_of_macaulayPow_le e (by omega)

  have h3 : x - low (e + 1 + 1) x ≤ low (e + 1) y := by omega
  have h4 : x ≤ Nat.macaulayPow (e + 1) (low (e + 1) y) :=
    (le_macaulayPow_sub_low e x).trans (macaulayPow_mono _ h3)
  have h5 : x + y ≤ Nat.macaulayPow (e + 1) y := by
    have := macaulayPow_low_add e y; omega

  have h6 : x ≤ low (e + 1 + 1) (x + y) := by
    have := le_add_low (e + 1) (x + y) y h5; omega
  have h7 := macaulayPow_mono (e + 1 + 1) h6
  have h8 := macaulayPow_low_add (e + 1) (x + y)
  omega

end S_Nat_macaulayPow_add_add_le_macaulayPow_add_of_le_add
end P2MW
export P2MW.S_Nat_macaulayPow_add_add_le_macaulayPow_add_of_le_add (solution)
