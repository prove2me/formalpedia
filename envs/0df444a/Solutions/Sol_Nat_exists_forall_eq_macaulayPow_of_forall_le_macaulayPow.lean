-- Prove2me | solution 1 for Nat.exists_forall_eq_macaulayPow_of_forall_le_macaulayPow
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/94aaf151-12dd-5686-b52d-970ec952c1c3

import Mathlib
import Definitions.Def_Nat_MacaulayPow
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Nat_exists_forall_eq_macaulayPow_of_forall_le_macaulayPow

set_option autoImplicit false

namespace GotzNum

def top (d a : ℕ) : ℕ := Nat.findGreatest (fun k => k.choose (d + 1) ≤ a) (a + d + 1)

def rem (d a : ℕ) : ℕ := a - (top d a).choose (d + 1)

theorem macaulayPow_zero (a : ℕ) : Nat.macaulayPow 0 a = 0 := by
  simp [Nat.macaulayPow]

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

theorem top_le (d a : ℕ) : top d a ≤ a + d + 1 := Nat.findGreatest_le _

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

theorem d_le_top (d a : ℕ) : d ≤ top d a :=
  le_top_of_choose_le d a d (by simp)

theorem top_zero_right (d : ℕ) : top d 0 = d :=
  top_eq_of d 0 d (by simp) (by simp)

theorem d_lt_top_of_pos (d a : ℕ) (ha : 0 < a) : d < top d a := by
  have := le_top_of_choose_le d a (d + 1) (by simp; omega)
  omega

theorem top_zero_left (a : ℕ) : top 0 a = a :=
  top_eq_of 0 a a (by simp) (by simp)

theorem rem_zero_left (a : ℕ) : rem 0 a = 0 := by
  simp [rem, top_zero_left]

theorem rem_add_choose (d a : ℕ) : rem d a + (top d a).choose (d + 1) = a := by
  unfold rem; have := choose_top_le d a; omega

theorem rem_lt (d a : ℕ) : rem d a < (top d a).choose d := by
  have h := lt_choose_top_succ d a
  rw [Nat.choose_succ_succ'] at h
  unfold rem; have := choose_top_le d a; omega

theorem top_mono (d : ℕ) {a b : ℕ} (h : a ≤ b) : top d a ≤ top d b :=
  le_top_of_choose_le d b _ ((choose_top_le d a).trans h)

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

theorem top_macaulayPow (d a : ℕ) :
    top (d + 1) (Nat.macaulayPow (d + 1) a) = top d a + 1 := by
  apply top_eq_of
  · rw [macaulayPow_succ]; exact Nat.le_add_right _ _
  · rw [macaulayPow_succ]
    show _ < (top d a + 1 + 1).choose (d + 1 + 1)
    rw [Nat.choose_succ_succ' (top d a + 1) (d + 1)]
    show (top d a + 1).choose (d + 2) + Nat.macaulayPow d (rem d a) <
      (top d a + 1).choose (d + 1) + (top d a + 1).choose (d + 2)
    have := macaulayPow_lt_choose d (top d a) (rem d a) (rem_lt d a)
    omega

theorem rem_macaulayPow (d a : ℕ) :
    rem (d + 1) (Nat.macaulayPow (d + 1) a) = Nat.macaulayPow d (rem d a) := by
  show Nat.macaulayPow (d + 1) a - (top (d + 1) (Nat.macaulayPow (d + 1) a)).choose (d + 1 + 1) = _
  rw [top_macaulayPow, macaulayPow_succ]
  simp

def vec : ℕ → ℕ → ℕ → ℕ
  | 0, _, _ => 0
  | d + 1, a, 0 => top d a - d
  | d + 1, a, p + 1 => vec d (rem d a) p

@[scoped simp] theorem vec_zero (a p : ℕ) : vec 0 a p = 0 := rfl
@[scoped simp] theorem vec_succ_zero (d a : ℕ) : vec (d + 1) a 0 = top d a - d := rfl
@[scoped simp] theorem vec_succ_succ (d a p : ℕ) : vec (d + 1) a (p + 1) = vec d (rem d a) p := rfl

theorem vec_macaulayPow : ∀ (d a : ℕ), vec (d + 1) (Nat.macaulayPow d a) = vec d a
  | 0, a => by
      funext p
      cases p with
      | zero => simp [macaulayPow_zero, top_zero_right]
      | succ p => simp
  | d + 1, a => by
      funext p
      cases p with
      | zero =>
          simp only [vec_succ_zero, top_macaulayPow]
          omega
      | succ p =>
          simp only [vec_succ_succ, rem_macaulayPow]
          rw [vec_macaulayPow d (rem d a)]

theorem vec_eq_zero_of_le : ∀ (d a p : ℕ), d ≤ p → vec d a p = 0
  | 0, _, _, _ => rfl
  | d + 1, a, 0, h => by omega
  | d + 1, a, p + 1, h => by
      simp only [vec_succ_succ]; exact vec_eq_zero_of_le d _ p (by omega)

theorem vec_succ_le : ∀ (d a p : ℕ), vec d a (p + 1) ≤ vec d a p
  | 0, _, _ => by simp
  | d + 1, a, p + 1 => by
      simp only [vec_succ_succ]; exact vec_succ_le d _ p
  | 0 + 1, a, 0 => by simp
  | (e + 1) + 1, a, 0 => by
      simp only [vec_succ_succ, vec_succ_zero]

      have h := rem_lt (e + 1) a
      have := top_lt_of_lt_choose e (rem (e + 1) a) (top (e + 1) a) h
      omega

theorem vec_antitone (d a : ℕ) : Antitone (vec d a) :=
  antitone_nat_of_succ_le (vec_succ_le d a)

theorem lex_vec_of_lt : ∀ (d : ℕ) {a b : ℕ}, a < b →
    Pi.Lex (· < ·) (fun {_} => (· < ·)) (vec (d + 1) a) (vec (d + 1) b)
  | 0, a, b, h => ⟨0, fun j hj => (Nat.not_lt_zero j hj).elim, by simpa [top_zero_left] using h⟩
  | d + 1, a, b, h => by
      rcases lt_trichotomy (top (d + 1) a) (top (d + 1) b) with ht | ht | ht
      · refine ⟨0, fun j hj => (Nat.not_lt_zero j hj).elim, ?_⟩
        have := d_le_top (d + 1) a
        simp only [vec_succ_zero]
        omega
      ·
        have hrem : rem (d + 1) a < rem (d + 1) b := by
          have ha := rem_add_choose (d + 1) a
          have hb := rem_add_choose (d + 1) b
          rw [ht] at ha; omega
        obtain ⟨i, hi, hlt⟩ := lex_vec_of_lt d hrem
        refine ⟨i + 1, fun j hj => ?_, by simpa using hlt⟩
        cases j with
        | zero => simp [ht]
        | succ j => simpa using hi j (by omega)
      · exfalso
        have h1 := lt_choose_top_succ (d + 1) b
        have h2 : (top (d + 1) b + 1).choose (d + 1 + 1) ≤ (top (d + 1) a).choose (d + 1 + 1) :=
          Nat.choose_le_choose _ ht
        have h3 := choose_top_le (d + 1) a
        omega

theorem not_lex_self (x : ℕ → ℕ) : ¬ Pi.Lex (· < ·) (fun {_} => (· < ·)) x x := by
  rintro ⟨i, -, h⟩; exact lt_irrefl _ h

theorem vec_injective (d : ℕ) {a b : ℕ} (h : vec (d + 1) a = vec (d + 1) b) : a = b := by
  rcases lt_trichotomy a b with hab | hab | hab
  · have := lex_vec_of_lt d hab; rw [h] at this; exact (not_lex_self _ this).elim
  · exact hab
  · have := lex_vec_of_lt d hab; rw [h] at this; exact (not_lex_self _ this).elim

theorem eq_or_lex_of_le (d : ℕ) {a b : ℕ} (h : a ≤ b) :
    vec (d + 1) a = vec (d + 1) b ∨
      Pi.Lex (· < ·) (fun {_} => (· < ·)) (vec (d + 1) a) (vec (d + 1) b) := by
  rcases h.eq_or_lt with h | h
  · exact Or.inl (by rw [h])
  · exact Or.inr (lex_vec_of_lt d h)

theorem head_le_of_eq_or_lex {x y : ℕ → ℕ}
    (h : x = y ∨ Pi.Lex (· < ·) (fun {_} => (· < ·)) x y) : x 0 ≤ y 0 := by
  rcases h with h | ⟨i, hi, hlt⟩
  · rw [h]
  · cases i with
    | zero => exact hlt.le
    | succ i => exact (hi 0 (by omega)).le

open Classical in

noncomputable def cnt (t : ℕ) (x : ℕ → ℕ) : ℕ :=
  if h : ∃ p, x p < t then Nat.find h else 0

theorem cnt_eq (t : ℕ) (x : ℕ → ℕ) (h : ∃ p, x p < t) : cnt t x = Nat.find h := by
  rw [cnt, dif_pos h]

noncomputable def cv (M : ℕ) (x : ℕ → ℕ) : Fin M → ℕ := fun i => cnt (M - i) x

theorem cv_lex {M : ℕ} {x y : ℕ → ℕ} (hy : Antitone y) (hyM : y 0 ≤ M) (hy0 : ∃ q, y q = 0)
    (h : Pi.Lex (· < ·) (fun {_} => (· < ·)) x y) :
    Pi.Lex (· < ·) (fun {_} => (· < ·)) (cv M x) (cv M y) := by
  obtain ⟨p, hp, hlt⟩ := h

  set t := y p with ht
  have ht1 : 1 ≤ t := by simp only [ht]; omega
  have htM : t ≤ M := (hy (Nat.zero_le p)).trans hyM
  refine ⟨⟨M - t, by omega⟩, fun j hj => ?_, ?_⟩
  ·
    have hj' : (j : ℕ) < M - t := hj
    set t' := M - (j : ℕ) with ht'
    have htt' : t < t' := by omega
    have hey : ∃ q, y q < t' := ⟨p, by omega⟩
    show cnt t' x = cnt t' y
    rw [cnt_eq t' y hey]
    set c := Nat.find hey with hc
    have hcspec : y c < t' := Nat.find_spec hey
    have hcmin : ∀ q < c, ¬ y q < t' := fun q hq => Nat.find_min hey hq
    have hcp : c ≤ p := Nat.find_min' hey (show y p < t' by omega)
    have hex : ∃ q, x q < t' := ⟨c, by
      rcases hcp.eq_or_lt with h | h
      · rw [h]; omega
      · rw [hp c h]; exact hcspec⟩
    rw [cnt_eq t' x hex, Nat.find_eq_iff]
    refine ⟨?_, fun q hq => ?_⟩
    · rcases hcp.eq_or_lt with h | h
      · rw [h]; omega
      · rw [hp c h]; exact hcspec
    · rw [hp q (by omega)]; exact hcmin q hq
  ·
    show cnt (M - (M - t)) x < cnt (M - (M - t)) y
    have hMt : M - (M - t) = t := by omega
    rw [hMt]
    have hex : ∃ q, x q < t := ⟨p, hlt⟩
    have hey : ∃ q, y q < t := by obtain ⟨q, hq⟩ := hy0; exact ⟨q, by omega⟩
    rw [cnt_eq t x hex, cnt_eq t y hey]
    have h1 : Nat.find hex = p := by
      rw [Nat.find_eq_iff]
      refine ⟨hlt, fun q hq => ?_⟩
      rw [hp q hq]
      have := hy hq.le
      omega
    rw [h1, Nat.lt_find_iff]
    intro q hq
    have := hy hq
    omega

theorem eventually_eq (H : ℕ → ℕ) (d₀ : ℕ)
    (hH : ∀ d, d₀ ≤ d → H (d + 1) ≤ Nat.macaulayPow d (H d)) :
    ∃ D₀ : ℕ, ∀ e, D₀ ≤ e → H (e + 1) = Nat.macaulayPow e (H e) := by

  set w : ℕ → ℕ → ℕ := fun d => vec d (H d) with hw

  have hstep : ∀ d, d₀ ≤ d →
      w (d + 1) = w d ∨ Pi.Lex (· < ·) (fun {_} => (· < ·)) (w (d + 1)) (w d) := by
    intro d hd
    have h := eq_or_lex_of_le d (hH d hd)
    rw [vec_macaulayPow d (H d)] at h
    exact h

  set M := w d₀ 0 with hM
  have hhead : ∀ d, d₀ ≤ d → w d 0 ≤ M := by
    intro d hd
    induction d, hd using Nat.le_induction with
    | base => exact le_rfl
    | succ d hd ih => exact (head_le_of_eq_or_lex (hstep d hd)).trans ih

  have wf : WellFounded (Pi.Lex (· < ·) (fun {_ : Fin M} => ((· < ·) : ℕ → ℕ → Prop))) :=
    Pi.Lex.wellFounded (· < ·) (fun _ => wellFounded_lt)
  obtain ⟨_, ⟨n₀, rfl⟩, hmin⟩ :=
    wf.has_min (Set.range fun n : ℕ => cv M (w (d₀ + n))) ⟨_, 0, rfl⟩
  refine ⟨d₀ + n₀, ?_⟩

  have hconst : ∀ d, d₀ + n₀ ≤ d → w d = w (d₀ + n₀) := by
    intro d hd
    induction d, hd using Nat.le_induction with
    | base => rfl
    | succ d hd ih =>
        rcases hstep d (by omega) with h | h
        · exact h.trans ih
        · exfalso
          rw [ih] at h
          have hlex := cv_lex (M := M) (vec_antitone _ _) (hhead _ (by omega))
            ⟨d₀ + n₀, vec_eq_zero_of_le _ _ _ le_rfl⟩ h
          refine hmin (cv M (w (d + 1))) ⟨d + 1 - d₀, ?_⟩ hlex
          show cv M (w (d₀ + (d + 1 - d₀))) = cv M (w (d + 1))
          rw [show d₀ + (d + 1 - d₀) = d + 1 by omega]
  intro e he
  have h1 : w (e + 1) = w e := (hconst (e + 1) (by omega)).trans (hconst e he).symm
  have h2 : vec (e + 1) (H (e + 1)) = vec (e + 1) (Nat.macaulayPow e (H e)) := by
    rw [vec_macaulayPow e (H e)]; exact h1
  exact vec_injective e h2

end GotzNum
p2m_reactivate "P2MW.S_Nat_exists_forall_eq_macaulayPow_of_forall_le_macaulayPow.GotzNum"

open GotzNum in
theorem solution
    (H : ℕ → ℕ) (d₀ : ℕ) (hd₀ : 1 ≤ d₀)
    (hH : ∀ d, d₀ ≤ d → H (d + 1) ≤ Nat.macaulayPow d (H d)) :
    ∃ D₀ : ℕ, ∀ e, D₀ ≤ e → H (e + 1) = Nat.macaulayPow e (H e) :=
  eventually_eq H d₀ hH

end S_Nat_exists_forall_eq_macaulayPow_of_forall_le_macaulayPow
end P2MW
export P2MW.S_Nat_exists_forall_eq_macaulayPow_of_forall_le_macaulayPow (solution)
