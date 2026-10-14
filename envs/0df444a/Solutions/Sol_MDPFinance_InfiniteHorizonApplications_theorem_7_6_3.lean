-- Prove2me | solution 1 for MDPFinance.InfiniteHorizonApplications.theorem_7_6_3
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-13T04:16:43.54761+00:00
-- url     : https://prove2.me/submissions/b2896231-3b96-40c1-9710-876be988237b

import Mathlib
import Definitions.Def_MDPFinance_InfiniteHorizonApplications_Casino

open MeasureTheory ProbabilityTheory


namespace MDPFinance.InfiniteHorizonApplications

/-- continuous bold-play n-step win probability -/
noncomputable def rbQ (p : ℝ) : ℕ → ℝ → ℝ
  | 0, x => if x = 1 then 1 else 0
  | (n + 1), x => if x ≤ 1 / 2 then p * rbQ p n (2 * x) else p + (1 - p) * rbQ p n (2 * x - 1)

lemma rbQ_zero_pt (p : ℝ) (n : ℕ) : rbQ p n 0 = 0 := by
  induction n with
  | zero => simp [rbQ]
  | succ n ih => simp [rbQ, ih]

lemma rbQ_one_pt (p : ℝ) (n : ℕ) : rbQ p n 1 = 1 := by
  induction n with
  | zero => simp [rbQ]
  | succ n ih =>
    rw [rbQ, if_neg (by norm_num)]
    norm_num [ih]

lemma rbQ_lo (p : ℝ) (n : ℕ) (x : ℝ) (hx : x ≤ 1 / 2) : rbQ p (n + 1) x = p * rbQ p n (2 * x) := by
  rw [rbQ, if_pos hx]

lemma rbQ_hi (p : ℝ) (n : ℕ) (x : ℝ) (hx : 1 / 2 ≤ x) :
    rbQ p (n + 1) x = p + (1 - p) * rbQ p n (2 * x - 1) := by
  rw [rbQ]
  split_ifs with h
  · have : x = 1 / 2 := le_antisymm h hx
    subst this
    norm_num [rbQ_one_pt, rbQ_zero_pt]
  · rfl

lemma rbQ_bounds {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (n : ℕ) :
    ∀ x, 0 ≤ rbQ p n x ∧ rbQ p n x ≤ 1 := by
  induction n with
  | zero => intro x; simp only [rbQ]; split_ifs <;> norm_num
  | succ n ih =>
    intro x
    simp only [rbQ]
    split_ifs
    · have := ih (2 * x); constructor <;> nlinarith
    · have := ih (2 * x - 1); constructor <;> nlinarith

/-- superadditivity (A) and its dual (B) -/
lemma rbQ_AB {p : ℝ} (hp0 : 0 ≤ p) (hp : p ≤ 1 / 2) (n : ℕ) :
    (∀ u v : ℝ, 0 ≤ u → 0 ≤ v → u + v ≤ 1 → rbQ p n u + rbQ p n v ≤ rbQ p n (u + v)) ∧
    (∀ u v : ℝ, u ≤ 1 → v ≤ 1 → 1 ≤ u + v → rbQ p n u + rbQ p n v ≤ 1 + rbQ p n (u + v - 1)) := by
  have hp1 : p ≤ 1 := by linarith
  have bd := rbQ_bounds hp0 hp1
  induction n with
  | zero =>
    constructor
    · intro u v hu hv huv
      by_cases hu1 : u = 1
      · have hv0 : v = 0 := by linarith
        subst hu1 hv0; norm_num [rbQ]
      by_cases hv1 : v = 1
      · have hu0 : u = 0 := by linarith
        subst hv1 hu0; norm_num [rbQ]
      have := (bd 0 (u + v)).1
      simp only [rbQ, if_neg hu1, if_neg hv1] at *
      linarith
    · intro u v hu hv huv
      by_cases hu1 : u = 1
      · subst hu1
        rw [show 1 + v - 1 = v by ring]
        have := (bd 0 v).2; simp only [rbQ, if_true] at *; linarith
      have := (bd 0 v).2
      have := (bd 0 (u + v - 1)).1
      simp only [rbQ, if_neg hu1] at *
      linarith
  | succ n ih =>
    obtain ⟨A, B⟩ := ih
    constructor
    · intro u v hu hv huv
      rcases le_total (u + v) (1 / 2) with h1 | h1
      · rw [rbQ_lo p n u (by linarith), rbQ_lo p n v (by linarith), rbQ_lo p n _ h1]
        have := A (2 * u) (2 * v) (by linarith) (by linarith) (by linarith)
        rw [show 2 * (u + v) = 2 * u + 2 * v by ring]; nlinarith
      · rw [rbQ_hi p n _ h1]
        rcases le_total u (1 / 2) with hu2 | hu2 <;> rcases le_total v (1 / 2) with hv2 | hv2
        · rw [rbQ_lo p n u hu2, rbQ_lo p n v hv2]
          have := B (2 * u) (2 * v) (by linarith) (by linarith) (by linarith)
          rw [show 2 * (u + v) - 1 = 2 * u + 2 * v - 1 by ring]
          have := (bd n (2 * u + 2 * v - 1)).1
          nlinarith
        · rw [rbQ_lo p n u hu2, rbQ_hi p n v hv2]
          have := A (2 * u) (2 * v - 1) (by linarith) (by linarith) (by linarith)
          have := (bd n (2 * u)).1
          rw [show 2 * (u + v) - 1 = 2 * u + (2 * v - 1) by ring]
          nlinarith
        · rw [rbQ_hi p n u hu2, rbQ_lo p n v hv2]
          have := A (2 * v) (2 * u - 1) (by linarith) (by linarith) (by linarith)
          have := (bd n (2 * v)).1
          rw [show 2 * (u + v) - 1 = 2 * v + (2 * u - 1) by ring]
          nlinarith
        · have hu' : u = 1 / 2 := by linarith
          have hv' : v = 1 / 2 := by linarith
          subst hu' hv'
          rw [rbQ_lo p n _ le_rfl]
          norm_num [rbQ_one_pt, rbQ_zero_pt]
          linarith
    · intro u v hu hv huv
      rcases le_total u (1 / 2) with hu2 | hu2 <;> rcases le_total v (1 / 2) with hv2 | hv2
      · have hu' : u = 1 / 2 := by linarith
        have hv' : v = 1 / 2 := by linarith
        subst hu' hv'
        rw [rbQ_lo p n _ le_rfl]
        norm_num [rbQ_one_pt, rbQ_zero_pt]
        nlinarith
      · rw [rbQ_lo p n u hu2, rbQ_hi p n v hv2, rbQ_lo p n _ (by linarith)]
        have := B (2 * u) (2 * v - 1) (by linarith) (by linarith) (by linarith)
        have := (bd n (2 * v - 1)).2
        rw [show 2 * (u + v - 1) = 2 * u + (2 * v - 1) - 1 by ring]
        nlinarith
      · rw [rbQ_hi p n u hu2, rbQ_lo p n v hv2, rbQ_lo p n _ (by linarith)]
        have := B (2 * v) (2 * u - 1) (by linarith) (by linarith) (by linarith)
        have := (bd n (2 * u - 1)).2
        rw [show 2 * (u + v - 1) = 2 * v + (2 * u - 1) - 1 by ring]
        nlinarith
      · rw [rbQ_hi p n u hu2, rbQ_hi p n v hv2]
        rcases le_total (u + v - 1) (1 / 2) with h1 | h1
        · rw [rbQ_lo p n _ h1]
          have := A (2 * u - 1) (2 * v - 1) (by linarith) (by linarith) (by linarith)
          have := (bd n (2 * (u + v - 1))).2
          rw [show 2 * (u + v - 1) = (2 * u - 1) + (2 * v - 1) by ring] at *
          nlinarith
        · rw [rbQ_hi p n _ h1]
          have := B (2 * u - 1) (2 * v - 1) (by linarith) (by linarith) (by linarith)
          rw [show 2 * (u + v - 1) - 1 = (2 * u - 1) + (2 * v - 1) - 1 by ring]
          nlinarith

/-- the excessive inequality -/
lemma rbQ_exc {p : ℝ} (hp0 : 0 ≤ p) (hp : p ≤ 1 / 2) (n : ℕ) :
    ∀ r s : ℝ, 0 ≤ r → r ≤ s → s ≤ 1 →
      p * rbQ p n s + (1 - p) * rbQ p n r ≤ rbQ p (n + 1) ((r + s) / 2) := by
  have hp1 : p ≤ 1 := by linarith
  have bd := rbQ_bounds hp0 hp1
  induction n with
  | zero =>
    intro r s hr hrs hs
    by_cases h : s = 1
    · subst h
      rw [rbQ_hi p 0 _ (by linarith), show 2 * ((r + 1) / 2) - 1 = r by ring]
      simp only [rbQ, if_true]; linarith
    · have hr1 : r ≠ 1 := by intro h'; apply h; linarith
      have := (bd 1 ((r + s) / 2)).1
      have e1 : rbQ p 0 s = 0 := by simp [rbQ, h]
      have e2 : rbQ p 0 r = 0 := by simp [rbQ, hr1]
      rw [e1, e2]; linarith
  | succ n ih =>
    intro r s hr hrs hs
    obtain ⟨A, B⟩ := rbQ_AB hp0 hp n
    rcases le_total s (1 / 2) with hs2 | hs2
    · rw [rbQ_lo p n s hs2, rbQ_lo p n r (by linarith), rbQ_lo p (n + 1) _ (by linarith)]
      have := ih (2 * r) (2 * s) (by linarith) (by linarith) (by linarith)
      rw [show 2 * ((r + s) / 2) = (2 * r + 2 * s) / 2 by ring]
      nlinarith
    rcases le_total (1 / 2) r with hr2 | hr2
    · rw [rbQ_hi p n s hs2, rbQ_hi p n r hr2, rbQ_hi p (n + 1) _ (by linarith)]
      have := ih (2 * r - 1) (2 * s - 1) (by linarith) (by linarith) (by linarith)
      rw [show 2 * ((r + s) / 2) - 1 = ((2 * r - 1) + (2 * s - 1)) / 2 by ring]
      nlinarith
    rw [rbQ_hi p n s hs2, rbQ_lo p n r hr2]
    rcases le_total ((r + s) / 2) (1 / 2) with hm | hm
    · rw [rbQ_lo p (n + 1) _ hm, rbQ_hi p n _ (by linarith)]
      have := A (2 * r) (2 * s - 1) (by linarith) (by linarith) (by linarith)
      rw [show 2 * (2 * ((r + s) / 2)) - 1 = 2 * r + (2 * s - 1) by ring]
      have hpq : 0 ≤ p * (1 - p) := mul_nonneg hp0 (by linarith)
      nlinarith [mul_le_mul_of_nonneg_left this hpq]
    · rw [rbQ_hi p (n + 1) _ hm, rbQ_lo p n _ (by linarith)]
      have := B (2 * r) (2 * s - 1) (by linarith) (by linarith) (by linarith)
      rw [show 2 * (2 * ((r + s) / 2) - 1) = 2 * r + (2 * s - 1) - 1 by ring]
      have hpq : 0 ≤ p * (1 - p) := mul_nonneg hp0 (by linarith)
      nlinarith [mul_le_mul_of_nonneg_left this hpq]

section
variable (Mk : CasinoMarket)

lemma rb_bold_eq (hB : 1 ≤ Mk.B) (n : ℕ) :
    ∀ x : Fin (Mk.B + 1), Mk.Vpi Mk.bold n x = rbQ Mk.p n ((x.1 : ℝ) / Mk.B) := by
  have hBpos : (0 : ℝ) < Mk.B := by exact_mod_cast hB
  induction n with
  | zero =>
    intro x
    unfold CasinoMarket.Vpi
    rw [CasinoMarket.VpiSeq, rbQ]
    by_cases h : x.1 = Mk.B
    · rw [if_pos h, if_pos (by rw [h]; field_simp)]
    · rw [if_neg h, if_neg]
      intro h'
      rw [div_eq_one_iff_eq hBpos.ne'] at h'
      exact h (by exact_mod_cast h')
  | succ n ih =>
    intro x
    unfold CasinoMarket.Vpi at ih ⊢
    rw [CasinoMarket.VpiSeq]
    split_ifs with h1 h2
    · rw [h2]; rw [show ((Mk.B : ℕ) : ℝ) / Mk.B = 1 by field_simp, rbQ_one_pt]
    · have h0 : x.1 = 0 := by tauto
      rw [h0]; simp [rbQ_zero_pt]
    · dsimp only
      rw [ih, ih]
      have hb : Mk.bold x = min x.1 (Mk.B - x.1) := rfl
      simp only
      rw [hb, min_self]
      have hx := x.2
      rcases le_total x.1 (Mk.B - x.1) with h | h
      · rw [min_eq_left h, rbQ_lo]
        · simp only [Nat.sub_self, Nat.cast_zero, zero_div, rbQ_zero_pt, mul_zero, add_zero]
          congr 1; push_cast; ring
        · rw [div_le_iff₀ hBpos]
          have : (x.1 : ℝ) ≤ Mk.B - x.1 := by
            have := (Nat.cast_le (α := ℝ)).2 h; rwa [Nat.cast_sub (by omega)] at this
          linarith
      · rw [min_eq_right h, rbQ_hi]
        · have e1 : x.1 + (Mk.B - x.1) = Mk.B := by omega
          rw [e1, show ((Mk.B : ℕ) : ℝ) / Mk.B = 1 by field_simp, rbQ_one_pt, mul_one]
          congr 2
          rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
          field_simp; ring
        · rw [le_div_iff₀ hBpos]
          have : (Mk.B : ℝ) - x.1 ≤ x.1 := by
            have := (Nat.cast_le (α := ℝ)).2 h; rwa [Nat.cast_sub (by omega)] at this
          linarith

lemma rb_vbound (hp : Mk.p ≤ 1 / 2) (hB : 1 ≤ Mk.B) (n : ℕ) :
    ∀ (π : ℕ → Fin (Mk.B + 1) → ℕ) (x : Fin (Mk.B + 1)),
      Mk.VpiSeq π n x ≤ rbQ Mk.p n ((x.1 : ℝ) / Mk.B) := by
  have hBpos : (0 : ℝ) < Mk.B := by exact_mod_cast hB
  have hp0 := Mk.hp0
  have hp1 := Mk.hp1
  have bd := rbQ_bounds hp0.le hp1.le
  induction n with
  | zero =>
    intro π x
    rw [CasinoMarket.VpiSeq, rbQ]
    by_cases h : x.1 = Mk.B
    · rw [if_pos h, if_pos (by rw [h]; field_simp)]
    · rw [if_neg h]; split_ifs <;> norm_num
  | succ n ih =>
    intro π x
    rw [CasinoMarket.VpiSeq]
    split_ifs with h1 h2
    · rw [h2]; rw [show ((Mk.B : ℕ) : ℝ) / Mk.B = 1 by field_simp, rbQ_one_pt]
    · exact (bd _ _).1
    · dsimp only
      have hx := x.2
      set a := min (π 0 x) (min x.1 (Mk.B - x.1)) with ha
      have ha1 : a ≤ x.1 := le_trans (min_le_right _ _) (min_le_left _ _)
      have ha2 : a ≤ Mk.B - x.1 := le_trans (min_le_right _ _) (min_le_right _ _)
      have i1 := ih (fun k => π (k + 1)) ⟨x.1 + a, by omega⟩
      have i2 := ih (fun k => π (k + 1)) ⟨x.1 - a, by omega⟩
      simp only at i1 i2
      have hexc := rbQ_exc hp0.le hp n ((((x.1 - a : ℕ) : ℝ)) / Mk.B) (((x.1 + a : ℕ) : ℝ) / Mk.B)
        (by positivity) (by gcongr; omega)
        (by rw [div_le_one hBpos]; exact_mod_cast (by omega : x.1 + a ≤ Mk.B))
      have em : ((((x.1 - a : ℕ) : ℝ)) / Mk.B + (((x.1 + a : ℕ) : ℝ)) / Mk.B) / 2 =
          (x.1 : ℝ) / Mk.B := by
        rw [Nat.cast_sub ha1]; push_cast; field_simp; ring
      rw [em] at hexc
      nlinarith [mul_le_mul_of_nonneg_left i1 hp0.le,
        mul_le_mul_of_nonneg_left i2 (by linarith : (0:ℝ) ≤ 1 - Mk.p)]

lemma rb_B0 (hB : Mk.B = 0) (π : ℕ → Fin (Mk.B + 1) → ℕ) (n : ℕ) (x : Fin (Mk.B + 1)) :
    Mk.VpiSeq π n x = 1 := by
  have hx : x.1 = Mk.B := by have := x.2; omega
  cases n with
  | zero => rw [CasinoMarket.VpiSeq, if_pos hx]
  | succ n => rw [CasinoMarket.VpiSeq, if_pos (Or.inr hx), if_pos hx]

theorem t763_core (hp : Mk.p ≤ 1 / 2) : ∀ x, Mk.Jinfpi Mk.bold x = Mk.Jinf x := by
  intro x
  rcases Nat.eq_zero_or_pos Mk.B with hB | hB
  · unfold CasinoMarket.Jinfpi CasinoMarket.Jinf CasinoMarket.Vpi
    simp only [rb_B0 Mk hB, ciSup_const]
  have bd := rbQ_bounds Mk.hp0.le Mk.hp1.le
  have hsup : ∀ π : ℕ → Fin (Mk.B + 1) → ℕ, (⨆ n, Mk.VpiSeq π n x) ≤ 1 :=
    fun π => ciSup_le (fun n => (rb_vbound Mk hp hB n π x).trans (bd _ _).2)
  have hbdd : BddAbove (Set.range fun n => Mk.Vpi Mk.bold n x) :=
    ⟨1, by rintro _ ⟨n, rfl⟩; exact (rb_vbound Mk hp hB n _ x).trans (bd _ _).2⟩
  apply le_antisymm
  · unfold CasinoMarket.Jinfpi CasinoMarket.Jinf
    exact le_ciSup (f := fun π => ⨆ n, Mk.VpiSeq π n x)
      ⟨1, by rintro _ ⟨π, rfl⟩; exact hsup π⟩ (fun _ => Mk.bold)
  · unfold CasinoMarket.Jinf
    apply ciSup_le; intro π
    apply ciSup_le; intro n
    calc Mk.VpiSeq π n x ≤ rbQ Mk.p n ((x.1 : ℝ) / Mk.B) := rb_vbound Mk hp hB n π x
      _ = Mk.Vpi Mk.bold n x := (rb_bold_eq Mk hB n x).symm
      _ ≤ Mk.Jinfpi Mk.bold x := le_ciSup hbdd n

end

end MDPFinance.InfiniteHorizonApplications

open MDPFinance.InfiniteHorizonApplications


theorem solution (Mk : CasinoMarket) (hp : Mk.p ≤ 1 / 2) :
    ∀ x, Mk.Jinfpi Mk.bold x = Mk.Jinf x := by
  exact t763_core Mk hp
