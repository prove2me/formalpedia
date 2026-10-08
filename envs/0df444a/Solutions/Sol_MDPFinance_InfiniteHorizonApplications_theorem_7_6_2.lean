-- Prove2me | solution 1 for MDPFinance.InfiniteHorizonApplications.theorem_7_6_2
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-06T03:58:32.453372+00:00
-- url     : https://prove2.me/submissions/f679be25-5c3b-4a47-ba2b-2f89ed1fee72

import Mathlib
import Definitions.Def_MDPFinance_InfiniteHorizonApplications_Casino

open MeasureTheory ProbabilityTheory


namespace MDPFinance.InfiniteHorizonApplications

noncomputable def cgG (r : ℝ) (x : ℕ) : ℝ := ∑ i ∈ Finset.range x, r ^ i

lemma cgG_add (r : ℝ) (y a : ℕ) : cgG r (y + a) = cgG r y + r ^ y * cgG r a := by
  unfold cgG; rw [Finset.sum_range_add, Finset.mul_sum]; simp [pow_add]

lemma cgG_nonneg {r : ℝ} (hr : 0 ≤ r) (x : ℕ) : 0 ≤ cgG r x :=
  Finset.sum_nonneg (fun i _ => pow_nonneg hr i)

lemma cgG_mono {r : ℝ} (hr : 0 ≤ r) {x y : ℕ} (h : x ≤ y) : cgG r x ≤ cgG r y := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [cgG_add]; nlinarith [pow_nonneg hr x, cgG_nonneg hr d]

lemma cgG_pos {r : ℝ} (hr : 0 < r) (x : ℕ) (hx : 0 < x) : 0 < cgG r x :=
  Finset.sum_pos (fun i _ => pow_pos hr i) (by simp; omega)

lemma cgG_zero (r : ℝ) : cgG r 0 = 0 := by simp [cgG]

lemma cgG_exc {p r : ℝ} (hp0 : 0 < p) (hr0 : 0 < r) (hr1 : r ≤ 1) (hpr : p * r = 1 - p)
    (x a : ℕ) (ha : a ≤ x) : p * cgG r (x + a) + (1 - p) * cgG r (x - a) ≤ cgG r x := by
  obtain ⟨y, rfl⟩ := Nat.exists_eq_add_of_le' ha
  have e1 : y + a + a = y + a + a := rfl
  rw [Nat.add_sub_cancel, cgG_add r (y + a) a, cgG_add r y a, pow_add]
  have hGa := cgG_nonneg hr0.le a
  have hry := pow_nonneg hr0.le y
  rcases Nat.eq_zero_or_pos a with h | h
  · subst h; simp [cgG_zero]; nlinarith
  · have hra : r ^ a ≤ r := by
      calc r ^ a ≤ r ^ 1 := pow_le_pow_of_le_one hr0.le hr1 h
        _ = r := pow_one r
    have : p * r ^ a ≤ 1 - p := by nlinarith
    have h2 : 0 ≤ r ^ y * cgG r a := mul_nonneg hry hGa
    nlinarith [mul_le_mul_of_nonneg_left this h2]

lemma cgG_harm {p r : ℝ} (hpr : p * r = 1 - p) (y : ℕ) :
    p * cgG r (y + 1 + 1) + (1 - p) * cgG r y = cgG r (y + 1) := by
  rw [cgG_add r (y + 1) 1, cgG_add r y 1]
  simp [cgG, pow_succ]
  linear_combination (r ^ y) * hpr

section
variable (Mk : CasinoMarket)

noncomputable def cgR : ℝ := (1 - Mk.p) / Mk.p
noncomputable def cgH (x : ℕ) : ℝ := cgG (cgR Mk) x / cgG (cgR Mk) Mk.B

lemma cgR_pos : 0 < cgR Mk := div_pos (by linarith [Mk.hp1]) Mk.hp0
lemma cgR_mul : Mk.p * cgR Mk = 1 - Mk.p := by
  unfold cgR; field_simp [Mk.hp0.ne']

lemma cgH_exc (hp : 1 / 2 ≤ Mk.p) (x a : ℕ) (ha : a ≤ x) :
    Mk.p * cgH Mk (x + a) + (1 - Mk.p) * cgH Mk (x - a) ≤ cgH Mk x := by
  have hr1 : cgR Mk ≤ 1 := by
    unfold cgR; rw [div_le_one Mk.hp0]; linarith
  have := cgG_exc Mk.hp0 (cgR_pos Mk) hr1 (cgR_mul Mk) x a ha
  have hS := cgG_nonneg (cgR_pos Mk).le Mk.B
  unfold cgH
  rw [mul_div_assoc', mul_div_assoc', ← add_div]
  exact div_le_div_of_nonneg_right this hS

lemma cgH_harm (y : ℕ) :
    Mk.p * cgH Mk (y + 1 + 1) + (1 - Mk.p) * cgH Mk y = cgH Mk (y + 1) := by
  unfold cgH
  rw [mul_div_assoc', mul_div_assoc', ← add_div, cgG_harm (cgR_mul Mk)]

lemma cgH_B (hB : 1 ≤ Mk.B) : cgH Mk Mk.B = 1 := by
  unfold cgH; exact div_self (cgG_pos (cgR_pos Mk) _ hB).ne'

lemma cgH_zero : cgH Mk 0 = 0 := by simp [cgH, cgG_zero]

lemma cgH_nonneg (x : ℕ) : 0 ≤ cgH Mk x :=
  div_nonneg (cgG_nonneg (cgR_pos Mk).le x) (cgG_nonneg (cgR_pos Mk).le _)

lemma cgH_le_one (hB : 1 ≤ Mk.B) (x : ℕ) (hx : x ≤ Mk.B) : cgH Mk x ≤ 1 := by
  unfold cgH
  rw [div_le_one (cgG_pos (cgR_pos Mk) _ hB)]
  exact cgG_mono (cgR_pos Mk).le hx

lemma cg_vbound (hp : 1 / 2 ≤ Mk.p) (hB : 1 ≤ Mk.B) (n : ℕ) :
    ∀ (π : ℕ → Fin (Mk.B + 1) → ℕ) (x : Fin (Mk.B + 1)), Mk.VpiSeq π n x ≤ cgH Mk x.1 := by
  induction n with
  | zero =>
    intro π x
    rw [CasinoMarket.VpiSeq]
    split_ifs with h
    · rw [h, cgH_B Mk hB]
    · exact cgH_nonneg Mk _
  | succ n ih =>
    intro π x
    rw [CasinoMarket.VpiSeq]
    split_ifs with h1 h2
    · rw [h2, cgH_B Mk hB]
    · exact cgH_nonneg Mk _
    · dsimp only
      have hx := x.2
      set a := min (π 0 x) (min x.1 (Mk.B - x.1)) with ha
      have ha1 : a ≤ x.1 := le_trans (min_le_right _ _) (min_le_left _ _)
      have i1 := ih (fun k => π (k + 1)) ⟨x.1 + a, by omega⟩
      have i2 := ih (fun k => π (k + 1)) ⟨x.1 - a, by omega⟩
      have hexc := cgH_exc Mk hp x.1 a ha1
      simp only at i1 i2
      have hp1 := Mk.hp1; have hp0 := Mk.hp0
      nlinarith [mul_le_mul_of_nonneg_left i1 hp0.le,
        mul_le_mul_of_nonneg_left i2 (by linarith : (0:ℝ) ≤ 1 - Mk.p)]

lemma cg_timid_int (n : ℕ) (x : Fin (Mk.B + 1)) (h0 : 0 < x.1) (hB : x.1 < Mk.B) :
    Mk.Vpi Mk.timid (n + 1) x = Mk.p * Mk.Vpi Mk.timid n ⟨x.1 + 1, by omega⟩ +
      (1 - Mk.p) * Mk.Vpi Mk.timid n ⟨x.1 - 1, by omega⟩ := by
  unfold CasinoMarket.Vpi
  rw [CasinoMarket.VpiSeq, if_neg (by omega)]
  have ha : min (Mk.timid x) (min x.1 (Mk.B - x.1)) = 1 := by
    unfold CasinoMarket.timid; rw [if_neg (by omega)]; omega
  dsimp only
  have e1 : (⟨x.1 + min (Mk.timid x) (min x.1 (Mk.B - x.1)), by omega⟩ : Fin (Mk.B + 1)) =
      ⟨x.1 + 1, by omega⟩ := Fin.ext (by simp only; rw [ha])
  have e2 : (⟨x.1 - min (Mk.timid x) (min x.1 (Mk.B - x.1)), by omega⟩ : Fin (Mk.B + 1)) =
      ⟨x.1 - 1, by omega⟩ := Fin.ext (by simp only; rw [ha])
  rw [e1, e2]

lemma cg_timid_B (n : ℕ) (x : Fin (Mk.B + 1)) (hx : x.1 = Mk.B) : Mk.Vpi Mk.timid n x = 1 := by
  unfold CasinoMarket.Vpi
  cases n with
  | zero => rw [CasinoMarket.VpiSeq, if_pos hx]
  | succ n => rw [CasinoMarket.VpiSeq, if_pos (Or.inr hx), if_pos hx]

lemma cg_timid_0 (hB : 1 ≤ Mk.B) (n : ℕ) (x : Fin (Mk.B + 1)) (hx : x.1 = 0) :
    Mk.Vpi Mk.timid n x = 0 := by
  unfold CasinoMarket.Vpi
  cases n with
  | zero => rw [CasinoMarket.VpiSeq, if_neg (by omega)]
  | succ n => rw [CasinoMarket.VpiSeq, if_pos (Or.inl hx), if_neg (by omega)]


lemma cg_decay' (hB : 1 ≤ Mk.B) (n : ℕ) (M : ℝ) (hM : 0 ≤ M)
    (h : ∀ x : Fin (Mk.B + 1), cgH Mk x.1 - Mk.Vpi Mk.timid n x ≤ M) (k : ℕ) :
    (∀ x : Fin (Mk.B + 1), cgH Mk x.1 - Mk.Vpi Mk.timid (n + k) x ≤ M) ∧
    (∀ x : Fin (Mk.B + 1), Mk.B - x.1 ≤ k →
      cgH Mk x.1 - Mk.Vpi Mk.timid (n + k) x ≤ M * (1 - Mk.p ^ k)) := by
  have hp0 := Mk.hp0; have hp1 := Mk.hp1
  induction k with
  | zero =>
    refine ⟨h, fun x hx => ?_⟩
    have hxB : x.1 = Mk.B := by have := x.2; omega
    rw [cg_timid_B Mk _ x hxB, hxB, cgH_B Mk hB]; simp
  | succ k ih =>
    obtain ⟨ih1, ih2⟩ := ih
    have hpk : Mk.p ^ k ≤ 1 := pow_le_one₀ hp0.le hp1.le
    have hpk0 : 0 ≤ Mk.p ^ k := pow_nonneg hp0.le k
    have hzero : ∀ x : Fin (Mk.B + 1), (x.1 = 0 ∨ x.1 = Mk.B) →
        cgH Mk x.1 - Mk.Vpi Mk.timid (n + (k + 1)) x = 0 := by
      intro x hx
      rcases hx with hx | hx
      · rw [cg_timid_0 Mk hB _ x hx, hx, cgH_zero]; simp
      · rw [cg_timid_B Mk _ x hx, hx, cgH_B Mk hB]; simp
    have hint : ∀ x : Fin (Mk.B + 1), ∀ (_h0 : 0 < x.1) (_h1 : x.1 < Mk.B),
        cgH Mk x.1 - Mk.Vpi Mk.timid (n + (k + 1)) x =
          Mk.p * (cgH Mk (x.1 + 1) - Mk.Vpi Mk.timid (n + k) ⟨x.1 + 1, by omega⟩) +
          (1 - Mk.p) * (cgH Mk (x.1 - 1) - Mk.Vpi Mk.timid (n + k) ⟨x.1 - 1, by omega⟩) := by
      intro x h0 h1
      rw [← add_assoc, cg_timid_int Mk _ x h0 h1]
      have := cgH_harm Mk (x.1 - 1)
      have e : x.1 - 1 + 1 = x.1 := by omega
      rw [e] at this
      rw [← this]; ring
    have hpk1 : 0 ≤ 1 - Mk.p ^ (k + 1) := by
      have := pow_le_one₀ (n := k + 1) hp0.le hp1.le; linarith
    constructor
    · intro x
      by_cases hb : x.1 = 0 ∨ x.1 = Mk.B
      · rw [hzero x hb]; exact hM
      · have h0 : 0 < x.1 := by omega
        have h1 : x.1 < Mk.B := by have := x.2; omega
        rw [hint x h0 h1]
        have a1 := ih1 ⟨x.1 + 1, by omega⟩
        have a2 := ih1 ⟨x.1 - 1, by omega⟩
        simp only at a1 a2
        nlinarith [mul_le_mul_of_nonneg_left a1 hp0.le,
          mul_le_mul_of_nonneg_left a2 (by linarith : (0:ℝ) ≤ 1 - Mk.p)]
    · intro x hxk
      by_cases hb : x.1 = 0 ∨ x.1 = Mk.B
      · rw [hzero x hb]; exact mul_nonneg hM hpk1
      · have h0 : 0 < x.1 := by omega
        have h1 : x.1 < Mk.B := by have := x.2; omega
        rw [hint x h0 h1]
        have a1 := ih2 ⟨x.1 + 1, by omega⟩ (by simp only; omega)
        have a2 := ih1 ⟨x.1 - 1, by omega⟩
        simp only at a1 a2
        rw [pow_succ]
        nlinarith [mul_le_mul_of_nonneg_left a1 hp0.le,
          mul_le_mul_of_nonneg_left a2 (by linarith : (0:ℝ) ≤ 1 - Mk.p)]

lemma cg_iter (hB : 1 ≤ Mk.B) (j : ℕ) :
    ∀ x : Fin (Mk.B + 1), cgH Mk x.1 - Mk.Vpi Mk.timid (j * Mk.B) x ≤ (1 - Mk.p ^ Mk.B) ^ j := by
  have hp0 := Mk.hp0; have hp1 := Mk.hp1
  have hq0 : 0 ≤ 1 - Mk.p ^ Mk.B := by
    have := pow_le_one₀ (n := Mk.B) hp0.le hp1.le; linarith
  induction j with
  | zero =>
    intro x
    simp only [zero_mul, pow_zero]
    unfold CasinoMarket.Vpi
    rw [CasinoMarket.VpiSeq]
    split_ifs with h
    · rw [h, cgH_B Mk hB]; simp
    · have := cgH_le_one Mk hB x.1 (by have := x.2; omega); linarith
  | succ j ih =>
    intro x
    have := (cg_decay' Mk hB (j * Mk.B) _ (pow_nonneg hq0 j) ih Mk.B).2 x (by omega)
    rw [show (j + 1) * Mk.B = j * Mk.B + Mk.B by ring, pow_succ]
    exact this

lemma cg_B0 (hB : Mk.B = 0) (π : ℕ → Fin (Mk.B + 1) → ℕ) (n : ℕ) (x : Fin (Mk.B + 1)) :
    Mk.VpiSeq π n x = 1 := by
  have hx : x.1 = Mk.B := by have := x.2; omega
  cases n with
  | zero => rw [CasinoMarket.VpiSeq, if_pos hx]
  | succ n => rw [CasinoMarket.VpiSeq, if_pos (Or.inr hx), if_pos hx]

theorem thm762_core (hp : 1 / 2 ≤ Mk.p) : ∀ x, Mk.Jinfpi Mk.timid x = Mk.Jinf x := by
  intro x
  rcases Nat.eq_zero_or_pos Mk.B with hB | hB
  · unfold CasinoMarket.Jinfpi CasinoMarket.Jinf CasinoMarket.Vpi
    simp only [cg_B0 Mk hB, ciSup_const]
  have hbdd : ∀ π : ℕ → Fin (Mk.B + 1) → ℕ, BddAbove (Set.range fun n => Mk.VpiSeq π n x) :=
    fun π => ⟨cgH Mk x.1, by rintro _ ⟨n, rfl⟩; exact cg_vbound Mk hp hB n π x⟩
  have hsup : ∀ π : ℕ → Fin (Mk.B + 1) → ℕ, (⨆ n, Mk.VpiSeq π n x) ≤ cgH Mk x.1 :=
    fun π => ciSup_le (fun n => cg_vbound Mk hp hB n π x)
  have h1 : Mk.Jinf x ≤ cgH Mk x.1 := ciSup_le hsup
  have h2 : Mk.Jinfpi Mk.timid x ≤ Mk.Jinf x := by
    unfold CasinoMarket.Jinfpi CasinoMarket.Jinf CasinoMarket.Vpi
    exact le_ciSup (f := fun π => ⨆ n, Mk.VpiSeq π n x)
      ⟨cgH Mk x.1, by rintro _ ⟨π, rfl⟩; exact hsup π⟩ (fun _ => Mk.timid)
  have h3 : cgH Mk x.1 ≤ Mk.Jinfpi Mk.timid x := by
    apply le_of_forall_pos_lt_add
    intro ε hε
    have hp0 := Mk.hp0; have hp1 := Mk.hp1
    have hq1 : 1 - Mk.p ^ Mk.B < 1 := by have := pow_pos hp0 Mk.B; linarith
    obtain ⟨j, hj⟩ := exists_pow_lt_of_lt_one hε hq1
    have := cg_iter Mk hB j x
    have h4 : Mk.Vpi Mk.timid (j * Mk.B) x ≤ Mk.Jinfpi Mk.timid x := by
      unfold CasinoMarket.Jinfpi
      exact le_ciSup (hbdd (fun _ => Mk.timid)) (j * Mk.B)
    linarith
  linarith

end

end MDPFinance.InfiniteHorizonApplications

open MDPFinance.InfiniteHorizonApplications


theorem solution (Mk : CasinoMarket) (hp : 1 / 2 ≤ Mk.p) :
    ∀ x, Mk.Jinfpi Mk.timid x = Mk.Jinf x := by
  exact thm762_core Mk hp
