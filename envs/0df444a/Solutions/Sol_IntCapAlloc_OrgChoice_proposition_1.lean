-- Prove2me | solution 1 for IntCapAlloc.OrgChoice.proposition_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-29T16:07:46.451234+00:00
-- url     : https://prove2.me/submissions/7bf8c103-1a0e-4d7c-b517-8ae51e18971a

import Mathlib
import Definitions.Def_IntCapAlloc_OrgChoice_Model

open IntCapAlloc.OrgChoice

namespace IntCapP1

lemma exIcc_iff (E X R : ℝ) (hE : 0 ≤ E) (hX : 0 < X) (hR : 0 < R) :
    (∃ α ∈ Set.Icc (0 : ℝ) 1, E * α * X = R) ↔ R ≤ E * X := by
  constructor
  · rintro ⟨α, ⟨h0, h1⟩, h⟩
    rw [← h]
    have : E * α * X = (E * X) * α := by ring
    rw [this]
    have : 0 ≤ E * X := mul_nonneg hE hX.le
    nlinarith
  · intro h
    have hEX : 0 < E * X := lt_of_lt_of_le hR h
    have hE0 : E ≠ 0 := by rintro rfl; simp at hEX
    refine ⟨R / (E * X), ⟨div_nonneg hR.le hEX.le, (div_le_one hEX).mpr h⟩, ?_⟩
    field_simp

@[simp] lemma m1 (t : Bool) : msg1 t true = some t := by simp [msg1]
@[simp] lemma m0 (t : Bool) : msg1 t false = none := by simp [msg1]

lemma Eθ1_eq (μ : Belief1) (m : Option Bool) : Eθ1 μ m = μ m true := by
  simp [Eθ1, th, Fintype.sum_bool]

lemma adm_some {μ : Belief1} (hμ : Admissible1 μ) (b : Bool) :
    μ (some b) b = 1 ∧ μ (some b) (!b) = 0 := by
  obtain ⟨_, hs, hc⟩ := hμ (some b)
  have h0 : μ (some b) (!b) = 0 := by
    by_contra hne
    have := hc _ hne b rfl
    cases b <;> simp at this
  refine ⟨?_, h0⟩
  rw [Fintype.sum_bool] at hs
  cases b <;> simp_all

lemma inv_some_true {X c : ℝ} {μ : Belief1} (hμ : Admissible1 μ) (hX : 0 < X) (hc : 0 < c)
    (hf : 1 + c ≤ X) : invest1 X c μ (some true) = 1 := by
  have h1 := (adm_some hμ true).1
  unfold invest1
  rw [if_pos]
  rw [exIcc_iff _ _ _ (by rw [Eθ1_eq, h1]; norm_num) hX (by simp [nD1]; linarith)]
  simp [Eθ1_eq, h1, nD1]; linarith

lemma inv_some_false {X c : ℝ} {μ : Belief1} (hμ : Admissible1 μ) (hX : 0 < X) (hc : 0 < c) :
    invest1 X c μ (some false) = 0 := by
  have h1 := (adm_some hμ false).2
  unfold invest1
  rw [if_neg]
  rw [exIcc_iff _ _ _ (by rw [Eθ1_eq]; simp at h1; rw [h1]) hX (by simp [nD1]; linarith)]
  simp [Eθ1_eq] at h1 ⊢; rw [h1]; simp [nD1]; linarith

lemma inv_none {X c : ℝ} {μ : Belief1} (hμ : Admissible1 μ) (hX : 0 < X) :
    invest1 X c μ none = if 1 ≤ μ none true * X then 1 else 0 := by
  have hnn := (hμ none).1 true
  unfold invest1
  rw [exIcc_iff _ _ _ (by rw [Eθ1_eq]; exact hnn) hX (by simp [nD1])]
  simp [Eθ1_eq, nD1]

lemma pay_true_some {X c q bet : ℝ} {μ : Belief1} (hμ : Admissible1 μ) (hX : 0 < X) (hc : 0 < c)
    (hf : 1 + c ≤ X) : mgrPayoff1 X c q bet μ true (some true) = q * (X - 1 - c) + bet := by
  have hi := inv_some_true (c := c) hμ hX hc hf
  have h1 := (adm_some hμ true).1
  simp only [mgrPayoff1, share1, hi, if_true, Eθ1_eq, h1, th, nD1]
  simp
  field_simp
  ring

lemma pay_false_some {X c q bet : ℝ} {μ : Belief1} (hμ : Admissible1 μ) (hX : 0 < X) (hc : 0 < c) :
    mgrPayoff1 X c q bet μ false (some false) = 0 := by
  have hi := inv_some_false (c := c) hμ hX hc
  simp [mgrPayoff1, hi]

lemma pay_none {X c q bet : ℝ} {μ : Belief1} (hμ : Admissible1 μ) (hX : 0 < X) (t : Bool) :
    mgrPayoff1 X c q bet μ t none =
      if 1 ≤ μ none true * X then q * th t * (1 - 1 / (μ none true * X)) * X + bet else 0 := by
  have hi := inv_none (c := c) hμ hX
  split_ifs with h
  · rw [if_pos h] at hi
    simp [mgrPayoff1, share1, hi, Eθ1_eq, nD1]
  · rw [if_neg h] at hi
    simp [mgrPayoff1, hi]

lemma pay_none_nonneg {X c q bet : ℝ} {μ : Belief1} (hμ : Admissible1 μ) (hX : 0 < X)
    (hq : 0 < q) (hbet : q * X < bet) (t : Bool) : 0 ≤ mgrPayoff1 X c q bet μ t none := by
  rw [pay_none (c := c) hμ hX]
  split_ifs with h
  · have hr : 0 < μ none true * X := by linarith
    have : 0 ≤ 1 - 1 / (μ none true * X) := by
      rw [sub_nonneg, div_le_one hr]; exact h
    have hth : 0 ≤ th t := by cases t <;> simp [th]
    have : 0 ≤ q * th t * (1 - 1 / (μ none true * X)) * X := by positivity
    nlinarith
  · exact le_refl _

/-- Classification of the equilibria of a stand-alone firm. -/
lemma classify {p X c q bet : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (hX : 1 < X) (hc : 0 < c)
    (hq0 : 0 < q) (hbet : q * X < bet) (hf : 1 + c ≤ X)
    {σ : Bool → Bool} {μ : Belief1} (hE : IsEquilibrium1 p X c q bet σ μ) :
    σ false = false ∧
      ((σ true = true ∧ invest1 X c μ none = 0 ∧ efficiency1 p X c σ μ = p * (X - 1 - c)) ∨
       (σ true = false ∧ 1 ≤ p * (1 + c) ∧ invest1 X c μ none = 1 ∧
          efficiency1 p X c σ μ = p * X - 1)) := by
  obtain ⟨hA, hB, hIC, hT⟩ := hE
  have hX0 : 0 < X := by linarith
  have hf0 : σ false = false := by
    by_contra h
    simp only [Bool.not_eq_false] at h
    have := hT false h
    rw [h] at this
    simp only [m1, m0] at this
    rw [pay_false_some hA hX0 hc] at this
    have := pay_none_nonneg (c := c) hA hX0 hq0 hbet false
    linarith
  refine ⟨hf0, ?_⟩
  have hnone : ∃ t, msg1 t (σ t) = none := ⟨false, by simp [msg1, hf0]⟩
  have hBn := hB none hnone true
  cases ht : σ true
  · -- pooling
    right
    have hpm : pathMass1 p σ none = 1 := by
      simp [pathMass1, Fintype.sum_bool, msg1, ht, hf0, prior1]
    rw [hpm] at hBn
    have hr : μ none true = p := by simp [hBn, msg1, ht, prior1]
    have hic := hIC true true
    rw [ht] at hic
    simp only [m1, m0] at hic
    rw [pay_true_some hA hX0 hc hf, pay_none (c := c) hA hX0, hr] at hic
    have hpay : 0 < q * (X - 1 - c) + bet := by nlinarith
    split_ifs at hic with h1
    · have hpX : 0 < p * X := by linarith
      have key : q * (X - 1 - c) ≤ q * (X - 1 / p) := by
        have : q * th true * (1 - 1 / (p * X)) * X = q * (X - 1 / p) := by
          simp [th]; field_simp
        linarith
      have k2 : X - 1 - c ≤ X - 1 / p := le_of_mul_le_mul_left key hq0
      have k3 : 1 / p ≤ 1 + c := by linarith
      rw [div_le_iff₀ hp0] at k3
      have hinv : invest1 X c μ none = 1 := by rw [inv_none hA hX0, hr, if_pos h1]
      refine ⟨rfl, by linarith, hinv, ?_⟩
      simp [efficiency1, Fintype.sum_bool, ht, hf0, msg1, hinv, netCF1, th, prior1, nD1]
      ring
    · linarith
  · -- separating
    left
    have hr : μ none true = 0 := by simp [hBn, msg1, ht]
    have hinv : invest1 X c μ none = 0 := by rw [inv_none hA hX0, hr]; simp
    refine ⟨rfl, hinv, ?_⟩
    have hi1 := inv_some_true (c := c) hA hX0 hc hf
    simp [efficiency1, Fintype.sum_bool, ht, hf0, msg1, hinv, hi1, netCF1, th, prior1, nD1]
    all_goals (ring_nf; try simp)

/-- The separating belief. -/
noncomputable def muS : Belief1 := fun m t =>
  match m with
  | some b => if t = b then 1 else 0
  | none => if t then 0 else 1

/-- The pooling belief. -/
noncomputable def muP (p : ℝ) : Belief1 := fun m t =>
  match m with
  | some b => if t = b then 1 else 0
  | none => if t then p else 1 - p

lemma adm_muP {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) : Admissible1 (muP p) := by
  intro m
  cases m with
  | none =>
    refine ⟨?_, ?_, ?_⟩
    · intro t; cases t <;> simp [muP] <;> linarith
    · simp [muP, Fintype.sum_bool]
    · intro t _ b hb; cases hb
  | some b =>
    refine ⟨?_, ?_, ?_⟩
    · intro t; simp only [muP]; split_ifs <;> norm_num
    · cases b <;> simp [muP, Fintype.sum_bool]
    · intro t ht b' hb'
      simp only [Option.some.injEq] at hb'
      subst hb'
      simp only [muP] at ht
      by_contra h; exact ht (if_neg h)

lemma muS_eq : muS = muP 0 := by
  funext m t; cases m <;> cases t <;> simp [muS, muP]

lemma sep_eq {p X c q bet : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (hX : 1 < X) (hc : 0 < c)
    (hq0 : 0 < q) (hbet : q * X < bet) (hf : 1 + c ≤ X) :
    IsEquilibrium1 p X c q bet (fun b => b) muS ∧
      efficiency1 p X c (fun b => b) muS = p * (X - 1 - c) := by
  have hX0 : 0 < X := by linarith
  have hA : Admissible1 muS := by rw [muS_eq]; exact adm_muP le_rfl zero_le_one
  have hr : muS none true = 0 := by simp [muS]
  have hinv : invest1 X c muS none = 0 := by rw [inv_none hA hX0, hr]; simp
  have hi1 := inv_some_true (c := c) hA hX0 hc hf
  have hPt := pay_true_some (q := q) (bet := bet) hA hX0 hc hf
  have hPf := pay_false_some (q := q) (bet := bet) hA hX0 hc
  have hPn : ∀ t, mgrPayoff1 X c q bet muS t none = 0 := by
    intro t; rw [pay_none (c := c) hA hX0, hr]; simp
  have hpos : 0 < q * (X - 1 - c) + bet := by nlinarith
  refine ⟨⟨hA, ?_, ?_, ?_⟩, ?_⟩
  · rintro m ⟨t0, rfl⟩ t'
    have hq : (1:ℝ) - p ≠ 0 := by linarith
    have hq' : p - 1 ≠ 0 := by linarith
    cases t0 <;> cases t' <;> simp [msg1, pathMass1, Fintype.sum_bool, prior1, muS, hp0.ne', hq, hq']
  · intro t d
    cases t <;> cases d <;> simp only [m1, m0] <;>
      simp only [hPt, hPf, hPn] <;> linarith
  · intro t ht
    cases t
    · simp at ht
    · simp only [m1, m0, hPt, hPn]; exact hpos
  · simp [efficiency1, Fintype.sum_bool, msg1, hinv, hi1, netCF1, th, prior1, nD1]
    all_goals (ring_nf; try simp)

lemma pool_eq {p X c q bet : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (hX : 1 < X) (hc : 0 < c)
    (hq0 : 0 < q) (hbet : q * X < bet) (hf : 1 + c ≤ X) (hpc : 1 ≤ p * (1 + c)) :
    IsEquilibrium1 p X c q bet (fun _ => false) (muP p) ∧ invest1 X c (muP p) none = 1 ∧
      efficiency1 p X c (fun _ => false) (muP p) = p * X - 1 := by
  have hX0 : 0 < X := by linarith
  have hA : Admissible1 (muP p) := adm_muP hp0.le hp1.le
  have hr : muP p none true = p := by simp [muP]
  have hpX : 1 ≤ p * X := by nlinarith
  have hinv : invest1 X c (muP p) none = 1 := by rw [inv_none hA hX0, hr, if_pos hpX]
  have hPt := pay_true_some (q := q) (bet := bet) hA hX0 hc hf
  have hPf := pay_false_some (q := q) (bet := bet) hA hX0 hc
  have hPn : ∀ t, mgrPayoff1 X c q bet (muP p) t none = q * th t * (X - 1 / p) + bet := by
    intro t; rw [pay_none (c := c) hA hX0, hr, if_pos hpX]; field_simp
  have hk : X - 1 - c ≤ X - 1 / p := by
    have : 1 / p ≤ 1 + c := by rw [div_le_iff₀ hp0]; linarith
    linarith
  have hnn : 0 ≤ X - 1 / p := by
    have : 1 / p ≤ X := by rw [div_le_iff₀ hp0]; linarith
    linarith
  refine ⟨⟨hA, ?_, ?_, ?_⟩, hinv, ?_⟩
  · rintro m ⟨t0, rfl⟩ t'
    cases t' <;> simp [msg1, pathMass1, Fintype.sum_bool, prior1, muP]
  · intro t d
    cases t <;> cases d <;> simp only [m1, m0] <;>
      simp only [hPt, hPf, hPn, th, if_true, if_false, Bool.false_eq_true]
    all_goals nlinarith [mul_le_mul_of_nonneg_left hk hq0.le]
  · intro t ht; simp at ht
  · simp [efficiency1, Fintype.sum_bool, msg1, hinv, netCF1, th, prior1, nD1]
    ring

end IntCapP1

open IntCapP1 in
theorem solution (p X c q bet : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (hX : 1 < X) (hc : 0 < c)
    (hq0 : 0 < q) (hq1 : q < 1) (hbet : q * X < bet) (hfocus : 1 + c ≤ X) :
    (c < (1 - p) / p →
      IsGreatest (effSet1 p X c q bet) (p * (X - 1 - c)) ∧
      ∀ σ μ, IsEquilibrium1 p X c q bet σ μ →
        σ true = true ∧ σ false = false ∧
        invest1 X c μ (msg1 true true) = 1 ∧ invest1 X c μ (msg1 false false) = 0) ∧
    ((1 - p) / p ≤ c →
      IsGreatest (effSet1 p X c q bet) (p * X - 1) ∧
      (∃ μ, IsEquilibrium1 p X c q bet (fun _ => false) μ ∧ invest1 X c μ none = 1 ∧
        efficiency1 p X c (fun _ => false) μ = p * X - 1) ∧
      ((1 - p) / p < c → ∀ σ μ, IsEquilibrium1 p X c q bet σ μ →
        efficiency1 p X c σ μ = p * X - 1 →
          σ = (fun _ => false) ∧ invest1 X c μ none = 1)) := by
  have hX0 : 0 < X := by linarith
  obtain ⟨hSE, hSv⟩ := sep_eq hp0 hp1 hX hc hq0 hbet hfocus
  refine ⟨fun hcl => ?_, fun hcl => ?_⟩
  · rw [lt_div_iff₀ hp0] at hcl
    refine ⟨⟨⟨_, _, hSE, hSv.symm⟩, ?_⟩, ?_⟩
    · rintro v ⟨σ, μ, hE, rfl⟩
      rcases (classify hp0 hp1 hX hc hq0 hbet hfocus hE).2 with h | h
      · rw [h.2.2]
      · nlinarith [h.2.1]
    · intro σ μ hE
      obtain ⟨hf0, h | h⟩ := classify hp0 hp1 hX hc hq0 hbet hfocus hE
      · refine ⟨h.1, hf0, ?_, ?_⟩
        · exact inv_some_true hE.1 hX0 hc hfocus
        · simpa [msg1] using h.2.1
      · nlinarith [h.2.1]
  · rw [div_le_iff₀ hp0] at hcl
    have hpc : 1 ≤ p * (1 + c) := by linarith
    obtain ⟨hPE, hPi, hPv⟩ := pool_eq hp0 hp1 hX hc hq0 hbet hfocus hpc
    refine ⟨⟨⟨_, _, hPE, hPv.symm⟩, ?_⟩, ⟨_, hPE, hPi, hPv⟩, ?_⟩
    · rintro v ⟨σ, μ, hE, rfl⟩
      rcases (classify hp0 hp1 hX hc hq0 hbet hfocus hE).2 with h | h
      · rw [h.2.2]; nlinarith
      · rw [h.2.2.2]
    · intro hcs σ μ hE hv
      rw [div_lt_iff₀ hp0] at hcs
      obtain ⟨hf0, h | h⟩ := classify hp0 hp1 hX hc hq0 hbet hfocus hE
      · rw [h.2.2] at hv; nlinarith
      · refine ⟨?_, h.2.2.1⟩
        funext b; cases b
        · exact hf0
        · exact h.1
