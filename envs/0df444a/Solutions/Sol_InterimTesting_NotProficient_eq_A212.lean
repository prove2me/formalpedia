-- Prove2me | solution 1 for InterimTesting.NotProficient.eq_A212
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T14:19:56.243855+00:00
-- url     : https://prove2.me/submissions/5d51c78b-3749-45c8-af6f-945444d5af9e

import Mathlib
import Definitions.Def_InterimTesting_NotProficient_Model
import Theorems.Thm_InterimTesting_NotProficient_lemma_1

open InterimTesting.NotProficient

namespace ITNPAux

/-- second-period value as explicit max -/
lemma J1_eq (θ : Params) (hθ : θ.Standing) (π p : ℝ) (hπ : 0 ≤ π)
    (hp : p ∈ Set.Icc (0 : ℝ) 1) :
    J1 θ π p = π * θ.B * (θ.μ + (1 - θ.μ) * p)
      + max 0 (π * θ.A * (θ.μ + (1 - θ.μ) * p) - 1) := by
  obtain ⟨hA, hB, hAB, hμ0, hμ1, hb0, hba, ha1⟩ := hθ
  obtain ⟨hp0, hp1⟩ := hp
  have hq : 0 < θ.μ + (1 - θ.μ) * p := by nlinarith
  have hAq : 0 < θ.A * ((1 - θ.μ) * p + θ.μ) := by nlinarith
  have hiff : T1p θ p ≤ π ↔ 0 ≤ π * θ.A * (θ.μ + (1 - θ.μ) * p) - 1 := by
    unfold T1p
    rw [div_le_iff₀ hAq]
    constructor <;> intro h <;> nlinarith
  unfold J1
  rw [lemma_1 θ ⟨hA, hB, hAB, hμ0, hμ1, hb0, hba, ha1⟩ π p hπ ⟨hp0, hp1⟩]
  by_cases h : T1p θ p ≤ π
  · rw [if_pos h, max_eq_right (hiff.mp h)]
    simp only [obj1, finalP, toP]
    ring
  · rw [if_neg h, max_eq_left (le_of_lt (not_le.mp (fun h' => h (hiff.mpr h'))))]
    simp only [obj1, finalP, toP]
    ring

/-- `obs * J1 (jP / obs)` as explicit max. -/
lemma term_eq (θ : Params) (hθ : θ.Standing) (π obs jP : ℝ) (hπ : 0 ≤ π)
    (hj0 : 0 ≤ jP) (hjo : jP ≤ obs) :
    obs * J1 θ π (jP / obs) = π * θ.B * (θ.μ * obs + (1 - θ.μ) * jP)
      + max 0 (π * θ.A * (θ.μ * obs + (1 - θ.μ) * jP) - obs) := by
  have hobs : 0 ≤ obs := le_trans hj0 hjo
  rcases eq_or_lt_of_le hobs with h0 | hpos
  · subst h0
    have : jP = 0 := le_antisymm hjo hj0
    subst this
    simp
  · have hp : jP / obs ∈ Set.Icc (0 : ℝ) 1 :=
      ⟨div_nonneg hj0 hobs, div_le_one_of_le₀ hjo hobs⟩
    rw [J1_eq θ hθ π _ hπ hp]
    have hmul : obs * (jP / obs) = jP := by field_simp
    rw [mul_add, mul_max_of_nonneg _ _ hobs, mul_zero,
      show obs * (π * θ.B * (θ.μ + (1 - θ.μ) * (jP / obs))) =
        π * θ.B * (θ.μ * obs + (1 - θ.μ) * (obs * (jP / obs))) by ring,
      show obs * (π * θ.A * (θ.μ + (1 - θ.μ) * (jP / obs)) - 1) =
        π * θ.A * (θ.μ * obs + (1 - θ.μ) * (obs * (jP / obs))) - obs by ring, hmul]

noncomputable def LP (θ : Params) (a b π m : ℝ) : ℝ :=
  π * θ.A * (θ.μ * (a * m + b * (1 - m)) + (1 - θ.μ) * (m * a)) - (a * m + b * (1 - m))

noncomputable def LN (θ : Params) (a b π m : ℝ) : ℝ :=
  π * θ.A * (θ.μ * ((1 - a) * m + (1 - b) * (1 - m)) + (1 - θ.μ) * (m * (1 - a)))
    - ((1 - a) * m + (1 - b) * (1 - m))

noncomputable def G (θ : Params) (a b π e : ℝ) : ℝ :=
  π * θ.B * (θ.μ + (1 - θ.μ) * (θ.μ * (θ.A * e + θ.B)))
    + max 0 (LP θ a b π (θ.μ * (θ.A * e + θ.B)))
    + max 0 (LN θ a b π (θ.μ * (θ.A * e + θ.B))) - e

lemma acc_bounds (θ : Params) (hθ : θ.Standing) (zI : Bool) :
    0 < (acc θ zI).1 ∧ (acc θ zI).1 ≤ 1 ∧ 0 ≤ (acc θ zI).2 ∧ (acc θ zI).2 ≤ (acc θ zI).1
      ∧ (acc θ zI).2 < 1 := by
  obtain ⟨hA, hB, hAB, hμ0, hμ1, hb0, hba, ha1⟩ := hθ
  cases zI <;> simp [acc] <;> refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> linarith

lemma m_bounds (θ : Params) (hθ : θ.Standing) (e : ℝ) (he : e ∈ Set.Icc (0 : ℝ) 1) :
    0 ≤ toP θ .N e ∧ toP θ .N e < 1 := by
  obtain ⟨hA, hB, hAB, hμ0, hμ1, hb0, hba, ha1⟩ := hθ
  obtain ⟨he0, he1⟩ := he
  simp only [toP]
  have h1 : θ.A * e + θ.B ≤ 1 := by nlinarith
  constructor
  · positivity
  · nlinarith [mul_le_mul_of_nonneg_left h1 hμ0.le]

lemma obj0_eq (θ : Params) (hθ : θ.Standing) (zI : Bool) (π e : ℝ) (hπ : 0 ≤ π)
    (he : e ∈ Set.Icc (0 : ℝ) 1) :
    obj0 θ zI .N π e = G θ (acc θ zI).1 (acc θ zI).2 π e := by
  obtain ⟨ha0, ha1, hb0, hba, hb1⟩ := acc_bounds θ hθ zI
  obtain ⟨hm0, hm1⟩ := m_bounds θ hθ e he
  set a := (acc θ zI).1
  set b := (acc θ zI).2
  set m := toP θ .N e with hm
  unfold obj0 post
  have hoP : obsProb θ zI .N e .P = a * m + b * (1 - m) := by
    simp [obsProb, joint, sig, a, b, m]; ring
  have hoN : obsProb θ zI .N e .N = (1 - a) * m + (1 - b) * (1 - m) := by
    simp [obsProb, joint, sig, a, b, m]; ring
  have hjP : joint θ zI .N e .P .P = m * a := by simp [joint, sig, a, m]
  have hjN : joint θ zI .N e .P .N = m * (1 - a) := by simp [joint, sig, a, m]
  rw [hoP, hoN, hjP, hjN]
  rw [term_eq θ hθ π _ _ hπ (by positivity) (by nlinarith),
    term_eq θ hθ π _ _ hπ (by nlinarith) (by nlinarith)]
  unfold G LP LN
  have : m = θ.μ * (θ.A * e + θ.B) := by simp [m, toP]
  rw [← this]
  ring

lemma max0_convex (u v e : ℝ) (he : e ∈ Set.Icc (0 : ℝ) 1) :
    max 0 ((1 - e) * u + e * v) ≤ (1 - e) * max 0 u + e * max 0 v := by
  obtain ⟨he0, he1⟩ := he
  have h1 : 0 ≤ (1 - e) * max 0 u := mul_nonneg (by linarith) (le_max_left _ _)
  have h2 : 0 ≤ e * max 0 v := mul_nonneg he0 (le_max_left _ _)
  have h3 : (1 - e) * u ≤ (1 - e) * max 0 u :=
    mul_le_mul_of_nonneg_left (le_max_right _ _) (by linarith)
  have h4 : e * v ≤ e * max 0 v := mul_le_mul_of_nonneg_left (le_max_right _ _) he0
  apply max_le <;> linarith

lemma G_convex (θ : Params) (a b π e : ℝ) (he : e ∈ Set.Icc (0 : ℝ) 1) :
    G θ a b π e ≤ (1 - e) * G θ a b π 0 + e * G θ a b π 1 := by
  have hP : LP θ a b π (θ.μ * (θ.A * e + θ.B)) =
      (1 - e) * LP θ a b π (θ.μ * (θ.A * 0 + θ.B)) + e * LP θ a b π (θ.μ * (θ.A * 1 + θ.B)) := by
    unfold LP; ring
  have hN : LN θ a b π (θ.μ * (θ.A * e + θ.B)) =
      (1 - e) * LN θ a b π (θ.μ * (θ.A * 0 + θ.B)) + e * LN θ a b π (θ.μ * (θ.A * 1 + θ.B)) := by
    unfold LN; ring
  have c1 := max0_convex (LP θ a b π (θ.μ * (θ.A * 0 + θ.B)))
    (LP θ a b π (θ.μ * (θ.A * 1 + θ.B))) e he
  have c2 := max0_convex (LN θ a b π (θ.μ * (θ.A * 0 + θ.B)))
    (LN θ a b π (θ.μ * (θ.A * 1 + θ.B))) e he
  unfold G
  rw [hP, hN]
  nlinarith

lemma sSup_argmax (f : ℝ → ℝ)
    (hf : ∀ e ∈ Set.Icc (0 : ℝ) 1, f e ≤ (1 - e) * f 0 + e * f 1) :
    sSup {e | e ∈ Set.Icc (0 : ℝ) 1 ∧ ∀ e' ∈ Set.Icc (0 : ℝ) 1, f e' ≤ f e}
      = if f 0 ≤ f 1 then 1 else 0 := by
  split_ifs with h
  · apply IsGreatest.csSup_eq
    refine ⟨⟨⟨zero_le_one, le_refl _⟩, fun e' he' => ?_⟩, fun e he => he.1.2⟩
    have := hf e' he'
    obtain ⟨h0, h1⟩ := he'
    nlinarith
  · apply IsGreatest.csSup_eq
    push Not at h
    refine ⟨⟨⟨le_refl _, zero_le_one⟩, fun e' he' => ?_⟩, fun e he => ?_⟩
    · have := hf e' he'
      obtain ⟨h0, h1⟩ := he'
      nlinarith
    · obtain ⟨⟨h0, h1⟩, hmax⟩ := he
      have h2 := hmax 0 ⟨le_refl _, zero_le_one⟩
      have h3 := hf e ⟨h0, h1⟩
      nlinarith

lemma e0Star_eq (θ : Params) (hθ : θ.Standing) (zI : Bool) (π : ℝ) (hπ : 0 ≤ π) :
    e0Star θ zI .N π = if G θ (acc θ zI).1 (acc θ zI).2 π 0
      ≤ G θ (acc θ zI).1 (acc θ zI).2 π 1 then 1 else 0 := by
  unfold e0Star
  have h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨le_refl _, zero_le_one⟩
  have h1 : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨zero_le_one, le_refl _⟩
  rw [sSup_argmax (obj0 θ zI .N π) (fun e he => by
    rw [obj0_eq θ hθ zI π e hπ he, obj0_eq θ hθ zI π 0 hπ h0, obj0_eq θ hθ zI π 1 hπ h1]
    exact G_convex θ _ _ π e he)]
  rw [obj0_eq θ hθ zI π 0 hπ h0, obj0_eq θ hθ zI π 1 hπ h1]

lemma LP_nonneg (θ : Params) (a b π m : ℝ) (hA : 0 < θ.A) (hμ0 : 0 < θ.μ) (hμ1 : θ.μ < 1)
    (ha0 : 0 < a) (hb0 : 0 ≤ b) (hπ : 0 ≤ π) (hm0 : 0 ≤ m) (hm1 : m ≤ 1)
    (hbig : 1 ≤ π * θ.A * θ.μ) : 0 ≤ LP θ a b π m := by
  have e : LP θ a b π m = (π * θ.A * θ.μ - 1) * (a * m + b * (1 - m))
      + π * θ.A * (1 - θ.μ) * (m * a) := by unfold LP; ring
  rw [e]
  have h1 : 0 ≤ a * m + b * (1 - m) := by
    have : 0 ≤ b * (1 - m) := mul_nonneg hb0 (by linarith)
    have : 0 ≤ a * m := mul_nonneg ha0.le hm0
    linarith
  have h2 : 0 ≤ π * θ.A * (1 - θ.μ) * (m * a) := by
    have : 0 ≤ π * θ.A := mul_nonneg hπ hA.le
    have : 0 ≤ π * θ.A * (1 - θ.μ) := mul_nonneg this (by linarith)
    exact mul_nonneg this (mul_nonneg hm0 ha0.le)
  have h3 := mul_nonneg (sub_nonneg.mpr hbig) h1
  linarith

lemma LN_nonneg (θ : Params) (a b π m : ℝ) (hA : 0 < θ.A) (hμ0 : 0 < θ.μ) (hμ1 : θ.μ < 1)
    (ha1 : a ≤ 1) (hb1 : b < 1) (hπ : 0 ≤ π) (hm0 : 0 ≤ m) (hm1 : m ≤ 1)
    (hbig : 1 ≤ π * θ.A * θ.μ) : 0 ≤ LN θ a b π m := by
  have e : LN θ a b π m = LP θ (1 - a) (1 - b) π m := by unfold LN LP; ring
  rw [e]
  have e2 : LP θ (1 - a) (1 - b) π m = (π * θ.A * θ.μ - 1) * ((1 - a) * m + (1 - b) * (1 - m))
      + π * θ.A * (1 - θ.μ) * (m * (1 - a)) := by unfold LP; ring
  rw [e2]
  have h1 : 0 ≤ (1 - a) * m + (1 - b) * (1 - m) := by
    have : 0 ≤ (1 - b) * (1 - m) := mul_nonneg (by linarith) (by linarith)
    have : 0 ≤ (1 - a) * m := mul_nonneg (by linarith) hm0
    linarith
  have h2 : 0 ≤ π * θ.A * (1 - θ.μ) * (m * (1 - a)) := by
    have : 0 ≤ π * θ.A := mul_nonneg hπ hA.le
    have : 0 ≤ π * θ.A * (1 - θ.μ) := mul_nonneg this (by linarith)
    exact mul_nonneg this (mul_nonneg hm0 (by linarith))
  have h3 := mul_nonneg (sub_nonneg.mpr hbig) h1
  linarith

lemma LP_pos_of_LN_pos (θ : Params) (a b π m : ℝ) (ha0 : 0 < a) (ha1 : a ≤ 1) (hba : b ≤ a)
    (hm1 : m ≤ 1) (hsmall : π * θ.A * θ.μ ≤ 1) (hN : 0 < LN θ a b π m) :
    0 < LP θ a b π m := by
  have e : (1 - a) * LP θ a b π m - a * LN θ a b π m
      = (1 - π * θ.A * θ.μ) * (1 - m) * (a - b) := by unfold LP LN; ring
  have h1 : 0 ≤ (1 - π * θ.A * θ.μ) * (1 - m) * (a - b) :=
    mul_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith)
  have h2 : 0 < a * LN θ a b π m := mul_pos ha0 hN
  have h3 : 0 < (1 - a) * LP θ a b π m := by linarith
  rcases eq_or_lt_of_le ha1 with h | h
  · subst h; simp at h3
  · exact pos_of_mul_pos_right h3 (by linarith)

lemma G_sign (θ : Params) (hθ : θ.Standing) (a b π : ℝ) (ha0 : 0 < a) (ha1 : a ≤ 1)
    (hb0 : 0 ≤ b) (hba : b ≤ a) (hb1 : b < 1) (hπ : 0 ≤ π) :
    G θ a b π 0 ≤ G θ a b π 1 ↔
      1 ≤ π * (θ.μ * (1 - θ.μ) * θ.A * (θ.A + θ.B)) := by
  obtain ⟨hA, hB, hAB, hμ0, hμ1, -, -, -⟩ := hθ
  set m0 := θ.μ * (θ.A * 0 + θ.B) with hm0
  set m1 := θ.μ * (θ.A * 1 + θ.B) with hm1
  have hm0a : 0 ≤ m0 := by rw [hm0]; positivity
  have hm0b : m0 ≤ 1 := by rw [hm0]; nlinarith
  have hm1a : 0 ≤ m1 := by rw [hm1]; positivity
  have hm1b : m1 ≤ 1 := by rw [hm1]; nlinarith
  have hsum : ∀ m, LP θ a b π m + LN θ a b π m = π * θ.A * (θ.μ + (1 - θ.μ) * m) - 1 := by
    intro m; unfold LP LN; ring
  have hK : π * (θ.μ * (1 - θ.μ) * θ.A * (θ.A + θ.B)) ≤ π * θ.A * θ.μ := by
    have : (1 - θ.μ) * (θ.A + θ.B) ≤ 1 := by nlinarith
    have hp : 0 ≤ π * θ.A * θ.μ := by positivity
    nlinarith [mul_le_mul_of_nonneg_left this hp]
  have hdiff : m1 - m0 = θ.μ * θ.A := by rw [hm0, hm1]; ring
  unfold G
  rw [← hm0, ← hm1]
  by_cases hbig : 1 ≤ π * θ.A * θ.μ
  · rw [max_eq_right (LP_nonneg θ a b π m0 hA hμ0 hμ1 ha0 hb0 hπ hm0a hm0b hbig),
      max_eq_right (LP_nonneg θ a b π m1 hA hμ0 hμ1 ha0 hb0 hπ hm1a hm1b hbig),
      max_eq_right (LN_nonneg θ a b π m0 hA hμ0 hμ1 ha1 hb1 hπ hm0a hm0b hbig),
      max_eq_right (LN_nonneg θ a b π m1 hA hμ0 hμ1 ha1 hb1 hπ hm1a hm1b hbig)]
    have e : π * θ.B * (θ.μ + (1 - θ.μ) * m1) + LP θ a b π m1 + LN θ a b π m1 - 1
        - (π * θ.B * (θ.μ + (1 - θ.μ) * m0) + LP θ a b π m0 + LN θ a b π m0 - 0)
        = π * (θ.μ * (1 - θ.μ) * θ.A * (θ.A + θ.B)) - 1 := by
      have := hsum m0; have := hsum m1
      rw [hm0, hm1] at *; nlinarith
    constructor <;> intro h <;> linarith
  · push Not at hbig
    have hKlt : π * (θ.μ * (1 - θ.μ) * θ.A * (θ.A + θ.B)) < 1 := lt_of_le_of_lt hK hbig
    have hdN : 0 ≤ LN θ a b π m1 - LN θ a b π m0 := by
      have e : LN θ a b π m1 - LN θ a b π m0 = (m1 - m0) * ((a - b) * (1 - π * θ.A * θ.μ)
          + π * θ.A * (1 - θ.μ) * (1 - a)) := by unfold LN; ring
      rw [e, hdiff]
      have : 0 ≤ π * θ.A * (1 - θ.μ) * (1 - a) :=
        mul_nonneg (mul_nonneg (mul_nonneg hπ hA.le) (by linarith)) (by linarith)
      have : 0 ≤ (a - b) * (1 - π * θ.A * θ.μ) := mul_nonneg (by linarith) (by linarith)
      positivity
    have hS : (LP θ a b π m1 + LN θ a b π m1) - (LP θ a b π m0 + LN θ a b π m0)
        = π * θ.A * (1 - θ.μ) * (θ.μ * θ.A) := by
      rw [hsum, hsum, ← hdiff]; ring
    have hBpart : π * θ.B * (θ.μ + (1 - θ.μ) * m1) - π * θ.B * (θ.μ + (1 - θ.μ) * m0)
        = π * θ.B * (1 - θ.μ) * (θ.μ * θ.A) := by rw [← hdiff]; ring
    have hKe : π * (θ.μ * (1 - θ.μ) * θ.A * (θ.A + θ.B))
        = π * θ.A * (1 - θ.μ) * (θ.μ * θ.A) + π * θ.B * (1 - θ.μ) * (θ.μ * θ.A) := by ring
    have hlt : π * θ.B * (θ.μ + (1 - θ.μ) * m1) + max 0 (LP θ a b π m1)
        + max 0 (LN θ a b π m1) - 1 <
        π * θ.B * (θ.μ + (1 - θ.μ) * m0) + max 0 (LP θ a b π m0)
        + max 0 (LN θ a b π m0) - 0 := by
      have p0 := le_max_left 0 (LP θ a b π m0)
      have p0' := le_max_right 0 (LP θ a b π m0)
      have n0 := le_max_left 0 (LN θ a b π m0)
      have n0' := le_max_right 0 (LN θ a b π m0)
      by_cases hN1 : LN θ a b π m1 ≤ 0
      · rw [max_eq_left hN1]
        have : max 0 (LP θ a b π m1) ≤ max 0 (LP θ a b π m0)
            + π * θ.A * (1 - θ.μ) * (θ.μ * θ.A) := by
          have hpos : 0 ≤ π * θ.A * (1 - θ.μ) * (θ.μ * θ.A) := by
            have : 0 ≤ 1 - θ.μ := by linarith
            positivity
          apply max_le <;> linarith
        linarith
      · push Not at hN1
        have hP1 := LP_pos_of_LN_pos θ a b π m1 ha0 ha1 hba hm1b hbig.le hN1
        rw [max_eq_right hP1.le, max_eq_right hN1.le]
        linarith
    constructor
    · intro h; linarith
    · intro h; linarith

lemma T0N_le_iff (θ : Params) (hθ : θ.Standing) (π : ℝ) :
    T0N θ ≤ π ↔ 1 ≤ π * (θ.μ * (1 - θ.μ) * θ.A * (θ.A + θ.B)) := by
  obtain ⟨hA, hB, hAB, hμ0, hμ1, -, -, -⟩ := hθ
  have hD : 0 < θ.μ * (1 - θ.μ) * θ.A * (θ.A + θ.B) := by
    have : 0 < 1 - θ.μ := by linarith
    have : 0 < θ.A + θ.B := by linarith
    positivity
  unfold T0N
  rw [div_le_iff₀ hD]

theorem e0Star_closed (θ : Params) (hθ : θ.Standing) (zI : Bool) (π : ℝ) (hπ : 0 ≤ π) :
    e0Star θ zI .N π = if T0N θ ≤ π then 1 else 0 := by
  obtain ⟨ha0, ha1, hb0, hba, hb1⟩ := acc_bounds θ hθ zI
  rw [e0Star_eq θ hθ zI π hπ]
  have := G_sign θ hθ _ _ π ha0 ha1 hb0 hba hb1 hπ
  rw [← T0N_le_iff θ hθ π] at this
  by_cases h : T0N θ ≤ π
  · rw [if_pos h, if_pos (this.mpr h)]
  · rw [if_neg h, if_neg (fun h' => h (this.mp h'))]

lemma post_mem (θ : Params) (hθ : θ.Standing) (zI : Bool) (e : ℝ)
    (he : e ∈ Set.Icc (0 : ℝ) 1) (x : Prof) : post θ zI .N e x ∈ Set.Icc (0 : ℝ) 1 := by
  obtain ⟨ha0, ha1, hb0, hba, hb1⟩ := acc_bounds θ hθ zI
  obtain ⟨hm0, hm1⟩ := m_bounds θ hθ e he
  unfold post
  cases x
  · have hoP : obsProb θ zI .N e .P = (acc θ zI).1 * toP θ .N e
        + (acc θ zI).2 * (1 - toP θ .N e) := by
      simp [obsProb, joint, sig]; ring
    have hjP : joint θ zI .N e .P .P = toP θ .N e * (acc θ zI).1 := by simp [joint, sig]
    rw [hoP, hjP]
    exact ⟨div_nonneg (by positivity) (by nlinarith),
      div_le_one_of_le₀ (by nlinarith) (by nlinarith)⟩
  · have hoN : obsProb θ zI .N e .N = (1 - (acc θ zI).1) * toP θ .N e
        + (1 - (acc θ zI).2) * (1 - toP θ .N e) := by
      simp [obsProb, joint, sig]; ring
    have hjN : joint θ zI .N e .P .N = toP θ .N e * (1 - (acc θ zI).1) := by simp [joint, sig]
    rw [hoN, hjN]
    exact ⟨div_nonneg (by nlinarith) (by nlinarith),
      div_le_one_of_le₀ (by nlinarith) (by nlinarith)⟩

lemma e1_ind (θ : Params) (hθ : θ.Standing) (zI : Bool) (π e : ℝ) (hπ : 0 ≤ π)
    (he : e ∈ Set.Icc (0 : ℝ) 1) (x : Prof) :
    e1Star θ π (post θ zI .N e x) = if T1 θ zI .N e x ≤ π then 1 else 0 := by
  rw [lemma_1 θ hθ π _ hπ (post_mem θ hθ zI e he x)]
  rfl

lemma fc_P (θ : Params) (hθ : θ.Standing) (zI : Bool) (π e : ℝ) (hπ : 0 ≤ π)
    (he : e ∈ Set.Icc (0 : ℝ) 1) :
    finalContrib θ zI .N π e .P =
      (θ.A * (if T1 θ zI .N e .P ≤ π then 1 else 0) + θ.B) *
        (θ.μ * ((acc θ zI).1 * (θ.μ * (θ.A * e + θ.B))
          + (acc θ zI).2 * (1 - θ.μ * (θ.A * e + θ.B)))
         + (1 - θ.μ) * ((θ.μ * (θ.A * e + θ.B)) * (acc θ zI).1)) := by
  unfold finalContrib
  simp only
  rw [e1_ind θ hθ zI π e hπ he .P]
  simp only [joint, sig, toP]
  ring

lemma fc_N (θ : Params) (hθ : θ.Standing) (zI : Bool) (π e : ℝ) (hπ : 0 ≤ π)
    (he : e ∈ Set.Icc (0 : ℝ) 1) :
    finalContrib θ zI .N π e .N =
      (θ.A * (if T1 θ zI .N e .N ≤ π then 1 else 0) + θ.B) *
        (θ.μ * ((1 - (acc θ zI).1) * (θ.μ * (θ.A * e + θ.B))
          + (1 - (acc θ zI).2) * (1 - θ.μ * (θ.A * e + θ.B)))
         + (1 - θ.μ) * ((θ.μ * (θ.A * e + θ.B)) * (1 - (acc θ zI).1))) := by
  unfold finalContrib
  simp only
  rw [e1_ind θ hθ zI π e hπ he .N]
  simp only [joint, sig, toP]
  ring

lemma post_N_le_P (θ : Params) (hθ : θ.Standing) (zI : Bool) (e : ℝ)
    (he : e ∈ Set.Icc (0 : ℝ) 1) : post θ zI .N e .N ≤ post θ zI .N e .P := by
  obtain ⟨ha0, ha1, hb0, hba, hb1⟩ := acc_bounds θ hθ zI
  obtain ⟨hm0, hm1⟩ := m_bounds θ hθ e he
  set a := (acc θ zI).1
  set b := (acc θ zI).2
  set m := toP θ .N e
  unfold post
  have hoP : obsProb θ zI .N e .P = a * m + b * (1 - m) := by
    simp [obsProb, joint, sig, a, b, m]; ring
  have hoN : obsProb θ zI .N e .N = (1 - a) * m + (1 - b) * (1 - m) := by
    simp [obsProb, joint, sig, a, b, m]; ring
  have hjP : joint θ zI .N e .P .P = m * a := by simp [joint, sig, a, m]
  have hjN : joint θ zI .N e .P .N = m * (1 - a) := by simp [joint, sig, a, m]
  rw [hoP, hoN, hjP, hjN]
  have hNpos : 0 < (1 - a) * m + (1 - b) * (1 - m) := by nlinarith
  rcases eq_or_lt_of_le (show 0 ≤ a * m + b * (1 - m) by nlinarith) with h | h
  · have hm : m = 0 := by nlinarith
    rw [hm]; simp
  · rw [div_le_div_iff₀ hNpos h]
    nlinarith [mul_nonneg (mul_nonneg hm0 (by linarith : (0:ℝ) ≤ 1 - m)) (by linarith : (0:ℝ) ≤ a - b)]

lemma T1p_anti (θ : Params) (hθ : θ.Standing) (p q : ℝ) (hp : 0 ≤ p) (hpq : p ≤ q) :
    T1p θ q ≤ T1p θ p := by
  obtain ⟨hA, hB, hAB, hμ0, hμ1, -, -, -⟩ := hθ
  unfold T1p
  have h1 : 0 ≤ (1 - θ.μ) * p := mul_nonneg (by linarith) hp
  have h2 : (1 - θ.μ) * p ≤ (1 - θ.μ) * q := mul_le_mul_of_nonneg_left hpq (by linarith)
  apply one_div_le_one_div_of_le
  · exact mul_pos hA (by linarith)
  · exact mul_le_mul_of_nonneg_left (by linarith) hA.le

lemma T1p_le (θ : Params) (hθ : θ.Standing) (p : ℝ) (hp : 0 ≤ p) :
    T1p θ p ≤ 1 / (θ.μ * θ.A) := by
  have := T1p_anti θ hθ 0 p le_rfl hp
  unfold T1p at *
  simpa [mul_comm] using this

lemma inv_muA_le_T0N (θ : Params) (hθ : θ.Standing) : 1 / (θ.μ * θ.A) ≤ T0N θ := by
  obtain ⟨hA, hB, hAB, hμ0, hμ1, -, -, -⟩ := hθ
  unfold T0N
  apply one_div_le_one_div_of_le
  · have : 0 < 1 - θ.μ := by linarith
    have : 0 < θ.A + θ.B := by linarith
    positivity
  · have : (1 - θ.μ) * (θ.A + θ.B) ≤ 1 := by nlinarith
    have hp : 0 < θ.μ * θ.A := by positivity
    nlinarith [mul_le_mul_of_nonneg_left this hp.le]

theorem PrStar_closed (θ : Params) (hθ : θ.Standing) (zI : Bool)
    (π : ℝ) (hπ : 0 ≤ π) :
    PrStar θ zI .N π =
      if π < T1 θ zI .N 0 .P then θ.μ * θ.B * (1 + (1 - θ.μ) * θ.B)
      else if π < T1 θ zI .N 0 .N then
        θ.μ * (θ.B * (θ.A * (acc θ zI).1 + θ.B)
          + (1 - θ.μ * θ.B) * (θ.A * (acc θ zI).2 + θ.B))
      else if π < T0N θ then θ.μ * (θ.A + θ.B) * (1 + (1 - θ.μ) * θ.B)
      else θ.μ * (θ.A + θ.B) * (1 + (1 - θ.μ) * (θ.A + θ.B)) := by
  have h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨le_refl _, zero_le_one⟩
  have h1 : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨zero_le_one, le_refl _⟩
  have hPN : T1 θ zI .N 0 .P ≤ T1 θ zI .N 0 .N :=
    T1p_anti θ hθ _ _ (post_mem θ hθ zI 0 h0 .N).1 (post_N_le_P θ hθ zI 0 h0)
  have hNT : T1 θ zI .N 0 .N ≤ T0N θ :=
    le_trans (T1p_le θ hθ _ (post_mem θ hθ zI 0 h0 .N).1) (inv_muA_le_T0N θ hθ)
  unfold PrStar
  rw [e0Star_closed θ hθ zI π hπ]
  by_cases hT : T0N θ ≤ π
  · rw [if_pos hT, fc_P θ hθ zI π 1 hπ h1, fc_N θ hθ zI π 1 hπ h1]
    have hP1 : T1 θ zI .N 1 .P ≤ π := le_trans (le_trans (T1p_le θ hθ _
      (post_mem θ hθ zI 1 h1 .P).1) (inv_muA_le_T0N θ hθ)) hT
    have hN1 : T1 θ zI .N 1 .N ≤ π := le_trans (le_trans (T1p_le θ hθ _
      (post_mem θ hθ zI 1 h1 .N).1) (inv_muA_le_T0N θ hθ)) hT
    rw [if_pos hP1, if_pos hN1, if_neg (by linarith), if_neg (by linarith), if_neg (by linarith)]
    ring
  · rw [if_neg hT, fc_P θ hθ zI π 0 hπ h0, fc_N θ hθ zI π 0 hπ h0]
    push Not at hT
    by_cases hP : T1 θ zI .N 0 .P ≤ π
    · by_cases hN : T1 θ zI .N 0 .N ≤ π
      · rw [if_pos hP, if_pos hN, if_neg (by linarith), if_neg (by linarith), if_pos hT]
        ring
      · push Not at hN
        rw [if_pos hP, if_neg (by linarith), if_neg (by linarith), if_pos hN]
        ring
    · push Not at hP
      rw [if_neg (by linarith), if_neg (by linarith), if_pos hP]
      ring

/-- value set of the district's problem for a step response -/
lemma opt4 (f : ℝ → ℝ) (t1 t2 t3 v1 v2 v3 v4 M : ℝ) (ht1 : 0 < t1) (ht12 : t1 < t2)
    (ht23 : t2 < t3) (hv1 : 0 ≤ v1) (hv12 : v1 < v2) (hv23 : v2 < v3) (hv34 : v3 < v4)
    (hf : ∀ π, 0 ≤ π → f π = if π < t1 then v1 else if π < t2 then v2
      else if π < t3 then v3 else v4)
    (hM : 0 ≤ M) (hH12 : t1 * v2 ≤ t2 * v3) (hH23 : t2 * v3 ≤ t3 * v4) :
    sSup {q | ∃ π : ℝ, 0 ≤ π ∧ π * f π ≤ M ∧ q = f π} =
        (if M < t1 * v2 then v1 else if M < t2 * v3 then v2
          else if M < t3 * v4 then v3 else v4) ∧
      IsLeast {π | 0 ≤ π ∧ π * f π ≤ M ∧ f π = sSup {q | ∃ π : ℝ, 0 ≤ π ∧ π * f π ≤ M ∧ q = f π}}
        (if M < t1 * v2 then 0 else if M < t2 * v3 then t1
          else if M < t3 * v4 then t2 else t3) := by
  have f0 : f 0 = v1 := by rw [hf 0 le_rfl, if_pos ht1]
  have f1 : f t1 = v2 := by rw [hf t1 ht1.le, if_neg (lt_irrefl _), if_pos ht12]
  have f2 : f t2 = v3 := by
    rw [hf t2 (by linarith), if_neg (by linarith), if_neg (lt_irrefl _), if_pos ht23]
  have f3 : f t3 = v4 := by
    rw [hf t3 (by linarith), if_neg (by linarith), if_neg (by linarith), if_neg (lt_irrefl _)]
  set w := (if M < t1 * v2 then v1 else if M < t2 * v3 then v2
          else if M < t3 * v4 then v3 else v4) with hw
  set τ := (if M < t1 * v2 then 0 else if M < t2 * v3 then t1
          else if M < t3 * v4 then t2 else t3) with hτ
  have hτmem : 0 ≤ τ ∧ τ * f τ ≤ M ∧ f τ = w := by
    rw [hτ, hw]
    split_ifs with h1 h2 h3
    · exact ⟨le_rfl, by rw [f0]; linarith, f0⟩
    · exact ⟨ht1.le, by rw [f1]; linarith, f1⟩
    · exact ⟨by linarith, by rw [f2]; linarith, f2⟩
    · exact ⟨by linarith, by rw [f3]; linarith, f3⟩
  have hub : ∀ π, 0 ≤ π → π * f π ≤ M → f π ≤ w ∧ (f π = w → τ ≤ π) := by
    intro π hπ hb
    rw [hf π hπ] at hb ⊢
    rw [hw, hτ]
    split_ifs at hb ⊢ <;>
      first
      | exact ⟨le_rfl, fun _ => by linarith⟩
      | exact ⟨by linarith, fun h => by linarith⟩
      | (exfalso; nlinarith)
  have hsup : sSup {q | ∃ π : ℝ, 0 ≤ π ∧ π * f π ≤ M ∧ q = f π} = w := by
    apply IsGreatest.csSup_eq
    refine ⟨⟨τ, hτmem.1, hτmem.2.1, hτmem.2.2.symm⟩, ?_⟩
    rintro q ⟨π, hπ, hb, rfl⟩
    exact (hub π hπ hb).1
  refine ⟨hsup, ?_, ?_⟩
  · rw [hsup]; exact hτmem
  · rintro π ⟨hπ, hb, heq⟩
    rw [hsup] at heq
    exact (hub π hπ hb).2 heq

lemma opt3 (f : ℝ → ℝ) (t1 t2 v1 v2 v3 M : ℝ) (ht1 : 0 < t1) (ht12 : t1 < t2)
    (hv1 : 0 ≤ v1) (hv12 : v1 < v2) (hv23 : v2 < v3)
    (hf : ∀ π, 0 ≤ π → f π = if π < t1 then v1 else if π < t2 then v2 else v3)
    (hM : 0 ≤ M) (hH12 : t1 * v2 ≤ t2 * v3) :
    sSup {q | ∃ π : ℝ, 0 ≤ π ∧ π * f π ≤ M ∧ q = f π} =
        (if M < t1 * v2 then v1 else if M < t2 * v3 then v2 else v3) ∧
      IsLeast {π | 0 ≤ π ∧ π * f π ≤ M ∧ f π = sSup {q | ∃ π : ℝ, 0 ≤ π ∧ π * f π ≤ M ∧ q = f π}}
        (if M < t1 * v2 then 0 else if M < t2 * v3 then t1 else t2) := by
  have f0 : f 0 = v1 := by rw [hf 0 le_rfl, if_pos ht1]
  have f1 : f t1 = v2 := by rw [hf t1 ht1.le, if_neg (lt_irrefl _), if_pos ht12]
  have f2 : f t2 = v3 := by
    rw [hf t2 (by linarith), if_neg (by linarith), if_neg (lt_irrefl _)]
  set w := (if M < t1 * v2 then v1 else if M < t2 * v3 then v2 else v3) with hw
  set τ := (if M < t1 * v2 then 0 else if M < t2 * v3 then t1 else t2) with hτ
  have hτmem : 0 ≤ τ ∧ τ * f τ ≤ M ∧ f τ = w := by
    rw [hτ, hw]
    split_ifs with h1 h2
    · exact ⟨le_rfl, by rw [f0]; linarith, f0⟩
    · exact ⟨ht1.le, by rw [f1]; linarith, f1⟩
    · exact ⟨by linarith, by rw [f2]; linarith, f2⟩
  have hub : ∀ π, 0 ≤ π → π * f π ≤ M → f π ≤ w ∧ (f π = w → τ ≤ π) := by
    intro π hπ hb
    rw [hf π hπ] at hb ⊢
    rw [hw, hτ]
    split_ifs at hb ⊢ <;>
      first
      | exact ⟨le_rfl, fun _ => by linarith⟩
      | exact ⟨by linarith, fun h => by linarith⟩
      | (exfalso; nlinarith)
  have hsup : sSup {q | ∃ π : ℝ, 0 ≤ π ∧ π * f π ≤ M ∧ q = f π} = w := by
    apply IsGreatest.csSup_eq
    refine ⟨⟨τ, hτmem.1, hτmem.2.1, hτmem.2.2.symm⟩, ?_⟩
    rintro q ⟨π, hπ, hb, rfl⟩
    exact (hub π hπ hb).1
  refine ⟨hsup, ?_, ?_⟩
  · rw [hsup]; exact hτmem
  · rintro π ⟨hπ, hb, heq⟩
    rw [hsup] at heq
    exact (hub π hπ hb).2 heq

lemma inv_muA_lt_T0N (θ : Params) (hθ : θ.Standing) : 1 / (θ.μ * θ.A) < T0N θ := by
  obtain ⟨hA, hB, hAB, hμ0, hμ1, -, -, -⟩ := hθ
  unfold T0N
  apply one_div_lt_one_div_of_lt
  · have : 0 < 1 - θ.μ := by linarith
    have : 0 < θ.A + θ.B := by linarith
    positivity
  · have : (1 - θ.μ) * (θ.A + θ.B) < 1 := by nlinarith
    have hp : 0 < θ.μ * θ.A := by positivity
    nlinarith [mul_lt_mul_of_pos_left this hp]

lemma T0N_v4 (θ : Params) (hθ : θ.Standing) :
    T0N θ * (θ.μ * (θ.A + θ.B) * (1 + (1 - θ.μ) * (θ.A + θ.B))) = MU θ := by
  obtain ⟨hA, hB, hAB, hμ0, hμ1, -, -, -⟩ := hθ
  have : 0 < 1 - θ.μ := by linarith
  have : 0 < θ.A + θ.B := by linarith
  unfold T0N MU
  field_simp
  ring

theorem PrStar_B0 (θ : Params) (hθ : θ.Standing) (hB : θ.B = 0) (zI : Bool) (π : ℝ)
    (hπ : 0 ≤ π) :
    PrStar θ zI .N π =
      if π < 1 / (θ.μ * θ.A) then 0
      else if π < 1 / (θ.μ * (1 - θ.μ) * θ.A ^ 2) then θ.μ * θ.A
      else θ.μ * θ.A * (1 + (1 - θ.μ) * θ.A) := by
  rw [PrStar_closed θ hθ zI π hπ]
  have hpost : ∀ x : Prof, post θ zI .N 0 x = 0 := by
    intro x
    unfold post
    have : joint θ zI .N 0 .P x = 0 := by simp [joint, toP, hB]
    rw [this, zero_div]
  have hT : ∀ x : Prof, T1 θ zI .N 0 x = 1 / (θ.μ * θ.A) := by
    intro x
    unfold T1 T1p
    rw [hpost x]
    ring
  have hT0 : T0N θ = 1 / (θ.μ * (1 - θ.μ) * θ.A ^ 2) := by unfold T0N; rw [hB]; ring
  rw [hT .P, hT .N, hT0, hB]
  by_cases h1 : π < 1 / (θ.μ * θ.A)
  · rw [if_pos h1, if_pos h1]; ring
  · rw [if_neg h1, if_neg h1, if_neg h1]
    by_cases h2 : π < 1 / (θ.μ * (1 - θ.μ) * θ.A ^ 2)
    · rw [if_pos h2, if_pos h2]; ring
    · rw [if_neg h2, if_neg h2]; ring

theorem opt_B0 (θ : Params) (hθ : θ.Standing) (hB : θ.B = 0) (zI : Bool) (M : ℝ)
    (hM : 0 ≤ M) :
    optProb θ zI .N M =
        (if M < 1 then 0
        else if M < 1 + 1 / ((1 - θ.μ) * θ.A) then θ.μ * θ.A
        else θ.μ * θ.A * (1 + (1 - θ.μ) * θ.A)) ∧
      IsLeast {π | IsOptIncentive θ zI .N M π}
        (if M < 1 then 0
         else if M < 1 + 1 / ((1 - θ.μ) * θ.A) then 1 / (θ.μ * θ.A)
         else 1 / (θ.μ * (1 - θ.μ) * θ.A ^ 2)) := by
  have hθ' := hθ
  obtain ⟨hA, hB0, hAB, hμ0, hμ1, -, -, -⟩ := hθ
  have h1μ : 0 < 1 - θ.μ := by linarith
  have hA1 : θ.A ≤ 1 := by linarith
  have ht1 : 0 < 1 / (θ.μ * θ.A) := by positivity
  have ht12 : 1 / (θ.μ * θ.A) < 1 / (θ.μ * (1 - θ.μ) * θ.A ^ 2) := by
    apply one_div_lt_one_div_of_lt
    · positivity
    · have : (1 - θ.μ) * θ.A < 1 := by nlinarith
      have hp : 0 < θ.μ * θ.A := by positivity
      nlinarith [mul_lt_mul_of_pos_left this hp]
  have hv12 : (0 : ℝ) < θ.μ * θ.A := by positivity
  have hv23 : θ.μ * θ.A < θ.μ * θ.A * (1 + (1 - θ.μ) * θ.A) := by
    have : 0 < θ.μ * θ.A * ((1 - θ.μ) * θ.A) := by positivity
    nlinarith
  have e1 : 1 / (θ.μ * θ.A) * (θ.μ * θ.A) = 1 := by field_simp
  have e2 : 1 / (θ.μ * (1 - θ.μ) * θ.A ^ 2) * (θ.μ * θ.A * (1 + (1 - θ.μ) * θ.A))
      = 1 + 1 / ((1 - θ.μ) * θ.A) := by field_simp; ring
  have h := opt3 (PrStar θ zI .N) _ _ 0 _ _ M ht1 ht12 le_rfl hv12 hv23
    (fun π hπ => PrStar_B0 θ hθ' hB zI π hπ) hM
    (by rw [e1, e2]; have : 0 < 1 / ((1 - θ.μ) * θ.A) := by positivity
        linarith)
  rw [e1, e2] at h
  exact ⟨h.1, h.2⟩

lemma T1_false_P (θ : Params) (hθ : θ.Standing) :
    T1 θ false .N 0 .P = (θ.φPP * (θ.μ * θ.B) + θ.φPN * (1 - θ.μ * θ.B)) /
      (θ.A * θ.μ * (θ.B * θ.φPP + θ.φPN * (1 - θ.μ * θ.B))) := by
  obtain ⟨hA, hB, hAB, hμ0, hμ1, hb0, hba, ha1⟩ := hθ
  have hs : θ.μ * θ.B < 1 := by nlinarith
  have hD2 : 0 < θ.φPP * (θ.μ * θ.B) + θ.φPN * (1 - θ.μ * θ.B) := by
    have : 0 < θ.φPN * (1 - θ.μ * θ.B) := mul_pos hb0 (by linarith)
    have : 0 ≤ θ.φPP * (θ.μ * θ.B) := mul_nonneg (by linarith) (mul_nonneg hμ0.le hB)
    linarith
  have hD1 : 0 < θ.B * θ.φPP + θ.φPN * (1 - θ.μ * θ.B) := by
    have : 0 < θ.φPN * (1 - θ.μ * θ.B) := mul_pos hb0 (by linarith)
    have : 0 ≤ θ.B * θ.φPP := mul_nonneg hB (by linarith)
    linarith
  have hpost : post θ false .N 0 .P = θ.φPP * (θ.μ * θ.B) /
      (θ.φPP * (θ.μ * θ.B) + θ.φPN * (1 - θ.μ * θ.B)) := by
    unfold post
    have h1 : joint θ false .N 0 .P .P = θ.φPP * (θ.μ * θ.B) := by
      simp [joint, sig, acc, toP]; ring
    have h2 : obsProb θ false .N 0 .P = θ.φPP * (θ.μ * θ.B) + θ.φPN * (1 - θ.μ * θ.B) := by
      simp [obsProb, joint, sig, acc, toP]; ring
    rw [h1, h2]
  unfold T1 T1p
  rw [hpost]
  have key : θ.A * ((1 - θ.μ) * (θ.φPP * (θ.μ * θ.B) /
      (θ.φPP * (θ.μ * θ.B) + θ.φPN * (1 - θ.μ * θ.B))) + θ.μ) =
      θ.A * θ.μ * (θ.B * θ.φPP + θ.φPN * (1 - θ.μ * θ.B)) /
      (θ.φPP * (θ.μ * θ.B) + θ.φPN * (1 - θ.μ * θ.B)) := by
    rw [eq_div_iff hD2.ne']
    have hc : θ.φPP * (θ.μ * θ.B) /
        (θ.φPP * (θ.μ * θ.B) + θ.φPN * (1 - θ.μ * θ.B)) *
        (θ.φPP * (θ.μ * θ.B) + θ.φPN * (1 - θ.μ * θ.B)) =
        θ.φPP * (θ.μ * θ.B) := div_mul_cancel₀ _ hD2.ne'
    linear_combination θ.A * (1 - θ.μ) * hc
  rw [key, one_div_div]

lemma T1_false_N (θ : Params) (hθ : θ.Standing) :
    T1 θ false .N 0 .N = ((1 - θ.φPP) * (θ.μ * θ.B) + (1 - θ.φPN) * (1 - θ.μ * θ.B)) /
      (θ.A * θ.μ * ((1 - θ.φPP) * θ.B + (1 - θ.φPN) * (1 - θ.μ * θ.B))) := by
  obtain ⟨hA, hB, hAB, hμ0, hμ1, hb0, hba, ha1⟩ := hθ
  have hs : θ.μ * θ.B < 1 := by nlinarith
  have hE : 0 < (1 - θ.φPP) * (θ.μ * θ.B) + (1 - θ.φPN) * (1 - θ.μ * θ.B) := by
    have : 0 < (1 - θ.φPN) * (1 - θ.μ * θ.B) := mul_pos (by linarith) (by linarith)
    have : 0 ≤ (1 - θ.φPP) * (θ.μ * θ.B) := mul_nonneg (by linarith) (mul_nonneg hμ0.le hB)
    linarith
  have hF : 0 < (1 - θ.φPP) * θ.B + (1 - θ.φPN) * (1 - θ.μ * θ.B) := by
    have : 0 < (1 - θ.φPN) * (1 - θ.μ * θ.B) := mul_pos (by linarith) (by linarith)
    have : 0 ≤ (1 - θ.φPP) * θ.B := mul_nonneg (by linarith) hB
    linarith
  have hpost : post θ false .N 0 .N = (1 - θ.φPP) * (θ.μ * θ.B) /
      ((1 - θ.φPP) * (θ.μ * θ.B) + (1 - θ.φPN) * (1 - θ.μ * θ.B)) := by
    unfold post
    have h1 : joint θ false .N 0 .P .N = (1 - θ.φPP) * (θ.μ * θ.B) := by
      simp [joint, sig, acc, toP]; ring
    have h2 : obsProb θ false .N 0 .N =
        (1 - θ.φPP) * (θ.μ * θ.B) + (1 - θ.φPN) * (1 - θ.μ * θ.B) := by
      simp [obsProb, joint, sig, acc, toP]; ring
    rw [h1, h2]
  unfold T1 T1p
  rw [hpost]
  have key : θ.A * ((1 - θ.μ) * ((1 - θ.φPP) * (θ.μ * θ.B) /
      ((1 - θ.φPP) * (θ.μ * θ.B) + (1 - θ.φPN) * (1 - θ.μ * θ.B))) + θ.μ) =
      θ.A * θ.μ * ((1 - θ.φPP) * θ.B + (1 - θ.φPN) * (1 - θ.μ * θ.B)) /
      ((1 - θ.φPP) * (θ.μ * θ.B) + (1 - θ.φPN) * (1 - θ.μ * θ.B)) := by
    rw [eq_div_iff hE.ne']
    have hc : (1 - θ.φPP) * (θ.μ * θ.B) /
        ((1 - θ.φPP) * (θ.μ * θ.B) + (1 - θ.φPN) * (1 - θ.μ * θ.B)) *
        ((1 - θ.φPP) * (θ.μ * θ.B) + (1 - θ.φPN) * (1 - θ.μ * θ.B)) =
        (1 - θ.φPP) * (θ.μ * θ.B) := div_mul_cancel₀ _ hE.ne'
    linear_combination θ.A * (1 - θ.μ) * hc
  rw [key, one_div_div]

lemma H1_eq (θ : Params) (hθ : θ.Standing) :
    H1 θ = θ.μ * (θ.B * (θ.A * θ.φPP + θ.B) + (1 - θ.μ * θ.B) * (θ.A * θ.φPN + θ.B))
        * T1 θ false .N 0 .P := by
  have hθ' := hθ
  obtain ⟨hA, hB, hAB, hμ0, hμ1, hb0, hba, ha1⟩ := hθ
  have hs : θ.μ * θ.B < 1 := by nlinarith
  have hD1 : 0 < θ.B * θ.φPP + θ.φPN * (1 - θ.μ * θ.B) := by
    have : 0 < θ.φPN * (1 - θ.μ * θ.B) := mul_pos hb0 (by linarith)
    have : 0 ≤ θ.B * θ.φPP := mul_nonneg hB (by linarith)
    linarith
  rw [T1_false_P θ hθ']
  unfold H1
  have hv : θ.μ * (θ.B * (θ.A * θ.φPP + θ.B) + (1 - θ.μ * θ.B) * (θ.A * θ.φPN + θ.B)) =
      θ.μ * (θ.A * (θ.B * θ.φPP + θ.φPN * (1 - θ.μ * θ.B)) + θ.B * (1 + (1 - θ.μ) * θ.B)) := by
    ring
  rw [hv, show θ.φPP * θ.μ * θ.B = θ.φPP * (θ.μ * θ.B) by ring]
  generalize θ.B * θ.φPP + θ.φPN * (1 - θ.μ * θ.B) = X at *
  field_simp

lemma H2_eq (θ : Params) (hθ : θ.Standing) :
    H2 θ = (θ.A + θ.B) * (1 + (1 - θ.μ) * θ.B)
      * ((1 - θ.φPP) * (θ.μ * θ.B) + (1 - θ.φPN) * (1 - θ.μ * θ.B)) /
      (θ.A * ((1 - θ.φPP) * θ.B + (1 - θ.φPN) * (1 - θ.μ * θ.B))) := by
  have hθ' := hθ
  obtain ⟨hA, hB, hAB, hμ0, hμ1, hb0, hba, ha1⟩ := hθ
  have hs : θ.μ * θ.B < 1 := by nlinarith
  have hF : 0 < (1 - θ.φPP) * θ.B + (1 - θ.φPN) * (1 - θ.μ * θ.B) := by
    have : 0 < (1 - θ.φPN) * (1 - θ.μ * θ.B) := mul_pos (by linarith) (by linarith)
    have : 0 ≤ (1 - θ.φPP) * θ.B := mul_nonneg (by linarith) hB
    linarith
  unfold H2
  rw [T1_false_N θ hθ']
  field_simp

lemma H1_le_H2 (θ : Params) (hθ : θ.Standing) : H1 θ ≤ H2 θ := by
  have hθ' := hθ
  obtain ⟨hA, hB, hAB, hμ0, hμ1, hb0, hba, ha1⟩ := hθ
  rw [H1_eq θ hθ', T1_false_P θ hθ', H2_eq θ hθ']
  have hs0 : 0 ≤ θ.μ * θ.B := mul_nonneg hμ0.le hB
  have hsB : θ.μ * θ.B ≤ θ.B := by nlinarith
  have hs : θ.μ * θ.B < 1 := by nlinarith
  set a := θ.φPP
  set b := θ.φPN
  set S := θ.μ * θ.B with hS
  have hD1 : 0 < θ.B * a + b * (1 - S) := by
    have : 0 < b * (1 - S) := mul_pos hb0 (by linarith)
    have : 0 ≤ θ.B * a := mul_nonneg hB (by linarith)
    linarith
  have hF : 0 < (1 - a) * θ.B + (1 - b) * (1 - S) := by
    have : 0 < (1 - b) * (1 - S) := mul_pos (by linarith) (by linarith)
    have : 0 ≤ (1 - a) * θ.B := mul_nonneg (by linarith) hB
    linarith
  set C := 1 + (1 - θ.μ) * θ.B with hC
  set D1 := θ.B * a + b * (1 - S)
  set D2 := a * S + b * (1 - S)
  set E := (1 - a) * S + (1 - b) * (1 - S)
  set F := (1 - a) * θ.B + (1 - b) * (1 - S)
  have hCB : C = 1 + θ.B - S := by rw [hC, hS]; ring
  have I1 : 0 ≤ C * E - D2 * F := by
    have e : C * E - D2 * F = E ^ 2 + (θ.B - S) * ((1 - a) ^ 2 * S + (1 - S) * (1 - 2 * b + a * b)) := by
      rw [hCB]; ring
    rw [e]
    have : 0 ≤ 1 - 2 * b + a * b := by nlinarith
    have : 0 ≤ (1 - a) ^ 2 * S + (1 - S) * (1 - 2 * b + a * b) :=
      add_nonneg (mul_nonneg (sq_nonneg _) hs0) (mul_nonneg (by linarith) this)
    have : 0 ≤ (θ.B - S) * ((1 - a) ^ 2 * S + (1 - S) * (1 - 2 * b + a * b)) :=
      mul_nonneg (by linarith) this
    positivity
  have I2 : 0 ≤ E * D1 - D2 * F := by
    have e : E * D1 - D2 * F = (1 - S) * (a - b) * (θ.B - S) := by ring
    rw [e]
    exact mul_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith)
  have hv : θ.μ * (θ.B * (θ.A * a + θ.B) + (1 - S) * (θ.A * b + θ.B)) =
      θ.μ * (θ.A * D1 + θ.B * C) := by rw [hC, hS]; ring
  rw [hv, mul_div_assoc', div_le_div_iff₀ (by positivity) (by positivity)]
  have key : (θ.A + θ.B) * C * E * (θ.A * θ.μ * D1) - θ.μ * (θ.A * D1 + θ.B * C) * D2 * (θ.A * F)
      = θ.μ * θ.A * (θ.A * D1 * (C * E - D2 * F) + θ.B * C * (E * D1 - D2 * F)) := by ring
  have hC0 : 0 ≤ C := by rw [hCB]; linarith
  have : 0 ≤ θ.μ * θ.A * (θ.A * D1 * (C * E - D2 * F) + θ.B * C * (E * D1 - D2 * F)) := by
    have := mul_nonneg (mul_nonneg hA.le hD1.le) I1
    have := mul_nonneg (mul_nonneg hB hC0) I2
    positivity
  linarith

lemma HI1_le_H2 (θ : Params) (hθ : θ.Standing) : HI1 θ ≤ H2 θ := by
  have hθ' := hθ
  obtain ⟨hA, hB, hAB, hμ0, hμ1, hb0, hba, ha1⟩ := hθ
  rw [H2_eq θ hθ']
  unfold HI1
  have hs0 : 0 ≤ θ.μ * θ.B := mul_nonneg hμ0.le hB
  have hsB : θ.μ * θ.B ≤ θ.B := by nlinarith
  have hs : θ.μ * θ.B < 1 := by nlinarith
  set a := θ.φPP
  set b := θ.φPN
  set S := θ.μ * θ.B with hS
  have hF : 0 < (1 - a) * θ.B + (1 - b) * (1 - S) := by
    have : 0 < (1 - b) * (1 - S) := mul_pos (by linarith) (by linarith)
    have : 0 ≤ (1 - a) * θ.B := mul_nonneg (by linarith) hB
    linarith
  set C := 1 + (1 - θ.μ) * θ.B with hC
  set E := (1 - a) * S + (1 - b) * (1 - S)
  set F := (1 - a) * θ.B + (1 - b) * (1 - S)
  have hEF : θ.μ * F ≤ E := by
    have e : E - θ.μ * F = (1 - b) * (1 - S) * (1 - θ.μ) := by rw [hS]; ring
    have : 0 ≤ (1 - b) * (1 - S) * (1 - θ.μ) :=
      mul_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith)
    linarith
  have hBC : θ.B ≤ C := by rw [hC]; nlinarith
  have h1 : θ.μ * θ.B * ((θ.A + 1 + (1 - θ.μ) * θ.B) / θ.A) = S * (θ.A + C) / θ.A := by
    rw [hS, hC]; ring
  rw [h1, div_le_div_iff₀ hA (by positivity)]
  -- S (A + C) * (A F) ≤ (A+B) C E * A
  have hC0 : 0 ≤ C := le_trans hB hBC
  have k1 : S * (θ.A + C) ≤ θ.μ * ((θ.A + θ.B) * C) := by
    rw [hS]; nlinarith [mul_le_mul_of_nonneg_left hBC (le_of_lt hμ0), mul_nonneg hμ0.le hA.le]
  have k2 : θ.μ * ((θ.A + θ.B) * C) * F ≤ (θ.A + θ.B) * C * E := by
    have : 0 ≤ (θ.A + θ.B) * C := mul_nonneg (by linarith) hC0
    nlinarith [mul_le_mul_of_nonneg_left hEF this]
  have k3 : S * (θ.A + C) * F ≤ (θ.A + θ.B) * C * E := by
    nlinarith [mul_le_mul_of_nonneg_right k1 hF.le]
  nlinarith [mul_le_mul_of_nonneg_left k3 hA.le]

lemma H2_le_HI2 (θ : Params) (hθ : θ.Standing) : H2 θ ≤ HI2 θ := by
  have hθ' := hθ
  obtain ⟨hA, hB, hAB, hμ0, hμ1, hb0, hba, ha1⟩ := hθ
  rw [H2_eq θ hθ']
  unfold HI2
  have hs0 : 0 ≤ θ.μ * θ.B := mul_nonneg hμ0.le hB
  have hsB : θ.μ * θ.B ≤ θ.B := by nlinarith
  have hs : θ.μ * θ.B < 1 := by nlinarith
  have hF : 0 < (1 - θ.φPP) * θ.B + (1 - θ.φPN) * (1 - θ.μ * θ.B) := by
    have : 0 < (1 - θ.φPN) * (1 - θ.μ * θ.B) := mul_pos (by linarith) (by linarith)
    have : 0 ≤ (1 - θ.φPP) * θ.B := mul_nonneg (by linarith) hB
    linarith
  have hEF : (1 - θ.φPP) * (θ.μ * θ.B) + (1 - θ.φPN) * (1 - θ.μ * θ.B) ≤
      (1 - θ.φPP) * θ.B + (1 - θ.φPN) * (1 - θ.μ * θ.B) := by
    nlinarith [mul_le_mul_of_nonneg_left hsB (by linarith : (0:ℝ) ≤ 1 - θ.φPP)]
  have hK : 0 ≤ (θ.A + θ.B) * (1 + (1 - θ.μ) * θ.B) := by
    have : 0 ≤ (1 - θ.μ) * θ.B := mul_nonneg (by linarith) hB
    have : 0 ≤ θ.A + θ.B := by linarith
    positivity
  rw [div_le_div_iff₀ (by positivity) hA]
  nlinarith [mul_le_mul_of_nonneg_left hEF (mul_nonneg hK hA.le)]

lemma HI2_le_MU (θ : Params) (hθ : θ.Standing) : HI2 θ ≤ MU θ := by
  obtain ⟨hA, hB, hAB, hμ0, hμ1, hb0, hba, ha1⟩ := hθ
  unfold HI2 MU
  have h1 : 0 < 1 - θ.μ := by linarith
  have hC : 0 ≤ 1 + (1 - θ.μ) * θ.B := by nlinarith
  have : (θ.A + θ.B) * (1 + (1 - θ.μ) * θ.B) / θ.A ≤
      (1 + (1 - θ.μ) * θ.B) / ((1 - θ.μ) * θ.A) := by
    rw [div_le_div_iff₀ hA (by positivity)]
    have : (θ.A + θ.B) * (1 - θ.μ) ≤ 1 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left this (mul_nonneg hC hA.le)]
  linarith

lemma HI1_le_HI2 (θ : Params) (hθ : θ.Standing) : HI1 θ ≤ HI2 θ :=
  le_trans (HI1_le_H2 θ hθ) (H2_le_HI2 θ hθ)

lemma hab_of_14 (θ : Params) (hθ : θ.Standing) (h14 : Cond14 θ) : θ.φPN < θ.φPP := by
  obtain ⟨hA, hB, hAB, hμ0, hμ1, hb0, hba, ha1⟩ := hθ
  rcases eq_or_lt_of_le hba with h | h
  · exfalso
    unfold Cond14 at h14
    rw [h, sub_self, mul_zero] at h14
    have : 0 < (1 - θ.φPP) * θ.φPP * θ.A := by
      have : 0 < 1 - θ.φPP := by linarith
      have : 0 < θ.φPP := by linarith
      positivity
    linarith
  · exact h

theorem opt_false (θ : Params) (hθ : θ.Standing) (hB : 0 < θ.B) (h14 : Cond14 θ) (M : ℝ)
    (hM : 0 ≤ M) :
    optProb θ false .N M =
        (if M < H1 θ then θ.μ * θ.B * (1 + (1 - θ.μ) * θ.B)
          else if M < H2 θ then
            θ.μ * (θ.B * (θ.A * θ.φPP + θ.B) + (1 - θ.μ * θ.B) * (θ.A * θ.φPN + θ.B))
          else if M < MU θ then θ.μ * (θ.A + θ.B) * (1 + (1 - θ.μ) * θ.B)
          else θ.μ * (θ.A + θ.B) * (1 + (1 - θ.μ) * (θ.A + θ.B))) ∧
      IsLeast {π | IsOptIncentive θ false .N M π}
        (if M < H1 θ then 0
         else if M < H2 θ then T1 θ false .N 0 .P
         else if M < MU θ then T1 θ false .N 0 .N
         else T0N θ) := by
  have hθ' := hθ
  have hab := hab_of_14 θ hθ h14
  obtain ⟨hA, hB0, hAB, hμ0, hμ1, hb0, hba, ha1⟩ := hθ
  have h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨le_refl _, zero_le_one⟩
  have hs0 : 0 < θ.μ * θ.B := mul_pos hμ0 hB
  have hsB : θ.μ * θ.B < θ.B := by nlinarith
  have hs : θ.μ * θ.B < 1 := by nlinarith
  have hD2 : 0 < θ.φPP * (θ.μ * θ.B) + θ.φPN * (1 - θ.μ * θ.B) := by
    have : 0 < θ.φPN * (1 - θ.μ * θ.B) := mul_pos hb0 (by linarith)
    have : 0 ≤ θ.φPP * (θ.μ * θ.B) := mul_nonneg (by linarith) hs0.le
    linarith
  have hD1 : 0 < θ.B * θ.φPP + θ.φPN * (1 - θ.μ * θ.B) := by
    have : 0 < θ.φPN * (1 - θ.μ * θ.B) := mul_pos hb0 (by linarith)
    have : 0 ≤ θ.B * θ.φPP := mul_nonneg hB0 (by linarith)
    linarith
  have hE : 0 < (1 - θ.φPP) * (θ.μ * θ.B) + (1 - θ.φPN) * (1 - θ.μ * θ.B) := by
    have : 0 < (1 - θ.φPN) * (1 - θ.μ * θ.B) := mul_pos (by linarith) (by linarith)
    have : 0 ≤ (1 - θ.φPP) * (θ.μ * θ.B) := mul_nonneg (by linarith) hs0.le
    linarith
  have hF : 0 < (1 - θ.φPP) * θ.B + (1 - θ.φPN) * (1 - θ.μ * θ.B) := by
    have : 0 < (1 - θ.φPN) * (1 - θ.μ * θ.B) := mul_pos (by linarith) (by linarith)
    have : 0 ≤ (1 - θ.φPP) * θ.B := mul_nonneg (by linarith) hB0
    linarith
  have ht1 : 0 < T1 θ false .N 0 .P := by rw [T1_false_P θ hθ']; positivity
  have ht12 : T1 θ false .N 0 .P < T1 θ false .N 0 .N := by
    rw [T1_false_P θ hθ', T1_false_N θ hθ', div_lt_div_iff₀ (by positivity) (by positivity)]
    have e : ((1 - θ.φPP) * (θ.μ * θ.B) + (1 - θ.φPN) * (1 - θ.μ * θ.B)) *
        (θ.A * θ.μ * (θ.B * θ.φPP + θ.φPN * (1 - θ.μ * θ.B))) -
        (θ.φPP * (θ.μ * θ.B) + θ.φPN * (1 - θ.μ * θ.B)) *
        (θ.A * θ.μ * ((1 - θ.φPP) * θ.B + (1 - θ.φPN) * (1 - θ.μ * θ.B)))
        = θ.A * θ.μ * ((1 - θ.μ * θ.B) * (θ.φPP - θ.φPN) * (θ.B - θ.μ * θ.B)) := by ring
    have : 0 < θ.A * θ.μ * ((1 - θ.μ * θ.B) * (θ.φPP - θ.φPN) * (θ.B - θ.μ * θ.B)) := by
      have : 0 < 1 - θ.μ * θ.B := by linarith
      have : 0 < θ.φPP - θ.φPN := by linarith
      have : 0 < θ.B - θ.μ * θ.B := by linarith
      positivity
    linarith
  have ht23 : T1 θ false .N 0 .N < T0N θ :=
    lt_of_le_of_lt (T1p_le θ hθ' _ (post_mem θ hθ' false 0 h0 .N).1) (inv_muA_lt_T0N θ hθ')
  have hacc : acc θ false = (θ.φPP, θ.φPN) := by simp [acc]
  have hf : ∀ π, 0 ≤ π → PrStar θ false .N π =
      if π < T1 θ false .N 0 .P then θ.μ * θ.B * (1 + (1 - θ.μ) * θ.B)
      else if π < T1 θ false .N 0 .N then
        θ.μ * (θ.B * (θ.A * θ.φPP + θ.B) + (1 - θ.μ * θ.B) * (θ.A * θ.φPN + θ.B))
      else if π < T0N θ then θ.μ * (θ.A + θ.B) * (1 + (1 - θ.μ) * θ.B)
      else θ.μ * (θ.A + θ.B) * (1 + (1 - θ.μ) * (θ.A + θ.B)) := by
    intro π hπ
    rw [PrStar_closed θ hθ' false π hπ, hacc]
  have hv1 : 0 ≤ θ.μ * θ.B * (1 + (1 - θ.μ) * θ.B) := by
    have : 0 ≤ (1 - θ.μ) * θ.B := mul_nonneg (by linarith) hB0
    have : 0 ≤ 1 + (1 - θ.μ) * θ.B := by linarith
    positivity
  have hv12 : θ.μ * θ.B * (1 + (1 - θ.μ) * θ.B) <
      θ.μ * (θ.B * (θ.A * θ.φPP + θ.B) + (1 - θ.μ * θ.B) * (θ.A * θ.φPN + θ.B)) := by
    have e : θ.μ * (θ.B * (θ.A * θ.φPP + θ.B) + (1 - θ.μ * θ.B) * (θ.A * θ.φPN + θ.B))
        - θ.μ * θ.B * (1 + (1 - θ.μ) * θ.B)
        = θ.μ * θ.A * (θ.φPP * θ.B + θ.φPN * (1 - θ.μ * θ.B)) := by ring
    have : 0 < θ.μ * θ.A * (θ.φPP * θ.B + θ.φPN * (1 - θ.μ * θ.B)) := by
      have : 0 < θ.φPP * θ.B + θ.φPN * (1 - θ.μ * θ.B) := by linarith
      positivity
    linarith
  have hv23 : θ.μ * (θ.B * (θ.A * θ.φPP + θ.B) + (1 - θ.μ * θ.B) * (θ.A * θ.φPN + θ.B)) <
      θ.μ * (θ.A + θ.B) * (1 + (1 - θ.μ) * θ.B) := by
    have e : θ.μ * (θ.A + θ.B) * (1 + (1 - θ.μ) * θ.B) -
        θ.μ * (θ.B * (θ.A * θ.φPP + θ.B) + (1 - θ.μ * θ.B) * (θ.A * θ.φPN + θ.B))
        = θ.μ * θ.A * ((1 - θ.μ * θ.B) * (1 - θ.φPN) + θ.B * (1 - θ.φPP)) := by ring
    have : 0 < θ.μ * θ.A * ((1 - θ.μ * θ.B) * (1 - θ.φPN) + θ.B * (1 - θ.φPP)) := by
      have : 0 < (1 - θ.μ * θ.B) * (1 - θ.φPN) := mul_pos (by linarith) (by linarith)
      have : 0 ≤ θ.B * (1 - θ.φPP) := mul_nonneg hB0 (by linarith)
      have : 0 < (1 - θ.μ * θ.B) * (1 - θ.φPN) + θ.B * (1 - θ.φPP) := by linarith
      positivity
    linarith
  have hv34 : θ.μ * (θ.A + θ.B) * (1 + (1 - θ.μ) * θ.B) <
      θ.μ * (θ.A + θ.B) * (1 + (1 - θ.μ) * (θ.A + θ.B)) := by
    have : 0 < θ.μ * (θ.A + θ.B) * ((1 - θ.μ) * θ.A) := by
      have : 0 < 1 - θ.μ := by linarith
      have : 0 < θ.A + θ.B := by linarith
      positivity
    nlinarith
  have e1 : T1 θ false .N 0 .P *
      (θ.μ * (θ.B * (θ.A * θ.φPP + θ.B) + (1 - θ.μ * θ.B) * (θ.A * θ.φPN + θ.B))) = H1 θ := by
    rw [H1_eq θ hθ', mul_comm]
  have e2 : T1 θ false .N 0 .N * (θ.μ * (θ.A + θ.B) * (1 + (1 - θ.μ) * θ.B)) = H2 θ := by
    unfold H2; ring
  have e3 := T0N_v4 θ hθ'
  have h := opt4 (PrStar θ false .N) _ _ _ _ _ _ _ M ht1 ht12 ht23 hv1 hv12 hv23 hv34 hf hM
    (by rw [e1, e2]; exact H1_le_H2 θ hθ')
    (by rw [e2, e3]; exact le_trans (H2_le_HI2 θ hθ') (HI2_le_MU θ hθ'))
  rw [e1, e2, e3] at h
  exact ⟨h.1, h.2⟩

lemma post_true (θ : Params) (hθ : θ.Standing) (hB : 0 < θ.B) :
    post θ true .N 0 .P = 1 ∧ post θ true .N 0 .N = 0 := by
  obtain ⟨hA, hB0, hAB, hμ0, hμ1, hb0, hba, ha1⟩ := hθ
  have hs0 : 0 < θ.μ * θ.B := mul_pos hμ0 hB
  unfold post
  constructor
  · have h1 : joint θ true .N 0 .P .P = θ.μ * θ.B := by simp [joint, sig, acc, toP]
    have h2 : obsProb θ true .N 0 .P = θ.μ * θ.B := by simp [obsProb, joint, sig, acc, toP]
    rw [h1, h2, div_self hs0.ne']
  · have h1 : joint θ true .N 0 .P .N = 0 := by simp [joint, sig, acc, toP]
    rw [h1, zero_div]

theorem opt_true (θ : Params) (hθ : θ.Standing) (hB : 0 < θ.B) (M : ℝ) (hM : 0 ≤ M) :
    optProb θ true .N M =
      if M < HI1 θ then θ.μ * θ.B * (1 + (1 - θ.μ) * θ.B)
      else if M < HI2 θ then θ.μ * θ.B * ((θ.A + θ.B) + (1 - θ.μ * θ.B))
      else if M < MU θ then θ.μ * (θ.A + θ.B) * (1 + (1 - θ.μ) * θ.B)
      else θ.μ * (θ.A + θ.B) * (1 + (1 - θ.μ) * (θ.A + θ.B)) := by
  have hθ' := hθ
  obtain ⟨hA, hB0, hAB, hμ0, hμ1, hb0, hba, ha1⟩ := hθ
  have hs0 : 0 < θ.μ * θ.B := mul_pos hμ0 hB
  have hs : θ.μ * θ.B < 1 := by nlinarith
  obtain ⟨hpP, hpN⟩ := post_true θ hθ' hB
  have hT1P : T1 θ true .N 0 .P = 1 / θ.A := by
    unfold T1 T1p; rw [hpP]; ring_nf
  have hT1N : T1 θ true .N 0 .N = 1 / (θ.μ * θ.A) := by
    unfold T1 T1p; rw [hpN]; ring_nf
  have hacc : acc θ true = (1, 0) := by simp [acc]
  have hf : ∀ π, 0 ≤ π → PrStar θ true .N π =
      if π < 1 / θ.A then θ.μ * θ.B * (1 + (1 - θ.μ) * θ.B)
      else if π < 1 / (θ.μ * θ.A) then θ.μ * θ.B * ((θ.A + θ.B) + (1 - θ.μ * θ.B))
      else if π < T0N θ then θ.μ * (θ.A + θ.B) * (1 + (1 - θ.μ) * θ.B)
      else θ.μ * (θ.A + θ.B) * (1 + (1 - θ.μ) * (θ.A + θ.B)) := by
    intro π hπ
    rw [PrStar_closed θ hθ' true π hπ, hacc, hT1P, hT1N]
    split_ifs <;> ring
  have ht1 : 0 < 1 / θ.A := by positivity
  have ht12 : 1 / θ.A < 1 / (θ.μ * θ.A) := by
    apply one_div_lt_one_div_of_lt (by positivity)
    nlinarith
  have ht23 := inv_muA_lt_T0N θ hθ'
  have hv1 : 0 ≤ θ.μ * θ.B * (1 + (1 - θ.μ) * θ.B) := by
    have : 0 ≤ (1 - θ.μ) * θ.B := mul_nonneg (by linarith) hB0
    have : 0 ≤ 1 + (1 - θ.μ) * θ.B := by linarith
    positivity
  have hv12 : θ.μ * θ.B * (1 + (1 - θ.μ) * θ.B) <
      θ.μ * θ.B * ((θ.A + θ.B) + (1 - θ.μ * θ.B)) := by
    have : 0 < θ.μ * θ.B * θ.A := by positivity
    nlinarith
  have hv23 : θ.μ * θ.B * ((θ.A + θ.B) + (1 - θ.μ * θ.B)) <
      θ.μ * (θ.A + θ.B) * (1 + (1 - θ.μ) * θ.B) := by
    have : 0 < θ.μ * θ.A * (1 - θ.μ * θ.B) := by
      have : 0 < 1 - θ.μ * θ.B := by linarith
      positivity
    nlinarith
  have hv34 : θ.μ * (θ.A + θ.B) * (1 + (1 - θ.μ) * θ.B) <
      θ.μ * (θ.A + θ.B) * (1 + (1 - θ.μ) * (θ.A + θ.B)) := by
    have : 0 < θ.μ * (θ.A + θ.B) * ((1 - θ.μ) * θ.A) := by
      have : 0 < 1 - θ.μ := by linarith
      have : 0 < θ.A + θ.B := by linarith
      positivity
    nlinarith
  have e1 : 1 / θ.A * (θ.μ * θ.B * ((θ.A + θ.B) + (1 - θ.μ * θ.B))) = HI1 θ := by
    unfold HI1; field_simp; ring
  have e2 : 1 / (θ.μ * θ.A) * (θ.μ * (θ.A + θ.B) * (1 + (1 - θ.μ) * θ.B)) = HI2 θ := by
    unfold HI2; field_simp
  have e3 := T0N_v4 θ hθ'
  have h := opt4 (PrStar θ true .N) _ _ _ _ _ _ _ M ht1 ht12 ht23 hv1 hv12 hv23 hv34 hf hM
    (by rw [e1, e2]; exact HI1_le_HI2 θ hθ')
    (by rw [e2, e3]; exact HI2_le_MU θ hθ')
  rw [e1, e2, e3] at h
  exact h.1

end ITNPAux

theorem solution (θ : Params) (hθ : θ.Standing) (hB : 0 < θ.B) (M : ℝ) (hM : 0 ≤ M) :
    optProb θ true .N M =
      if M < HI1 θ then θ.μ * θ.B * (1 + (1 - θ.μ) * θ.B)
      else if M < HI2 θ then θ.μ * θ.B * ((θ.A + θ.B) + (1 - θ.μ * θ.B))
      else if M < MU θ then θ.μ * (θ.A + θ.B) * (1 + (1 - θ.μ) * θ.B)
      else θ.μ * (θ.A + θ.B) * (1 + (1 - θ.μ) * (θ.A + θ.B)) :=
  ITNPAux.opt_true θ hθ hB M hM
