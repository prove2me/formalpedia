-- Prove2me | solution 1 for OAI.PiExponent.separated_weight_logarithmic_interpolation
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T14:20:17.827236+00:00
-- url     : https://prove2.me/submissions/fdf77da4-b2e4-4e5e-b22f-4afa239f4dde
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_PiExponent_DeterminantSetup
import Theorems.Thm_OAI_PiExponent_logarithmic_interpolation_one_transverse_threshold
import Theorems.Thm_OAI_PiExponent_logarithmic_interpolation_transverse_dimension_lift
import Mathlib.Algebra.Order.Archimedean.Basic

open scoped BigOperators

/- Reduction by induction on the number of transverse variables.
The two imported interpolation lemmas are the proposed open children.
The rational margin selection and induction are proved here. -/

private theorem choose_lower_dimension_contraction
    (n K : ℕ) (hn : 0 < n) (hK : 0 < K)
    (w0 v0 q : ℚ) (hw0 : 0 < w0) (hv0 : 0 < v0)
    (hq : 0 < q) (hq1 : q < 1)
    (hvol1 : (K : ℚ) * q ^ (n + 1) < 1)
    (hvol2 : (K : ℚ) * (w0 / v0) * q ^ (n + 1) < 1) :
    ∃ a : ℚ, 0 < a ∧ a < 1 ∧ q ^ (n + 1) < a ^ n ∧
      (K : ℚ) * a ^ n < 1 ∧
      (K : ℚ) * (w0 / v0) * a ^ n < 1 := by
  have hKq : (0 : ℚ) < (K : ℚ) := Nat.cast_pos.mpr hK
  let R : ℚ := (K : ℚ) * (w0 / v0)
  have hR : 0 < R := mul_pos hKq (div_pos hw0 hv0)
  let u : ℚ := min 1 (min (1 / (K : ℚ)) (1 / R))
  have hqpow : 0 < q ^ (n + 1) := pow_pos hq _
  have hqpow1 : q ^ (n + 1) < 1 :=
    pow_lt_one₀ hq.le hq1 (Nat.succ_ne_zero n)
  have hqK : q ^ (n + 1) < 1 / (K : ℚ) := by
    apply (lt_div_iff₀ hKq).2
    simpa only [mul_comm] using hvol1
  have hqR : q ^ (n + 1) < 1 / R := by
    apply (lt_div_iff₀ hR).2
    simpa only [R, mul_comm] using hvol2
  have hqu : q ^ (n + 1) < u :=
    lt_min hqpow1 (lt_min hqK hqR)
  obtain ⟨a, ha, hqa, hau⟩ :
      ∃ a : ℚ, 0 < a ∧ q ^ (n + 1) < a ^ n ∧ a ^ n < u :=
    exists_pow_btwn (ne_of_gt hn) hqu (hqpow.trans hqu)
  have hu1 : u ≤ 1 := min_le_left _ _
  have huK : u ≤ 1 / (K : ℚ) :=
    (min_le_right _ _).trans (min_le_left _ _)
  have huR : u ≤ 1 / R :=
    (min_le_right _ _).trans (min_le_right _ _)
  have ha1 : a < 1 :=
    (pow_lt_one_iff_of_nonneg ha.le (ne_of_gt hn)).1 (hau.trans_le hu1)
  refine ⟨a, ha, ha1, hqa, ?_, ?_⟩
  · have h := (lt_div_iff₀ hKq).1 (hau.trans_le huK)
    simpa only [mul_comm] using h
  · have h := (lt_div_iff₀ hR).1 (hau.trans_le huR)
    simpa only [R, mul_comm] using h

theorem solution
    (m K : ℕ) (hm : 0 < m) (hK : 0 < K)
    (w0 v0 theta : ℚ) (hw0 : 0 < w0) (hv0 : 0 < v0)
    (htheta : 0 < theta) (htheta1 : theta < 1)
    (hvol1 : (K : ℚ) * theta ^ m < 1)
    (hvol2 : (K : ℚ) * (w0 / v0) * theta ^ m < 1) :
    ∃ S : List ℕ → ℕ,
      ∀ w : Fin m → ℕ, (∀ i, 0 < w i) →
        OAI.PiExponent.separatedWeights S w →
        ∀ c : Fin K → Fin m → ℂ,
          (∀ i : Fin m, Function.Injective (fun j : Fin K => c j i)) →
          OAI.PiExponent.eventualLogJetSurjective m K w0 v0 theta w c := by
  have hall :
      ∀ n : ℕ, 0 < n →
        ∀ q : ℚ, 0 < q → q < 1 →
          (K : ℚ) * q ^ n < 1 →
          (K : ℚ) * (w0 / v0) * q ^ n < 1 →
          ∃ S : List ℕ → ℕ,
            ∀ w : Fin n → ℕ, (∀ i, 0 < w i) →
              OAI.PiExponent.separatedWeights S w →
              ∀ c : Fin K → Fin n → ℂ,
                (∀ i : Fin n, Function.Injective (fun j : Fin K => c j i)) →
                OAI.PiExponent.eventualLogJetSurjective n K w0 v0 q w c := by
    intro n
    induction n with
    | zero =>
        intro hn
        exact (Nat.lt_irrefl 0 hn).elim
    | succ n ih =>
        intro hn q hq hq1 hqvol1 hqvol2
        by_cases hn0 : n = 0
        · subst n
          obtain ⟨B, hB⟩ :=
            OAI.PiExponent.logarithmic_interpolation_one_transverse_threshold
              K hK w0 v0 q hw0 hv0 hq hq1
              (by simpa only [Nat.zero_add, pow_one] using hqvol1)
              (by simpa only [Nat.zero_add, pow_one] using hqvol2)
          refine ⟨fun _ => B, ?_⟩
          intro w hw hs c hc
          exact hB w hw (hs 0) c hc
        · have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
          obtain ⟨a, ha, ha1, hqa, havol1, havol2⟩ :=
            choose_lower_dimension_contraction n K hnpos hK
              w0 v0 q hw0 hv0 hq hq1 hqvol1 hqvol2
          exact
            OAI.PiExponent.logarithmic_interpolation_transverse_dimension_lift
              n K hnpos hK w0 v0 a q hw0 hv0 ha ha1 hq hq1 hqa
              (ih hnpos a ha ha1 havol1 havol2)
  exact hall m hm theta htheta htheta1 hvol1 hvol2

-- At degree zero, the strict jet cutoff is empty.
theorem OAI.PiExponent.logJetSurjective_zero_degree
    (m K : ℕ) (w0 v0 theta : ℚ) (w : Fin m → ℕ)
    (c : Fin K → Fin m → ℂ)
    (hv0 : 0 ≤ (v0 : ℝ)) (htheta : 0 ≤ (theta : ℝ)) :
    OAI.PiExponent.logJetSurjective m K w0 v0 theta w c 0 := by
  dsimp only [OAI.PiExponent.logJetSurjective]
  intro J
  refine ⟨0, ?_, ?_⟩
  · simp
  · intro j d hd
    have hterm (i : Fin m) :
        0 ≤ ((w i : ℝ) / (theta : ℝ)) * (d i.succ : ℝ) :=
      mul_nonneg
        (div_nonneg (Nat.cast_nonneg (w i)) htheta)
        (Nat.cast_nonneg (d i.succ))
    have hnonneg :
        0 ≤ (v0 : ℝ) * (d 0 : ℝ) +
          ∑ i : Fin m, ((w i : ℝ) / (theta : ℝ)) * (d i.succ : ℝ) :=
      add_nonneg
        (mul_nonneg hv0 (Nat.cast_nonneg (d 0)))
        (Finset.sum_nonneg (fun i _ => hterm i))
    exact (not_lt_of_ge hnonneg (by simpa using hd)).elim
