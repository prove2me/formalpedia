-- Prove2me | solution 1 for MassartDKW.Binom.theorem_2
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T13:18:27.234986+00:00
-- url     : https://prove2.me/submissions/46e5e5e2-cd43-45e4-bb71-91de8ebc54cf

import Mathlib
import Definitions.Def_MassartDKW_Binom_Setting

open MeasureTheory ProbabilityTheory


namespace MassartDKW.Binom

/-- derivative of `phi` -/
noncomputable def phiD (t : ℝ) : ℝ := t ^ 3 / ((3 + 2 * t) ^ 2 * (1 + t))

lemma phi_hasDerivAt {t : ℝ} (ht : 0 ≤ t) : HasDerivAt phi (phiD t) t := by
  have h1 : (0:ℝ) < 1 + t := by linarith
  have h2 : (2 * (1 + 2 * t / 3) : ℝ) ≠ 0 := by positivity
  have ha : HasDerivAt (fun t : ℝ => t ^ 2) (2 * t) t := by
    simpa using hasDerivAt_pow 2 t
  have hb : HasDerivAt (fun t : ℝ => 2 * (1 + 2 * t / 3)) (2 * (2 / 3)) t := by
    have := ((((hasDerivAt_id t).const_mul (2:ℝ)).div_const 3).const_add 1).const_mul (2:ℝ)
    simp only [id] at this
    exact this.congr_deriv (by ring)
  have hc : HasDerivAt (fun t : ℝ => Real.log (1 + t)) (1 / (1 + t)) t := by
    have := ((hasDerivAt_id t).const_add 1).log (ne_of_gt h1)
    simp only [id] at this
    exact this.congr_deriv (by ring)
  have hd := ((hasDerivAt_id t).sub (ha.div hb h2)).sub hc
  refine hd.congr_deriv ?_
  unfold phiD
  have h3 : (3 + 2 * t : ℝ) ≠ 0 := by positivity
  field_simp
  ring

lemma phiD_pos {t : ℝ} (ht : 0 < t) : 0 < phiD t := by
  unfold phiD; positivity

lemma phi_continuousOn : ContinuousOn phi (Set.Ici 0) := by
  intro t ht
  exact (phi_hasDerivAt ht).continuousAt.continuousWithinAt

lemma phi_deriv {t : ℝ} (ht : 0 ≤ t) : deriv phi t = phiD t := (phi_hasDerivAt ht).deriv

lemma phi_zero : phi 0 = 0 := by simp [phi]

lemma phi_strictMonoOn : StrictMonoOn phi (Set.Ici 0) := by
  refine strictMonoOn_of_deriv_pos (convex_Ici 0) phi_continuousOn ?_
  intro x hx
  rw [interior_Ici] at hx
  rw [phi_deriv (le_of_lt hx)]
  exact phiD_pos hx

lemma phi_pos {t : ℝ} (ht : 0 < t) : 0 < phi t := by
  have := phi_strictMonoOn ((Set.mem_Ici.2 le_rfl)) (le_of_lt ht : (0:ℝ) ≤ t) ht
  rwa [phi_zero] at this


/-- `g u = log(1+u) - 3u(6+u)/(2(3+u)^2)`, with `g' u = 1/(1+u) - 27/(3+u)^3 ≥ 0`. -/
noncomputable def gB (u : ℝ) : ℝ := Real.log (1 + u) - 3 * u * (6 + u) / (2 * (3 + u) ^ 2)

/-- `f u = (1+u) log(1+u) - u - u^2/(2(1+u/3))`, with `f' = g`. -/
noncomputable def fB (u : ℝ) : ℝ := (1 + u) * Real.log (1 + u) - u - u ^ 2 / (2 * (1 + u / 3))

lemma log_one_add_hasDerivAt {u : ℝ} (hu : 0 ≤ u) :
    HasDerivAt (fun u : ℝ => Real.log (1 + u)) (1 / (1 + u)) u := by
  have h1 : (1 + u : ℝ) ≠ 0 := by positivity
  have := ((hasDerivAt_id u).const_add 1).log h1
  simp only [id] at this
  exact this.congr_deriv (by ring)

lemma gB_hasDerivAt {u : ℝ} (hu : 0 ≤ u) :
    HasDerivAt gB (1 / (1 + u) - 27 / (3 + u) ^ 3) u := by
  have h3 : (3 + u : ℝ) ≠ 0 := by positivity
  have h3' : (2 * (3 + u) ^ 2 : ℝ) ≠ 0 := by positivity
  have ha : HasDerivAt (fun u : ℝ => 3 * u * (6 + u)) (3 * 1 * (6 + u) + 3 * u * 1) u := by
    have := ((hasDerivAt_id u).const_mul (3:ℝ)).mul ((hasDerivAt_id u).const_add 6)
    simp only [id] at this
    exact this.congr_deriv (by ring)
  have hb : HasDerivAt (fun u : ℝ => 2 * (3 + u) ^ 2) (2 * (2 * (3 + u))) u := by
    have := (((hasDerivAt_id u).const_add 3).pow 2).const_mul (2:ℝ)
    simp only [id] at this
    exact this.congr_deriv (by ring)
  have hd := (log_one_add_hasDerivAt hu).sub (ha.div hb h3')
  refine hd.congr_deriv ?_
  field_simp
  ring

lemma fB_hasDerivAt {u : ℝ} (hu : 0 ≤ u) : HasDerivAt fB (gB u) u := by
  have h1 : (1 + u : ℝ) ≠ 0 := by positivity
  have h3 : (3 + u : ℝ) ≠ 0 := by positivity
  have h2 : (2 * (1 + u / 3) : ℝ) ≠ 0 := by positivity
  have ha : HasDerivAt (fun u : ℝ => (1 + u) * Real.log (1 + u))
      (1 * Real.log (1 + u) + (1 + u) * (1 / (1 + u))) u := by
    have := ((hasDerivAt_id u).const_add 1).mul (log_one_add_hasDerivAt hu)
    simp only [id] at this
    exact this.congr_deriv (by ring)
  have hb : HasDerivAt (fun u : ℝ => u ^ 2) (2 * u) u := by
    simpa using hasDerivAt_pow 2 u
  have hc : HasDerivAt (fun u : ℝ => 2 * (1 + u / 3)) (2 * (1 / 3)) u := by
    have := (((hasDerivAt_id u).div_const 3).const_add 1).const_mul (2:ℝ)
    simp only [id] at this
    exact this.congr_deriv (by ring)
  have hd := (ha.sub (hasDerivAt_id u)).sub (hb.div hc h2)
  refine hd.congr_deriv ?_
  unfold gB
  field_simp
  ring

lemma gB_zero : gB 0 = 0 := by simp [gB]
lemma fB_zero : fB 0 = 0 := by simp [fB]

lemma gB_nonneg {u : ℝ} (hu : 0 ≤ u) : 0 ≤ gB u := by
  have hmono : MonotoneOn gB (Set.Ici 0) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici 0) ?_ ?_ ?_
    · intro x hx
      exact (gB_hasDerivAt hx).continuousAt.continuousWithinAt
    · intro x hx
      rw [interior_Ici] at hx
      exact (gB_hasDerivAt (le_of_lt hx)).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Ici] at hx
      have hx' : 0 < x := hx
      rw [(gB_hasDerivAt (le_of_lt hx')).deriv]
      have h27 : 27 * (1 + x) ≤ (3 + x) ^ 3 := by nlinarith [sq_nonneg x, pow_pos hx' 3]
      have hpos : (0:ℝ) < (3 + x) ^ 3 := by positivity
      have : 27 / (3 + x) ^ 3 ≤ 1 / (1 + x) := by
        rw [div_le_div_iff₀ hpos (by positivity)]
        linarith
      linarith
  have := hmono (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 hu) hu
  rwa [gB_zero] at this

lemma fB_nonneg {u : ℝ} (hu : 0 ≤ u) : 0 ≤ fB u := by
  have hmono : MonotoneOn fB (Set.Ici 0) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici 0) ?_ ?_ ?_
    · intro x hx
      exact (fB_hasDerivAt hx).continuousAt.continuousWithinAt
    · intro x hx
      rw [interior_Ici] at hx
      exact (fB_hasDerivAt (le_of_lt hx)).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Ici] at hx
      have hx' : 0 < x := hx
      rw [(fB_hasDerivAt (le_of_lt hx')).deriv]
      exact gB_nonneg (le_of_lt hx')
  have := hmono (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 hu) hu
  rwa [fB_zero] at this

/-- Bennett-type inequality: `(1+u) log(1+u) - u ≥ u^2/(2(1+u/3))` for `u ≥ 0`. -/
lemma bennett_ineq {u : ℝ} (hu : 0 ≤ u) :
    u ^ 2 / (2 * (1 + u / 3)) ≤ (1 + u) * Real.log (1 + u) - u := by
  have := fB_nonneg hu
  unfold fB at this
  linarith

/-- Scaled version: `ε + ε²/(2(p+ε/3)) ≤ (p+ε) log((p+ε)/p)`. -/
lemma key_ineq {p ε : ℝ} (hp : 0 < p) (hε : 0 ≤ ε) :
    ε + ε ^ 2 / (2 * (p + ε / 3)) ≤ (p + ε) * Real.log ((p + ε) / p) := by
  have hu : 0 ≤ ε / p := by positivity
  have h := bennett_ineq hu
  have e1 : (p + ε) / p = 1 + ε / p := by field_simp
  rw [e1]
  have e2 : (p + ε) * Real.log (1 + ε / p) = p * ((1 + ε / p) * Real.log (1 + ε / p)) := by
    field_simp
  have e3 : ε + ε ^ 2 / (2 * (p + ε / 3)) = p * ((ε / p) ^ 2 / (2 * (1 + ε / p / 3)) + ε / p) := by
    field_simp
    ring
  rw [e2, e3]
  apply mul_le_mul_of_nonneg_left _ (le_of_lt hp)
  linarith

theorem lemma_1_ii_core (p ε : ℝ) (hp : 0 < p) (hε : 0 < ε) (hεq : ε ≤ 1 - p) :
    (ε < 1 - p →
      ε ^ 2 / (2 * (p + ε / 3) * (1 - p - ε / 3))
          + ε * phi (ε / (1 - p - ε)) / (ε / (1 - p - ε)) ≤ h p ε) ∧
    (ε = 1 - p →
      ε ^ 2 / (2 * (p + ε / 3) * (1 - p - ε / 3)) + ε / 4 ≤ h p ε) := by
  have hK := key_ineq hp (le_of_lt hε)
  constructor
  · intro hlt
    have hq : 0 < 1 - p - ε := by linarith
    have hq' : 0 < 1 - p := by linarith
    set t := ε / (1 - p - ε) with ht
    have htpos : 0 < t := by positivity
    have e1 : 1 + t = (1 - p) / (1 - p - ε) := by rw [ht]; field_simp; ring
    have e2 : Real.log (1 + t) = - Real.log ((1 - p - ε) / (1 - p)) := by
      rw [e1, ← Real.log_inv, inv_div]
    have e3 : ε * phi t / t
        = ε - ε ^ 2 / (2 * (1 - p - ε / 3)) + (1 - p - ε) * Real.log ((1 - p - ε) / (1 - p)) := by
      unfold phi
      rw [e2, ht]
      have hQ : (1 - p - ε) ≠ 0 := hq.ne'
      have e13 : (1 - p - ε / 3) = (1 - p - ε) + 2 * ε / 3 := by ring
      rw [e13]
      generalize hL : Real.log ((1 - p - ε) / (1 - p)) = L
      generalize hQe : 1 - p - ε = Q at hQ hq ⊢
      have h5 : Q + 2 * ε / 3 ≠ 0 := by positivity
      have h6 : 3 * Q + 2 * ε ≠ 0 := by positivity
      have h7 : 1 + 2 * (ε / Q) / 3 ≠ 0 := by positivity
      field_simp
      ring
    have e4 : ε ^ 2 / (2 * (p + ε / 3) * (1 - p - ε / 3)) + (ε - ε ^ 2 / (2 * (1 - p - ε / 3)))
        = ε + ε ^ 2 / (2 * (p + ε / 3)) := by
      have h3' : (1 - p - ε / 3 : ℝ) ≠ 0 := by intro h; linarith
      have h4 : (p + ε / 3 : ℝ) ≠ 0 := by positivity
      generalize hD : 1 - p - ε / 3 = D at h3'
      generalize hA : p + ε / 3 = A at h4
      have hAD : A + D = 1 := by rw [← hA, ← hD]; ring
      field_simp
      linear_combination (-ε) * hAD
    unfold h
    rw [e3]
    linarith
  · intro heq
    subst heq
    unfold h
    have e0 : (1 - p - (1 - p)) = (0:ℝ) := by ring
    rw [e0, zero_mul, add_zero]
    have h3 : (0:ℝ) < 1 - p - (1 - p) / 3 := by linarith
    have h4 : (0:ℝ) < p + (1 - p) / 3 := by linarith
    have e5 : (1 - p) ^ 2 / (2 * (p + (1 - p) / 3) * (1 - p - (1 - p) / 3)) + (1 - p) / 4
        = (1 - p) + (1 - p) ^ 2 / (2 * (p + (1 - p) / 3)) := by
      field_simp
      ring
    rw [e5]
    exact hK


/-- Chernoff bound for a binomial random variable (any `t ≥ 0`). -/
lemma chernoff_binom {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (p : unitInterval) (S : Ω → ℕ) (hS : HasLaw S (binomial n p) P)
    (t : ℝ) (ht : 0 ≤ t) (a : ℝ) :
    P {ω | a ≤ (S ω : ℝ)} ≤
      ENNReal.ofReal (Real.exp (-t * a) * ((p : ℝ) * Real.exp t + (1 - (p : ℝ))) ^ n) := by
  have hg : AEStronglyMeasurable (fun k : ℕ => Real.exp (t * (k : ℝ))) (P.map S) :=
    Measurable.of_discrete.aestronglyMeasurable
  have hint : Integrable (fun ω => Real.exp (t * (S ω : ℝ))) P := by
    have := (integrable_map_measure hg hS.aemeasurable).1
    rw [hS.map_eq] at this
    exact this (integrable_binomial _)
  have hmgf : mgf (fun ω => (S ω : ℝ)) P t = ((p : ℝ) * Real.exp t + (1 - (p : ℝ))) ^ n := by
    unfold mgf
    rw [← integral_map hS.aemeasurable hg, hS.map_eq, integral_binomial, add_pow,
      ← Nat.range_succ_eq_Iic]
    apply Finset.sum_congr rfl
    intro k hk
    rw [mul_comm t, Real.exp_nat_mul, mul_pow, smul_eq_mul]
    ring
  have hch := measure_ge_le_exp_mul_mgf (X := fun ω => (S ω : ℝ)) (μ := P) a ht hint
  rw [hmgf, measureReal_def] at hch
  have hnn : 0 ≤ Real.exp (-t * a) * ((p : ℝ) * Real.exp t + (1 - (p : ℝ))) ^ n :=
    mul_nonneg (Real.exp_pos _).le
      (pow_nonneg (add_nonneg (mul_nonneg p.2.1 (Real.exp_pos t).le) (by linarith [p.2.2])) n)
  rw [ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) hnn]
  exact hch

theorem comment_3_core {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (p : unitInterval) (S : Ω → ℕ) (hS : HasLaw S (binomial n p) P)
    (hp : 0 < (p : ℝ)) (ε : ℝ) (hε : 0 < ε) (hεq : ε ≤ 1 - (p : ℝ)) :
    P {ω | (n : ℝ) * ε < (S ω : ℝ) - n * (p : ℝ)} ≤
      ENNReal.ofReal (Real.exp (-((n : ℝ) * h (p : ℝ) ε))) := by
  rcases hεq.lt_or_eq with hlt | heq
  · have hq : 0 < 1 - (p : ℝ) - ε := by linarith
    have hq' : 0 < 1 - (p : ℝ) := by linarith
    have hpe : 0 < (p : ℝ) + ε := by linarith
    have hratio : 1 ≤ ((p : ℝ) + ε) * (1 - p) / (p * (1 - p - ε)) := by
      rw [le_div_iff₀ (by positivity)]
      nlinarith
    have ht : 0 ≤ Real.log (((p : ℝ) + ε) * (1 - p) / (p * (1 - p - ε))) :=
      Real.log_nonneg hratio
    have hexp : Real.exp (Real.log (((p : ℝ) + ε) * (1 - p) / (p * (1 - p - ε))))
        = ((p : ℝ) + ε) * (1 - p) / (p * (1 - p - ε)) := Real.exp_log (by positivity)
    have hsub : {ω | (n : ℝ) * ε < (S ω : ℝ) - n * (p : ℝ)} ⊆
        {ω | (n : ℝ) * ((p : ℝ) + ε) ≤ (S ω : ℝ)} := by
      intro ω hω
      simp only [Set.mem_ofPred_eq] at hω ⊢
      linarith
    calc P {ω | (n : ℝ) * ε < (S ω : ℝ) - n * (p : ℝ)}
        ≤ P {ω | (n : ℝ) * ((p : ℝ) + ε) ≤ (S ω : ℝ)} := measure_mono hsub
      _ ≤ ENNReal.ofReal (Real.exp (-Real.log (((p : ℝ) + ε) * (1 - p) / (p * (1 - p - ε)))
            * ((n : ℝ) * ((p : ℝ) + ε))) *
            ((p : ℝ) * Real.exp (Real.log (((p : ℝ) + ε) * (1 - p) / (p * (1 - p - ε))))
              + (1 - (p : ℝ))) ^ n) := chernoff_binom P n p S hS _ ht _
      _ = ENNReal.ofReal (Real.exp (-((n : ℝ) * h (p : ℝ) ε))) := by
        congr 1
        rw [hexp]
        have e1 : (p : ℝ) * (((p : ℝ) + ε) * (1 - p) / (p * (1 - p - ε))) + (1 - (p : ℝ))
            = (1 - (p : ℝ)) / (1 - p - ε) := by
          field_simp
          ring
        rw [e1]
        have e2 : ((1 - (p : ℝ)) / (1 - p - ε)) ^ n
            = Real.exp ((n : ℝ) * Real.log ((1 - (p : ℝ)) / (1 - p - ε))) := by
          rw [Real.exp_nat_mul, Real.exp_log (by positivity)]
        rw [e2, ← Real.exp_add]
        congr 1
        unfold h
        rw [Real.log_div (by positivity) (by positivity), Real.log_div (by positivity) (by positivity),
          Real.log_div (by positivity) (by positivity), Real.log_div (by positivity) (by positivity),
          Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity)]
        ring
  · have h0 : P {ω | ¬ S ω ≤ n} = 0 := ae_iff.1 (ae_le_of_hasLaw_binomial hS)
    have hsub : {ω | (n : ℝ) * ε < (S ω : ℝ) - n * (p : ℝ)} ⊆ {ω | ¬ S ω ≤ n} := by
      intro ω hω
      simp only [Set.mem_ofPred_eq] at hω ⊢
      intro hle
      have : (S ω : ℝ) ≤ n := by exact_mod_cast hle
      rw [heq] at hω
      nlinarith
    calc P {ω | (n : ℝ) * ε < (S ω : ℝ) - n * (p : ℝ)} ≤ P {ω | ¬ S ω ≤ n} := measure_mono hsub
      _ = 0 := h0
      _ ≤ _ := bot_le

theorem theorem_2_core {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (p : unitInterval) (S : Ω → ℕ) (hS : HasLaw S (binomial n p) P)
    (ε : ℝ) (hε : 0 < ε) (hεq : ε ≤ 1 - (p : ℝ)) :
    P {ω | (n : ℝ) * ε < (S ω : ℝ) - n * (p : ℝ)} ≤
      ENNReal.ofReal (Real.exp (-((n : ℝ) * ε ^ 2) /
        (2 * ((p : ℝ) + ε / 3) * (1 - (p : ℝ) - ε / 3)))) := by
  have hD : 0 < 2 * ((p : ℝ) + ε / 3) * (1 - (p : ℝ) - ε / 3) := by
    have := p.2.1
    have : 0 < 1 - (p : ℝ) - ε / 3 := by linarith
    positivity
  by_cases hp : 0 < (p : ℝ)
  · have hkey : ε ^ 2 / (2 * ((p : ℝ) + ε / 3) * (1 - (p : ℝ) - ε / 3)) ≤ h (p : ℝ) ε := by
      obtain ⟨h1, h2⟩ := lemma_1_ii_core (p : ℝ) ε hp hε hεq
      rcases hεq.lt_or_eq with hlt | heq
      · have := h1 hlt
        have hq : 0 < 1 - (p : ℝ) - ε := by linarith
        have htpos : 0 < ε / (1 - (p : ℝ) - ε) := by positivity
        have : 0 ≤ ε * phi (ε / (1 - (p : ℝ) - ε)) / (ε / (1 - (p : ℝ) - ε)) := by
          have := phi_pos htpos
          positivity
        linarith
      · have := h2 heq
        linarith
    calc P {ω | (n : ℝ) * ε < (S ω : ℝ) - n * (p : ℝ)}
        ≤ ENNReal.ofReal (Real.exp (-((n : ℝ) * h (p : ℝ) ε))) := comment_3_core P n p S hS hp ε hε hεq
      _ ≤ _ := by
        apply ENNReal.ofReal_le_ofReal
        apply Real.exp_le_exp.2
        have := mul_le_mul_of_nonneg_left hkey (Nat.cast_nonneg n)
        have e : -((n : ℝ) * ε ^ 2) / (2 * ((p : ℝ) + ε / 3) * (1 - (p : ℝ) - ε / 3))
            = -((n : ℝ) * (ε ^ 2 / (2 * ((p : ℝ) + ε / 3) * (1 - (p : ℝ) - ε / 3)))) := by ring
        rw [e]
        linarith
  · have hp0 : (p : ℝ) = 0 := le_antisymm (not_lt.1 hp) p.2.1
    set t : ℝ := ε / (2 * ((p : ℝ) + ε / 3) * (1 - (p : ℝ) - ε / 3)) with ht
    have ht0 : 0 ≤ t := by positivity
    have hsub : {ω | (n : ℝ) * ε < (S ω : ℝ) - n * (p : ℝ)} ⊆ {ω | (n : ℝ) * ε ≤ (S ω : ℝ)} := by
      intro ω hω
      simp only [Set.mem_ofPred_eq] at hω ⊢
      rw [hp0] at hω
      linarith
    calc P {ω | (n : ℝ) * ε < (S ω : ℝ) - n * (p : ℝ)}
        ≤ P {ω | (n : ℝ) * ε ≤ (S ω : ℝ)} := measure_mono hsub
      _ ≤ ENNReal.ofReal (Real.exp (-t * ((n : ℝ) * ε)) * ((p : ℝ) * Real.exp t + (1 - (p : ℝ))) ^ n) :=
          chernoff_binom P n p S hS t ht0 _
      _ = _ := by
        congr 1
        rw [hp0, zero_mul, zero_add, sub_zero, one_pow, mul_one, ht]
        congr 1
        rw [hp0]
        ring

end MassartDKW.Binom

open MassartDKW.Binom


theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (p : unitInterval) (S : Ω → ℕ) (hS : HasLaw S (binomial n p) P)
    (ε : ℝ) (hε : 0 < ε) (hεq : ε ≤ 1 - (p : ℝ)) :
    P {ω | (n : ℝ) * ε < (S ω : ℝ) - n * (p : ℝ)} ≤
      ENNReal.ofReal (Real.exp (-((n : ℝ) * ε ^ 2) /
        (2 * ((p : ℝ) + ε / 3) * (1 - (p : ℝ) - ε / 3)))) := by
  exact theorem_2_core P n p S hS ε hε hεq
