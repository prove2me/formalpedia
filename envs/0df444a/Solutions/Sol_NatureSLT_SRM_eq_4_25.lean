-- Prove2me | solution 1 for NatureSLT.SRM.eq_4_25
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T14:40:06.919809+00:00
-- url     : https://prove2.me/submissions/a1ccec33-2e36-495d-8471-66b1bcc4d7e6

import Mathlib

open MeasureTheory
theorem g70slt_expneg (x : ℝ) (hx : 0 ≤ x) : Real.exp (-x) ≤ 1 - x + x ^ 2 / 2 := by
  have h1 := Real.quadratic_le_exp_of_nonneg hx
  have hpos : 0 < 1 + x + x ^ 2 / 2 := by positivity
  rw [Real.exp_neg, inv_le_iff_one_le_mul₀ (Real.exp_pos x)]
  nlinarith [sq_nonneg (x ^ 2), sq_nonneg x]

theorem g70slt_chernoff {Z : Type*} [MeasurableSpace Z] (F : Measure Z) [IsProbabilityMeasure F]
    (q : Z → ℝ) (hq01 : ∀ z, q z = 0 ∨ q z = 1) (hqm : Measurable q) (ℓ : ℕ) (δ : ℝ)
    (hδ : 0 ≤ δ) :
    (Measure.pi fun _ : Fin ℓ => F).real {z | ∑ i, q (z i) ≤ ℓ * (∫ x, q x ∂F) * (1 - δ)}
      ≤ Real.exp (-(ℓ * (∫ x, q x ∂F) * δ ^ 2 / 2)) := by
  set p := ∫ x, q x ∂F with hp
  set μ := Measure.pi fun _ : Fin ℓ => F
  have hqb : ∀ z, 0 ≤ q z ∧ q z ≤ 1 := fun z => by rcases hq01 z with h | h <;> rw [h] <;> norm_num
  have hqi : Integrable q F := Integrable.of_bound hqm.aestronglyMeasurable 1
    (Filter.Eventually.of_forall fun z => by rw [Real.norm_eq_abs, abs_of_nonneg (hqb z).1]; exact (hqb z).2)
  have hp0 : 0 ≤ p := integral_nonneg fun z => (hqb z).1
  have hp1 : p ≤ 1 := by
    have : ∫ x, q x ∂F ≤ ∫ _x, (1:ℝ) ∂F := integral_mono hqi (integrable_const _) fun z => (hqb z).2
    simpa using this
  have hXm : Measurable fun z : Fin ℓ → Z => ∑ i, q (z i) :=
    Finset.measurable_sum _ fun i _ => hqm.comp (measurable_pi_apply i)
  have hint : Integrable (fun z : Fin ℓ → Z => Real.exp (-δ * ∑ i, q (z i))) μ := by
    refine Integrable.of_bound ((hXm.const_mul (-δ)).exp).aestronglyMeasurable 1 (Filter.Eventually.of_forall fun z => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff]
    have : 0 ≤ ∑ i, q (z i) := Finset.sum_nonneg fun i _ => (hqb _).1
    nlinarith
  have h := ProbabilityTheory.measure_le_le_exp_mul_mgf (μ := μ)
    (X := fun z : Fin ℓ → Z => ∑ i, q (z i)) (ℓ * p * (1 - δ)) (t := -δ) (by linarith) hint
  have hpt : ∀ z, Real.exp (-δ * q z) = 1 + (Real.exp (-δ) - 1) * q z := by
    intro z; rcases hq01 z with h | h <;> rw [h] <;> simp
  have hmgf : ProbabilityTheory.mgf (fun z : Fin ℓ → Z => ∑ i, q (z i)) μ (-δ)
      = (1 + (Real.exp (-δ) - 1) * p) ^ ℓ := by
    unfold ProbabilityTheory.mgf
    have e : (fun z : Fin ℓ → Z => Real.exp (-δ * ∑ i, q (z i))) =
        fun z => ∏ i, Real.exp (-δ * q (z i)) := by
      funext z; rw [Finset.mul_sum, Real.exp_sum]
    rw [e, integral_fintype_prod_eq_prod (f := fun _ x => Real.exp (-δ * q x))]
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    congr 1
    simp only [hpt]
    rw [integral_add (integrable_const _) (hqi.const_mul _), integral_const, integral_const_mul]
    simp [hp]
  rw [hmgf] at h
  have hm0 : 0 ≤ 1 + (Real.exp (-δ) - 1) * p := by
    nlinarith [Real.exp_pos (-δ)]
  have hm1 : (1 + (Real.exp (-δ) - 1) * p) ^ ℓ ≤ Real.exp (ℓ * ((Real.exp (-δ) - 1) * p)) := by
    rw [Real.exp_nat_mul]
    exact pow_le_pow_left₀ hm0 (by linarith [Real.add_one_le_exp ((Real.exp (-δ) - 1) * p)]) ℓ
  refine h.trans ?_
  calc Real.exp (-(-δ) * (ℓ * p * (1 - δ))) * (1 + (Real.exp (-δ) - 1) * p) ^ ℓ
      ≤ Real.exp (-(-δ) * (ℓ * p * (1 - δ))) * Real.exp (ℓ * ((Real.exp (-δ) - 1) * p)) :=
        mul_le_mul_of_nonneg_left hm1 (Real.exp_pos _).le
    _ = Real.exp (ℓ * p * (δ - δ ^ 2 + Real.exp (-δ) - 1)) := by rw [← Real.exp_add]; ring_nf
    _ ≤ _ := by
        apply Real.exp_le_exp.mpr
        have := g70slt_expneg δ hδ
        have hlp : 0 ≤ (ℓ:ℝ) * p := by positivity
        nlinarith


/-- **Eq. (4.25)** (Vapnik, *The Nature of Statistical Learning Theory*, 2nd ed., p. 108): for a
learning machine with a finite number `N` of measurable indicator functions `Q(z, α) ∈ {0, 1}`,
`α ∈ Λ`, `N = |Λ|` (the `N` tables of a codebook), with probability at least `1 − η` the
inequality `R(α) ≤ R_emp(α) + ((ln N − ln η)/ℓ) (1 + √(1 + 2 R_emp(α) ℓ/(ln N − ln η)))`
holds simultaneously for all `N` functions. -/
theorem solution {Z Λ : Type*} [MeasurableSpace Z] (F : Measure Z) [IsProbabilityMeasure F]
    [Fintype Λ] [Nonempty Λ]
    (Q : Λ → Z → ℝ) (hQ01 : ∀ α z, Q α z = 0 ∨ Q α z = 1) (hQmeas : ∀ α, Measurable (Q α))
    (ℓ : ℕ) (hℓ : 0 < ℓ) (η : ℝ) (hη0 : 0 < η) (hη1 : η < 1) :
    let L : ℝ := Real.log (Fintype.card Λ) - Real.log η
    let Remp : Λ → (Fin ℓ → Z) → ℝ := fun α z => (1 / (ℓ : ℝ)) * ∑ i, Q α (z i)
    ENNReal.ofReal (1 - η) ≤ (Measure.pi fun _ : Fin ℓ => F)
      {z | ∀ α, ∫ x, Q α x ∂F ≤
        Remp α z + L / ℓ * (1 + Real.sqrt (1 + 2 * Remp α z * ℓ / L))} := by
  intro L Remp
  classical
  set μ := Measure.pi fun _ : Fin ℓ => F with hμ
  have hN : (1:ℝ) ≤ Fintype.card Λ := by exact_mod_cast Fintype.card_pos
  have hNpos : (0:ℝ) < Fintype.card Λ := by linarith
  have hL : 0 < L := by
    have h1 : 0 ≤ Real.log (Fintype.card Λ) := Real.log_nonneg hN
    have h2 : Real.log η < 0 := Real.log_neg hη0 hη1
    show 0 < Real.log (Fintype.card Λ) - Real.log η
    linarith
  have hℓpos : (0:ℝ) < ℓ := by exact_mod_cast hℓ
  have hRemp0 : ∀ α z, 0 ≤ Remp α z := fun α z => by
    have : ∀ i, 0 ≤ Q α (z i) := fun i => by rcases hQ01 α (z i) with h | h <;> rw [h] <;> norm_num
    exact mul_nonneg (by positivity) (Finset.sum_nonneg fun i _ => this i)
  set bad : Λ → Set (Fin ℓ → Z) := fun α => {z | ¬ (∫ x, Q α x ∂F ≤
    Remp α z + L / ℓ * (1 + Real.sqrt (1 + 2 * Remp α z * ℓ / L)))} with hbaddef
  have hbad : ∀ α, μ (bad α) ≤ ENNReal.ofReal (η / Fintype.card Λ) := by
    intro α
    set p := ∫ x, Q α x ∂F with hp
    have hp0 : 0 ≤ p := integral_nonneg fun z => by
      rcases hQ01 α z with h | h <;> rw [h] <;> norm_num
    rcases hp0.eq_or_lt with hp0 | hppos
    · have : bad α = ∅ := by
        ext z
        simp only [hbaddef, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_not]
        have hr := hRemp0 α z
        have : 0 ≤ L / ℓ * (1 + Real.sqrt (1 + 2 * Remp α z * ℓ / L)) := by positivity
        rw [← hp, ← hp0]; linarith
      rw [this, measure_empty]; exact bot_le
    · set δ := Real.sqrt (2 * L / (ℓ * p)) with hδ
      have hδ0 : 0 ≤ δ := Real.sqrt_nonneg _
      have hδsq : δ ^ 2 = 2 * L / (ℓ * p) := Real.sq_sqrt (by positivity)
      have hsub : bad α ⊆ {z | ∑ i, Q α (z i) ≤ ℓ * p * (1 - δ)} := by
        intro z hz
        simp only [hbaddef, Set.mem_setOf_eq, not_le] at hz
        simp only [Set.mem_setOf_eq]
        by_contra hc
        push Not at hc
        have hr0 := hRemp0 α z
        set r := Remp α z with hrdef
        have hsum : ∑ i, Q α (z i) = ℓ * r := by
          simp only [hrdef, Remp]; field_simp
        rw [hsum] at hc
        have h1 : p * (1 - δ) < r := lt_of_mul_lt_mul_left (by linarith) hℓpos.le
        set s := Real.sqrt (1 + 2 * r * ℓ / L) with hs
        have hs0 : 0 ≤ s := Real.sqrt_nonneg _
        have hs2 : s ^ 2 = 1 + 2 * r * ℓ / L := Real.sq_sqrt (by positivity)
        set c := L / ℓ with hc'
        have hc0 : 0 < c := by positivity
        have hpr : r < p := by
          have : 0 ≤ c * (1 + s) := by positivity
          linarith
        have hk : (p - r) ^ 2 < 2 * c * p := by
          have h2 : p - r < p * δ := by linarith
          have h3 : (p - r) ^ 2 < (p * δ) ^ 2 := by
            apply pow_lt_pow_left₀ h2 (by linarith)
            norm_num
          have h4 : (p * δ) ^ 2 = 2 * c * p := by
            rw [mul_pow, hδsq, hc']; field_simp
          linarith
        have hcs : (c * s) ^ 2 = c ^ 2 + 2 * c * r := by
          rw [mul_pow, hs2, hc']; field_simp
        have hcs0 : 0 ≤ c * s := by positivity
        nlinarith
      calc μ (bad α) ≤ μ {z | ∑ i, Q α (z i) ≤ ℓ * p * (1 - δ)} := measure_mono hsub
        _ = ENNReal.ofReal (μ.real {z | ∑ i, Q α (z i) ≤ ℓ * p * (1 - δ)}) :=
          (ofReal_measureReal).symm
        _ ≤ ENNReal.ofReal (Real.exp (-(ℓ * p * δ ^ 2 / 2))) :=
          ENNReal.ofReal_le_ofReal (g70slt_chernoff F (Q α) (hQ01 α) (hQmeas α) ℓ δ hδ0)
        _ = ENNReal.ofReal (η / Fintype.card Λ) := by
          congr 1
          have : ℓ * p * δ ^ 2 / 2 = L := by rw [hδsq]; field_simp
          rw [this]
          show Real.exp (-(Real.log (Fintype.card Λ) - Real.log η)) = _
          rw [neg_sub, Real.exp_sub, Real.exp_log hη0, Real.exp_log hNpos]
  have hU : μ (⋃ α, bad α) ≤ ENNReal.ofReal η :=
    calc μ (⋃ α, bad α) ≤ ∑ α, μ (bad α) := measure_iUnion_fintype_le μ bad
      _ ≤ ∑ _α : Λ, ENNReal.ofReal (η / Fintype.card Λ) := Finset.sum_le_sum fun α _ => hbad α
      _ = ENNReal.ofReal η := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
          ← ENNReal.ofReal_mul (by positivity)]
        congr 1; field_simp
  set S := {z : Fin ℓ → Z | ∀ α, ∫ x, Q α x ∂F ≤
        Remp α z + L / ℓ * (1 + Real.sqrt (1 + 2 * Remp α z * ℓ / L))} with hS
  have hcover : Set.univ ⊆ S ∪ ⋃ α, bad α := by
    intro z _
    by_cases h : z ∈ S
    · exact Or.inl h
    · right
      simp only [hS, Set.mem_setOf_eq, not_forall] at h
      obtain ⟨α, hα⟩ := h
      exact Set.mem_iUnion.mpr ⟨α, hα⟩
  have h1 : (1 : ENNReal) ≤ μ S + ENNReal.ofReal η :=
    calc (1 : ENNReal) = μ Set.univ := measure_univ.symm
      _ ≤ μ (S ∪ ⋃ α, bad α) := measure_mono hcover
      _ ≤ μ S + μ (⋃ α, bad α) := measure_union_le _ _
      _ ≤ μ S + ENNReal.ofReal η := add_le_add_right hU _
  rw [ENNReal.ofReal_sub _ hη0.le, ENNReal.ofReal_one]
  exact tsub_le_iff_right.mpr h1

