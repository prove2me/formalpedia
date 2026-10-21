-- Prove2me | solution 1 for LQGMapII.Kolmogorov.eq_2_11
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T00:55:34.025727+00:00
-- url     : https://prove2.me/submissions/0748b000-b171-43fc-9c07-67a0133a1904

import Mathlib
import Definitions.Def_LQGMapII_Kolmogorov_Setting

set_option autoImplicit false
open MeasureTheory ProbabilityTheory LQGMapII.Kolmogorov
open scoped NNReal ENNReal

theorem kc_cheb {d : ℕ} {α β : ℝ} {c₀ : ℝ≥0} (hα : 0 < α) (hβ : 0 < β) 
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Cube d → Ω → ℝ) (hX : IsKolmogorovProcess X P α ((d : ℝ) + β) c₀)
    (u v : Cube d) (δ : ℝ) (hδ : 0 < δ) :
    P {ω | δ ≤ |X u ω - X v ω|} ≤
      ENNReal.ofReal ((c₀ : ℝ) * δ ^ (-α) * dist u v ^ ((d : ℝ) + β)) := by
  set ε : ℝ≥0∞ := ENNReal.ofReal δ ^ α with hε
  have hε0 : ε ≠ 0 := by
    have : 0 < ENNReal.ofReal δ := ENNReal.ofReal_pos.2 hδ
    exact (ENNReal.rpow_pos this ENNReal.ofReal_ne_top).ne'
  have hεt : ε ≠ ∞ := ENNReal.rpow_ne_top_of_nonneg hα.le ENNReal.ofReal_ne_top
  have hmeas : Measurable (fun ω => edist (X u ω) (X v ω)) := hX.measurable_edist
  have hsub : {ω | δ ≤ |X u ω - X v ω|} ⊆
      {ω | ε ≤ edist (X u ω) (X v ω) ^ α} := by
    intro ω hω
    simp only [Set.mem_setOf_eq] at hω ⊢
    rw [hε]
    apply ENNReal.rpow_le_rpow _ hα.le
    rw [edist_dist, Real.dist_eq]
    exact ENNReal.ofReal_le_ofReal hω
  have hmark := mul_meas_ge_le_lintegral₀ (μ := P)
    ((hmeas.pow_const α).aemeasurable) ε
  have hk := hX.kolmogorovCondition u v
  have h1 : ε * P {ω | δ ≤ |X u ω - X v ω|} ≤ (c₀ : ℝ≥0∞) * edist u v ^ ((d : ℝ) + β) :=
    calc ε * P {ω | δ ≤ |X u ω - X v ω|} ≤ ε * P {ω | ε ≤ edist (X u ω) (X v ω) ^ α} := by
          gcongr
      _ ≤ _ := hmark
      _ ≤ _ := hk
  rw [ENNReal.mul_le_iff_le_inv hε0 hεt] at h1
  refine h1.trans (le_of_eq ?_)
  have hdist : edist u v = ENNReal.ofReal (dist u v) := edist_dist u v
  have hq : (0:ℝ) ≤ (d : ℝ) + β := by positivity
  rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity), hdist,
    ← ENNReal.ofReal_rpow_of_nonneg dist_nonneg hq, Real.rpow_neg hδ.le,
    ENNReal.ofReal_inv_of_pos (by positivity), ← ENNReal.ofReal_rpow_of_pos hδ, ENNReal.ofReal_coe_nnreal,
    hε]
  ring


lemma kc_dist_adj {d k : ℕ} {u v : Cube d} (h : IsAdjacentPair d k u v) :
    dist u v = (2 : ℝ)⁻¹ ^ k := by
  obtain ⟨_, _, i, hi, hd⟩ := h
  rw [Subtype.dist_eq, EuclideanSpace.dist_eq]
  rw [Finset.sum_eq_single i]
  · rw [Real.dist_eq, sq_abs, Real.sqrt_sq_eq_abs, hd]
  · intro j _ hj
    rw [hi j hj]; simp
  · intro h; exact absurd (Finset.mem_univ i) h

theorem kc_pair {d : ℕ} {α β γ : ℝ} {c₀ : ℝ≥0} (hα : 0 < α) (hβ : 0 < β) (hc₀ : 0 < c₀)
    (hγ : 0 < γ) (hγβ : γ < β / α)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Cube d → Ω → ℝ) (hX : IsKolmogorovProcess X P α ((d : ℝ) + β) c₀)
    (k : ℕ) (u v : Cube d) (huv : IsAdjacentPair d k u v) (t : ℝ) (ht : 0 < t) :
    P {ω | t * (2 : ℝ) ^ (-(γ * k)) ≤ |X u ω - X v ω|} ≤
      ENNReal.ofReal ((c₀ : ℝ) * t ^ (-α) * (2 : ℝ) ^ (-((k : ℝ) * ((d : ℝ) + β - α * γ)))) := by
  have h2 : (0:ℝ) < (2:ℝ) ^ (-(γ * k)) := by positivity
  have := kc_cheb hα hβ P X hX u v (t * (2 : ℝ) ^ (-(γ * k))) (by positivity)
  refine this.trans (le_of_eq ?_)
  congr 1
  rw [kc_dist_adj huv, Real.mul_rpow ht.le h2.le, ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
  have e1 : ((2:ℝ)⁻¹ ^ k) = (2:ℝ) ^ (-(k:ℝ)) := by
    rw [Real.rpow_neg (by norm_num), Real.rpow_natCast, inv_pow]
  rw [e1, ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
  have e2 : (2:ℝ) ^ (-(γ * k) * -α) * (2:ℝ) ^ (-(k:ℝ) * ((d:ℝ) + β)) = (2:ℝ) ^ (-((k : ℝ) * ((d : ℝ) + β - α * γ))) := by
    rw [← Real.rpow_add (by norm_num)]
    congr 1; ring
  rw [← e2]
  ring


/-- parametrisation of the level-`k` adjacent pairs -/
abbrev KcG (d k : ℕ) := Fin d × Bool × (Fin d → Fin (2 ^ k + 1))

noncomputable def kcpu {d : ℕ} (k : ℕ) (g : KcG d k) (j : Fin d) : ℝ :=
  ((g.2.2 j : ℕ) : ℝ) / (2:ℝ) ^ k

noncomputable def kcpv {d : ℕ} (k : ℕ) (g : KcG d k) (j : Fin d) : ℝ :=
  kcpu k g j + (if j = g.1 then (if g.2.1 then (2:ℝ)⁻¹ ^ k else -((2:ℝ)⁻¹ ^ k)) else 0)

lemma kc_param {d k : ℕ} {u v : Cube d} (h : IsAdjacentPair d k u v) :
    ∃ g : KcG d k, (∀ j, (u : EuclideanSpace ℝ (Fin d)) j = kcpu k g j) ∧
      (∀ j, (v : EuclideanSpace ℝ (Fin d)) j = kcpv k g j) := by
  obtain ⟨hu, hv, i, hi, hd⟩ := h
  choose m hm using hu
  have hk : (0:ℝ) < (2:ℝ) ^ k := by positivity
  have hb : ∀ j, 0 ≤ m j ∧ m j ≤ 2 ^ k := by
    intro j
    have h1 := (u.2 j).1
    have h2 := (u.2 j).2
    rw [hm j] at h1 h2
    constructor
    · have : (0:ℝ) ≤ (m j : ℝ) := by
        rwa [le_div_iff₀ hk, zero_mul] at h1
      exact_mod_cast this
    · have : (m j : ℝ) ≤ (2:ℝ) ^ k := by
        rwa [div_le_one hk] at h2
      exact_mod_cast this
  let mm : Fin d → Fin (2 ^ k + 1) := fun j => ⟨(m j).toNat, by
    have := (hb j).2
    have h3 : ((m j).toNat : ℤ) = m j := Int.toNat_of_nonneg (hb j).1
    have : ((m j).toNat : ℤ) ≤ 2 ^ k := by rw [h3]; exact (hb j).2
    have : (m j).toNat ≤ 2 ^ k := by exact_mod_cast this
    omega⟩
  have hmm : ∀ j, ((mm j : ℕ) : ℝ) = (m j : ℝ) := by
    intro j
    have h3 : ((m j).toNat : ℤ) = m j := Int.toNat_of_nonneg (hb j).1
    show (((m j).toNat : ℕ) : ℝ) = (m j : ℝ)
    exact_mod_cast h3
  have hpu : ∀ j, (u : EuclideanSpace ℝ (Fin d)) j = ((mm j : ℕ) : ℝ) / (2:ℝ) ^ k := by
    intro j; rw [hm j, hmm j]
  rcases (abs_eq (by positivity : (0:ℝ) ≤ (2:ℝ)⁻¹ ^ k)).1 hd with h1 | h1
  · -- u i - v i = c, so v i = u i - c
    refine ⟨(i, false, mm), hpu, ?_⟩
    intro j
    by_cases hj : j = i
    · subst hj
      simp only [kcpv, kcpu, if_true]
      have := hpu j
      simp only [Bool.false_eq_true, if_false]
      linarith
    · simp only [kcpv, kcpu, hj, if_false, add_zero]
      rw [← hi j hj]; exact hpu j
  · refine ⟨(i, true, mm), hpu, ?_⟩
    intro j
    by_cases hj : j = i
    · subst hj
      simp only [kcpv, kcpu, if_true]
      have := hpu j
      linarith
    · simp only [kcpv, kcpu, hj, if_false, add_zero]
      rw [← hi j hj]; exact hpu j

lemma kc_card {d k : ℕ} : ∃ (F : Fintype {p : Cube d × Cube d // IsAdjacentPair d k p.1 p.2}),
    Fintype.card {p : Cube d × Cube d // IsAdjacentPair d k p.1 p.2} ≤ d * 2 * (2 ^ k + 1) ^ d := by
  classical
  have hs : ∀ p : {p : Cube d × Cube d // IsAdjacentPair d k p.1 p.2},
      ∃ g : KcG d k, (∀ j, (p.1.1 : EuclideanSpace ℝ (Fin d)) j = kcpu k g j) ∧
        (∀ j, (p.1.2 : EuclideanSpace ℝ (Fin d)) j = kcpv k g j) := fun p => kc_param p.2
  choose σ hσ using hs
  have hinj : Function.Injective σ := by
    intro p q h
    apply Subtype.ext
    have h1 := hσ p
    have h2 := hσ q
    rw [h] at h1
    apply Prod.ext
    · apply Subtype.ext
      ext j
      rw [h1.1 j, h2.1 j]
    · apply Subtype.ext
      ext j
      rw [h1.2 j, h2.2 j]
  letI : Fintype {p : Cube d × Cube d // IsAdjacentPair d k p.1 p.2} := Fintype.ofInjective σ hinj
  refine ⟨this, ?_⟩
  calc Fintype.card {p : Cube d × Cube d // IsAdjacentPair d k p.1 p.2}
      ≤ Fintype.card (KcG d k) := Fintype.card_le_of_injective σ hinj
    _ = d * 2 * (2 ^ k + 1) ^ d := by simp; ring

theorem solution (d : ℕ) (α β γ : ℝ) (c₀ : ℝ≥0) (hα : 0 < α) (hβ : 0 < β) (hc₀ : 0 < c₀)
    (hγ : 0 < γ) (hγβ : γ < β / α) :
    ∃ c₁ : ℝ, 0 < c₁ ∧
      ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (X : Cube d → Ω → ℝ), IsKolmogorovProcess X P α ((d : ℝ) + β) c₀ →
        ∀ (k : ℕ) (t : ℝ), 0 < t →
          P {ω | ∃ u v, IsAdjacentPair d k u v ∧ t * (2 : ℝ) ^ (-(γ * k)) ≤ |X u ω - X v ω|} ≤
            ENNReal.ofReal (c₁ * t ^ (-α) * (2 : ℝ) ^ (-((k : ℝ) * (β - α * γ)))) := by
  refine ⟨(2 * d + 1) * 2 ^ d * (c₀ : ℝ), by positivity, ?_⟩
  intro Ω _ P _ X hX k t ht
  obtain ⟨F, hF⟩ := kc_card (d := d) (k := k)
  letI := F
  have hunion : {ω | ∃ u v, IsAdjacentPair d k u v ∧ t * (2 : ℝ) ^ (-(γ * k)) ≤ |X u ω - X v ω|}
      = ⋃ p : {p : Cube d × Cube d // IsAdjacentPair d k p.1 p.2},
          {ω | t * (2 : ℝ) ^ (-(γ * k)) ≤ |X p.1.1 ω - X p.1.2 ω|} := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_iUnion]
    constructor
    · rintro ⟨u, v, h1, h2⟩; exact ⟨⟨(u, v), h1⟩, h2⟩
    · rintro ⟨⟨⟨u, v⟩, h1⟩, h2⟩; exact ⟨u, v, h1, h2⟩
  rw [hunion]
  set b : ℝ := (c₀ : ℝ) * t ^ (-α) * (2 : ℝ) ^ (-((k : ℝ) * ((d : ℝ) + β - α * γ))) with hb
  calc P (⋃ p : {p : Cube d × Cube d // IsAdjacentPair d k p.1 p.2},
          {ω | t * (2 : ℝ) ^ (-(γ * k)) ≤ |X p.1.1 ω - X p.1.2 ω|})
      ≤ ∑ p : {p : Cube d × Cube d // IsAdjacentPair d k p.1 p.2},
          P {ω | t * (2 : ℝ) ^ (-(γ * k)) ≤ |X p.1.1 ω - X p.1.2 ω|} := measure_iUnion_fintype_le _ _
    _ ≤ ∑ p : {p : Cube d × Cube d // IsAdjacentPair d k p.1 p.2}, ENNReal.ofReal b := by
        apply Finset.sum_le_sum
        intro p _
        exact kc_pair hα hβ hc₀ hγ hγβ P X hX k p.1.1 p.1.2 p.2 t ht
    _ = (Fintype.card {p : Cube d × Cube d // IsAdjacentPair d k p.1 p.2} : ℝ≥0∞) * ENNReal.ofReal b := by
        simp
    _ ≤ ((d * 2 * (2 ^ k + 1) ^ d : ℕ) : ℝ≥0∞) * ENNReal.ofReal b := by
        gcongr
    _ = ENNReal.ofReal (((d * 2 * (2 ^ k + 1) ^ d : ℕ) : ℝ) * b) := by
        rw [ENNReal.ofReal_mul (p := ((d * 2 * (2 ^ k + 1) ^ d : ℕ) : ℝ)) (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
    _ ≤ _ := by
        apply ENNReal.ofReal_le_ofReal
        have hk2 : (0:ℝ) < (2:ℝ) ^ k := by positivity
        have h1 : ((2:ℝ) ^ k + 1) ^ d ≤ 2 ^ d * ((2:ℝ) ^ k) ^ d := by
          rw [← mul_pow]
          apply pow_le_pow_left₀ (by positivity)
          have : (1:ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
          linarith
        have hbpos : 0 ≤ b := by positivity
        have h2 : ((d * 2 * (2 ^ k + 1) ^ d : ℕ) : ℝ) ≤ d * 2 * (2 ^ d * ((2:ℝ) ^ k) ^ d) := by
          push_cast
          gcongr
        calc ((d * 2 * (2 ^ k + 1) ^ d : ℕ) : ℝ) * b ≤ d * 2 * (2 ^ d * ((2:ℝ) ^ k) ^ d) * b := by gcongr
          _ ≤ _ := by
            have e1 : ((2:ℝ) ^ k) ^ d = (2:ℝ) ^ ((k:ℝ) * d) := by
              rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
            have e2 : (2:ℝ) ^ ((k:ℝ) * d) * (2:ℝ) ^ (-((k : ℝ) * ((d : ℝ) + β - α * γ))) =
                (2:ℝ) ^ (-((k : ℝ) * (β - α * γ))) := by
              rw [← Real.rpow_add (by norm_num)]
              congr 1; ring
            have e3 : d * 2 * (2 ^ d * ((2:ℝ) ^ k) ^ d) * b =
                (2 * d) * 2 ^ d * (c₀:ℝ) * t ^ (-α) *
                  ((2:ℝ) ^ ((k:ℝ) * d) * (2:ℝ) ^ (-((k : ℝ) * ((d : ℝ) + β - α * γ)))) := by
              rw [hb, e1]; ring
            rw [e3, e2]
            have : (2 * (d:ℝ)) ≤ 2 * d + 1 := by linarith
            have hpos : 0 ≤ (2:ℝ) ^ d * (c₀:ℝ) * t ^ (-α) * (2:ℝ) ^ (-((k : ℝ) * (β - α * γ))) := by positivity
            nlinarith [hpos]
