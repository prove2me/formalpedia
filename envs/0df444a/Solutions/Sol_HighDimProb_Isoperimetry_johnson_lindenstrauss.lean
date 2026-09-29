-- Prove2me | solution 1 for HighDimProb.Isoperimetry.johnson_lindenstrauss
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-27T04:23:48.156809+00:00
-- url     : https://prove2.me/submissions/a59527e4-b70b-4dee-92b4-812592a0af88

import Mathlib
import Theorems.Thm_HighDimProb_Isoperimetry_random_projection_concentration
import Definitions.Def_HighDimProb_Isoperimetry_UniformProjection

open MeasureTheory


namespace HighDimProb.Isoperimetry

theorem jl_main :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (Prob : Measure Ω) [IsProbabilityMeasure Prob]
        {n : ℕ} (m : ℕ) (X : Finset (EuclideanSpace ℝ (Fin n))) {ε : ℝ} (hε : 0 < ε),
        (m : ℝ) ≥ (C / ε ^ 2) * Real.log (X.card : ℝ) →
        ∀ (P : Ω → (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))),
        IsUniformProjection Prob m P →
        1 - 2 * Real.exp (-(c * ε ^ 2 * (m : ℝ))) ≤
          Prob.real {ω | ∀ x ∈ X, ∀ y ∈ X,
            (1 - ε) * ‖x - y‖ ≤ ‖Real.sqrt ((n : ℝ) / (m : ℝ)) • P ω (x - y)‖ ∧
            ‖Real.sqrt ((n : ℝ) / (m : ℝ)) • P ω (x - y)‖ ≤ (1 + ε) * ‖x - y‖} := by
  obtain ⟨c₀, hc₀, hconc⟩ := random_projection_concentration
  refine ⟨4 / c₀, c₀ / 2, by positivity, by positivity, ?_⟩
  intro Ω _ Prob _ n m X ε hε hm P hP
  set G : Set Ω := {ω | ∀ x ∈ X, ∀ y ∈ X,
    (1 - ε) * ‖x - y‖ ≤ ‖Real.sqrt ((n : ℝ) / (m : ℝ)) • P ω (x - y)‖ ∧
    ‖Real.sqrt ((n : ℝ) / (m : ℝ)) • P ω (x - y)‖ ≤ (1 + ε) * ‖x - y‖} with hGdef
  have hexp0 : 0 < Real.exp (-(c₀ / 2 * ε ^ 2 * (m : ℝ))) := Real.exp_pos _
  rcases Nat.eq_zero_or_pos m with hm0 | hmpos
  · subst hm0
    have e : 1 - 2 * Real.exp (-(c₀ / 2 * ε ^ 2 * ((0:ℕ):ℝ))) = -1 := by norm_num
    rw [e]
    linarith [measureReal_nonneg (μ := Prob) (s := G)]
  rcases Nat.eq_zero_or_pos n with hn0 | hnpos
  · subst hn0
    have hG : G = Set.univ := by
      ext ω
      simp only [hGdef, Set.mem_setOf_eq, Set.mem_univ, iff_true]
      intro x _ y _
      have hxy : x - y = 0 := Subsingleton.elim _ _
      simp [hxy]
    rw [hG, probReal_univ]
    linarith
  rcases Nat.eq_zero_or_pos X.card with hN0 | hNpos
  · have hX : X = ∅ := Finset.card_eq_zero.mp hN0
    have hG : G = Set.univ := by
      ext ω; simp [hGdef, hX]
    rw [hG, probReal_univ]
    linarith
  have hmR : (0:ℝ) < m := by exact_mod_cast hmpos
  have hnR : (0:ℝ) < n := by exact_mod_cast hnpos
  set A : (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) → Set Ω := fun p =>
    {ω | (1 - ε) * Real.sqrt ((m : ℝ) / (n : ℝ)) * ‖p.1 - p.2‖ ≤ ‖P ω (p.1 - p.2)‖ ∧
      ‖P ω (p.1 - p.2)‖ ≤ (1 + ε) * Real.sqrt ((m : ℝ) / (n : ℝ)) * ‖p.1 - p.2‖} with hAdef
  have hAm : ∀ p, MeasurableSet (A p) := by
    intro p
    have hf : Measurable (fun ω => ‖P ω (p.1 - p.2)‖) :=
      (continuous_norm.comp (ContinuousLinearMap.apply ℝ (EuclideanSpace ℝ (Fin n))
        (p.1 - p.2)).continuous).measurable.comp hP.1
    exact (measurableSet_le measurable_const hf).inter (measurableSet_le hf measurable_const)
  have hAc : ∀ p, Prob.real (A p)ᶜ ≤ 2 * Real.exp (-(c₀ * ε ^ 2 * (m : ℝ))) := by
    intro p
    have := hconc Prob m P hP (p.1 - p.2) hε
    rw [measureReal_compl (hAm p), probReal_univ]
    linarith
  have hs : Real.sqrt ((n : ℝ) / m) * Real.sqrt ((m : ℝ) / n) = 1 := by
    rw [← Real.sqrt_mul (by positivity), div_mul_div_comm, mul_comm (n : ℝ) m,
      div_self (by positivity), Real.sqrt_one]
  have hs0 : 0 ≤ Real.sqrt ((n : ℝ) / m) := Real.sqrt_nonneg _
  have hsub : (⋂ p ∈ X ×ˢ X, A p) ⊆ G := by
    intro ω hω
    simp only [Set.mem_iInter] at hω
    intro x hx y hy
    have h := hω (x, y) (Finset.mem_product.mpr ⟨hx, hy⟩)
    simp only [hAdef, Set.mem_setOf_eq] at h
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hs0]
    have e1 : Real.sqrt ((n : ℝ) / m) * ((1 - ε) * Real.sqrt ((m : ℝ) / n) * ‖x - y‖) =
        (1 - ε) * ‖x - y‖ := by
      rw [show Real.sqrt ((n : ℝ) / m) * ((1 - ε) * Real.sqrt ((m : ℝ) / n) * ‖x - y‖) =
        (1 - ε) * ‖x - y‖ * (Real.sqrt ((n : ℝ) / m) * Real.sqrt ((m : ℝ) / n)) by ring, hs,
        mul_one]
    have e2 : Real.sqrt ((n : ℝ) / m) * ((1 + ε) * Real.sqrt ((m : ℝ) / n) * ‖x - y‖) =
        (1 + ε) * ‖x - y‖ := by
      rw [show Real.sqrt ((n : ℝ) / m) * ((1 + ε) * Real.sqrt ((m : ℝ) / n) * ‖x - y‖) =
        (1 + ε) * ‖x - y‖ * (Real.sqrt ((n : ℝ) / m) * Real.sqrt ((m : ℝ) / n)) by ring, hs,
        mul_one]
    constructor
    · have := mul_le_mul_of_nonneg_left h.1 hs0
      linarith
    · have := mul_le_mul_of_nonneg_left h.2 hs0
      linarith
  have hImeas : MeasurableSet (⋂ p ∈ X ×ˢ X, A p) :=
    Finset.measurableSet_biInter _ (fun p _ => hAm p)
  have hunion : Prob.real (⋂ p ∈ X ×ˢ X, A p)ᶜ ≤
      (X.card : ℝ) ^ 2 * (2 * Real.exp (-(c₀ * ε ^ 2 * (m : ℝ)))) := by
    rw [Set.compl_iInter₂]
    calc Prob.real (⋃ p ∈ X ×ˢ X, (A p)ᶜ) ≤ ∑ p ∈ X ×ˢ X, Prob.real (A p)ᶜ :=
          measureReal_biUnion_finset_le _ _
      _ ≤ ∑ p ∈ X ×ˢ X, 2 * Real.exp (-(c₀ * ε ^ 2 * (m : ℝ))) :=
          Finset.sum_le_sum fun p _ => hAc p
      _ = (X.card : ℝ) ^ 2 * (2 * Real.exp (-(c₀ * ε ^ 2 * (m : ℝ)))) := by
          rw [Finset.sum_const, Finset.card_product, nsmul_eq_mul]; push_cast; ring
  have hNR : (0:ℝ) < X.card := by exact_mod_cast hNpos
  have hkey : (X.card : ℝ) ^ 2 * Real.exp (-(c₀ * ε ^ 2 * (m : ℝ))) ≤
      Real.exp (-(c₀ / 2 * ε ^ 2 * (m : ℝ))) := by
    have hN2 : (X.card : ℝ) ^ 2 = Real.exp (2 * Real.log X.card) := by
      rw [show 2 * Real.log X.card = Real.log X.card + Real.log X.card by ring, Real.exp_add,
        Real.exp_log hNR, sq]
    rw [hN2, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have h1 := mul_le_mul_of_nonneg_left (ge_iff_le.mp hm)
      (show (0:ℝ) ≤ c₀ / 2 * ε ^ 2 by positivity)
    have e : c₀ / 2 * ε ^ 2 * (4 / c₀ / ε ^ 2 * Real.log X.card) = 2 * Real.log X.card := by
      field_simp; ring
    linarith
  calc 1 - 2 * Real.exp (-(c₀ / 2 * ε ^ 2 * (m : ℝ)))
      ≤ 1 - (X.card : ℝ) ^ 2 * (2 * Real.exp (-(c₀ * ε ^ 2 * (m : ℝ)))) := by nlinarith
    _ ≤ 1 - Prob.real (⋂ p ∈ X ×ˢ X, A p)ᶜ := by linarith
    _ = Prob.real (⋂ p ∈ X ×ˢ X, A p) := by
        rw [measureReal_compl hImeas, probReal_univ]; ring
    _ ≤ Prob.real G := measureReal_mono hsub

end HighDimProb.Isoperimetry

open HighDimProb.Isoperimetry

theorem solution :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (Prob : Measure Ω) [IsProbabilityMeasure Prob]
        {n : ℕ} (m : ℕ) (X : Finset (EuclideanSpace ℝ (Fin n))) {ε : ℝ} (hε : 0 < ε),
        (m : ℝ) ≥ (C / ε ^ 2) * Real.log (X.card : ℝ) →
        ∀ (P : Ω → (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))),
        IsUniformProjection Prob m P →
        1 - 2 * Real.exp (-(c * ε ^ 2 * (m : ℝ))) ≤
          Prob.real {ω | ∀ x ∈ X, ∀ y ∈ X,
            (1 - ε) * ‖x - y‖ ≤ ‖Real.sqrt ((n : ℝ) / (m : ℝ)) • P ω (x - y)‖ ∧
            ‖Real.sqrt ((n : ℝ) / (m : ℝ)) • P ω (x - y)‖ ≤ (1 + ε) * ‖x - y‖} := by
  exact jl_main
