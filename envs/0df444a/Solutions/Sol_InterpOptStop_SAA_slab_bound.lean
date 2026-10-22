-- Prove2me | solution 1 for InterpOptStop.SAA.slab_bound
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T15:41:04.505327+00:00
-- url     : https://prove2.me/submissions/d70bf825-f634-47c7-b18c-d343bb645c2e

import Mathlib
import Definitions.Def_InterpOptStop_SAA_StoppingModel
import Definitions.Def_InterpOptStop_SAA_TreePolicy
open MeasureTheory ProbabilityTheory Filter Topology

open InterpOptStop.SAA in
theorem solution {n T : ℕ}
    (hT : 0 < T)
    (X : Set (Fin n → ℝ)) (Xi : Fin n → Set ℝ) (hXprod : X = Set.univ.pi Xi)
    (hXtb : TotallyBounded X) (hXdiam : ∀ x ∈ X, ∀ y ∈ X, ‖x - y‖ ≤ 1)
    (μ : Measure (Fin T → Fin n → ℝ)) [IsProbabilityMeasure μ]
    (hinX : ∀ᵐ x ∂μ, ∀ k, x k ∈ X)
    (f : ℝ → ℝ) (hf0 : f 0 = 0) (hfmono : StrictMonoOn f (Set.Ici 0))
    (hfcont : ContinuousOn f (Set.Ici 0))
    (hA3 : ∀ A : Set (Fin n → ℝ), MeasurableSet A → volume A ≠ ⊤ →
      ∀ k : Fin T, (k : ℕ) ≠ 0 → (μ {x | x k ∈ A}).toReal ≤ f (volume A).toReal) :
    ∀ k : Fin T, (k : ℕ) ≠ 0 → ∀ (i : Fin n) (a b : ℝ),
      (μ {x | x k i ∈ Set.uIcc a b}).toReal ≤ f |a - b| := by
  intro k hk i a b
  obtain ⟨x0, hx0⟩ := hinX.exists
  set y0 := x0 k with hy0
  have hy0X : y0 ∈ X := hx0 k
  have hmemX : ∀ y : Fin n → ℝ, (∀ j, y j ∈ Xi j) → y ∈ X := by
    intro y hy; rw [hXprod]; exact fun j _ => hy j
  have hXi : ∀ y ∈ X, ∀ j, y j ∈ Xi j := by
    intro y hy j; rw [hXprod] at hy; exact hy j (Set.mem_univ _)
  -- each factor has diameter at most one
  have hdiam : ∀ j, ∀ s ∈ Xi j, ∀ t ∈ Xi j, |s - t| ≤ 1 := by
    intro j s hs t ht
    have h1 : Function.update y0 j s ∈ X := by
      apply hmemX; intro l
      by_cases hl : l = j
      · subst hl; simpa using hs
      · simpa [hl] using hXi y0 hy0X l
    have h2 : Function.update y0 j t ∈ X := by
      apply hmemX; intro l
      by_cases hl : l = j
      · subst hl; simpa using ht
      · simpa [hl] using hXi y0 hy0X l
    have h3 := hXdiam _ h1 _ h2
    have h4 := norm_le_pi_norm (Function.update y0 j s - Function.update y0 j t) j
    simp only [Pi.sub_apply, Function.update_self, Real.norm_eq_abs] at h4
    linarith
  set c : Fin n → ℝ := fun j => sInf (Xi j) with hc
  have hbdd : ∀ j, BddBelow (Xi j) := by
    intro j
    refine ⟨y0 j - 1, fun t ht => ?_⟩
    have := hdiam j t ht (y0 j) (hXi y0 hy0X j)
    have := (abs_le.mp this).1
    linarith
  have hne : ∀ j, (Xi j).Nonempty := fun j => ⟨y0 j, hXi y0 hy0X j⟩
  have hcI : ∀ j, ∀ t ∈ Xi j, t ∈ Set.Icc (c j) (c j + 1) := by
    intro j t ht
    refine ⟨csInf_le (hbdd j) ht, ?_⟩
    have : t - 1 ≤ c j := by
      apply le_csInf (hne j)
      intro s hs
      have := (abs_le.mp (hdiam j t ht s hs)).2
      linarith
    linarith
  -- the slab `A_s`
  set A : Set (Fin n → ℝ) := Set.univ.pi
    (fun j => if j = i then Set.uIcc a b else Set.Icc (c j) (c j + 1)) with hA
  have hAm : MeasurableSet A := by
    apply MeasurableSet.univ_pi
    intro j
    split_ifs
    · exact measurableSet_uIcc
    · exact measurableSet_Icc
  have hvol : volume A = ENNReal.ofReal |a - b| := by
    rw [hA, volume_pi_pi]
    have : ∀ j, volume (if j = i then Set.uIcc a b else Set.Icc (c j) (c j + 1)) =
        if j = i then ENNReal.ofReal |a - b| else 1 := by
      intro j
      split_ifs
      · rw [Real.volume_interval, abs_sub_comm]
      · rw [Real.volume_Icc]; simp
    simp_rw [this]
    rw [Finset.prod_ite_eq']
    simp
  have hsub : {x : Fin T → Fin n → ℝ | x k i ∈ Set.uIcc a b} ≤ᵐ[μ] {x | x k ∈ A} := by
    filter_upwards [hinX] with x hx
    intro hxi
    change x k i ∈ Set.uIcc a b at hxi
    change x k ∈ A
    rw [hA]
    intro j _
    by_cases hj : j = i
    · subst hj; simpa using hxi
    · simp only [hj, if_false]
      exact hcI j _ (hXi _ (hx k) j)
  have h1 : (μ {x : Fin T → Fin n → ℝ | x k i ∈ Set.uIcc a b}).toReal ≤
      (μ {x | x k ∈ A}).toReal :=
    ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae hsub)
  have h2 := hA3 A hAm (by rw [hvol]; exact ENNReal.ofReal_ne_top) k hk
  rw [hvol, ENNReal.toReal_ofReal (abs_nonneg _)] at h2
  linarith
