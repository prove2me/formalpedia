-- Prove2me | solution 1 for MasulloGRH.nuclear_trace_hasSum_hilbertBasis
-- status  : ACCEPTED   (prove)
-- author  : @marozols
-- created : 2026-11-21T00:47:05.764374+00:00
-- url     : https://prove2.me/submissions/2a21009b-e831-4cdf-bbcc-c3ad8a9ec5f6

import Theorems.Thm_MasulloGRH_operatorTrace_of_nuclear_series

set_option autoImplicit false

open MasulloGRH Filter Topology

namespace TraceBasisAux

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

set_option linter.unusedSectionVars false

/-- Parseval: `∑ |⟨bᵢ, x⟩|² = ‖x‖²`. -/
theorem hasSum_sq_norm_inner {ι : Type*} (b : HilbertBasis ι ℂ H) (x : H) :
    HasSum (fun i => ‖inner ℂ (b i) x‖ ^ 2) (‖x‖ ^ 2) := by
  have h := b.hasSum_inner_mul_inner x x
  have e : (fun i => inner ℂ x (b i) * inner ℂ (b i) x) =
      fun i => ((‖inner ℂ (b i) x‖ ^ 2 : ℝ) : ℂ) := by
    funext i
    rw [← inner_conj_symm x (b i), Complex.conj_mul']
    norm_cast
  rw [e] at h
  have h2 : inner ℂ x x = ((‖x‖ ^ 2 : ℝ) : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K]
    norm_cast
  rw [h2] at h
  exact Complex.hasSum_ofReal.1 h

/-- Cauchy–Schwarz for nonnegative square-summable families. -/
theorem summable_mul_le {ι : Type*} (a c : ι → ℝ) (ha : ∀ i, 0 ≤ a i) (hc : ∀ i, 0 ≤ c i)
    (α β : ℝ) (hα : 0 ≤ α) (hβ : 0 ≤ β) (hA : HasSum (fun i => a i ^ 2) (α ^ 2))
    (hC : HasSum (fun i => c i ^ 2) (β ^ 2)) :
    Summable (fun i => a i * c i) ∧ ∑' i, a i * c i ≤ α * β := by
  have hsum : Summable fun i => a i * c i := by
    refine Summable.of_nonneg_of_le (fun i => mul_nonneg (ha i) (hc i)) (fun i => ?_)
      ((hA.summable.add hC.summable).div_const 2)
    nlinarith [sq_nonneg (a i - c i)]
  refine ⟨hsum, ?_⟩
  by_cases hα0 : α = 0
  · have ha0 : ∀ i, a i = 0 := by
      intro i
      have h1 := le_hasSum hA i fun j _ => sq_nonneg (a j)
      rw [hα0] at h1
      have h2 : a i ^ 2 = 0 := le_antisymm (by simpa using h1) (sq_nonneg _)
      exact pow_eq_zero_iff (by norm_num) |>.1 h2
    simp [ha0, hα0]
  by_cases hβ0 : β = 0
  · have hc0 : ∀ i, c i = 0 := by
      intro i
      have h1 := le_hasSum hC i fun j _ => sq_nonneg (c j)
      rw [hβ0] at h1
      have h2 : c i ^ 2 = 0 := le_antisymm (by simpa using h1) (sq_nonneg _)
      exact pow_eq_zero_iff (by norm_num) |>.1 h2
    simp [hc0, hβ0]
  have hαp : 0 < α := lt_of_le_of_ne hα (Ne.symm hα0)
  have hβp : 0 < β := lt_of_le_of_ne hβ (Ne.symm hβ0)
  -- weighted AM–GM with `t = β / α`
  have hdom : HasSum (fun i => (β / α * a i ^ 2 + α / β * c i ^ 2) / 2)
      ((β / α * α ^ 2 + α / β * β ^ 2) / 2) :=
    ((hA.mul_left (β / α)).add (hC.mul_left (α / β))).div_const 2
  have hle : ∀ i, a i * c i ≤ (β / α * a i ^ 2 + α / β * c i ^ 2) / 2 := by
    intro i
    have h1 : 0 ≤ (β * a i - α * c i) ^ 2 := sq_nonneg _
    have h2 : (β / α * a i ^ 2 + α / β * c i ^ 2) / 2 - a i * c i =
        (β * a i - α * c i) ^ 2 / (2 * α * β) := by
      field_simp
      ring
    have h3 : 0 ≤ (β * a i - α * c i) ^ 2 / (2 * α * β) := div_nonneg h1 (by positivity)
    linarith
  have h4 := hsum.tsum_le_tsum hle hdom.summable
  rw [hdom.tsum_eq] at h4
  have h5 : (β / α * α ^ 2 + α / β * β ^ 2) / 2 = α * β := by
    field_simp
    ring
  linarith

end TraceBasisAux

open TraceBasisAux in
theorem solution {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (T : H →L[ℂ] H) (hT : IsNuclearOperator T)
    {ι : Type*} (b : HilbertBasis ι ℂ H) :
    Summable (fun i => ‖inner ℂ (b i) (T (b i))‖) ∧
      HasSum (fun i => inner ℂ (b i) (T (b i))) (operatorTrace T) := by
  obtain ⟨x, y, hs, hxy⟩ := hT
  obtain ⟨F, hFdef⟩ : ∃ F : ℕ × ι → ℂ,
      ∀ p, F p = inner ℂ (x p.1) (b p.2) * inner ℂ (b p.2) (y p.1) := ⟨_, fun _ => rfl⟩
  -- rows are absolutely summable with sum at most `‖x m‖ ‖y m‖`
  have hrow : ∀ m, Summable (fun i => ‖F (m, i)‖) ∧ ∑' i, ‖F (m, i)‖ ≤ ‖x m‖ * ‖y m‖ := by
    intro m
    have h := summable_mul_le (fun i => ‖inner ℂ (b i) (x m)‖) (fun i => ‖inner ℂ (b i) (y m)‖)
      (fun _ => norm_nonneg _) (fun _ => norm_nonneg _) ‖x m‖ ‖y m‖ (norm_nonneg _)
      (norm_nonneg _) (hasSum_sq_norm_inner b (x m)) (hasSum_sq_norm_inner b (y m))
    have e : (fun i => ‖F (m, i)‖) =
        fun i => ‖inner ℂ (b i) (x m)‖ * ‖inner ℂ (b i) (y m)‖ := by
      funext i
      rw [hFdef, norm_mul, norm_inner_symm]
    rw [e]
    exact h
  have hsumF : Summable (fun p : ℕ × ι => ‖F p‖) := by
    rw [summable_prod_of_nonneg (fun p => norm_nonneg _)]
    exact ⟨fun m => (hrow m).1,
      Summable.of_nonneg_of_le (fun m => tsum_nonneg fun i => norm_nonneg _)
        (fun m => (hrow m).2) hs⟩
  have hF : Summable F := hsumF.of_norm
  -- summing the rows first gives the trace (Parseval)
  have hrowsum : ∀ m, HasSum (fun i => F (m, i)) (inner ℂ (x m) (y m)) := by
    intro m
    have e : (fun i => F (m, i)) = fun i => inner ℂ (x m) (b i) * inner ℂ (b i) (y m) :=
      funext fun i => hFdef (m, i)
    rw [e]
    exact b.hasSum_inner_mul_inner (x m) (y m)
  have h1 : HasSum (fun m => inner ℂ (x m) (y m)) (∑' p, F p) :=
    hF.hasSum.prod_fiberwise hrowsum
  have htr : operatorTrace T = ∑' p, F p := by
    rw [operatorTrace_of_nuclear_series T x y hs hxy]
    exact h1.tsum_eq
  -- summing the columns first gives the diagonal entries
  have hcol : ∀ i, HasSum (fun m => F (m, i)) (inner ℂ (b i) (T (b i))) := by
    intro i
    have h : HasSum (fun m => inner ℂ (b i) (inner ℂ (x m) (b i) • y m))
        (inner ℂ (b i) (T (b i))) := (hxy (b i)).mapL (innerSL ℂ (b i))
    have e : (fun m => F (m, i)) = fun m => inner ℂ (b i) (inner ℂ (x m) (b i) • y m) := by
      funext m
      rw [hFdef, inner_smul_right]
    rw [e]
    exact h
  obtain ⟨F', hF'def⟩ : ∃ F' : ι × ℕ → ℂ, F' = fun p => F (p.2, p.1) := ⟨_, rfl⟩
  have hF' : Summable F' := by
    rw [hF'def]
    exact (Equiv.prodComm ι ℕ).summable_iff.2 hF
  have hcol' : ∀ i, HasSum (fun m => F' (i, m)) (inner ℂ (b i) (T (b i))) := by
    intro i
    rw [hF'def]
    exact hcol i
  have h2 : HasSum (fun i => inner ℂ (b i) (T (b i))) (∑' p, F' p) :=
    hF'.hasSum.prod_fiberwise hcol'
  have heq : ∑' p, F' p = ∑' p, F p := by
    rw [hF'def]
    exact (Equiv.prodComm ι ℕ).tsum_eq F
  refine ⟨?_, ?_⟩
  · have hsumF' : Summable (fun p : ι × ℕ => ‖F' p‖) := by
      rw [hF'def]
      exact (Equiv.prodComm ι ℕ).summable_iff.2 hsumF
    have h3 := (summable_prod_of_nonneg (fun p => norm_nonneg _)).1 hsumF'
    refine Summable.of_nonneg_of_le (fun i => norm_nonneg _) (fun i => ?_) h3.2
    rw [← (hcol' i).tsum_eq]
    exact norm_tsum_le_tsum_norm (h3.1 i)
  · rw [htr, ← heq]
    exact h2
