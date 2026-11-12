-- Prove2me | solution 1 for HDXConc.upper_tail
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T04:38:09.281207+00:00
-- url     : https://prove2.me/submissions/3e6a9fe9-3576-4d15-91e4-e26be36e8e6a

import Mathlib
import Definitions.Def_SteurerHDX_IsPure
import Definitions.Def_HDXConc_IsTopDensity
import Definitions.Def_HDXConc_IsTopLinkExpander
import Definitions.Def_HDXConc_tilt
import Definitions.Def_HDXConc_topVar
import Theorems.Thm_HDXConc_eq_13

section
set_option autoImplicit false
namespace HDXConc
open HDXConc in
theorem chk_upper_tail {V : Type*} [Fintype V] [DecidableEq V] {d : ℕ} (hd : 2 ≤ d) {η : ℝ} (hη0 : 0 < η)
    (hη1 : η ≤ 1) {X : Finset (Finset V)} {π : Finset V → ℝ} (hX : SteurerHDX.IsPure X d)
    (hπ : IsTopDensity X d π) (hexp : IsTopLinkExpander X d π ((1 - η) / ((d : ℝ) - 1)))
    (f : V → ℝ) (hf : ∀ v, ({v} : Finset V) ∈ X → 0 ≤ f v ∧ f v ≤ 1) {α : ℝ} (hα0 : 0 < α)
    (hα1 : α ≤ 1) :
    ∑ σ ∈ (SteurerHDX.faces X d).filter (fun σ => α * (d : ℝ) ≤ topSum f σ - topMean X d π (topSum f)), π σ ≤
      Real.exp (-(η / 4) * α ^ 2 * (d : ℝ)) := by
  set m := topMean X d π (topSum f) with hm
  set t : ℝ := α * η / 2 with ht
  have htpos : 0 < t := by positivity
  have htle : |t| ≤ η / 2 := by
    rw [abs_of_pos htpos, ht]; nlinarith
  have h13 := (HDXConc.eq_13 hd hη0 hη1 hX hπ hexp f hf htle).2
  set Z := ∑ σ ∈ SteurerHDX.faces X d, π σ * Real.exp (t * (topSum f σ - m)) with hZ
  have hne : (SteurerHDX.faces X d).Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    have := hπ.sum_eq_one
    rw [h] at this; simp at this
  have hZpos : 0 < Z := Finset.sum_pos (fun σ hσ => mul_pos (hπ.pos σ hσ) (Real.exp_pos _)) hne
  have hZe : Z = Real.exp (logMGF X d π f t) := by
    unfold logMGF; rw [Real.exp_log hZpos]
  set d' : ℝ := (d : ℝ)
  have step1 : ∑ σ ∈ (SteurerHDX.faces X d).filter (fun σ => α * d' ≤ topSum f σ - m), π σ
      ≤ Real.exp (-(t * (α * d'))) * Z := by
    rw [hZ, Finset.mul_sum]
    calc _ ≤ ∑ σ ∈ (SteurerHDX.faces X d).filter (fun σ => α * d' ≤ topSum f σ - m),
          Real.exp (-(t * (α * d'))) * (π σ * Real.exp (t * (topSum f σ - m))) := by
            apply Finset.sum_le_sum
            intro σ hσ
            rw [Finset.mem_filter] at hσ
            have h1 : 1 ≤ Real.exp (-(t * (α * d'))) * Real.exp (t * (topSum f σ - m)) := by
              rw [← Real.exp_add]; apply Real.one_le_exp
              nlinarith [hσ.2]
            have := hπ.pos σ hσ.1
            nlinarith [mul_le_mul_of_nonneg_left h1 this.le]
      _ ≤ _ := by
            apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            intro σ hσ _
            exact mul_nonneg (Real.exp_pos _).le (mul_nonneg (hπ.pos σ hσ).le (Real.exp_pos _).le)
  refine step1.trans ?_
  rw [hZe, ← Real.exp_add]
  apply Real.exp_le_exp.2
  have hdpos : (0:ℝ) ≤ d' := by positivity
  have : logMGF X d π f t ≤ d' * (α * η / 2) ^ 2 / (4 * η) := by rw [← ht]; exact h13
  have e : d' * (α * η / 2) ^ 2 / (4 * η) = η * α ^ 2 * d' / 16 := by field_simp; ring
  rw [e] at this
  have : 0 ≤ η * α ^ 2 * d' := by positivity
  rw [ht]; nlinarith
end HDXConc
end

theorem solution : type_of% @HDXConc.chk_upper_tail := @HDXConc.chk_upper_tail
