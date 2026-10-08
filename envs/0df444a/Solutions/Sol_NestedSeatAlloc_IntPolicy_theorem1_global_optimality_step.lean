-- Prove2me | solution 1 for NestedSeatAlloc.IntPolicy.theorem1_global_optimality_step
-- status  : ACCEPTED   (disprove)
-- author  : @Nickrobbins95
-- created : 2026-10-07T01:41:21.135595+00:00
-- url     : https://prove2.me/submissions/089d2595-218f-4ad9-9366-7eb97c1d605a

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model

set_option autoImplicit false

namespace Cex1a225ec4

open MeasureTheory ProbabilityTheory NestedSeatAlloc.IntPolicy

theorem rev1 (f p x : ℕ → ℝ) (s : ℝ) :
    revenue f p x 1 s = if s < x 1 then f 1 * s else f 1 * x 1 := by
  rw [revenue]

theorem rev2 (f p x : ℕ → ℝ) (s : ℝ) :
    revenue f p x 2 s =
      if s < p 1 then revenue f p x 1 s
      else if s < p 1 + x 2 then (s - p 1) * f 2 + revenue f p x 1 (p 1)
      else x 2 * f 2 + revenue f p x 1 (s - x 2) := by
  rfl

theorem rev3 (f p x : ℕ → ℝ) (s : ℝ) :
    revenue f p x 3 s =
      if s < p 2 then revenue f p x 2 s
      else if s < p 2 + x 3 then (s - p 2) * f 3 + revenue f p x 2 (p 2)
      else x 3 * f 3 + revenue f p x 2 (s - x 3) := by
  rfl

/-- Demands: every class has deterministic demand `1`, on the one-point space. -/
noncomputable def X : ℕ → Unit → ℝ := fun _ _ => 1
/-- Fares `f k = 3 - k`: `f 1 = 2, f 2 = 1, f 3 = 0, …` (strictly decreasing). -/
noncomputable def f : ℕ → ℝ := fun k => 3 - (k : ℝ)
/-- The candidate policy: `p 1 = 2`, `p 2 = 3/2`. -/
noncomputable def p : ℕ → ℝ := fun k => if k = 1 then 2 else 3 / 2
/-- The better policy: `q 1 = 1`, `q 2 = 2`. -/
noncomputable def q : ℕ → ℝ := fun k => (k : ℝ)

theorem hER (r : ℕ → ℝ) (k : ℕ) (s : ℝ) :
    expRevenue (Measure.dirac ()) X f r k s = revenue f r (fun _ => 1) k s := by
  unfold expRevenue
  rw [integral_dirac]
  rfl

theorem indep : iIndepFun X (Measure.dirac ()) := by
  rw [iIndepFun_iff_measure_inter_preimage_eq_mul]
  intro S sets _
  simp only [Measure.dirac_apply]
  by_cases h : ∀ i ∈ S, (1 : ℝ) ∈ sets i
  · have hmem : () ∈ ⋂ i ∈ S, X i ⁻¹' sets i := by
      simp only [Set.mem_iInter, Set.mem_preimage]
      intro i hi
      exact h i hi
    rw [Set.indicator_of_mem hmem]
    symm
    apply Finset.prod_eq_one
    intro i hi
    exact Set.indicator_of_mem (show () ∈ X i ⁻¹' sets i from h i hi) _
  · push Not at h
    obtain ⟨i, hi, hni⟩ := h
    have hnm : () ∉ ⋂ i ∈ S, X i ⁻¹' sets i := by
      simp only [Set.mem_iInter, Set.mem_preimage, not_forall]
      exact ⟨i, hi, hni⟩
    rw [Set.indicator_of_notMem hnm]
    symm
    apply Finset.prod_eq_zero hi
    exact Set.indicator_of_notMem (show () ∉ X i ⁻¹' sets i from hni) _

theorem hM : IsSeatModel (Measure.dirac ()) X f where
  isProb := inferInstance
  meas := fun _ => measurable_const
  indep := indep
  nonneg := fun _ _ => zero_le_one
  fare_strictAnti := fun k _ => by
    simp only [f]
    push_cast
    linarith

theorem hp : IsProtectionPolicy p := by
  intro k _
  simp only [p]
  split_ifs <;> norm_num

theorem hq : IsProtectionPolicy q := by
  intro k _
  simp only [q]
  positivity

theorem h20k : InSubdiff (expRevenue (Measure.dirac ()) X f p 2) (p 2) (f (2 + 1)) := by
  have hp2 : p 2 = 3 / 2 := by simp [p]
  have hf3 : f (2 + 1) = 0 := by norm_num [f]
  rw [hp2, hf3]
  have heq : (fun s => expRevenue (Measure.dirac ()) X f p 2 s) =ᶠ[nhds (3 / 2 : ℝ)]
      fun _ => (2 : ℝ) := by
    filter_upwards [Ioo_mem_nhds (by norm_num : (1 : ℝ) < 3 / 2) (by norm_num : (3 / 2 : ℝ) < 2)]
      with s hs
    rw [hER, rev2, rev1]
    have h1 : s < p 1 := by simp [p]; linarith [hs.2]
    have h2 : ¬ s < 1 := by linarith [hs.1]
    rw [if_pos h1, if_neg h2]
    simp [f]
    norm_num
  have hd : HasDerivAt (fun s => expRevenue (Measure.dirac ()) X f p 2 s) 0 (3 / 2) :=
    (hasDerivAt_const (3 / 2 : ℝ) (2 : ℝ)).congr_of_eventuallyEq heq
  exact ⟨⟨0, hd.hasDerivWithinAt, le_refl _⟩, Or.inr ⟨0, hd.hasDerivWithinAt, le_refl _⟩⟩

theorem hprev : ∀ r, IsProtectionPolicy r →
    expRevenue (Measure.dirac ()) X f r 2 3 ≤ expRevenue (Measure.dirac ()) X f p 2 3 := by
  intro r hr
  have hr1 : 0 ≤ r 1 := hr 1 le_rfl
  have hp1 : p 1 = 2 := by simp [p]
  have hf1 : f 1 = 2 := by norm_num [f]
  have hf2 : f 2 = 1 := by norm_num [f]
  simp only [hER, rev2, rev1, hp1, hf1, hf2]
  split_ifs <;> (try norm_num at *) <;> linarith

theorem key_p : expRevenue (Measure.dirac ()) X f p (2 + 1) 3 = 2 := by
  have hp1 : p 1 = 2 := by simp [p]
  have hp2 : p 2 = 3 / 2 := by simp [p]
  have hf1 : f 1 = 2 := by norm_num [f]
  have hf2 : f 2 = 1 := by norm_num [f]
  have hf3 : f 3 = 0 := by norm_num [f]
  simp only [hER, show (2 + 1 : ℕ) = 3 from rfl, rev3, rev2, rev1, hp1, hp2, hf1, hf2, hf3]
  norm_num

theorem key_q : expRevenue (Measure.dirac ()) X f q (2 + 1) 3 = 3 := by
  have hq1 : q 1 = 1 := by simp [q]
  have hq2 : q 2 = 2 := by norm_num [q]
  have hf1 : f 1 = 2 := by norm_num [f]
  have hf2 : f 2 = 1 := by norm_num [f]
  have hf3 : f 3 = 0 := by norm_num [f]
  simp only [hER, show (2 + 1 : ℕ) = 3 from rfl, rev3, rev2, rev1, hq1, hq2, hf1, hf2, hf3]
  norm_num

theorem cex : ¬ (∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (X : ℕ → Ω → ℝ) (f p : ℕ → ℝ) (k : ℕ) (s : ℝ)
    (hM : IsSeatModel P X f) (hp : IsProtectionPolicy p)
    (hk : 1 ≤ k) (hs : 0 ≤ s)
    (h20k : InSubdiff (expRevenue P X f p k) (p k) (f (k + 1)))
    (hprev : ∀ q, IsProtectionPolicy q →
      expRevenue P X f q k s ≤ expRevenue P X f p k s),
    ∀ q, IsProtectionPolicy q →
      expRevenue P X f q (k + 1) s ≤ expRevenue P X f p (k + 1) s) := by
  intro h
  have := h (Ω := Unit) (Measure.dirac ()) X f p 2 3 hM hp (by norm_num) (by norm_num)
    h20k hprev q hq
  rw [key_p, key_q] at this
  norm_num at this

end Cex1a225ec4

open MeasureTheory ProbabilityTheory NestedSeatAlloc.IntPolicy in
theorem solution : ¬ (∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (X : ℕ → Ω → ℝ) (f p : ℕ → ℝ) (k : ℕ) (s : ℝ)
    (hM : IsSeatModel P X f) (hp : IsProtectionPolicy p)
    (hk : 1 ≤ k) (hs : 0 ≤ s)
    (h20k : InSubdiff (expRevenue P X f p k) (p k) (f (k + 1)))
    (hprev : ∀ q, IsProtectionPolicy q →
      expRevenue P X f q k s ≤ expRevenue P X f p k s),
    ∀ q, IsProtectionPolicy q →
      expRevenue P X f q (k + 1) s ≤ expRevenue P X f p (k + 1) s) := by
  exact Cex1a225ec4.cex
