-- Prove2me | solution 1 for NestedSeatAlloc.IntPolicy.theorem1_conditional_concavity_step
-- status  : ACCEPTED   (disprove)
-- author  : @Nickrobbins95
-- created : 2026-10-07T01:19:39.787338+00:00
-- url     : https://prove2.me/submissions/0fe842b9-f9b9-4670-84eb-ed72f2380de7

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model

set_option autoImplicit false

section Helpers9f
open NestedSeatAlloc.IntPolicy MeasureTheory ProbabilityTheory

/-- Constant demands on the one-point space are independent. -/
theorem indep_const_9f :
    iIndepFun (fun (_ : ℕ) (_ : Unit) => (1 : ℝ)) (Measure.dirac ()) := by
  rw [iIndepFun_iff_measure_inter_preimage_eq_mul]
  intro S sets _
  by_cases h : ∀ i ∈ S, (1 : ℝ) ∈ sets i
  · have hL : (⋂ i ∈ S, (fun (_ : Unit) => (1 : ℝ)) ⁻¹' sets i) = Set.univ := by
      ext u
      simp only [Set.mem_iInter, Set.mem_preimage, Set.mem_univ, iff_true]
      exact h
    rw [hL, measure_univ]
    symm
    apply Finset.prod_eq_one
    intro i hi
    have : (fun (_ : Unit) => (1 : ℝ)) ⁻¹' sets i = Set.univ := by
      ext u; simp [h i hi]
    rw [this, measure_univ]
  · push_neg at h
    obtain ⟨i, hi, hni⟩ := h
    have hL : (⋂ i ∈ S, (fun (_ : Unit) => (1 : ℝ)) ⁻¹' sets i) = ∅ := by
      ext u
      simp only [Set.mem_iInter, Set.mem_preimage, Set.mem_empty_iff_false, iff_false]
      intro hall
      exact hni (hall i hi)
    rw [hL, measure_empty]
    symm
    apply Finset.prod_eq_zero hi
    have : (fun (_ : Unit) => (1 : ℝ)) ⁻¹' sets i = ∅ := by
      ext u; simp [hni]
    rw [this, measure_empty]

/-- The fares `f k = 3 - k`. -/
noncomputable def fare9f : ℕ → ℝ := fun k => 3 - (k : ℝ)

/-- The protection levels `p 1 = 2`, `p 2 = 3/2`, all others `0`. -/
noncomputable def prot9f : ℕ → ℝ := fun k => if k = 1 then 2 else if k = 2 then 3 / 2 else 0

theorem seatModel_9f :
    IsSeatModel (Measure.dirac ()) (fun (_ : ℕ) (_ : Unit) => (1 : ℝ)) fare9f where
  isProb := inferInstance
  meas := fun _ => measurable_const
  indep := indep_const_9f
  nonneg := fun _ _ => zero_le_one
  fare_strictAnti := fun k _ => by
    simp only [fare9f]
    push_cast
    linarith

theorem policy_9f : IsProtectionPolicy prot9f := by
  intro k _
  simp only [prot9f]
  split_ifs <;> norm_num

/-- `R₁` with `x 1 = 1` and fare `2`. -/
theorem rev1_9f (x : ℕ → ℝ) (hx : x 1 = 1) (s : ℝ) :
    revenue fare9f prot9f x 1 s = min (2 * s) 2 := by
  simp only [revenue, fare9f, hx]
  norm_num
  split_ifs with h
  · rw [min_eq_left (by linarith)]
  · rw [min_eq_right (by linarith)]

theorem rev2_9f (x : ℕ → ℝ) (hx : x 1 = 1) (s : ℝ) :
    revenue fare9f prot9f x 2 s =
      if s < 2 then min (2 * s) 2
      else if s < 2 + x 2 then (s - 2) * 1 + 2
      else x 2 * 1 + min (2 * (s - x 2)) 2 := by
  show (if s < prot9f 1 then revenue fare9f prot9f x 1 s
      else if s < prot9f 1 + x 2 then
        (s - prot9f 1) * fare9f 2 + revenue fare9f prot9f x 1 (prot9f 1)
      else x 2 * fare9f 2 + revenue fare9f prot9f x 1 (s - x 2)) = _
  have h1 : prot9f 1 = 2 := by simp [prot9f]
  have hf2 : fare9f 2 = 1 := by norm_num [fare9f]
  rw [h1, hf2, rev1_9f x hx, rev1_9f x hx, rev1_9f x hx]
  norm_num

theorem rev3_9f (x : ℕ → ℝ) (s : ℝ) (h3 : x 3 = 0) :
    revenue fare9f prot9f x 3 s = revenue fare9f prot9f x 2 s := by
  show (if s < prot9f 2 then revenue fare9f prot9f x 2 s
      else if s < prot9f 2 + x 3 then
        (s - prot9f 2) * fare9f 3 + revenue fare9f prot9f x 2 (prot9f 2)
      else x 3 * fare9f 3 + revenue fare9f prot9f x 2 (s - x 3)) = _
  rw [h3]
  simp only [add_zero, zero_mul, zero_add, sub_zero]
  split_ifs <;> rfl

/-- The hypothesis `hprev` holds: freezing `X 2 = 0` gives `min (2 s) 2`. -/
theorem prev_9f :
    ConcaveOn ℝ (Set.Ici 0)
      (condRevenue (Measure.dirac ()) (fun (_ : ℕ) (_ : Unit) => (1 : ℝ)) fare9f prot9f 2 0) := by
  have heq : condRevenue (Measure.dirac ()) (fun (_ : ℕ) (_ : Unit) => (1 : ℝ)) fare9f prot9f 2 0
      = fun s => min (2 * s) 2 := by
    funext s
    simp only [condRevenue, integral_dirac]
    rw [rev2_9f _ (by simp [Function.update])]
    simp only [Function.update_self, add_zero, zero_mul, zero_add, sub_zero]
    split_ifs <;> rfl
  rw [heq]
  have hlin : ConcaveOn ℝ (Set.Ici (0 : ℝ)) (fun s : ℝ => 2 * s) :=
    ((LinearMap.mul ℝ ℝ 2).concaveOn (convex_Ici 0))
  have hc : ConcaveOn ℝ (Set.Ici (0 : ℝ)) (fun _ : ℝ => (2 : ℝ)) := concaveOn_const 2 (convex_Ici 0)
  exact hlin.inf hc

/-- The expected revenue `ER_2` equals `2` near `3/2`. -/
theorem er2_near_9f :
    expRevenue (Measure.dirac ()) (fun (_ : ℕ) (_ : Unit) => (1 : ℝ)) fare9f prot9f 2
      =ᶠ[nhds (3 / 2 : ℝ)] fun _ => (2 : ℝ) := by
  filter_upwards [Ioo_mem_nhds (show (1 : ℝ) < 3 / 2 by norm_num)
    (show (3 / 2 : ℝ) < 2 by norm_num)] with s hs
  simp only [expRevenue, integral_dirac]
  rw [rev2_9f _ rfl]
  rw [if_pos hs.2, min_eq_right (by linarith [hs.1])]

theorem subdiff_9f :
    InSubdiff (expRevenue (Measure.dirac ()) (fun (_ : ℕ) (_ : Unit) => (1 : ℝ)) fare9f prot9f 2)
      (prot9f 2) (fare9f (2 + 1)) := by
  have hp2 : prot9f 2 = 3 / 2 := by simp [prot9f]
  have hf3 : fare9f (2 + 1) = 0 := by norm_num [fare9f]
  rw [hp2, hf3]
  have hd : HasDerivAt
      (expRevenue (Measure.dirac ()) (fun (_ : ℕ) (_ : Unit) => (1 : ℝ)) fare9f prot9f 2) 0
      (3 / 2) :=
    (hasDerivAt_const (3 / 2 : ℝ) (2 : ℝ)).congr_of_eventuallyEq er2_near_9f
  exact ⟨⟨0, hd.hasDerivWithinAt, le_rfl⟩, Or.inr ⟨0, hd.hasDerivWithinAt, le_rfl⟩⟩

theorem cond3_val_9f (s : ℝ) :
    condRevenue (Measure.dirac ()) (fun (_ : ℕ) (_ : Unit) => (1 : ℝ)) fare9f prot9f (2 + 1) 0 s
      = revenue fare9f prot9f (fun _ => 1) 2 s := by
  simp only [condRevenue, integral_dirac]
  rw [rev3_9f _ s (by simp [Function.update])]
  rw [rev2_9f _ (by simp [Function.update]), rev2_9f _ rfl]
  simp [Function.update]

/-- The conclusion fails: the values at `1, 2, 3` are `2, 2, 3`. -/
theorem not_concave_9f :
    ¬ ConcaveOn ℝ (Set.Ici 0)
      (condRevenue (Measure.dirac ()) (fun (_ : ℕ) (_ : Unit) => (1 : ℝ)) fare9f prot9f (2 + 1) 0) := by
  intro hc
  have h := hc.2 (show (1 : ℝ) ∈ Set.Ici 0 by norm_num) (show (3 : ℝ) ∈ Set.Ici 0 by norm_num)
    (show (0 : ℝ) ≤ 1 / 2 by norm_num) (show (0 : ℝ) ≤ 1 / 2 by norm_num) (by norm_num)
  simp only [smul_eq_mul, cond3_val_9f] at h
  rw [rev2_9f _ rfl, rev2_9f _ rfl, rev2_9f _ rfl] at h
  norm_num at h

end Helpers9f

open NestedSeatAlloc.IntPolicy MeasureTheory ProbabilityTheory in
theorem solution : ¬ (∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (X : ℕ → Ω → ℝ) (f p : ℕ → ℝ) (k : ℕ) (y : ℝ)
    (hM : IsSeatModel P X f) (hp : IsProtectionPolicy p)
    (hk : 1 ≤ k) (hy : 0 ≤ y)
    (h20k : InSubdiff (expRevenue P X f p k) (p k) (f (k + 1)))
    (hprev : ConcaveOn ℝ (Set.Ici 0) (condRevenue P X f p k y)),
    ConcaveOn ℝ (Set.Ici 0) (condRevenue P X f p (k + 1) y)) := by
  intro h
  exact not_concave_9f (h (Measure.dirac ()) (fun (_ : ℕ) (_ : Unit) => (1 : ℝ)) fare9f prot9f 2 0
    seatModel_9f policy_9f (by norm_num) le_rfl subdiff_9f prev_9f)
