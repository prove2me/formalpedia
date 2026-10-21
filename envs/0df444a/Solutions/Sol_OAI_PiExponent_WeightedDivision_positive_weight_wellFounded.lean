-- Prove2me | solution 1 for OAI.PiExponent.WeightedDivision.positive_weight_wellFounded
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-20T08:12:57.853731+00:00
-- url     : https://prove2.me/submissions/60b846b0-e7ba-420a-be4a-0ddb2228c731

import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Set.Finite.Lemmas
import Theorems.Thm_OAI_PiExponent_WeightedDivision_finite_weight_sublevel

open scoped BigOperators

theorem solution
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (d : ι → ℝ) (hd : ∀ i, 0 < d i) :
    WellFounded (fun u v : ι →₀ ℕ =>
      (∑ i, d i * (u i : ℝ)) < (∑ i, d i * (v i : ℝ))) := by
  rw [WellFounded.wellFounded_iff_has_min]
  intro s hs
  obtain ⟨v, hv⟩ := hs
  let wt : (ι →₀ ℕ) → ℝ := fun u => ∑ i, d i * (u i : ℝ)
  have hfinite : {u : ι →₀ ℕ | wt u ≤ wt v}.Finite := by
    simpa [wt] using
      OAI.PiExponent.WeightedDivision.finite_weight_sublevel d hd (wt v)
  let t : Set (ι →₀ ℕ) := {u | wt u ≤ wt v} ∩ s
  have htfinite : t.Finite := hfinite.inter_of_left s
  have htnonempty : t.Nonempty := ⟨v, by simp [t, wt], hv⟩
  obtain ⟨m, hm, hmin⟩ := Set.exists_min_image t wt htfinite htnonempty
  refine ⟨m, hm.2, ?_⟩
  intro x hx hxm
  have hxle : wt x ≤ wt v := le_of_lt (lt_of_lt_of_le hxm hm.1)
  have hxt : x ∈ t := ⟨hxle, hx⟩
  exact (not_lt_of_ge (hmin x hxt)) hxm