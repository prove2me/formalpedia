-- Prove2me | solution 1 for Kyprianou.Ch04.cor412_dyadic_reward_eq
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T08:13:00.907486+00:00
-- url     : https://prove2.me/submissions/1fa53d59-8a62-47ca-a0a8-1155ab6fc723

import Mathlib
import Theorems.Thm_AvramDividend_Classical_dyadic_ceiling_nnreal_tendsto
import Theorems.Thm_AvramDividend_Classical_dyadic_ceiling_time_ge_nnreal
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
set_option autoImplicit false

/-- For a lower-bounded right-continuous path, countable dyadic infima give its actual infimum. -/
theorem solution (f : NNReal → ℝ)
    (hRC : ∀ t, ContinuousWithinAt f (Ici t) t)
    (hB : BddBelow (range f)) (β : ℝ) (hβ : 0 ≤ β) :
    (⨅ q : ℕ × ℕ, ENNReal.ofReal (Real.exp (β * f ((q.1 : NNReal) / 2 ^ q.2)))) =
      ENNReal.ofReal (Real.exp (β * sInf (range f))) := by
  let e : ℝ → ℝ≥0∞ := fun x => ENNReal.ofReal (Real.exp (β * x))
  let g : ℕ × ℕ → ℝ := fun q => f ((q.1 : NNReal) / 2 ^ q.2)
  have hmono : Monotone e := fun a b hab =>
    ENNReal.ofReal_le_ofReal ((Real.exp_le_exp).mpr (mul_le_mul_of_nonneg_left hab hβ))
  have hcont : Continuous e :=
    ENNReal.continuous_ofReal.comp (Real.continuous_exp.comp (continuous_const.mul continuous_id))
  have hg : BddBelow (range g) := hB.mono (by
    rintro x ⟨q,rfl⟩
    exact ⟨_,rfl⟩)
  have heq : sInf (range g) = sInf (range f) := by
    apply le_antisymm
    · apply le_csInf (range_nonempty f)
      rintro x ⟨t,rfl⟩
      let a : ℕ → NNReal := fun n =>
        (Nat.ceil ((t : ℝ) * (2 : ℝ) ^ n) : NNReal) / (2 : NNReal) ^ n
      have hlim : Tendsto a atTop (𝓝[≥] t) :=
        tendsto_nhdsWithin_iff.mpr ⟨dyadic_ceiling_nnreal_tendsto t,
          Eventually.of_forall (dyadic_ceiling_time_ge_nnreal t)⟩
      apply le_of_tendsto_of_tendsto tendsto_const_nhds ((hRC t).tendsto.comp hlim)
      exact Eventually.of_forall fun n =>
        csInf_le hg ⟨(Nat.ceil ((t : ℝ) * (2 : ℝ) ^ n), n), rfl⟩
    · apply le_csInf (range_nonempty g)
      rintro x ⟨q,rfl⟩
      exact csInf_le hB ⟨_,rfl⟩
  change (⨅ q, e (g q)) = e (sInf (range f))
  rw [← heq]
  exact (hmono.map_ciInf_of_continuousAt hcont.continuousAt hg).symm
