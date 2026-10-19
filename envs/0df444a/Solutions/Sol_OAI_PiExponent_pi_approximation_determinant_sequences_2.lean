-- Prove2me | solution 2 for OAI.PiExponent.pi_approximation_determinant_sequences
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-16T11:23:35.941166+00:00
-- url     : https://prove2.me/submissions/07745842-fc72-48b4-b50c-0f1d5cdef4a2
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_OAI_PiExponent_pi_cofinal_real_height_determinant_certificates
import Mathlib.Order.Filter.AtTopBot.Archimedean
import Mathlib.Order.Filter.AtTopBot.Tendsto
import Definitions.Def_OAI_PiExponent_ApproximationDefinitions
import Mathlib.Topology.Instances.Real.Lemmas

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter Topology

-- Sequence interface extracted from the pinned source's determinant argument.
-- The construction of these sequences is the open analytic/geometric obligation.

theorem solution
    (nu : ℝ) (hnu : 2 < nu)
    (hbad : ∀ Q : ℕ, ∃ (p : ℤ) (q : ℕ),
      Q ≤ q ∧ |Real.pi - (p : ℝ) / (q : ℝ)| ≤ (q : ℝ) ^ (-nu)) :
    ∃ theta x ear ean collisionLimit : ℝ,
      ∃ b d err collision : ℕ → ℝ,
        ear + ean < nu * (x - theta) - (1 - theta) ∧
        1 + ear + ean < collisionLimit ∧
        Tendsto err atTop (𝓝 0) ∧
        Tendsto collision atTop (𝓝 collisionLimit) ∧
        (∀ᶠ n in atTop, 0 ≤ b n) ∧
        (∀ᶠ n in atTop, b n ≤ theta) ∧
        (∀ᶠ n in atTop, -(1 - b n) - ear ≤ d n) ∧
        (∀ᶠ n in atTop,
          d n ≤ ean + err n + max (-collision n) (-nu * (x - b n))) := by
  classical
  obtain ⟨theta, x, ear, ean, collisionLimit,
    mean, error, rate, hbudget, hcollision, herr, hrate, hcert⟩ :=
      OAI.PiExponent.pi_cofinal_real_height_determinant_certificates nu hnu hbad
  let H : ℕ → ℝ := fun n => Classical.choose (hcert (n : ℝ))
  let D : ℕ → ℝ := fun n =>
    Classical.choose (Classical.choose_spec (hcert (n : ℝ)))
  have hp (n : ℕ) :
      (n : ℝ) ≤ H n ∧ 0 < H n ∧
      0 ≤ mean (H n) ∧ mean (H n) ≤ theta ∧
      -(1 - mean (H n)) - ear ≤ D n ∧
      D n ≤ ean + error (H n) +
        max (-rate (H n)) (-nu * (x - mean (H n))) :=
    Classical.choose_spec (Classical.choose_spec (hcert (n : ℝ)))
  have hH : Tendsto H atTop atTop :=
    Filter.tendsto_atTop_mono (fun n => (hp n).1)
      (tendsto_natCast_atTop_atTop :
        Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop)
  refine ⟨theta, x, ear, ean, collisionLimit,
    (fun n => mean (H n)), D, (fun n => error (H n)),
    (fun n => rate (H n)), hbudget, hcollision,
    herr.comp hH, hrate.comp hH, ?_, ?_, ?_, ?_⟩
  · exact Filter.Eventually.of_forall (fun n => (hp n).2.2.1)
  · exact Filter.Eventually.of_forall (fun n => (hp n).2.2.2.1)
  · exact Filter.Eventually.of_forall (fun n => (hp n).2.2.2.2.1)
  · exact Filter.Eventually.of_forall (fun n => (hp n).2.2.2.2.2)
