-- Prove2me | solution 1 for MartingaleHT.InfiniteServer.lemma_3_3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T14:58:44.425446+00:00
-- url     : https://prove2.me/submissions/53d9a727-784e-4867-9239-bcc8d1ed3d1d

import Mathlib
import Definitions.Def_BellWilliams2001_ThresholdPolicy_Paths
import Definitions.Def_ManyServerQED_Scheduling_Model
import Definitions.Def_ErlangA_Diffusion_SDE
import Definitions.Def_ErlangA_Diffusion_Queue
import Definitions.Def_MartingaleHT_InfiniteServer_Model
import Definitions.Def_MartingaleHT_InfiniteServer_Toolkit

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BoundedContinuousFunction

open MartingaleHT.InfiniteServer BellWilliams2001.ThresholdPolicy ManyServerQED.Scheduling
  ErlangA.Diffusion in
theorem solution (lam μ : ℝ) (hlam : 0 < lam) (hμ : 0 < μ) (A S : ℝ → ℝ) (Q : ℝ → ℕ)
    (hA : MonotoneOn A (Set.Ici 0)) (hS : ∀ u : ℝ, 0 ≤ u → 0 ≤ S u)
    (hint : ∀ t : ℝ, 0 ≤ t → IntervalIntegrable (fun s => (Q s : ℝ)) volume 0 t)
    (h12 : ∀ t : ℝ, 0 ≤ t →
      (Q t : ℝ) = (Q 0 : ℝ) + A (lam * t) - S (μ * ∫ s in (0 : ℝ)..t, (Q s : ℝ))) :
    ∀ t : ℝ, 0 ≤ t → (Q t : ℝ) ≤ (Q 0 : ℝ) + A (lam * t) ∧
      ∫ s in (0 : ℝ)..t, (Q s : ℝ) ≤ t * ((Q 0 : ℝ) + A (lam * t)) := by
  have first : ∀ t : ℝ, 0 ≤ t → (Q t : ℝ) ≤ (Q 0 : ℝ) + A (lam * t) := by
    intro t ht
    have hI : 0 ≤ ∫ s in (0 : ℝ)..t, (Q s : ℝ) :=
      intervalIntegral.integral_nonneg ht (fun s _ => Nat.cast_nonneg _)
    have := hS _ (mul_nonneg hμ.le hI)
    rw [h12 t ht]
    linarith
  intro t ht
  refine ⟨first t ht, ?_⟩
  have hmono : ∀ s ∈ Set.Icc (0 : ℝ) t, (Q s : ℝ) ≤ (Q 0 : ℝ) + A (lam * t) := by
    intro s hs
    have h1 := first s hs.1
    have h2 : A (lam * s) ≤ A (lam * t) :=
      hA (Set.mem_Ici.mpr (mul_nonneg hlam.le hs.1)) (Set.mem_Ici.mpr (mul_nonneg hlam.le ht))
        (mul_le_mul_of_nonneg_left hs.2 hlam.le)
    linarith
  have := intervalIntegral.integral_mono_on ht (hint t ht) intervalIntegrable_const hmono
  rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero] at this
  exact this
