-- Prove2me | solution 1 for ManyServerQED.Scheduling.queue_hjb_cost_comparison
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-25T20:43:59.740503+00:00
-- url     : https://prove2.me/submissions/9083b5f4-a5d2-4be8-aee8-7690568acee2
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_ManyServerQED_Scheduling_queue_hjb_subsequential_balance
import Mathlib
import Definitions.Def_BellWilliams2001_ThresholdPolicy_Paths
import Definitions.Def_ManyServerQED_Scheduling_Diffusion
import Definitions.Def_ManyServerQED_Scheduling_Model
import Definitions.Def_ManyServerQED_Scheduling_Policy

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

open ManyServerQED.Scheduling BellWilliams2001.ThresholdPolicy

theorem solution {Ω : Type*} [MeasurableSpace Ω] {k : ℕ} [NeZero k] (M : SystemSequence Ω k)
    (Lt : (Fin k → ℝ) → (Fin k → ℝ) → ℝ) (ϱ mL mU γ : ℝ)
    (hA2 : Assumption2 Lt ϱ mL) (hA3 : M.Assumption3 mL mU) (hγ : 0 < γ)
    (u0 : Fin k → ℝ) (hu0 : u0 ∈ stdSimplex ℝ (Fin k))
    (X0 : ℕ → Fin k → ℕ) (x : Fin k → ℝ)
    (hX0 : Tendsto (fun n => M.Xhat0 n (X0 n)) atTop (𝓝 x))
    (X Ψ : ℕ → Ω → ℝ → Fin k → ℝ)
    (hpol : ∀ n, 1 ≤ n → M.IsSCP n (X0 n) (X n) (Ψ n) ∧ M.IsAdmissible n (X n) (Ψ n) ∧
      IsWorkConserving n (X n) (Ψ n))
    (f : (Fin k → ℝ) → ℝ) (hf : IsC2Pol f)
    (hHJB : IsHJBSolution M.diffData (costOfTilde Lt) γ f)
    :
    ENNReal.ofReal (f x) ≤ liminf (fun n => M.queueCostL (costOfTilde Lt) γ n u0 (X n) (Ψ n)) atTop ∧
      ((UocInProb M.P
      (fun n ω t => ![∫ s in (0 : ℝ)..t, Real.exp (-γ * s) *
        (∑ i, drift M.diffData (M.Xhat n (X n) ω s) (uProc n u0 (X n) (Ψ n) ω s) i *
            grad f (M.Xhat n (X n) ω s) i +
          costOfTilde Lt (M.Xhat n (X n) ω s) (uProc n u0 (X n) (Ψ n) ω s) -
          hamiltonian M.diffData (costOfTilde Lt) (M.Xhat n (X n) ω s)
            (grad f (M.Xhat n (X n) ω s)))])
      (fun _ => 0)) →
        limsup (fun n => M.queueCostL (costOfTilde Lt) γ n u0 (X n) (Ψ n)) atTop ≤ ENNReal.ofReal (f x)) := by
  have hb := queue_hjb_subsequential_balance M Lt ϱ mL mU γ hA2 hA3 hγ u0 hu0
    X0 x hX0 X Ψ hpol f hf hHJB
  let C (n : ℕ) := M.queueCostL (costOfTilde Lt) γ n u0 (X n) (Ψ n)
  change ENNReal.ofReal (f x) ≤ liminf C atTop ∧ (_ → limsup C atTop ≤ ENNReal.ofReal (f x))
  constructor
  · by_contra! h
    obtain ⟨z, hzL, hzU⟩ := exists_between h
    obtain ⟨s, hs, hsZ⟩ := exists_seq_forall_of_frequently (frequently_lt_of_liminf_lt (by isBoundedDefault) hzL)
    obtain ⟨r, hr, g, hg, hlim, hgap⟩ := hb s hs
    have hle : ENNReal.ofReal (f x + g) ≤ z := le_of_tendsto hlim
      (Eventually.of_forall (fun j => (hsZ (r j)).le))
    exact (not_le_of_gt hzU) ((ENNReal.ofReal_le_ofReal (by linarith)).trans hle)
  · intro h49
    by_contra! h
    obtain ⟨z, hzL, hzU⟩ := exists_between h
    obtain ⟨s, hs, hsZ⟩ := exists_seq_forall_of_frequently (frequently_lt_of_lt_limsup (by isBoundedDefault) hzU)
    obtain ⟨r, hr, g, hg, hlim, hgap⟩ := hb s hs
    rw [hgap h49, add_zero] at hlim
    exact (not_le_of_gt hzL) (ge_of_tendsto hlim
      (Eventually.of_forall (fun j => (hsZ (r j)).le)))
