-- Prove2me | solution 1 for MarkovChainCLT.isStrictlyStationary_comp_of_measurable
-- status  : ACCEPTED   (prove)
-- author  : @LukeBernese
-- created : 2026-08-15T15:51:29.407555+00:00
-- url     : https://prove2.me/submissions/e6d83ae4-6457-444c-80c3-08b15062bc9b

import Definitions.Def_MixingCoefficients

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology ProbabilityTheory
open MarkovChainCLT

theorem solution {Ω X E : Type*} [MeasurableSpace Ω] [MeasurableSpace X] [MeasurableSpace E]
    (P : Measure Ω) (Y : ℕ → Ω → X) (hY : ∀ n, Measurable (Y n))
    (hstat : IsStrictlyStationary P Y) (g : X → E) (hg : Measurable g) :
    IsStrictlyStationary P (fun i ω => g (Y i ω)) := by
  intro k
  have hΦ : Measurable (fun (p : ℕ → X) (n : ℕ) => g (p n)) :=
    measurable_pi_lambda _ (fun n => hg.comp (measurable_pi_apply n))
  have hψk : Measurable (fun ω => fun n => Y (n + k) ω) :=
    measurable_pi_lambda _ (fun n => hY (n + k))
  have hψ0 : Measurable (fun ω => fun n => Y n ω) :=
    measurable_pi_lambda _ (fun n => hY n)
  have e1 : Measure.map (fun ω => fun n => g (Y (n + k) ω)) P
      = Measure.map (fun (p : ℕ → X) (n : ℕ) => g (p n))
          (Measure.map (fun ω => fun n => Y (n + k) ω) P) := by
    rw [Measure.map_map hΦ hψk]; rfl
  have e2 : Measure.map (fun ω => fun n => g (Y n ω)) P
      = Measure.map (fun (p : ℕ → X) (n : ℕ) => g (p n))
          (Measure.map (fun ω => fun n => Y n ω) P) := by
    rw [Measure.map_map hΦ hψ0]; rfl
  rw [e1, e2, hstat k]
