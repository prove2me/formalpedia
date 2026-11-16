-- Prove2me | solution 1 for Kyprianou.Ch01.independentLevySum_pairedIncrements
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T10:46:46.841942+00:00
-- url     : https://prove2.me/submissions/0145bfd1-856f-43cc-9a8d-658a40e6917d

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Theorems.Thm_Kyprianou_Ch01_iIndepFun_paired_independent_processes

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory
open scoped NNReal
set_option autoImplicit false

/-- Pair independent Lévy increments via the product-families independence lemma. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X Y : ℝ≥0 → Ω → ℝ)
    (hX : IsLevyProcess X P)
    (hY : IsLevyProcess Y P)
    (hXY : IndepFun (fun ω => fun t => X t ω)
      (fun ω => fun t => Y t ω) P) :
    ∀ (n : ℕ) (t : Fin (n + 1) → ℝ≥0), Monotone t →
      iIndepFun
        (fun k : Fin n => fun ω =>
          (increment X (t k.castSucc) (t k.succ) ω,
           increment Y (t k.castSucc) (t k.succ) ω)) P := by
  intro n t ht
  let f : Fin n → Ω → ℝ :=
    fun k => increment X (t k.castSucc) (t k.succ)
  let g : Fin n → Ω → ℝ :=
    fun k => increment Y (t k.castSucc) (t k.succ)
  have htrans : Measurable
      (fun path : ℝ≥0 → ℝ =>
        fun k : Fin n => path (t k.succ) - path (t k.castSucc)) := by
    apply measurable_pi_iff.mpr
    intro k
    exact (measurable_pi_apply (t k.succ)).sub
      (measurable_pi_apply (t k.castSucc))
  have hfg : IndepFun (fun ω => fun k => f k ω)
      (fun ω => fun k => g k ω) P := by
    simpa only [Function.comp_def, f, g, increment] using
      hXY.comp htrans htrans
  have hle (k : Fin n) : t k.castSucc ≤ t k.succ :=
    ht (Fin.castSucc_le_succ k)
  have hfm : ∀ k : Fin n, AEMeasurable (f k) P := by
    intro k
    have hs := (hX.stationary_increments
      (t k.castSucc) (t k.succ - t k.castSucc)).aemeasurable_fst
    simpa only [f, add_tsub_cancel_of_le (hle k)] using hs
  have hgm : ∀ k : Fin n, AEMeasurable (g k) P := by
    intro k
    have hs := (hY.stationary_increments
      (t k.castSucc) (t k.succ - t k.castSucc)).aemeasurable_fst
    simpa only [g, add_tsub_cancel_of_le (hle k)] using hs
  simpa only [f, g] using
    (Kyprianou.Ch01.iIndepFun_paired_independent_processes
      P f g (hX.indep_increments n t ht)
      (hY.indep_increments n t ht) hfg hfm hgm)
