-- Prove2me | solution 1 for InfoLossLAR.WorstCase.BDD.adaptive_trace_tv_bound
-- status  : ACCEPTED   (prove)
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-15T09:26:48.460825+00:00
-- url     : https://prove2.me/submissions/8b945ed0-98b4-4df4-9726-6d07e02310f6

import Definitions.Def_InfoLossLAR_LoadedBatchBundle_05

set_option autoImplicit false
open AFT
open scoped BigOperators
noncomputable section

/-- A full-transcript union bound that permits arbitrary dependence between
adaptive stages and pays for replacement of the complete source law once. -/
theorem solution {Ω : Type*} [Fintype Ω] (steps : ℕ)
    (actual ideal : FiniteDist Ω) (err : ℝ)
    (htv : FiniteDist.TVBound actual ideal err)
    (bad : Fin steps → Ω → Prop) [∀ i, DecidablePred (bad i)]
    (fail : Ω → Prop) [DecidablePred fail]
    (hfail : ∀ ω, fail ω → ∃ i, bad i ω)
    (bound : Fin steps → ℝ)
    (hstage : ∀ i, (∑ ω, if bad i ω then ideal.weight ω else 0) ≤ bound i) :
    (∑ ω, if fail ω then actual.weight ω else 0) ≤ err + ∑ i, bound i := by
  classical
  let event : Finset Ω := Finset.univ.filter fail
  have hv := (abs_le.mp (htv event)).2
  simp only [FiniteDist.event,event,Finset.sum_filter] at hv
  have hpoint (ω : Ω) : (if fail ω then ideal.weight ω else 0) ≤
      ∑ i : Fin steps, if bad i ω then ideal.weight ω else 0 := by
    by_cases hf : fail ω
    · obtain ⟨i, hi⟩ := hfail ω hf
      have hh : (if bad i ω then ideal.weight ω else 0) ≤
          ∑ j : Fin steps, if bad j ω then ideal.weight ω else 0 := by
        apply Finset.single_le_sum (fun j _ => ?_) (Finset.mem_univ i)
        split_ifs
        · exact ideal.nonneg ω
        · norm_num
      simpa only [if_pos hf, if_pos hi] using hh
    · rw [if_neg hf]
      apply Finset.sum_nonneg
      intro i _
      split_ifs
      · exact ideal.nonneg ω
      · norm_num
  have hi : (∑ ω, if fail ω then ideal.weight ω else 0) ≤ ∑ i, bound i := by
    calc
      _ ≤ ∑ ω, ∑ i : Fin steps, if bad i ω then ideal.weight ω else 0 :=
        Finset.sum_le_sum (fun ω _ => hpoint ω)
      _ = ∑ i : Fin steps, ∑ ω, if bad i ω then ideal.weight ω else 0 := Finset.sum_comm
      _ ≤ _ := Finset.sum_le_sum (fun i _ => hstage i)
  linarith

#print axioms solution
