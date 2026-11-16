-- Prove2me | solution 1 for InfoLossLAR.WorstCase.RegevSketch.finite_exact_sivp
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-15T08:58:51.10426+00:00
-- url     : https://prove2.me/submissions/6a1896a2-f1e4-4ecf-a10c-2cc9fbcffd0f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_InfoLossLAR_WorstCase_RegevSketch_finite_exact_sivp_classical
import Theorems.Thm_InfoLossLAR_WorstCase_RegevSketch_polytime_string_to_mqpt

set_option autoImplicit false
open QAlgorithms.Complexity InfoLossLAR.WorstCase InfoLossLAR.WorstCase.RegevSketch

theorem solution (cutoff : ℕ) :
    ∃ E : MFamily, IsMQPT E ∧ ∀ n, 1 ≤ n → n < cutoff → SolvesSIVP E (famN n) 1 := by
  obtain ⟨f, hf, hcorrect⟩ := finite_exact_sivp_classical cutoff
  obtain ⟨P, hP, hsim⟩ := polytime_string_to_mqpt f hf
  refine ⟨P, hP, ?_⟩
  intro n hn hcut
  change SolvesSIVP P n 1
  intro B hB
  obtain ⟨y, hp, hl, hi, hb⟩ := hcorrect n hn hcut B hB
  have h := hsim (encMat encI B) (fun out =>
      ∃ y : Fin n → Fin n → ℤ, encVec (encVec encI) y <+: out ∧
        (∀ i, intVecE (y i) ∈ lattice B) ∧ LinearIndependent ℝ (fun i => intVecE (y i)) ∧
        ∀ i, ‖intVecE (y i)‖ ≤ (1 : ℝ) * lamN B) (by
          intro s t hs hst
          obtain ⟨v, hpv, hlv, hiv, hbv⟩ := hs
          exact ⟨v, hpv.trans hst, hlv, hiv, hbv⟩) (by
            exact ⟨y, hp, hl, hi, by simpa using hb⟩)
  linarith
