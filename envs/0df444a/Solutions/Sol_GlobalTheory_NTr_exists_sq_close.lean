-- Prove2me | solution 1 for GlobalTheory.NTr.exists_sq_close
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T19:23:00.17391+00:00
-- url     : https://prove2.me/submissions/dffa5da7-7209-420d-8729-486956342777

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnramifiedQuadraticIntegralTraceFormPerfect
import Theorems.Thm_GlobalTheory_NTr_um_sub
import Theorems.Thm_GlobalTheory_NTr_mem_ball1

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.NTr
variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [hU : Unram F E]
variable {K : Type} [NormedField K] [IsUltrametricDist K]
namespace GlobalTheory.NTr
theorem _root_.solution [ProperSpace K] (h2 : ‖(2 : K)‖ < 1) (n : K) (hn : ‖n‖ ≤ 1) :
    ∃ s : K, ‖s‖ ≤ 1 ∧ ‖n - s ^ 2‖ < 1 := by
  classical
  let B := Metric.closedBall (0 : K) 1
  let S := closeSetoid K
  have hfin : Finite (Quotient S) := by
    obtain ⟨t, htB, htf, hcov⟩ := (isCompact_closedBall (0 : K) 1).finite_cover_balls (e := 1) one_pos
    haveI : Finite t := htf.to_subtype
    refine Finite.of_surjective (fun i : t => (Quotient.mk S ⟨i.1, htB i.2⟩ : Quotient S)) ?_
    intro q
    induction q using Quotient.inductionOn with
    | h a =>
      have := hcov a.2
      simp only [Set.mem_iUnion] at this
      obtain ⟨i, hi, hai⟩ := this
      refine ⟨⟨i, hi⟩, Quotient.sound ?_⟩
      show ‖i - (a : K)‖ < 1
      rw [norm_sub_rev]; simpa [dist_eq_norm] using hai
  have hsq : ∀ a : B, (a : K) ^ 2 ∈ B := fun a => by
    simp only [B, Metric.mem_closedBall, dist_zero_right, norm_pow]
    exact pow_le_one₀ (norm_nonneg _) (mem_ball1 a.2)
  let f : Quotient S → Quotient S := Quotient.map (fun a : B => (⟨(a : K) ^ 2, hsq a⟩ : B)) (by
    intro a b hab
    show ‖(a : K) ^ 2 - (b : K) ^ 2‖ < 1
    have hab' : ‖(a : K) - b‖ < 1 := hab
    have hp : (a : K) ^ 2 - (b : K) ^ 2 = ((a : K) - b) * ((a : K) + b) := by ring
    rw [hp, norm_mul]
    have : ‖(a : K) + b‖ ≤ 1 :=
      (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (mem_ball1 a.2) (mem_ball1 b.2))
    calc ‖(a : K) - b‖ * ‖(a : K) + b‖ ≤ ‖(a : K) - b‖ * 1 :=
          mul_le_mul_of_nonneg_left this (norm_nonneg _)
      _ < 1 := by simpa using hab')
  have hinj : Function.Injective f := by
    intro q1 q2 h
    induction q1 using Quotient.inductionOn with
    | h a =>
    induction q2 using Quotient.inductionOn with
    | h b =>
    have h' : ‖(a : K) ^ 2 - (b : K) ^ 2‖ < 1 := Quotient.exact h
    apply Quotient.sound
    show ‖(a : K) - b‖ < 1
    by_contra hc
    push_neg at hc
    have hle : ‖(a : K) - b‖ ≤ 1 := (um_sub _ _).trans (max_le (mem_ball1 a.2) (mem_ball1 b.2))
    have h1 : ‖(a : K) - b‖ = 1 := le_antisymm hle hc
    have h2b : ‖2 * (b : K)‖ < 1 := by
      rw [norm_mul]
      calc ‖(2 : K)‖ * ‖(b : K)‖ ≤ ‖(2 : K)‖ * 1 := mul_le_mul_of_nonneg_left (mem_ball1 b.2) (norm_nonneg _)
        _ < 1 := by simpa using h2
    have hplus : ‖(a : K) + b‖ = 1 := by
      have : (a : K) + b = ((a : K) - b) + 2 * (b : K) := by ring
      rw [this, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [h1]; exact h2b.ne'), h1]
      exact max_eq_left h2b.le
    have hp : (a : K) ^ 2 - (b : K) ^ 2 = ((a : K) - b) * ((a : K) + b) := by ring
    rw [hp, norm_mul, h1, hplus] at h'
    norm_num at h'
  obtain ⟨q, hq⟩ := (Finite.injective_iff_surjective.mp hinj) (Quotient.mk S ⟨n, by simpa using hn⟩)
  induction q using Quotient.inductionOn with
  | h s =>
  have hq' : ‖(s : K) ^ 2 - n‖ < 1 := Quotient.exact hq
  exact ⟨s, mem_ball1 s.2, by rwa [norm_sub_rev]⟩
end GlobalTheory.NTr
