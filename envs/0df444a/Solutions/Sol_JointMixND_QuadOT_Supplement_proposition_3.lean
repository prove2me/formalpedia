-- Prove2me | solution 1 for JointMixND.QuadOT.Supplement.proposition_3
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:24:05.104948+00:00
-- url     : https://prove2.me/submissions/4404c23b-6a8a-44d1-8469-92adbd4790bb

import Mathlib
import Definitions.Def_JointMixND_QuadOT_Basic
import Definitions.Def_JointMixND_QuadOT_Supplement_Dependence

open MeasureTheory ProbabilityTheory

open JointMixND
open JointMixND.QuadOT
open JointMixND.QuadOT.Supplement

theorem solution {n : ℕ} (F : Fin n → Measure ℝ) [∀ i, IsProbabilityMeasure (F i)]
    (hF : ∀ i, MemLp id 2 (F i))
    (hP : ∃ P : Measure (Fin n → ℝ), HasMarginals F P ∧ IsJointMix P ∧ IsNCD P) :
    ∀ j : Fin n, 2 * variance id (F j) ≤ ∑ i, variance id (F i) := by
      intro j
      obtain ⟨P, ⟨hPprob, hmarg⟩, ⟨c, hc⟩, hncd⟩ := hP
      have hmeas : ∀ i : Fin n, Measurable (fun x : Fin n → ℝ => x i) := fun i => measurable_pi_apply i
      have hL2 : ∀ i : Fin n, MemLp (fun x : Fin n → ℝ => x i) 2 P := by
        intro i
        have h := hF i
        rw [← hmarg i] at h
        exact (memLp_map_measure_iff h.aestronglyMeasurable (hmeas i).aemeasurable).1 h
      have hvar : ∀ i : Fin n, variance id (F i) = variance (fun x : Fin n → ℝ => x i) P := by
        intro i
        rw [← hmarg i, variance_id_map (hmeas i).aemeasurable]
      simp_rw [hvar]
      set s := Finset.univ.erase j with hs
      have hae : (fun x : Fin n → ℝ => ∑ i ∈ s, x i) =ᵐ[P] (fun x => c - x j) := by
        filter_upwards [hc] with x hx
        rw [← hx, ← Finset.add_sum_erase _ _ (Finset.mem_univ j)]
        ring
      have h1 : variance (fun x : Fin n → ℝ => ∑ i ∈ s, x i) P = variance (fun x : Fin n → ℝ => x j) P := by
        rw [variance_congr hae, variance_const_sub (hmeas j).aestronglyMeasurable]
      have h2 : variance (fun x : Fin n → ℝ => ∑ i ∈ s, x i) P
          = ∑ i ∈ s, ∑ k ∈ s, covariance (fun x : Fin n → ℝ => x i) (fun x => x k) P :=
        variance_fun_sum' (X := fun i (x : Fin n → ℝ) => x i) (fun i _ => hL2 i)
      have h3 : ∑ i ∈ s, ∑ k ∈ s, covariance (fun x : Fin n → ℝ => x i) (fun x => x k) P
          ≤ ∑ i ∈ s, variance (fun x : Fin n → ℝ => x i) P := by
        apply Finset.sum_le_sum
        intro i hi
        rw [← Finset.add_sum_erase _ _ hi, covariance_self (hmeas i).aemeasurable]
        have : ∑ k ∈ s.erase i, covariance (fun x : Fin n → ℝ => x i) (fun x => x k) P ≤ 0 := by
          apply Finset.sum_nonpos
          intro k hk
          exact hncd i k (Finset.ne_of_mem_erase hk).symm
        linarith
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j)]
      linarith
