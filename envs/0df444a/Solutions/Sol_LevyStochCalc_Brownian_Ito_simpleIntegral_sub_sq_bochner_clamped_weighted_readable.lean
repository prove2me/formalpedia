-- Prove2me | solution 1 for LevyStochCalc.Brownian.Ito.simpleIntegral_sub_sq_bochner_clamped_weighted_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:20:26.515852+00:00
-- url     : https://prove2.me/submissions/d3c0b331-2348-40af-a322-5534dacc8901

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoL2CompletionCompensator
import Theorems.Thm_LevyStochCalc_Brownian_Ito_integral_factor_increment_sq_readable
import Theorems.Thm_LevyStochCalc_Brownian_Ito_offDiagonal_increment_integral_zero_weighted_readable
import Theorems.Thm_LevyStochCalc_Brownian_Ito_simpleIntegral_sub_eq_clamp_sum_readable

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/ItoL2CompletionCompensator.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory
open scoped NNReal ENNReal
universe u
variable {Ω : Type u} [MeasurableSpace Ω]
/-- **Weighted clamped Bochner increment second moment.** For adapted simple `H`,
`0 ≤ s ≤ t`, and a bounded `F_s`-measurable weight `g`,
`∫ g·(I_t − I_s)² = ∑ᵢ (cᵢ₊₁ − cᵢ)·∫ g·ξᵢ²` with `cᵢ = max s (min pᵢ t)`.
The set-level (`g = 1_B`, `B ∈ F_s`) conditional Itô isometry at simple level:
the increment squares onto the `[s,t]`-clamped partition, off-diagonal terms vanish
(`offDiagonal_increment_integral_zero_weighted`), and the diagonal gives the
clamped lengths weighted by `g` (`integral_factor_increment_sq`). -/
lemma solution
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : LevyStochCalc.Brownian.IsBrownianFiltration W ℱ)
    {T : ℝ} (H : LevyStochCalc.Brownian.Ito.SimplePredictable Ω T)
    (h_adapt : ∀ i : Fin H.N, @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ (H.partition i.castSucc)) (H.ξ i))
    {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t)
    {g : Ω → ℝ} (hg : @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ s) g)
    {Cg : ℝ} (hg_bdd : ∀ ω, |g ω| ≤ Cg) :
    ∫ ω, g ω * (LevyStochCalc.Brownian.Ito.simpleIntegral W H t ω - LevyStochCalc.Brownian.Ito.simpleIntegral W H s ω) ^ 2 ∂P
      = ∑ i : Fin H.N,
        (max s (min (H.partition i.succ) t) - max s (min (H.partition i.castSucc) t))
          * ∫ ω, g ω * (H.ξ i ω) ^ 2 ∂P := by
  have hgmeas : Measurable g := (hg.mono (ℱ.le s)).measurable
  have h_cl_nn : ∀ p : ℝ, 0 ≤ max s (min p t) := fun p => le_trans hs (le_max_left _ _)
  have h_cl_mono : ∀ {a b : ℝ}, a ≤ b → max s (min a t) ≤ max s (min b t) :=
    fun hab => max_le_max (le_refl s) (min_le_min hab (le_refl t))
  have h_a_le_b : ∀ i : Fin H.N,
      max s (min (H.partition i.castSucc) t) ≤ max s (min (H.partition i.succ) t) :=
    fun i => h_cl_mono (le_of_lt (H.partition_strictMono Fin.castSucc_lt_succ))
  -- In the genuine (non-degenerate) case the lower clamp dominates the partition pt.
  have h_padapt : ∀ i : Fin H.N,
      max s (min (H.partition i.castSucc) t) < max s (min (H.partition i.succ) t) →
        H.partition i.castSucc ≤ max s (min (H.partition i.castSucc) t) := by
    intro i hlt
    by_cases hpt : H.partition i.castSucc ≤ t
    · rw [min_eq_left hpt]; exact le_max_right _ _
    · push Not at hpt
      exfalso
      have h1 : min (H.partition i.castSucc) t = t := min_eq_right (le_of_lt hpt)
      have h2 : min (H.partition i.succ) t = t :=
        min_eq_right (le_of_lt (lt_trans hpt (H.partition_strictMono Fin.castSucc_lt_succ)))
      rw [h1, h2] at hlt; exact lt_irrefl _ hlt
  -- ξ adaptedness lifted to the clamped left endpoint (genuine case).
  have h_ξ_cl : ∀ i : Fin H.N,
      max s (min (H.partition i.castSucc) t) < max s (min (H.partition i.succ) t) →
        @MeasureTheory.StronglyMeasurable Ω ℝ _
          (ℱ.seq (max s (min (H.partition i.castSucc) t))) (H.ξ i) :=
    fun i hlt => (h_adapt i).mono (ℱ.mono (h_padapt i hlt))
  set term : Fin H.N → Ω → ℝ := fun i ω =>
    H.ξ i ω * (W.W (max s (min (H.partition i.succ) t)) ω
      - W.W (max s (min (H.partition i.castSucc) t)) ω) with hterm
  -- integrability of every weighted cross product
  have h_cross : ∀ i j : Fin H.N,
      MeasureTheory.Integrable (fun ω => g ω * (term i ω * term j ω)) P := by
    intro i j
    obtain ⟨Mi, hMi⟩ := H.ξ_bounded i
    obtain ⟨Mj, hMj⟩ := H.ξ_bounded j
    refine MeasureTheory.Integrable.bdd_mul (c := Cg)
      (LevyStochCalc.Brownian.Ito.cross_increment_integrable W (h_cl_nn _) (h_a_le_b i) (h_cl_nn _) (h_a_le_b j)
        (H.ξ i) (H.ξ j) (H.ξ_measurable i) (H.ξ_measurable j) Mi hMi Mj hMj)
      hgmeas.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun ω => (Real.norm_eq_abs (g ω)).le.trans (hg_bdd ω)))
  -- off-diagonal vanishing for i < j
  have h_off : ∀ i j : Fin H.N, i < j → ∫ ω, g ω * (term i ω * term j ω) ∂P = 0 := by
    intro i j hij
    rcases eq_or_lt_of_le (h_a_le_b j) with hj_eq | hj_lt
    · rw [show (fun ω => g ω * (term i ω * term j ω)) = fun _ => (0 : ℝ) from by
        funext ω; simp only [hterm]; rw [← hj_eq]; ring]
      exact MeasureTheory.integral_zero _ _
    · rcases eq_or_lt_of_le (h_a_le_b i) with hi_eq | hi_lt
      · rw [show (fun ω => g ω * (term i ω * term j ω)) = fun _ => (0 : ℝ) from by
          funext ω; simp only [hterm]; rw [← hi_eq]; ring]
        exact MeasureTheory.integral_zero _ _
      · have hbi_le_aj : max s (min (H.partition i.succ) t)
            ≤ max s (min (H.partition j.castSucc) t) :=
          h_cl_mono (H.partition_strictMono.monotone (Fin.succ_le_castSucc_iff.mpr hij))
        exact LevyStochCalc.Brownian.Ito.offDiagonal_increment_integral_zero_weighted_readable W ℱ hℱ (h_cl_nn _) hi_lt hbi_le_aj hj_lt
          (H.ξ i) (H.ξ j) g (h_ξ_cl i hi_lt) (h_ξ_cl j hj_lt)
          (hg.mono (ℱ.mono (le_max_left s (min (H.partition i.castSucc) t))))
  rw [show (fun ω => g ω * (LevyStochCalc.Brownian.Ito.simpleIntegral W H t ω - LevyStochCalc.Brownian.Ito.simpleIntegral W H s ω) ^ 2)
        = fun ω => ∑ i : Fin H.N, ∑ j : Fin H.N, g ω * (term i ω * term j ω) from by
    funext ω
    rw [LevyStochCalc.Brownian.Ito.simpleIntegral_sub_eq_clamp_sum_readable W H hst ω,
      show (∑ i : Fin H.N, term i ω) ^ 2
          = ∑ i : Fin H.N, ∑ j : Fin H.N, term i ω * term j ω from by
        rw [sq, Finset.sum_mul_sum], Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i _ => by rw [Finset.mul_sum])]
  rw [MeasureTheory.integral_finsetSum _
    (fun i _ => MeasureTheory.integrable_finsetSum _ (fun j _ => h_cross i j))]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [MeasureTheory.integral_finsetSum _ (fun j _ => h_cross i j),
    Finset.sum_eq_single i]
  · -- diagonal j = i
    rcases eq_or_lt_of_le (h_a_le_b i) with hi_eq | hi_lt
    · rw [show (fun ω => g ω * (term i ω * term i ω)) = fun _ => (0 : ℝ) from by
        funext ω; simp only [hterm]; rw [← hi_eq]; ring, MeasureTheory.integral_zero,
        ← hi_eq, sub_self, zero_mul]
    · have hg2 : @MeasureTheory.StronglyMeasurable Ω ℝ _
          (ℱ.seq (max s (min (H.partition i.castSucc) t))) (fun ω => g ω * (H.ξ i ω) ^ 2) := by
        refine (hg.mono (ℱ.mono (le_max_left s (min (H.partition i.castSucc) t)))).mul ?_
        simpa [pow_two, Pi.mul_def] using (h_ξ_cl i hi_lt).mul (h_ξ_cl i hi_lt)
      have hdiag := LevyStochCalc.Brownian.Ito.integral_factor_increment_sq_readable W ℱ hℱ (h_cl_nn _) hi_lt hg2
      rw [show (fun ω => g ω * (term i ω * term i ω))
            = fun ω => (g ω * (H.ξ i ω) ^ 2)
                * (W.W (max s (min (H.partition i.succ) t)) ω
                    - W.W (max s (min (H.partition i.castSucc) t)) ω) ^ 2 from by
          funext ω; simp only [hterm]; ring, hdiag, mul_comm]
  · intro j _ hj
    rcases lt_or_gt_of_ne hj with h_lt | h_gt
    · rw [show (fun ω => g ω * (term i ω * term j ω))
            = fun ω => g ω * (term j ω * term i ω) from by funext ω; ring]
      exact h_off j i h_lt
    · exact h_off i j h_gt
  · intro h; exact absurd (Finset.mem_univ _) h
