-- Prove2me | solution 1 for MarketInterference.FluidBias.Supplement.proposition_3
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:09:26.399317+00:00
-- url     : https://prove2.me/submissions/2040b3b4-f024-4c31-aae4-b3b5d0f42bad

import Mathlib
import Definitions.Def_MarketInterference_FluidBias_Supplement_TwoLP

open MarketInterference
open MarketInterference.FluidBias
open MarketInterference.FluidBias.Supplement

theorem solution {nd ns : ℕ} {I E : Type} [Fintype I] [Fintype E] [DecidableEq I]
    (N : Network nd ns I E) (ρ τ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ < 1) (hτ : 0 < τ)
    (z : Counts nd ns) :
    twoLP N ρ τ z = (1 / τ) *
      (Phi N τ (fun i => (1 / ρ) * (z.1.2 i : ℝ)) (fun j => (z.2 j : ℝ)) -
       Phi N τ (fun i => (1 / (1 - ρ)) * (z.1.1 i : ℝ)) (fun j => (z.2 j : ℝ))) := by
         have hτ0 : τ ≠ 0 := hτ.ne'
         have hinv : (0 : ℝ) < 1 / τ := by positivity
         have key : ∀ (d d' : Fin nd → ℝ) (s s' : Fin ns → ℝ),
             (∀ i, d i = τ * d' i) → (∀ j, s j = τ * s' j) →
             Phi N 1 d' s' = (1 / τ) * Phi N τ d s := by
           intro d d' s s' hd hs
           open scoped Pointwise in
           have hset : obj N '' {x | Feasible N 1 d' s' x}
               = (1 / τ) • (obj N '' {x | Feasible N τ d s x}) := by
             ext r
             constructor
             · rintro ⟨x, ⟨h1, h2, h3, h4⟩, rfl⟩
               refine Set.mem_smul_set.2 ⟨obj N (fun e => τ * x e),
                 ⟨fun e => τ * x e, ⟨?_, ?_, ?_, ?_⟩, rfl⟩, ?_⟩
               · intro e
                 obtain ⟨ha, hb⟩ := h1 e
                 exact ⟨mul_nonneg hτ.le ha, mul_le_mul_of_nonneg_left (by linarith) hτ.le⟩
               · intro i
                 rw [← Finset.mul_sum, hd]
                 exact mul_le_mul_of_nonneg_left (h2 i) hτ.le
               · intro j
                 rw [← Finset.mul_sum, hs]
                 exact mul_le_mul_of_nonneg_left (h3 j) hτ.le
               · intro u
                 rw [← Finset.mul_sum, ← Finset.mul_sum, h4 u]
               · simp only [obj, smul_eq_mul, Finset.mul_sum]
                 refine Finset.sum_congr rfl fun e _ => ?_
                 field_simp
             · intro hr
               obtain ⟨_, ⟨x, ⟨h1, h2, h3, h4⟩, rfl⟩, rfl⟩ := Set.mem_smul_set.1 hr
               refine ⟨fun e => (1 / τ) * x e, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
               · intro e
                 obtain ⟨ha, hb⟩ := h1 e
                 refine ⟨mul_nonneg hinv.le ha, ?_⟩
                 calc (1 / τ) * x e ≤ (1 / τ) * (τ * N.k e) := mul_le_mul_of_nonneg_left hb hinv.le
                   _ = 1 * N.k e := by field_simp
               · intro i
                 rw [← Finset.mul_sum]
                 calc _ ≤ (1 / τ) * (τ * d' i) :=
                       mul_le_mul_of_nonneg_left ((h2 i).trans (hd i).le) hinv.le
                   _ = d' i := by field_simp
               · intro j
                 rw [← Finset.mul_sum]
                 calc _ ≤ (1 / τ) * (τ * s' j) :=
                       mul_le_mul_of_nonneg_left ((h3 j).trans (hs j).le) hinv.le
                   _ = s' j := by field_simp
               · intro u
                 rw [← Finset.mul_sum, ← Finset.mul_sum, h4 u]
               · simp only [obj, smul_eq_mul, Finset.mul_sum]
                 refine Finset.sum_congr rfl fun e _ => ?_
                 ring
           unfold Phi
           rw [hset, Real.sSup_smul_of_nonneg hinv.le, smul_eq_mul]
         have hρ1' : (1 - ρ) ≠ 0 := (sub_pos.2 hρ1).ne'
         have hρ0 : ρ ≠ 0 := hρ.ne'
         unfold twoLP
         rw [mul_sub]
         congr 1
         · apply key
           · intro i
             simp only [effectMLE, treatmentMLE, controlMLE, Pi.add_apply, Pi.sub_apply, add_sub_cancel]
             field_simp
           · intro j
             simp only [supplyMLE]
             field_simp
         · apply key
           · intro i
             simp only [controlMLE]
             field_simp
           · intro j
             simp only [supplyMLE]
             field_simp
