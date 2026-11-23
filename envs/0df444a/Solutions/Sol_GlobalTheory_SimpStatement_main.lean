-- Prove2me | solution 1 for GlobalTheory.SimpStatement.main
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:33:08.160847+00:00
-- url     : https://prove2.me/submissions/536d8ba1-cafa-40c5-9265-942c5ebd5ccf

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ImportsExtra

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.SimpStatement
open Finset
namespace GlobalTheory.SimpStatement
theorem _root_.solution {K B W G ι : Type} [Field K] [CommRing B] [IsDomain B] [Algebra K B]
    [AddCommGroup W] [Module B W] [Module K W] [IsScalarTower K B W] [Module.IsTorsionFree B W]
    (a : G → B → B) (σ : G → W →+ W)
    (hσ : ∀ (g : G) (b : B) (w : W), (σ g : W → W) (b • w) = a g b • (σ g : W → W) w)
    (ha : ∀ (b b' : B), b ≠ (0 : B) → (∀ (g : G), b * a g b' = a g b * b') →
      ∃ (c : K), b' = (Algebra.algebraMap K B : K → B) c * b)
    (v : ι → W) (hv : ∀ (g : G) (i : ι), (σ g : W → W) (v i) = v i)
    (s : Finset ι) (hK : LinearIndepOn K v (↑s : Set ι)) :
    LinearIndepOn B v (↑s : Set ι) := by
  classical

  have key : ∀ T : Finset ι, T ⊆ s → ∀ f : ι → B, ∑ i ∈ T, f i • v i = 0 → ∀ i ∈ T, f i = 0 := by
    intro T
    induction T using Finset.strongInduction with
    | H T ih =>
      intro hTs f hf
      by_contra hne
      push_neg at hne
      obtain ⟨i₀, hi₀, hfi₀⟩ := hne

      have hrel : ∀ j ∈ T, ∀ g : G, f i₀ * a g (f j) = a g (f i₀) * f j := by
        intro j hj g
        set f' : ι → B := fun i => f i₀ * a g (f i) - a g (f i₀) * f i with hf'
        have hsum : ∑ i ∈ T, f' i • v i = 0 := by
          have h1 : ∑ i ∈ T, a g (f i) • v i = 0 := by
            have := congrArg (σ g : W → W) hf
            rw [map_sum, map_zero] at this
            rw [← this]
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [hσ, hv]
          simp only [hf', sub_smul, Finset.sum_sub_distrib, mul_smul, ← Finset.smul_sum, h1, hf,
            smul_zero, sub_zero]
        have hf'i₀ : f' i₀ = 0 := by simp only [hf']; ring
        have hsum' : ∑ i ∈ T.erase i₀, f' i • v i = 0 := by
          rw [← Finset.add_sum_erase T _ hi₀, hf'i₀, zero_smul, zero_add] at hsum
          exact hsum
        by_cases hj0 : j = i₀
        · subst hj0; ring
        · have := ih (T.erase i₀) (Finset.erase_ssubset hi₀)
            ((Finset.erase_subset _ _).trans hTs) f' hsum' j (Finset.mem_erase.2 ⟨hj0, hj⟩)
          simp only [hf'] at this
          exact sub_eq_zero.1 this
      have hc : ∀ j ∈ T, ∃ c : K, f j = (Algebra.algebraMap K B : K → B) c * f i₀ :=
        fun j hj => ha (f i₀) (f j) hfi₀ (hrel j hj)
      choose! c hc using hc
      have hsumK : ∑ i ∈ T, c i • v i = 0 := by
        have : f i₀ • ∑ i ∈ T, c i • v i = 0 := by
          rw [← hf, Finset.smul_sum]
          refine Finset.sum_congr rfl fun i hi => ?_
          rw [hc i hi, mul_comm, mul_smul, smul_comm]
          rw [algebraMap_smul]
          exact smul_comm (c i) (f i₀) (v i)
        exact (smul_eq_zero_iff_right hfi₀).1 this
      have hKT : LinearIndepOn K v (↑T : Set ι) := hK.mono (by exact_mod_cast hTs)
      have hci₀ := (linearIndepOn_finset_iff.1 hKT) c hsumK i₀ hi₀
      apply hfi₀
      rw [hc i₀ hi₀, hci₀, map_zero, zero_mul]
  exact linearIndepOn_finset_iff.2 (key s subset_rfl)
end GlobalTheory.SimpStatement
