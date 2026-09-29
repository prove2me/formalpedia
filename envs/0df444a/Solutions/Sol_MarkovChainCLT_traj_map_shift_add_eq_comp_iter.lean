-- Prove2me | solution 1 for MarkovChainCLT.traj_map_shift_add_eq_comp_iter
-- status  : ACCEPTED   (prove)
-- author  : @LukeBernese
-- created : 2026-08-15T21:04:24.425671+00:00
-- url     : https://prove2.me/submissions/a8284c59-2e99-4689-8e5a-41143152efed

import Theorems.Thm_MarkovChainCLT_traj_map_shift_eq_comap
import Theorems.Thm_MarkovChainCLT_markovChainKernel_map_shift_iter

open Filter Finset Function MeasurableEquiv MeasurableSpace MeasureTheory Preorder ProbabilityTheory
open scoped ENNReal NNReal Topology
open MarkovChainCLT

set_option maxHeartbeats 1000000

/-- Given the trajectory up to time `k`, the future from time `k + n` on is a chain
started from `Pⁿ(u_k, ·)`. -/
theorem solution {X : Type*} [MeasurableSpace X] (P : Kernel X X) [IsMarkovKernel P]
    (k n : ℕ) (u : Π _i : Finset.Iic k, X) :
    (Kernel.traj (X := fun _ : ℕ => X) (BanditAlgorithm.markovChainStep P) k u).map
        (fun ω : ℕ → X => fun l => ω (k + n + l))
      = (BanditAlgorithm.markovChainKernel P)
          ∘ₘ (iterKernel P n (u ⟨k, Finset.mem_Iic.2 le_rfl⟩)) := by
  have hk : Measurable (fun (ω : ℕ → X) => fun l => ω (k + l)) :=
    measurable_pi_lambda _ (fun _ => measurable_pi_apply _)
  have hn : Measurable (fun (ω : ℕ → X) => fun l => ω (n + l)) :=
    measurable_pi_lambda _ (fun _ => measurable_pi_apply _)
  -- split the shift by `k + n` into a shift by `k` followed by a shift by `n`
  have hsplit : (fun (ω : ℕ → X) => fun l => ω (k + n + l))
      = (fun (ω : ℕ → X) => fun l => ω (n + l)) ∘ (fun (ω : ℕ → X) => fun l => ω (k + l)) := by
    funext ω; funext l
    show ω (k + n + l) = ω (k + (n + l))
    rw [Nat.add_assoc]
  rw [hsplit, ← Measure.map_map hn hk]
  -- the inner shift restarts the chain at `u k`
  have hinner : (Kernel.traj (X := fun _ : ℕ => X) (BanditAlgorithm.markovChainStep P) k u).map
      (fun ω : ℕ → X => fun l => ω (k + l))
      = BanditAlgorithm.markovChainKernel P (u ⟨k, Finset.mem_Iic.2 le_rfl⟩) := by
    have hthis : ((Kernel.traj (X := fun _ : ℕ => X) (BanditAlgorithm.markovChainStep P) k).map
        (fun ω : ℕ → X => fun l => ω (k + l))) u
        = ((BanditAlgorithm.markovChainKernel P).comap
            (fun v : Π _i : Finset.Iic k, X => v ⟨k, Finset.mem_Iic.2 le_rfl⟩)
            (measurable_pi_apply _)) u := by
      rw [MarkovChainCLT.traj_map_shift_eq_comap P k]
    rw [Kernel.map_apply _ hk] at hthis
    rw [hthis, Kernel.comap_apply]
  rw [hinner]
  -- the outer shift is `n` steps of `P`
  have hconv : (fun (ω : ℕ → X) => fun l => ω (n + l))
      = (fun (ω : ℕ → X) => fun l => ω (l + n)) := by
    funext ω; funext l
    rw [Nat.add_comm]
  rw [hconv]
  have hmn : Measurable (fun (ω : ℕ → X) => fun l => ω (l + n)) :=
    measurable_pi_lambda _ (fun _ => measurable_pi_apply _)
  have houter : ((BanditAlgorithm.markovChainKernel P).map
      (fun ω : ℕ → X => fun l => ω (l + n))) (u ⟨k, Finset.mem_Iic.2 le_rfl⟩)
      = ((BanditAlgorithm.markovChainKernel P) ∘ₖ (iterKernel P n))
          (u ⟨k, Finset.mem_Iic.2 le_rfl⟩) := by
    rw [MarkovChainCLT.markovChainKernel_map_shift_iter P n]
  rw [Kernel.map_apply _ hmn] at houter
  rw [houter, Kernel.comp_apply]
