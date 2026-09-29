-- Prove2me | solution 1 for MarkovChainCLT.partialTraj_map_shiftK_succ
-- status  : ACCEPTED   (prove)
-- author  : @LukeBernese
-- created : 2026-08-15T20:35:37.211997+00:00
-- url     : https://prove2.me/submissions/fbd74f33-df1b-4e6b-9964-d212b3f8c893

import Theorems.Thm_MarkovChainCLT_partialTraj_succ_self_apply_eq_map

set_option maxHeartbeats 1000000

open Filter Finset Function MeasurableEquiv MeasurableSpace MeasureTheory Preorder ProbabilityTheory
open scoped ENNReal NNReal Topology

/-- One-step time-homogeneity at an arbitrary offset `k`. -/
theorem solution {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P] (k m : ℕ) (v : Π _i : Finset.Iic (k + m), S) :
    (Kernel.partialTraj (X := fun _ : ℕ => S) (BanditAlgorithm.markovChainStep P)
        (k + m) (k + m + 1) v).map
        (fun u i => u ⟨k + i.1,
          Finset.mem_Iic.2 (Nat.add_le_add_left (Finset.mem_Iic.mp i.2) k)⟩)
      = Kernel.partialTraj (X := fun _ : ℕ => S) (BanditAlgorithm.markovChainStep P) m (m + 1)
          (fun i => v ⟨k + i.1,
            Finset.mem_Iic.2 (Nat.add_le_add_left (Finset.mem_Iic.mp i.2) k)⟩) := by
  set shk : (Π _i : Finset.Iic (k + m), S) → (Π _i : Finset.Iic m, S) :=
    fun u i => u ⟨k + i.1, Finset.mem_Iic.2 (Nat.add_le_add_left (Finset.mem_Iic.mp i.2) k)⟩
    with hshk
  have hmshk : Measurable (fun u i => u ⟨k + i.1,
      Finset.mem_Iic.2 (Nat.add_le_add_left (Finset.mem_Iic.mp i.2) k)⟩ :
      (Π _j : Finset.Iic (k + m + 1), S) → (Π _i : Finset.Iic (m + 1), S)) :=
    measurable_pi_lambda _ (fun _ => measurable_pi_apply _)
  have hps : ∀ (j : ℕ) (w : S) (i : Finset.Ioc j (j + 1)),
      MeasurableEquiv.piSingleton (X := fun _ : ℕ => S) j w i = w := by
    intro j w i
    simp [MeasurableEquiv.piSingleton]
  have hglue : Measurable (fun w : S => IicProdIoc (X := fun _ : ℕ => S) (k + m) (k + m + 1)
      (v, MeasurableEquiv.piSingleton (X := fun _ : ℕ => S) (k + m) w)) :=
    (measurable_IicProdIoc (X := fun _ : ℕ => S)).comp (measurable_const.prodMk
      (MeasurableEquiv.piSingleton (X := fun _ : ℕ => S) (k + m)).measurable)
  rw [MarkovChainCLT.partialTraj_succ_self_apply_eq_map P (k + m) v,
    MarkovChainCLT.partialTraj_succ_self_apply_eq_map P m (shk v),
    Measure.map_map hmshk hglue]
  have hlast : (shk v) ⟨m, Finset.mem_Iic.2 le_rfl⟩
      = v ⟨k + m, Finset.mem_Iic.2 le_rfl⟩ := rfl
  rw [hlast]
  congr 1
  funext w
  funext i
  show (IicProdIoc (X := fun _ : ℕ => S) (k + m) (k + m + 1)
      (v, MeasurableEquiv.piSingleton (X := fun _ : ℕ => S) (k + m) w))
      ⟨k + i.1, Finset.mem_Iic.2 (Nat.add_le_add_left (Finset.mem_Iic.mp i.2) k)⟩
    = IicProdIoc (X := fun _ : ℕ => S) m (m + 1)
      (shk v, MeasurableEquiv.piSingleton (X := fun _ : ℕ => S) m w) i
  by_cases h : i.1 ≤ m
  · simp only [_root_.IicProdIoc]
    rw [dif_pos (Nat.add_le_add_left h k), dif_pos h]
  · simp only [_root_.IicProdIoc]
    rw [dif_neg (fun hc => h (Nat.le_of_add_le_add_left hc)), dif_neg h, hps, hps]
