-- Prove2me | solution 1 for MarkovChainCLT.markovChainKernel_map_shift
-- status  : ACCEPTED   (prove)
-- author  : @LukeBernese
-- created : 2026-08-15T20:14:27.362646+00:00
-- url     : https://prove2.me/submissions/8db38923-1c94-4fef-a0f8-671b7a6507ad

import Theorems.Thm_MarkovChainCLT_partialTraj_succ_self_apply_eq_map
import Theorems.Thm_MarkovChainCLT_partialTraj_map_shift_succ
import Theorems.Thm_PathSpace_ext_of_map_frestrictLe

set_option maxHeartbeats 1000000

open Filter Finset Function MeasurableEquiv MeasurableSpace MeasureTheory Preorder ProbabilityTheory
open scoped ENNReal NNReal Topology

variable {S : Type*} [MeasurableSpace S]

/-- The shift on initial segments. -/
def sh (m : ℕ) (v : Π _j : Finset.Iic (m + 1), S) : Π _i : Finset.Iic m, S :=
  fun i => v ⟨i.1 + 1, Finset.mem_Iic.2 (Nat.succ_le_succ (Finset.mem_Iic.mp i.2))⟩

lemma measurable_sh (m : ℕ) : Measurable (sh (S := S) m) :=
  measurable_pi_lambda _ (fun _ => measurable_pi_apply _)

/-- Embed a point as a length-one initial segment. -/
def emb (x : S) : Π _i : Finset.Iic 0, S := fun _ => x

lemma measurable_emb : Measurable (emb (S := S)) :=
  measurable_pi_lambda _ (fun _ => measurable_id)

/-- `comap` commutes with composition on the right. -/
lemma comp_comap {α β γ δ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    [MeasurableSpace δ] (η : Kernel β γ) (κ : Kernel α β) {f : δ → α} (hf : Measurable f) :
    (η ∘ₖ κ).comap f hf = η ∘ₖ (κ.comap f hf) := by
  ext d s hs
  rw [Kernel.comap_apply, Kernel.comp_apply' _ _ _ hs, Kernel.comp_apply' _ _ _ hs]
  simp [Kernel.comap_apply]

/-- Kernel form of one-step time-homogeneity. -/
lemma homog_kernel (P : Kernel S S) [IsMarkovKernel P] (n : ℕ) :
    (Kernel.partialTraj (X := fun _ : ℕ => S) (BanditAlgorithm.markovChainStep P)
        (n + 1) (n + 1 + 1)).map (sh (n + 1))
      = (Kernel.partialTraj (X := fun _ : ℕ => S) (BanditAlgorithm.markovChainStep P)
          n (n + 1)).comap (sh n) (measurable_sh n) := by
  refine Kernel.ext (fun u => ?_)
  rw [Kernel.map_apply _ (measurable_sh (n + 1)), Kernel.comap_apply]
  exact MarkovChainCLT.partialTraj_map_shift_succ P n u

/-- The main induction. -/
theorem shift_step (P : Kernel S S) [IsMarkovKernel P] (n : ℕ) :
    ((Kernel.partialTraj (X := fun _ : ℕ => S) (BanditAlgorithm.markovChainStep P) 0
        (n + 1)).comap emb measurable_emb).map (sh n)
      = ((Kernel.partialTraj (X := fun _ : ℕ => S) (BanditAlgorithm.markovChainStep P) 0
          n).comap emb measurable_emb) ∘ₖ P := by
  induction n with
  | zero =>
    have hid : (Kernel.partialTraj (X := fun _ : ℕ => S)
          (BanditAlgorithm.markovChainStep P) 0 0).comap emb measurable_emb
        = Kernel.deterministic (emb (S := S)) measurable_emb := by
      rw [Kernel.partialTraj_self]
      refine Kernel.ext (fun x => ?_)
      rw [Kernel.comap_apply, Kernel.id_apply, Kernel.deterministic_apply]
    rw [hid, Kernel.deterministic_comp_eq_map]
    refine Kernel.ext (fun x => ?_)
    have hglue : Measurable (fun w : S => IicProdIoc (X := fun _ : ℕ => S) 0 (0 + 1)
        (emb x, MeasurableEquiv.piSingleton (X := fun _ : ℕ => S) 0 w)) :=
      (measurable_IicProdIoc (X := fun _ : ℕ => S)).comp (measurable_const.prodMk
        (MeasurableEquiv.piSingleton (X := fun _ : ℕ => S) 0).measurable)
    rw [Kernel.map_apply _ (measurable_sh 0), Kernel.comap_apply,
      MarkovChainCLT.partialTraj_succ_self_apply_eq_map P 0 (emb x),
      Measure.map_map (measurable_sh 0) hglue, Kernel.map_apply _ measurable_emb]
    congr 1
    funext w
    funext i
    show (IicProdIoc (X := fun _ : ℕ => S) 0 (0 + 1)
        (emb x, MeasurableEquiv.piSingleton (X := fun _ : ℕ => S) 0 w))
        ⟨i.1 + 1, Finset.mem_Iic.2 (Nat.succ_le_succ (Finset.mem_Iic.mp i.2))⟩ = emb w i
    simp only [_root_.IicProdIoc]
    rw [dif_neg (by omega : ¬ (i.1 + 1 ≤ 0))]
    simp [MeasurableEquiv.piSingleton, emb]
  | succ n ih =>
    have hsplit : Kernel.partialTraj (X := fun _ : ℕ => S)
          (BanditAlgorithm.markovChainStep P) 0 (n + 1 + 1)
        = Kernel.partialTraj (X := fun _ : ℕ => S) (BanditAlgorithm.markovChainStep P)
            (n + 1) (n + 1 + 1)
          ∘ₖ Kernel.partialTraj (X := fun _ : ℕ => S) (BanditAlgorithm.markovChainStep P) 0
            (n + 1) := Kernel.partialTraj_succ_eq_comp (Nat.zero_le _)
    rw [hsplit, comp_comap _ _ measurable_emb, Kernel.map_comp, homog_kernel,
      ← Kernel.comp_map _ _ (measurable_sh n), ih,
      ← Kernel.comp_assoc, ← comp_comap _ _ measurable_emb,
      ← Kernel.partialTraj_succ_eq_comp (Nat.zero_le n)]

/-- **Time-homogeneity as a shift identity.** -/
theorem solution {X : Type*} [MeasurableSpace X] (P : Kernel X X) [IsMarkovKernel P] :
    (BanditAlgorithm.markovChainKernel P).map (fun ω : ℕ → X => fun n => ω (n + 1))
      = (BanditAlgorithm.markovChainKernel P) ∘ₖ P := by
  have hσ : Measurable (fun (ω : ℕ → X) => fun n => ω (n + 1)) :=
    measurable_pi_lambda _ (fun _ => measurable_pi_apply _)
  -- the kernel identity holds after restricting to every initial segment
  have hker : ∀ n : ℕ,
      ((BanditAlgorithm.markovChainKernel P).map (fun ω : ℕ → X => fun n => ω (n + 1))).map
          (frestrictLe (π := fun _ : ℕ => X) n)
        = ((BanditAlgorithm.markovChainKernel P) ∘ₖ P).map
          (frestrictLe (π := fun _ : ℕ => X) n) := by
    intro n
    have hcomp : (frestrictLe (π := fun _ : ℕ => X) n) ∘ (fun ω : ℕ → X => fun k => ω (k + 1))
        = (sh n) ∘ (frestrictLe (π := fun _ : ℕ => X) (n + 1)) := by
      funext ω; funext i; rfl
    rw [← Kernel.map_comp_right _ hσ (measurable_frestrictLe n), hcomp,
      Kernel.map_comp_right _ (measurable_frestrictLe (n + 1)) (measurable_sh n),
      Kernel.map_comp]
    have hmck : BanditAlgorithm.markovChainKernel P
        = (Kernel.traj (X := fun _ : ℕ => X) (BanditAlgorithm.markovChainStep P) 0).comap
            emb measurable_emb := rfl
    rw [hmck, ← Kernel.comap_map_comm _ measurable_emb (measurable_frestrictLe (n + 1)),
      ← Kernel.comap_map_comm _ measurable_emb (measurable_frestrictLe n),
      Kernel.traj_map_frestrictLe, Kernel.traj_map_frestrictLe]
    exact shift_step P n
  haveI := Kernel.IsMarkovKernel.map (BanditAlgorithm.markovChainKernel P) hσ
  refine Kernel.ext (fun x => ?_)
  refine PathSpace.ext_of_map_frestrictLe (fun n => ?_)
  rw [← Kernel.map_apply _ (measurable_frestrictLe n),
    ← Kernel.map_apply _ (measurable_frestrictLe n), hker n]
