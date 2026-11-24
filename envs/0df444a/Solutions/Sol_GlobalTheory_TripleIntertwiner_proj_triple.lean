-- Prove2me | solution 1 for GlobalTheory.TripleIntertwiner.proj_triple
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:57:57.990808+00:00
-- url     : https://prove2.me/submissions/ab3ee70a-3b83-4571-952f-eae78292033e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_GaussPowFourHom
import Theorems.Thm_GlobalTheory_TripleIntertwiner_rep_mem
import Theorems.Thm_GlobalTheory_TripleIntertwiner_proj_translate

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.TripleIntertwiner
open Classical
variable {V : Type*} [AddCommGroup V] {F : Type} [AddCommGroup F] [Module ℂ F]
variable {W : V → F →ₗ[ℂ] F} {c : V → V → ℂ}
namespace GlobalTheory.TripleIntertwiner
theorem _root_.solution (H : (∀ x y f, W x (W y f) = c x y • W (x + y) f) ∧
      (∀ x x' y, c (x + x') y = c x y * c x' y) ∧ (∀ x y y', c x (y + y') = c x y * c x y') ∧
      ∀ x y, c x y ≠ 0)
    {A₀ A B C : AddSubgroup V} (hB : A₀ ≤ B) (hC : A₀ ≤ C)
    [Fintype (A ⧸ A₀.addSubgroupOf A)] [Fintype (B ⧸ A₀.addSubgroupOf B)]
    [Fintype (C ⧸ A₀.addSubgroupOf C)]
    (cA : ∀ x ∈ A, ∀ y ∈ A, c x y = 1) (cB : ∀ x ∈ B, ∀ y ∈ B, c x y = 1)
    (cC : ∀ x ∈ C, ∀ y ∈ C, c x y = 1)
    (hsd : ∀ v, (∀ x ∈ A, c x v = c v x) → v ∈ A)
    (f : F) (hf : ∀ x ∈ A, W x f = f) :
    ∑ x : A ⧸ A₀.addSubgroupOf A, W (rep x) (∑ z : C ⧸ A₀.addSubgroupOf C, W (rep z)
      (∑ y : B ⧸ A₀.addSubgroupOf B, W (rep y) f)) =
      ((A₀.relIndex A : ℂ) * ∑ z : C ⧸ A₀.addSubgroupOf C, ∑ y : B ⧸ A₀.addSubgroupOf B,
        if rep z + rep y ∈ A then c (rep z) (rep y) else 0) • f := by
  simp only [map_sum, H.1 (rep _ : V) (rep _ : V) f, map_smul]
  rw [Finset.sum_comm, Finset.mul_sum, Finset.sum_smul]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [Finset.sum_comm, Finset.mul_sum, Finset.sum_smul]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [← Finset.smul_sum, proj_translate H cA hsd f hf, smul_smul]
  · congr 1
    split_ifs <;> ring
  · intro l hl
    rw [H.2.1, H.2.2.1, cB _ (hB hl) _ (rep_mem y), cB _ (rep_mem y) _ (hB hl),
      cC _ (hC hl) _ (rep_mem z), cC _ (rep_mem z) _ (hC hl)]
    simp
end GlobalTheory.TripleIntertwiner
