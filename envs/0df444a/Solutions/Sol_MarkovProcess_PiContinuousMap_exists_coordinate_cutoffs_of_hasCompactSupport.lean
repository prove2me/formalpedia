-- Prove2me | solution 1 for MarkovProcess.PiContinuousMap.exists_coordinate_cutoffs_of_hasCompactSupport
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T18:25:59.039465+00:00
-- url     : https://prove2.me/submissions/a3b1e9da-fd71-46cd-a688-b698c9551f07

import Mathlib.Topology.ContinuousMap.StoneWeierstrass
import Mathlib.Topology.ContinuousMap.CompactlySupported
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.UrysohnsLemma
import Definitions.Def_MarkovProcess_CoordinateProductAlgebras
open Topology MarkovProcess.PiContinuousMap
open scoped CompactlySupported ZeroAtInfty
variable {I α : Type*} [Fintype I] [TopologicalSpace α]

theorem solution
    [T3Space α] [LocallyCompactSpace α] (f : C_c(I → α, ℝ)) :
    ∃ (φ : I → C₀(α, ℝ)) (B : Set (I → α)),
      IsCompact B ∧
      (∀ i x, 0 ≤ φ i x ∧ φ i x ≤ 1) ∧
      Set.EqOn (∏ i, coordinate i ((φ i : C₀(α, ℝ)) : C(α, ℝ))) 1 (tsupport f) ∧
      tsupport f ⊆ B ∧
      Set.EqOn (∏ i, coordinate i ((φ i : C₀(α, ℝ)) : C(α, ℝ))) 0 Bᶜ := by
  classical
  have hK : IsCompact (tsupport f) := f.hasCompactSupport
  have hKi : ∀ i, IsCompact ((fun x : I → α => x i) '' tsupport f) := fun i =>
    hK.image (continuous_apply i)
  choose g hg1 _ hgs hg01 using fun i =>
    exists_continuous_one_zero_of_isCompact (X := α) (hKi i) isClosed_empty
      (Set.disjoint_empty _)
  let φ : I → C₀(α, ℝ) := fun i => ⟨g i, HasCompactSupport.is_zero_at_infty (hgs i)⟩
  have hφ : ∀ i a, φ i a = g i a := fun _ _ => rfl
  have hprod : ∀ x : I → α,
      (∏ i, ⇑(coordinate i ((φ i : C₀(α, ℝ)) : C(α, ℝ)))) x = ∏ i, g i (x i) := by
    intro x
    rw [Finset.prod_apply]
    rfl
  refine ⟨φ, Set.univ.pi fun i => tsupport (g i), isCompact_univ_pi fun i => hgs i, fun i x => ?_,
    fun x hx => ?_, fun x hx i _ => ?_, fun x hx => ?_⟩
  · rw [hφ]; exact hg01 i x
  · rw [hprod]
    simp only [Pi.one_apply]
    exact Finset.prod_eq_one fun i _ => hg1 i ⟨x, hx, rfl⟩
  · exact subset_tsupport _ (Function.mem_support.2 (by
      rw [show g i (x i) = 1 from hg1 i ⟨x, hx, rfl⟩]; exact one_ne_zero))
  · rw [hprod]
    simp only [Set.mem_compl_iff, Set.mem_pi, Set.mem_univ, true_implies, not_forall] at hx
    obtain ⟨i, hi⟩ := hx
    exact Finset.prod_eq_zero (Finset.mem_univ i) (image_eq_zero_of_notMem_tsupport hi)
