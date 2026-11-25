-- Prove2me | solution 1 for GlobalTheory.ExpSeries.convex_and_differentiableOn_tsum_cexp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:41:53.386465+00:00
-- url     : https://prove2.me/submissions/b7243a23-11c1-4c44-a1a4-afae502fc08f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ConvexAndDifferentiableOnTsumCexp
import Theorems.Thm_GlobalTheory_ExpSeries_convexOn_norm_mul_cexp
import Theorems.Thm_GlobalTheory_SCV_differentiableOn_tsum_of_normal_on_compacts


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex
open GlobalTheory GlobalTheory.ExpSeries
namespace GlobalTheory.ExpSeries
theorem _root_.solution :
    ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V] (J : Type)
      (c : J → ℂ) (L : J → V →ₗ[ℂ] ℂ),
      Convex ℝ {z : V | Summable fun j => c j * cexp (L j z)} ∧
      DifferentiableOn ℂ (fun z : V => ∑' j, c j * cexp (L j z))
        (interior {z : V | Summable fun j => c j * cexp (L j z)}) := by
  intro V _ _ _ J c L
  refine ⟨?_, ?_⟩
  · intro x hx y hy a b ha hb hab
    simp only [Set.mem_ofPred_eq] at hx hy ⊢
    rw [← summable_norm_iff] at hx hy ⊢
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun j => ?_)
      ((hx.mul_left a).add (hy.mul_left b))
    exact (convexOn_norm_mul_cexp (c j) (L j)).2 (Set.mem_univ x) (Set.mem_univ y) ha hb hab
  · intro z0 hz0
    have : FiniteDimensional ℝ V := Module.Finite.trans ℂ V
    obtain ⟨b, hb0, hb⟩ := exists_mem_interior_convexHull_affineBasis
      (mem_interior_iff_mem_nhds.1 hz0)
    have hsum : Summable fun j => ∑ i, ‖c j * cexp (L j (b i))‖ := by
      refine summable_sum fun i _ => ?_
      have : b i ∈ {z : V | Summable fun j => c j * cexp (L j z)} :=
        hb (subset_convexHull ℝ _ ⟨i, rfl⟩)
      exact summable_norm_iff.2 this
    have hd := (GlobalTheory.SCV.differentiableOn_tsum_of_normal_on_compacts
      (F := fun j z => c j * cexp (L j z)) (U := interior (convexHull ℝ (Set.range b)))
      isOpen_interior
      (fun j => ((((L j).toContinuousLinearMap.differentiable).cexp).const_mul
        (c j)).differentiableOn)
      (fun K hK _ => ⟨_, hsum, fun j z hz => by
        obtain ⟨y, ⟨i, rfl⟩, hy⟩ := (convexOn_norm_mul_cexp (c j) (L j)).exists_ge_of_mem_convexHull
          (Set.subset_univ _) (interior_subset (hK hz))
        exact hy.trans (Finset.single_le_sum (f := fun i => ‖c j * cexp (L j (b i))‖)
          (fun _ _ => norm_nonneg _) (Finset.mem_univ i))⟩)).1
    exact (hd.differentiableAt (isOpen_interior.mem_nhds hb0)).differentiableWithinAt
end GlobalTheory.ExpSeries
