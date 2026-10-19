-- Prove2me | solution 1 for OAI.TriangularHilbert.Heat.gridLift_kernelOutput_eq
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T05:06:18.434991+00:00
-- url     : https://prove2.me/submissions/c7688e0f-13c8-4aae-8deb-8a0ab5f3d177

-- Generated from openai/math@1581d4c lean/OAI/Analysis/TriangularHilbert/SampledOutput.lean:L37-L57
-- (upload_full_project.md Phase 4): solution for node OAI.TriangularHilbert.Heat.gridLift_kernelOutput_eq. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_TriangularHilbert
import Definitions.Def_OAI_Analysis_TriangularHilbert_Gaussian
import Definitions.Def_OAI_Analysis_TriangularHilbert_MeshMass
import Definitions.Def_OAI_Analysis_TriangularHilbert_GaussianMoments
import Definitions.Def_OAI_Analysis_TriangularHilbert_SignedWindowScalar
import Definitions.Def_OAI_Analysis_TriangularHilbert_MatrixSupport
import Definitions.Def_OAI_Analysis_TriangularHilbert_Support
import Definitions.Def_OAI_Analysis_TriangularHilbert_WeightedGram
import Definitions.Def_OAI_Analysis_TriangularHilbert_WeightedStar
import Definitions.Def_OAI_Analysis_TriangularHilbert_GroupedGaussian
import Definitions.Def_OAI_Analysis_TriangularHilbert_HeatStar
import Definitions.Def_OAI_Analysis_TriangularHilbert_HeatCost
import Definitions.Def_OAI_Analysis_TriangularHilbert_NormBounds
import Definitions.Def_OAI_Analysis_TriangularHilbert_HeatInsert
import Definitions.Def_OAI_Analysis_TriangularHilbert_GaussianDom
import Definitions.Def_OAI_Analysis_TriangularHilbert_PlaneChart
import Definitions.Def_OAI_Analysis_TriangularHilbert_PlaneDom
import Definitions.Def_OAI_Analysis_TriangularHilbert_HeatBound
import Definitions.Def_OAI_Analysis_TriangularHilbert_GramDeriv
import Definitions.Def_OAI_Analysis_TriangularHilbert_PlaneIntegral
import Definitions.Def_OAI_Analysis_TriangularHilbert_PlaneDissipation
import Definitions.Def_OAI_Analysis_TriangularHilbert_SignedTraceOrder
import Definitions.Def_OAI_Analysis_TriangularHilbert_MassPlane
import Definitions.Def_OAI_Analysis_TriangularHilbert_SignedConvolution
import Definitions.Def_OAI_Analysis_TriangularHilbert_RankJump
import Definitions.Def_OAI_Analysis_TriangularHilbert_ZeroStar
import Definitions.Def_OAI_Analysis_TriangularHilbert_StarJump
import Definitions.Def_OAI_Analysis_TriangularHilbert_InitialAlgebra
import Definitions.Def_OAI_Analysis_TriangularHilbert_InitialPlane
import Definitions.Def_OAI_Analysis_TriangularHilbert_TotalJump
import Definitions.Def_OAI_Analysis_TriangularHilbert_IntWeak
import Definitions.Def_OAI_Analysis_TriangularHilbert_StrongLayer
import Definitions.Def_OAI_Analysis_TriangularHilbert_IntMax
import Definitions.Def_OAI_Analysis_TriangularHilbert_FiniteLineMax
import Definitions.Def_OAI_Analysis_TriangularHilbert_MeshJump
import Definitions.Def_OAI_Analysis_TriangularHilbert_JumpScalar
import Definitions.Def_OAI_Analysis_TriangularHilbert_Switch
import Definitions.Def_OAI_Analysis_TriangularHilbert_MaskedDissipation
import Definitions.Def_OAI_Analysis_TriangularHilbert_SortedWindows
import Definitions.Def_OAI_Analysis_TriangularHilbert_MaskedActual
import Definitions.Def_OAI_Analysis_TriangularHilbert_SignedCenter
import Definitions.Def_OAI_Analysis_TriangularHilbert_SelectedScale
import Definitions.Def_OAI_Analysis_TriangularHilbert_DiscretePairing
import Definitions.Def_OAI_Analysis_TriangularHilbert_SmoothFormula
import Definitions.Def_OAI_Analysis_TriangularHilbert_ErrorEnvelope
import Definitions.Def_OAI_Analysis_TriangularHilbert_ErrorPairing
import Definitions.Def_OAI_Analysis_TriangularHilbert_HardPairing
import Definitions.Def_OAI_Analysis_TriangularHilbert_GridCell
import Definitions.Def_OAI_Analysis_TriangularHilbert_Quantization
import Definitions.Def_OAI_Analysis_TriangularHilbert_GridLine
import Definitions.Def_OAI_Analysis_TriangularHilbert_BoundedBox
import Definitions.Def_OAI_Analysis_TriangularHilbert_SampledOutput
import Theorems.Thm_OAI_TriangularHilbert_gridLift_eq

-- ---- from OAI.Analysis.TriangularHilbert.GridCell ----
namespace OAI

universe uE uF

section
namespace TriangularHilbert
open MeasureTheory
open scoped BigOperators
noncomputable section

lemma gridCell_mem_iff {h x : ℝ} (hh : 0 < h) (i : ℤ) :
    x ∈ gridCell h i ↔ gridIndex h x = i := by
  unfold gridCell gridIndex
  rw [Int.floor_eq_iff]
  simp only [Set.mem_Ico]
  constructor
  · intro hx
    exact ⟨(le_div_iff₀ hh).mpr (by simpa only [mul_comm] using hx.1),
      (div_lt_iff₀ hh).mpr (by simpa only [mul_comm] using hx.2)⟩
  · intro hx
    exact ⟨by simpa only [mul_comm] using (le_div_iff₀ hh).mp hx.1,
      by simpa only [mul_comm] using (div_lt_iff₀ hh).mp hx.2⟩

lemma volume_gridCell (h : ℝ) (i : ℤ) : volume (gridCell h i) = ENNReal.ofReal h := by
  rw [gridCell,Real.volume_Ico]
  congr 1
  ring

end
end TriangularHilbert
end

end OAI

-- ---- from OAI.Analysis.TriangularHilbert.Quantization ----
namespace OAI

universe uE

section
namespace TriangularHilbert
open MeasureTheory Filter
open scoped Topology
noncomputable section

lemma mem_sampleIndices {h : ℝ} (hh : 0 < h) (M : ℝ) (i : ℤ) :
    i ∈ sampleIndices h M ↔ |h*i| ≤ M := by
  rw [sampleIndices,Finset.mem_Icc,Int.ceil_le,Int.le_floor,abs_le]
  constructor
  · rintro ⟨hi,hj⟩
    exact ⟨by simpa only [mul_comm] using (div_le_iff₀ hh).mp hi,
      by simpa only [mul_comm] using (le_div_iff₀ hh).mp hj⟩
  · rintro ⟨hi,hj⟩
    exact ⟨(div_le_iff₀ hh).mpr (by simpa only [mul_comm] using hi),
      (le_div_iff₀ hh).mpr (by simpa only [mul_comm] using hj)⟩

end
end TriangularHilbert
end

end OAI

-- ---- from OAI.Analysis.TriangularHilbert.GridLine ----
namespace OAI

universe uE

section
namespace TriangularHilbert
open MeasureTheory
open scoped BigOperators
noncomputable section

lemma gridLine_eq {D : Finset ℤ} {h : ℝ} (hh : 0 < h) {E : Type uE} [AddCommMonoid E]
    (f : D → E) (x : ℝ) : gridLine D h f x =
      if hi : gridIndex h x ∈ D then f ⟨gridIndex h x,hi⟩ else 0 := by
  classical
  unfold gridLine
  simp_rw [Set.indicator_apply,gridCell_mem_iff hh]
  split_ifs with hi
  · rw [Finset.sum_eq_single (⟨gridIndex h x,hi⟩:D)]
    · simp
    · intro i _ hi'
      have hne : gridIndex h x ≠ (i:ℤ) := by intro he; exact hi' (Subtype.ext he.symm)
      simp only [hne,ite_false]
    · simp
  · apply Finset.sum_eq_zero
    intro i _
    have hne : gridIndex h x ≠ (i:ℤ) := by intro he; exact hi (he ▸ i.property)
    simp only [hne,ite_false]

lemma gridLine_sampled {E : Type uE} [AddCommMonoid E] (f : ℝ → E) {h M : ℝ}
    (hh : 0 < h) (hf : ∀ x, f x ≠ 0 → |x| ≤ M) (x : ℝ) :
    gridLine (sampleIndices h M) h (fun i => f (h*(i:ℤ))) x = f (gridPoint h x) := by
  rw [gridLine_eq hh]
  split_ifs with hi
  · rfl
  · symm
    by_contra hn
    exact hi ((mem_sampleIndices hh M _).mpr (hf _ hn))

lemma integral_gridLine (D : Finset ℤ) (h : ℝ) {E : Type uE} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (f : D → E) (hh : 0 ≤ h) :
    (∫ x : ℝ, gridLine D h f x) = ∑ i, h • f i := by
  have hi (i : D) : Integrable ((gridCell h i).indicator (fun _ : ℝ => f i)) :=
    IntegrableOn.integrable_indicator
      (integrableOn_const (μ := volume) (s := gridCell h i) (C := f i)
        (by rw [volume_gridCell]; finiteness)) measurableSet_Ico
  unfold gridLine
  rw [integral_finsetSum _ (fun i _ => hi i)]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_indicator (show MeasurableSet (gridCell h i) from measurableSet_Ico),setIntegral_const,measureReal_def,volume_gridCell,
    ENNReal.toReal_ofReal hh]

lemma integral_sampled_line {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (f : ℝ → E) {h M : ℝ} (hh : 0 < h) (hf : ∀ x, f x ≠ 0 → |x| ≤ M) :
    (∫ x : ℝ, f (gridPoint h x)) = ∑ i : sampleIndices h M, h • f (h*(i:ℤ)) := by
  have he : (fun x => f (gridPoint h x)) = gridLine (sampleIndices h M) h (fun i => f (h*(i:ℤ))) :=
    funext (fun x => (gridLine_sampled f hh hf x).symm)
  rw [he,integral_gridLine _ _ _ hh.le]
end
end TriangularHilbert
end

end OAI

-- ---- from OAI.Analysis.TriangularHilbert.SampledOutput ----
namespace OAI

section
namespace TriangularHilbert.Heat
open MatrixEnergy MeasureTheory
open scoped BigOperators
noncomputable section

lemma sampledKernelOutput_eq_sum (B C : ℝ×ℝ → ℂ) {h M : ℝ} (hh : 0 < h)
    (hB : BoxSupport B M) (K : ℝ → ℝ) (z : ℝ×ℝ) :
    sampledKernelOutput B C h K z = ∑ k : sampleIndices h M,
      (h:ℂ)*B (gridPoint h z.2,h*(k:ℤ))*C (h*(k:ℤ),gridPoint h z.1)*
        (K (gridPoint h z.1+gridPoint h z.2+h*(k:ℤ)):ℂ) := by
  have hs (c : ℝ) (hc : B (gridPoint h z.2,c)*C (c,gridPoint h z.1)*
      (K (gridPoint h z.1+gridPoint h z.2+c):ℂ) ≠ 0) : |c| ≤ M := by
    exact (hB (gridPoint h z.2,c) (fun he => hc (by simp only [he,zero_mul]))).2
  have he := integral_sampled_line (fun c => B (gridPoint h z.2,c)*C (c,gridPoint h z.1)*
      (K (gridPoint h z.1+gridPoint h z.2+c):ℂ)) hh hs
  rw [show sampledKernelOutput B C h K z = _ from he]
  apply Finset.sum_congr rfl
  intro k _
  simp only [Complex.real_smul]
  ring

lemma gridLift_kernelOutput_eq (B C : ℝ×ℝ → ℂ) {h M : ℝ} (hh : 0 < h)
    (hB : BoxSupport B M) (hC : BoxSupport C M) (K : ℝ → ℝ) (z : ℝ×ℝ) :
    gridLift (sampleIndices h M) h (kernelOutput (sampledMatrix B h M) (sampledMatrix C h M) h
      (fun m => h*(m:ℤ)) (fun _ _ => K)) z = sampledKernelOutput B C h K z := by
  rw [gridLift_eq hh,sampledKernelOutput_eq_sum B C hh hB K z]
  split_ifs with hi hj
  · rfl
  · symm
    apply Finset.sum_eq_zero
    intro k _
    have he : B (gridPoint h z.2,h*(k:ℤ)) = 0 := by
      by_contra he
      exact hj ((mem_sampleIndices hh M _).mpr (hB _ he).1)
    simp only [he,mul_zero,zero_mul]
  · symm
    apply Finset.sum_eq_zero
    intro k _
    have he : C (h*(k:ℤ),gridPoint h z.1) = 0 := by
      by_contra he
      exact hi ((mem_sampleIndices hh M _).mpr (hC _ he).2)
    simp only [he,mul_zero,zero_mul]

end
end TriangularHilbert.Heat
end

end OAI

-- ---- platform node ----
open OAI OAI.TriangularHilbert OAI.TriangularHilbert.Heat
open MatrixEnergy MeasureTheory
open scoped BigOperators


theorem solution : type_of% @_root_.OAI.TriangularHilbert.Heat.gridLift_kernelOutput_eq := @_root_.OAI.TriangularHilbert.Heat.gridLift_kernelOutput_eq
