-- Prove2me | solution 1 for GroundTheory.Automorphic.MeasurablePartition.norm_toLp_sub_avgProj_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T01:54:20.531774+00:00
-- url     : https://prove2.me/submissions/233fc43b-28db-4980-86be-1f981b3a6684

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_TraceStrongLimit
import Definitions.Def_GroundTheory_AutomorphicForms_FinePartition
import Definitions.Def_GroundTheory_AutomorphicForms_HilbertSchmidtKernel
import Definitions.Def_GroundTheory_AutomorphicForms_KernelTrace
import Theorems.Thm_GroundTheory_Automorphic_Lp_coeFn_finsetSum
import Theorems.Thm_GroundTheory_Automorphic_MeasurablePartition_measureReal_pos
import Theorems.Thm_GroundTheory_Automorphic_MeasurablePartition_orthonormal_avgVec
import Theorems.Thm_GroundTheory_Automorphic_MeasurablePartition_coeFn_avgVec
import Theorems.Thm_GroundTheory_Automorphic_MeasurablePartition_index_eq_iff
import Theorems.Thm_GroundTheory_Automorphic_MeasurablePartition_index_lt
import Theorems.Thm_GroundTheory_Automorphic_MeasurablePartition_mem_index
import Theorems.Thm_GroundTheory_Automorphic_norm_sub_finProj_le


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open MeasureTheory Filter Topology Uniformity Set
open scoped InnerProductSpace ENNReal ComplexConjugate NNReal
noncomputable section
variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X] [MeasurableSpace X]
  [BorelSpace X] (μ : Measure X) [IsFiniteMeasure μ]
open GroundTheory.Automorphic.MeasurablePartition
variable (p : MeasurablePartition X)
omit [T2Space X]
namespace GroundTheory.Automorphic.MeasurablePartition
theorem _root_.solution {V : SetRel X X} (hp : p.IsFine V) (f : C(X, ℂ)) {ε : ℝ}
    (hε : 0 ≤ ε) (hf : ∀ x y, (x, y) ∈ V → ‖f x - f y‖ ≤ ε) :
    ‖ContinuousMap.toLp (E := ℂ) 2 μ ℂ f - p.avgProj μ (ContinuousMap.toLp (E := ℂ) 2 μ ℂ f)‖ ≤
      (measureUnivNNReal μ : ℝ) ^ (2 : ℝ≥0∞).toReal⁻¹ * ε := by
  classical
  set F := ContinuousMap.toLp (E := ℂ) 2 μ ℂ f
  have hne : ∀ i : p.nonnull μ, (p.E i).Nonempty := fun i =>
    nonempty_of_measure_ne_zero (Finset.mem_filter.1 i.2).2
  let pt : p.nonnull μ → X := fun i => (hne i).some
  let c : p.nonnull μ → ℂ := fun i => f (pt i) * ((Real.sqrt (μ.real (p.E i)) : ℝ) : ℂ)
  let g : Lp ℂ 2 μ := ∑ i, c i • p.avgVec μ i
  have hg : g ∈ Submodule.span ℂ (Set.range (p.avgVec μ)) :=
    Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  refine (norm_sub_finProj_le (p.orthonormal_avgVec μ) F hg).trans ?_
  refine Lp.norm_le_of_ae_bound hε ?_
  have hnull : ∀ᵐ x ∂μ, ∀ i, μ (p.E i) = 0 → x ∉ p.E i := by
    rw [ae_all_iff]
    intro i
    by_cases h : μ (p.E i) = 0
    · filter_upwards [measure_eq_zero_iff_ae_notMem.1 h] with x hx _ using hx
    · exact ae_of_all _ fun x h' => absurd h' h
  have hvec : ∀ᵐ x ∂μ, ∀ i : p.nonnull μ, (c i • p.avgVec μ i) x =
      c i * ((((Real.sqrt (μ.real (p.E i)))⁻¹ : ℝ) : ℂ) * (p.E i).indicator (fun _ => (1 : ℂ)) x) := by
    rw [ae_all_iff]
    intro i
    filter_upwards [Lp.coeFn_smul (c i) (p.avgVec μ i), coeFn_avgVec μ p i] with x h1 h2
    rw [h1, Pi.smul_apply, h2, smul_eq_mul]
  filter_upwards [Lp.coeFn_sub F g, ContinuousMap.coeFn_toLp (E := ℂ) (p := 2) (𝕜 := ℂ) μ f,
    Lp.coeFn_finsetSum Finset.univ (fun i => c i • p.avgVec μ i), hvec, hnull] with x h1 h2 h3 h4 h5
  rw [h1, Pi.sub_apply, h2, h3]
  simp_rw [h4]
  set j := p.index x
  have hxj : x ∈ p.E j := p.mem_index x
  have hjn : j ∈ p.nonnull μ :=
    Finset.mem_filter.2 ⟨Finset.mem_range.2 (p.index_lt x), fun h => h5 j h hxj⟩
  let j' : p.nonnull μ := ⟨j, hjn⟩
  rw [Finset.sum_eq_single j']
  · have hm : 0 < μ.real (p.E j) := measureReal_pos j'
    have hs : Real.sqrt (μ.real (p.E j)) ≠ 0 := (Real.sqrt_pos.2 hm).ne'
    have hval : c j' * ((((Real.sqrt (μ.real (p.E j)))⁻¹ : ℝ) : ℂ) *
        (p.E j).indicator (fun _ => (1 : ℂ)) x) = f (pt j') := by
      rw [Set.indicator_of_mem hxj, mul_one]
      simp only [c, j']
      rw [mul_assoc, ← Complex.ofReal_mul, mul_inv_cancel₀ hs, Complex.ofReal_one, mul_one]
    rw [hval]
    exact hf x (pt j') (hp j x hxj (pt j') (hne j').some_mem)
  · intro i _ hij
    have hx : x ∉ p.E i := fun hx => hij (Subtype.ext ((p.index_eq_iff).2 hx).symm)
    rw [Set.indicator_of_notMem hx, mul_zero, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ j') h
end GroundTheory.Automorphic.MeasurablePartition
