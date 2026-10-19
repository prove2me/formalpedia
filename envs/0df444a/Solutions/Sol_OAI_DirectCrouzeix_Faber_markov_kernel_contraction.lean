-- Prove2me | solution 1 for OAI.DirectCrouzeix.Faber.markov_kernel_contraction
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T07:25:53.49229+00:00
-- url     : https://prove2.me/submissions/21e8907e-5ad2-4ed2-b8c9-0696fa45bd99

-- Generated from openai/math@1581d4c lean/OAI/Analysis/DirectCrouzeix/KernelContraction.lean:L65-L95
-- (upload_full_project.md Phase 4): solution for node OAI.DirectCrouzeix.Faber.markov_kernel_contraction. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_DirectCrouzeix
import Definitions.Def_OAI_Analysis_DirectCrouzeix_PositiveBlocks
import Definitions.Def_OAI_Analysis_DirectCrouzeix_Resolvent
import Definitions.Def_OAI_Analysis_DirectCrouzeix_PolynomialCalculus
import Definitions.Def_OAI_Analysis_DirectCrouzeix_HilbertSchmidt
import Definitions.Def_OAI_Analysis_DirectCrouzeix_SingularPairs
import Definitions.Def_OAI_Analysis_DirectCrouzeix_Sharpness
import Definitions.Def_OAI_Analysis_DirectCrouzeix_CircleFourier
import Definitions.Def_OAI_Analysis_DirectCrouzeix_BoundaryEnergy
import Definitions.Def_OAI_Analysis_DirectCrouzeix_PolynomialEnergy
import Definitions.Def_OAI_Analysis_DirectCrouzeix_CompactIntegrals
import Definitions.Def_OAI_Analysis_DirectCrouzeix_DividedDifferences
import Definitions.Def_OAI_Analysis_DirectCrouzeix_TaylorFourier
import Definitions.Def_OAI_Analysis_DirectCrouzeix_FaberPolynomials
import Definitions.Def_OAI_Analysis_DirectCrouzeix_BoundaryKernel
import Definitions.Def_OAI_Analysis_DirectCrouzeix_KernelContraction

-- ---- from OAI.Analysis.DirectCrouzeix.KernelContraction ----
namespace OAI

universe u_117 u_118 u_119 u_120 u_121 u_122 u_123 u_124 u_125 u_126 u_127 u_128

noncomputable section

open scoped Matrix Matrix.Norms.L2Operator Kronecker

noncomputable section

open MeasureTheory Set Filter Metric

open scoped Topology Interval ENNReal NNReal ComplexConjugate

namespace DirectCrouzeix.Faber

theorem weighted_integral_norm_sq_le {α : Type u_117} {E : Type u_118} [MeasurableSpace α]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (μ : Measure α) (k : α → ℝ) (u : α → E)
    (hk : ∀ x, 0 ≤ k x) (hki : Integrable k μ)
    (hui : Integrable (fun x => k x • u x) μ)
    (hsqi : Integrable (fun x => k x * ‖u x‖ ^ 2) μ)
    (hmass : ∫ x, k x ∂μ = 1) :
    ‖∫ x, k x • u x ∂μ‖ ^ 2 ≤ ∫ x, k x * ‖u x‖ ^ 2 ∂μ := by
  let v := ∫ x, k x • u x ∂μ
  have hii : Integrable (fun x => inner ℝ v (k x • u x)) μ :=
    (innerSL ℝ v).integrable_comp hui
  have hi : (∫ x, inner ℝ v (k x • u x) ∂μ) = ‖v‖ ^ 2 := by
    change (∫ x, (innerSL ℝ v) (k x • u x) ∂μ) = _
    rw [(innerSL ℝ v).integral_comp_comm hui]
    exact real_inner_self_eq_norm_sq v
  have hn : 0 ≤ ∫ x, k x * ‖u x - v‖ ^ 2 ∂μ :=
    integral_nonneg (fun x => mul_nonneg (hk x) (sq_nonneg _))
  have hexp : (fun x => k x * ‖u x - v‖ ^ 2) =
      fun x => (k x * ‖u x‖ ^ 2 - 2 * inner ℝ v (k x • u x)) + k x * ‖v‖ ^ 2 := by
    funext x
    rw [norm_sub_sq_real, inner_smul_right, real_inner_comm v (u x)]
    ring
  rw [hexp] at hn
  have hsubi : Integrable (fun x => k x * ‖u x‖ ^ 2 - 2 * inner ℝ v (k x • u x)) μ :=
    hsqi.sub (hii.const_mul 2)
  have hconsti : Integrable (fun x => k x * ‖v‖ ^ 2) μ := hki.mul_const _
  rw [integral_add hsubi hconsti, integral_sub hsqi (hii.const_mul 2),
    integral_const_mul, integral_mul_const, hi, hmass] at hn
  change ‖v‖ ^ 2 ≤ _
  linarith

theorem continuous_integrable_compact {α : Type u_119} {E : Type u_120} [TopologicalSpace α]
    [MeasurableSpace α] [OpensMeasurableSpace α] [CompactSpace α]
    [NormedAddCommGroup E] (μ : Measure α) [IsFiniteMeasure μ]
    {f : α → E} (hf : Continuous f) : Integrable f μ :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)

theorem continuous_integral_compact {α : Type u_121} {β : Type u_122} {E : Type u_123}
    [TopologicalSpace α] [FirstCountableTopology α] [LocallyCompactSpace α]
    [TopologicalSpace β] [MeasurableSpace β] [OpensMeasurableSpace β]
    [CompactSpace β] [SecondCountableTopology β]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (μ : Measure β) [IsFiniteMeasure μ] {f : α → β → E}
    (hf : Continuous f.uncurry) : Continuous (fun x => ∫ y, f x y ∂μ) := by
  simpa using continuous_parametric_integral_of_continuous (μ := μ) hf isCompact_univ

theorem markov_kernel_contraction {α : Type u_124} {β : Type u_125} {E : Type u_126}
    [MetricSpace α] [MeasurableSpace α] [BorelSpace α] [CompactSpace α]
    [SecondCountableTopology α]
    [MetricSpace β] [MeasurableSpace β] [BorelSpace β] [CompactSpace β]
    [SecondCountableTopology β]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (μ : Measure α) (ν : Measure β) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (K : α → β → ℝ) (u : α → E)
    (hK : Continuous K.uncurry) (hu : Continuous u)
    (hpos : ∀ x y, 0 ≤ K x y)
    (hcol : ∀ y, ∫ x, K x y ∂μ = 1)
    (hrow : ∀ x, ∫ y, K x y ∂ν = 1) :
    (∫ y, ‖∫ x, K x y • u x ∂μ‖ ^ 2 ∂ν) ≤ ∫ x, ‖u x‖ ^ 2 ∂μ := by
  have hKcol (y : β) : Continuous (fun x => K x y) :=
    hK.comp (continuous_id.prodMk continuous_const)
  have hT : Continuous (fun y => ∫ x, K x y • u x ∂μ) := by
    apply continuous_integral_compact
    exact (hK.comp continuous_swap).smul (hu.comp continuous_snd)
  have hs : Integrable (fun p : α × β => K p.1 p.2 * ‖u p.1‖ ^ 2) (μ.prod ν) :=
    continuous_integrable_compact _ (hK.mul ((hu.comp continuous_fst).norm.pow 2))
  calc
    _ ≤ ∫ y, ∫ x, K x y * ‖u x‖ ^ 2 ∂μ ∂ν := by
      apply integral_mono (continuous_integrable_compact _ (hT.norm.pow 2))
        hs.integral_prod_right
      intro y
      exact weighted_integral_norm_sq_le μ (fun x => K x y) u (fun x => hpos x y)
        (continuous_integrable_compact _ (hKcol y))
        (continuous_integrable_compact _ ((hKcol y).smul hu))
        (continuous_integrable_compact _ ((hKcol y).mul (hu.norm.pow 2))) (hcol y)
    _ = ∫ x, ∫ y, K x y * ‖u x‖ ^ 2 ∂ν ∂μ := (integral_integral_swap hs).symm
    _ = _ := by simp_rw [integral_mul_const, hrow, one_mul]

section Hilbert

variable {E : Type u_127} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

end Hilbert

section FaberHilbert

variable {E : Type u_128} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

end FaberHilbert

end DirectCrouzeix.Faber

end

end

end OAI

-- ---- platform node ----
open OAI OAI.DirectCrouzeix OAI.DirectCrouzeix.Faber
open scoped Matrix Matrix.Norms.L2Operator Kronecker
open MeasureTheory Set Filter Metric
open scoped Topology Interval ENNReal NNReal ComplexConjugate


theorem solution : type_of% @_root_.OAI.DirectCrouzeix.Faber.markov_kernel_contraction := @_root_.OAI.DirectCrouzeix.Faber.markov_kernel_contraction
