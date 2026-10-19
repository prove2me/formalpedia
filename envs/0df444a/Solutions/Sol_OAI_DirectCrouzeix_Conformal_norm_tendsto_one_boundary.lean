-- Prove2me | solution 1 for OAI.DirectCrouzeix.Conformal.norm_tendsto_one_boundary
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T07:49:06.383354+00:00
-- url     : https://prove2.me/submissions/2f11b93f-e33c-4a1e-bd6f-daff0707def4

-- Generated from openai/math@1581d4c lean/OAI/Analysis/DirectCrouzeix/DiskMapping.lean:L257-L275
-- (upload_full_project.md Phase 4): solution for node OAI.DirectCrouzeix.Conformal.norm_tendsto_one_boundary. The node keeps its source
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
import Definitions.Def_OAI_Analysis_DirectCrouzeix_FaberEnergy
import Definitions.Def_OAI_Analysis_DirectCrouzeix_FaberCalculus
import Definitions.Def_OAI_Analysis_DirectCrouzeix_NormalFamilies
import Definitions.Def_OAI_Analysis_DirectCrouzeix_ExtremalEmbedding
import Definitions.Def_OAI_Analysis_DirectCrouzeix_DiskMapping

-- ---- from OAI.Analysis.DirectCrouzeix.DiskMapping ----
namespace OAI

noncomputable section

open scoped Matrix Matrix.Norms.L2Operator Kronecker

noncomputable section

open MeasureTheory Set Filter Metric

open scoped Topology Interval ENNReal NNReal ComplexConjugate

noncomputable section

open Filter Metric Set

open scoped Topology ComplexConjugate

namespace DirectCrouzeix

namespace Conformal

open Function Complex

open scoped Pointwise

theorem inverse_hasStrictDerivAt {U : Set ℂ} (hU : IsOpen U)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f U) (hi : InjOn f U)
    {z : ℂ} (hz : z ∈ U) (hd : deriv f z ≠ 0) :
    HasStrictDerivAt (Function.invFunOn f U) (deriv f z)⁻¹ (f z) := by
  apply ((hf.analyticOnNhd hU) z hz).hasStrictDerivAt.to_local_left_inverse hd
  filter_upwards [hU.mem_nhds hz] with w hw
  exact hi.leftInvOn_invFunOn hw

theorem inverse_holomorphic {U : Set ℂ} (hU : IsOpen U)
    {a : ℂ} {f : ℂ → ℂ} (hf : NormalizedEmbedding U a f) :
    DifferentiableOn ℂ (Function.invFunOn f U) (f '' U) := by
  rintro y ⟨z, hz, rfl⟩
  exact (inverse_hasStrictDerivAt hU hf.holomorphic hf.injective hz (hf.derivative z hz)).hasDerivAt.differentiableAt.differentiableWithinAt

theorem compact_inverse_disk {U : Set ℂ} (hU : IsOpen U)
    {a : ℂ} {f : ℂ → ℂ} (hf : NormalizedEmbedding U a f)
    (hs : f '' U = ball 0 1) {r : ℝ} (hr : r < 1) :
    IsCompact (Function.invFunOn f U '' closedBall 0 r) ∧
      Function.invFunOn f U '' closedBall 0 r ⊆ U := by
  have hsub : closedBall (0 : ℂ) r ⊆ f '' U := by
    rw [hs]
    apply closedBall_subset_ball
    exact hr
  refine ⟨(isCompact_closedBall (0 : ℂ) r).image_of_continuousOn
    ((inverse_holomorphic hU hf).continuousOn.mono hsub), ?_⟩
  rintro z ⟨w, hw, rfl⟩
  exact Function.invFunOn_mem (hsub hw)

theorem norm_tendsto_one_boundary {U : Set ℂ} (hU : IsOpen U)
    {a : ℂ} {f : ℂ → ℂ} (hf : NormalizedEmbedding U a f)
    (hs : f '' U = ball 0 1) {p : ℂ} (hp : p ∉ U) :
    Tendsto (fun z => ‖f z‖) (𝓝[U] p) (𝓝 1) := by
  rw [tendsto_order]
  constructor
  · intro r hr
    have hc := compact_inverse_disk hU hf hs hr
    have hpn : p ∉ Function.invFunOn f U '' closedBall 0 r := fun h => hp (hc.2 h)
    have he : ∀ᶠ z in 𝓝 p, z ∉ Function.invFunOn f U '' closedBall 0 r :=
      hc.1.isClosed.isOpen_compl.mem_nhds hpn
    filter_upwards [he.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with z hz hzU
    by_contra hn
    apply hz
    refine ⟨f z, ?_, hf.injective.leftInvOn_invFunOn hzU⟩
    simpa using le_of_not_gt hn
  · intro r hr
    filter_upwards [self_mem_nhdsWithin] with z hz
    exact (mem_ball_zero_iff.mp (hf.disk hz)).trans hr

open InnerProductSpace Real

end Conformal

end DirectCrouzeix

end

end

end

end OAI

-- ---- platform node ----
open OAI OAI.DirectCrouzeix OAI.DirectCrouzeix.Conformal
open scoped Matrix Matrix.Norms.L2Operator Kronecker
open MeasureTheory Set Filter Metric
open scoped Topology Interval ENNReal NNReal ComplexConjugate
open Filter Metric Set
open scoped Topology ComplexConjugate
open Function Complex
open scoped Pointwise


theorem solution : type_of% @_root_.OAI.DirectCrouzeix.Conformal.norm_tendsto_one_boundary := @_root_.OAI.DirectCrouzeix.Conformal.norm_tendsto_one_boundary
