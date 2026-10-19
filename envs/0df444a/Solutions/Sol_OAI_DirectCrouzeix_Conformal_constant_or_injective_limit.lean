-- Prove2me | solution 1 for OAI.DirectCrouzeix.Conformal.constant_or_injective_limit
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T07:39:23.508401+00:00
-- url     : https://prove2.me/submissions/888618f9-3862-40d5-999a-0fb697e778ce

-- Generated from openai/math@1581d4c lean/OAI/Analysis/DirectCrouzeix/NormalFamilies.lean:L86-L118
-- (upload_full_project.md Phase 4): solution for node OAI.DirectCrouzeix.Conformal.constant_or_injective_limit. The node keeps its source
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
import Theorems.Thm_OAI_DirectCrouzeix_Conformal_zero_or_nonvanishing_limit

-- ---- from OAI.Analysis.DirectCrouzeix.NormalFamilies ----
namespace OAI

universe u_131

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

theorem constant_or_injective_limit {U : Set ℂ} (hU : IsOpen U)
    (hUc : IsPreconnected U) {F : ℕ → ℂ → ℂ} {g : ℂ → ℂ}
    (hF : ∀ n, DifferentiableOn ℂ (F n) U)
    (hFi : ∀ n, InjOn (F n) U)
    (hl : TendstoLocallyUniformlyOn F g atTop U) :
    (∃ c : ℂ, EqOn g (fun _ => c) U) ∨ InjOn g U := by
  have hg := (hl.differentiableOn (Eventually.of_forall hF) hU).analyticOnNhd hU
  by_cases hc : ∃ c : ℂ, EqOn g (fun _ => c) U
  · exact Or.inl hc
  right
  intro a ha b hb hab
  by_contra hne
  have hV : IsOpen (U \ {a}) := hU.sdiff isClosed_singleton
  have hbV : b ∈ U \ {a} := ⟨hb, by simpa [eq_comm] using hne⟩
  obtain ⟨r, hr, hBr⟩ := Metric.isOpen_iff.mp hV b hbV
  have hBU : ball b r ⊆ U := hBr.trans sdiff_subset
  have hzero : ∀ n z, z ∈ ball b r → F n z - F n a ≠ 0 := by
    intro n z hz he
    have hza := hBr hz
    have heq := hFi n hza.1 ha (sub_eq_zero.mp he)
    exact hza.2 (by simpa using heq)
  have hlc : TendstoLocallyUniformlyOn (fun n z => F n z - F n a)
      (fun z => g z - g a) atTop (ball b r) := by
    exact (hl.sub (hl.tendsto_at ha).tendstoUniformly_const.tendstoLocallyUniformly.tendstoLocallyUniformlyOn).mono hBU
  have hh := zero_or_nonvanishing_limit isOpen_ball (convex_ball b r).isPreconnected
    (fun n => ((hF n).sub_const (F n a)).mono hBU) hzero hlc
  have he : EqOn (fun z => g z - g a) 0 (ball b r) := hh.resolve_right (by
    intro hn
    exact hn b (mem_ball_self hr) (sub_eq_zero.mpr hab.symm))
  have heg : g =ᶠ[𝓝 b] (fun _ => g a) := by
    filter_upwards [ball_mem_nhds b hr] with z hz
    exact sub_eq_zero.mp (he hz)
  exact hc ⟨g a, hg.eqOn_of_preconnected_of_eventuallyEq analyticOnNhd_const hUc hb heg⟩

open Function Complex

open scoped Pointwise

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


theorem solution : type_of% @_root_.OAI.DirectCrouzeix.Conformal.constant_or_injective_limit := @_root_.OAI.DirectCrouzeix.Conformal.constant_or_injective_limit
