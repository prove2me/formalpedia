-- Prove2me | solution 1 for OAI.DirectCrouzeix.Conformal.harmonic_le_boundary
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T07:52:11.30308+00:00
-- url     : https://prove2.me/submissions/6c3f62c0-cdba-46a4-b576-2a2a16e1e210

-- Generated from openai/math@1581d4c lean/OAI/Analysis/DirectCrouzeix/PoissonBoundary.lean:L166-L196
-- (upload_full_project.md Phase 4): solution for node OAI.DirectCrouzeix.Conformal.harmonic_le_boundary. The node keeps its source
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
import Definitions.Def_OAI_Analysis_DirectCrouzeix_PoissonBoundary

-- ---- from OAI.Analysis.DirectCrouzeix.PoissonBoundary ----
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

open InnerProductSpace Real

theorem harmonic_eventually_eq_of_isLocalMax {u : ℂ → ℝ} {a : ℂ}
    (hu : HarmonicAt u a) (hm : IsLocalMax u a) :
    u =ᶠ[𝓝 a] (fun _ => u a) := by
  obtain ⟨r, hr, hB⟩ := Metric.isOpen_iff.mp (isOpen_setOfPred_harmonicAt u) a hu
  obtain ⟨F, hF, hRe⟩ := (show HarmonicOnNhd u (ball a r) from hB).exists_analyticOnNhd_ball_re_eq
  have hd : ∀ᶠ z in 𝓝 a, DifferentiableAt ℂ (fun z => Complex.exp (F z)) z := by
    filter_upwards [ball_mem_nhds a hr] with z hz
    exact (hF z hz).differentiableAt.cexp
  have hmax : IsLocalMax (norm ∘ (fun z => Complex.exp (F z))) a := by
    filter_upwards [hm, ball_mem_nhds a hr] with z hz hzB
    simpa only [Function.comp_apply, Complex.norm_exp, hRe hzB,
      hRe (mem_ball_self hr), Real.exp_le_exp] using hz
  have he := Complex.norm_eventually_eq_of_isLocalMax hd hmax
  filter_upwards [he, ball_mem_nhds a hr] with z hz hzB
  simpa only [Complex.norm_exp, hRe hzB, hRe (mem_ball_self hr), Real.exp_eq_exp] using hz

theorem harmonic_le_boundary {U : Set ℂ} (hU : IsOpen U)
    (hb : Bornology.IsBounded U) {u : ℂ → ℝ}
    (hu : HarmonicContOnCl u U) {M : ℝ}
    (hM : ∀ z ∈ frontier U, u z ≤ M) :
    ∀ z ∈ closure U, u z ≤ M := by
  intro z hz
  by_contra hle
  obtain ⟨a, ha, hmax⟩ := hb.isCompact_closure.exists_isMaxOn ⟨z, hz⟩ hu.2
  have hhigh : M < u a := (lt_of_not_ge hle).trans_le (hmax hz)
  let S := {x ∈ closure U | u x = u a}
  have hSc : IsCompact S := by
    exact hb.isCompact_closure.of_isClosed_subset
      (hu.2.preimage_isClosed_of_isClosed isClosed_closure isClosed_singleton) (by intro x hx; exact hx.1)
  have hSo : IsOpen S := by
    rw [isOpen_iff_mem_nhds]
    intro x hx
    have hxU : x ∈ U := by
      by_contra hn
      have hf : x ∈ frontier U := by
        rw [frontier, hU.interior_eq]
        exact ⟨hx.1, hn⟩
      exact (not_le_of_gt hhigh) (hx.2 ▸ hM x hf)
    have hxmax : IsLocalMax u x := by
      filter_upwards [hU.mem_nhds hxU] with y hy
      exact hx.2 ▸ hmax (subset_closure hy)
    have he := harmonic_eventually_eq_of_isLocalMax (hu.1 x hxU) hxmax
    filter_upwards [he, hU.mem_nhds hxU] with y hy hyU
    exact ⟨subset_closure hyU, hy.trans hx.2⟩
  have hSne : S.Nonempty := ⟨a, ha, rfl⟩
  have hSun : S = univ := (show IsClopen S from ⟨hSc.isClosed, hSo⟩).eq_univ hSne
  exact hSc.ne_univ hSun

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
open InnerProductSpace Real


theorem solution : type_of% @_root_.OAI.DirectCrouzeix.Conformal.harmonic_le_boundary := @_root_.OAI.DirectCrouzeix.Conformal.harmonic_le_boundary
