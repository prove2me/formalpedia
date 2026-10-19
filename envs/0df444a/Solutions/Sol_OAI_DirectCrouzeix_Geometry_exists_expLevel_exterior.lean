-- Prove2me | solution 1 for OAI.DirectCrouzeix.Geometry.exists_expLevel_exterior
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T08:31:43.16921+00:00
-- url     : https://prove2.me/submissions/23f61514-4f6d-447d-a20d-26247753b85b

-- Generated from openai/math@1581d4c lean/OAI/Analysis/DirectCrouzeix/ExteriorMapping.lean:L148-L197
-- (upload_full_project.md Phase 4): solution for node OAI.DirectCrouzeix.Geometry.exists_expLevel_exterior. The node keeps its source
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
import Definitions.Def_OAI_Analysis_DirectCrouzeix_HarmonicReflection
import Definitions.Def_OAI_Analysis_DirectCrouzeix_HolomorphicReflection
import Definitions.Def_OAI_Analysis_DirectCrouzeix_ConformalCollar
import Definitions.Def_OAI_Analysis_DirectCrouzeix_AnalyticCharts
import Definitions.Def_OAI_Analysis_DirectCrouzeix_ExponentialLevels
import Definitions.Def_OAI_Analysis_DirectCrouzeix_InverseExterior
import Theorems.Thm_OAI_DirectCrouzeix_Conformal_exists_extremalEmbedding
import Theorems.Thm_OAI_DirectCrouzeix_Conformal_improve_embedding
import Theorems.Thm_OAI_DirectCrouzeix_Conformal_inverse_riemann_collar
import Theorems.Thm_OAI_DirectCrouzeix_Geometry_analytic_complex_chart
import Theorems.Thm_OAI_DirectCrouzeix_Geometry_expLevel_boundary_parametrization
import Theorems.Thm_OAI_DirectCrouzeix_Geometry_expLevel_convex
import Theorems.Thm_OAI_DirectCrouzeix_Geometry_exterior_laurent_form
import Theorems.Thm_OAI_DirectCrouzeix_Geometry_inverseExterior_bounded
import Theorems.Thm_OAI_DirectCrouzeix_Geometry_inverseExterior_frontier_level
import Theorems.Thm_OAI_DirectCrouzeix_Geometry_inverseExterior_isOpen

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

theorem exists_riemannMap {U : Set ℂ} (hU : IsOpen U)
    (hUc : IsSimplyConnected U) (hproper : U ≠ univ) {a : ℂ} (ha : a ∈ U) :
    ∃ f, NormalizedEmbedding U a f ∧ f '' U = ball 0 1 := by
  obtain ⟨f, hf, hmax⟩ := exists_extremalEmbedding hU hUc hproper ha
  refine ⟨f, hf, Subset.antisymm (by simpa using hf.disk.image_subset) ?_⟩
  intro b hb
  by_contra hmiss
  obtain ⟨G, hG, hlt⟩ := improve_embedding hU hUc ha hf (mem_ball_zero_iff.mp hb) hmiss
  exact (not_lt_of_ge (hmax G hG)) hlt

open InnerProductSpace Real

end Conformal

end DirectCrouzeix

end

end

end

end OAI

-- ---- from OAI.Analysis.DirectCrouzeix.ConformalCollar ----
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

theorem exists_riemann_collar {U : Set ℂ} (hU : IsOpen U)
    (hUs : IsSimplyConnected U) (hproper : U ≠ univ)
    (hUc : IsCompact (closure U)) (hUB : HasAnalyticBoundary U)
    {a : ℂ} (ha : a ∈ U) :
    ∃ R > 1, ∃ g : ℂ → ℂ, AnalyticOnNhd ℂ g (ball 0 R) ∧ InjOn g (ball 0 R) ∧
      g '' ball 0 1 = U ∧ g '' closedBall 0 1 = closure U ∧ g 0 = a ∧
      (∀ z ∈ ball 0 R, deriv g z ≠ 0) := by
  obtain ⟨f,hf,hs⟩ := exists_riemannMap hU hUs hproper ha
  exact inverse_riemann_collar hU hUc hUB ha hf hs

end Conformal

end DirectCrouzeix

noncomputable section

open Set Filter Metric

open scoped Topology ComplexConjugate

namespace DirectCrouzeix.Geometry

end DirectCrouzeix.Geometry

end

end

end

end

end OAI

-- ---- from OAI.Analysis.DirectCrouzeix.ExponentialLevels ----
namespace OAI

universe u_135 u_136 u_137

noncomputable section

open scoped Matrix Matrix.Norms.L2Operator Kronecker

noncomputable section

open MeasureTheory Set Filter Metric

open scoped Topology Interval ENNReal NNReal ComplexConjugate

noncomputable section

open Filter Metric Set

open scoped Topology ComplexConjugate

noncomputable section

open Set Filter Metric

open scoped Topology ComplexConjugate

noncomputable section

open Set Filter Metric

open scoped Topology ComplexConjugate

namespace DirectCrouzeix.Geometry

variable {ι : Type u_135} [Fintype ι]

theorem expLevel_contDiff (v : ι → ℂ) (b : ι → ℝ) : ContDiff ℝ ⊤ (expLevel v b) := by
  apply ContDiff.sum
  intro i hi
  exact ((innerSL ℝ (v i)).contDiff.add contDiff_const).exp

end DirectCrouzeix.Geometry

namespace DirectCrouzeix.Geometry

variable {ι : Type u_136} [Fintype ι]

end DirectCrouzeix.Geometry

namespace DirectCrouzeix.Geometry

end DirectCrouzeix.Geometry

namespace DirectCrouzeix.Geometry

variable {ι : Type u_137} [Fintype ι]

end DirectCrouzeix.Geometry

end

end

end

end

end

end OAI

-- ---- from OAI.Analysis.DirectCrouzeix.InverseExterior ----
namespace OAI

noncomputable section

open scoped Matrix Matrix.Norms.L2Operator Kronecker

noncomputable section

open MeasureTheory Set Filter Metric

open scoped Topology Interval ENNReal NNReal ComplexConjugate

noncomputable section

open Filter Metric Set

open scoped Topology ComplexConjugate

noncomputable section

open Set Filter Metric

open scoped Topology ComplexConjugate

noncomputable section

open Set Filter Metric

open scoped Topology ComplexConjugate

noncomputable section

open Set Filter Metric

open scoped Topology ComplexConjugate

namespace DirectCrouzeix.Geometry

theorem mem_inverseExterior_iff {f : ℂ → ℝ} {a w : ℂ} (hw : w ≠ 0) :
    w ∈ inverseExterior f a ↔ 1 < f (a+w⁻¹) := or_iff_right hw

theorem inverseExterior_starConvex {f : ℂ → ℝ} (hf : ConvexOn ℝ univ f)
    {a : ℂ} (ha : f a < 1) : StarConvex ℝ 0 (inverseExterior f a) := by
  intro x hx t s ht hs hts
  simp only [smul_zero,zero_add]
  by_cases hs0 : s = 0
  · simp [hs0]
  by_cases hx0 : x = 0
  · simp [hx0]
  have hxout := (mem_inverseExterior_iff hx0).mp hx
  apply Or.inr
  by_contra hn
  have hnew : f (a+(s • x)⁻¹) ≤ 1 := le_of_not_gt hn
  have hsC : (s:ℂ) ≠ 0 := by exact_mod_cast hs0
  have hsum : (t:ℂ)+(s:ℂ)=1 := by exact_mod_cast hts
  have he : t • a+s • (a+(s • x)⁻¹) = a+x⁻¹ := by
    simp only [Complex.real_smul,mul_add]
    rw [mul_inv_rev]
    have hh : (s:ℂ)*((x⁻¹)*(s:ℂ)⁻¹) = x⁻¹ := by field_simp
    rw [hh]
    linear_combination a*hsum
  have hconv := hf.2 (mem_univ a) (mem_univ (a+(s • x)⁻¹)) ht hs hts
  rw [he] at hconv
  have h1 := mul_le_mul_of_nonneg_left (le_of_lt ha) ht
  have h2 := mul_le_mul_of_nonneg_left hnew hs
  dsimp only [smul_eq_mul] at hconv
  nlinarith

theorem inverseExterior_simplyConnected {f : ℂ → ℝ} (hf : ConvexOn ℝ univ f)
    {a : ℂ} (ha : f a < 1) : IsSimplyConnected (inverseExterior f a) := by
  let : ContractibleSpace (inverseExterior f a) :=
    (inverseExterior_starConvex hf ha).contractibleSpace ⟨0,zero_mem_inverseExterior f a⟩
  change SimplyConnectedSpace (inverseExterior f a)
  infer_instance

theorem inverseExterior_compact_closure {f : ℂ → ℝ} (hf : Continuous f)
    {a : ℂ} (ha : f a < 1) : IsCompact (closure (inverseExterior f a)) := by
  obtain ⟨L,hL,hB⟩ := inverseExterior_bounded hf ha
  exact (isCompact_closedBall (0:ℂ) L).of_isClosed_subset isClosed_closure
    (closure_minimal hB isClosed_closedBall)

theorem inverseExterior_proper {f : ℂ → ℝ} (hf : Continuous f)
    {a : ℂ} (ha : f a < 1) : inverseExterior f a ≠ univ := by
  obtain ⟨L,hL,hB⟩ := inverseExterior_bounded hf ha
  intro he
  have hh := hB (show ((L+1:ℝ):ℂ) ∈ inverseExterior f a from he ▸ mem_univ _)
  rw [mem_closedBall_zero_iff,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (by linarith)] at hh
  linarith

end DirectCrouzeix.Geometry

noncomputable section

open Set Filter Metric

open scoped Topology ComplexConjugate

namespace DirectCrouzeix.Geometry

end DirectCrouzeix.Geometry

end

end

end

end

end

end

end

end OAI

-- ---- from OAI.Analysis.DirectCrouzeix.ExteriorMapping ----
namespace OAI

universe u_138 u_139

noncomputable section

open scoped Matrix Matrix.Norms.L2Operator Kronecker

noncomputable section

open MeasureTheory Set Filter Metric

open scoped Topology Interval ENNReal NNReal ComplexConjugate

noncomputable section

open Filter Metric Set

open scoped Topology ComplexConjugate

noncomputable section

open Set Filter Metric

open scoped Topology ComplexConjugate

noncomputable section

open Set Filter Metric

open scoped Topology ComplexConjugate

noncomputable section

open Set Filter Metric

open scoped Topology ComplexConjugate

noncomputable section

open Set Filter Metric

open scoped Topology ComplexConjugate

namespace DirectCrouzeix.Geometry

end DirectCrouzeix.Geometry

namespace DirectCrouzeix.Geometry

theorem inverseExterior_analytic_boundary {ι : Type u_138} [Fintype ι]
    (v : ι → ℂ) (b : ι → ℝ) (hc : IsCompact {z | expLevel v b z ≤ 1})
    {a : ℂ} (ha : expLevel v b a < 1) :
    Conformal.HasAnalyticBoundary (inverseExterior (expLevel v b) a) := by
  intro w hw
  obtain ⟨hw0,hlevel⟩ := inverseExterior_frontier_level (expLevel_contDiff v b).continuous hc hw
  obtain ⟨H,hHa,hH0,hHd,hside⟩ := expLevel_boundary_parametrization v b hlevel ha
  let k := fun z : ℂ => (H (-z)-a)⁻¹
  have hpa : H 0-a ≠ 0 := by rw [hH0,add_sub_cancel_left]; exact inv_ne_zero hw0
  have hk0 : k 0 = w := by simp [k,hH0]
  have hHneg : AnalyticAt ℂ (fun z : ℂ => H (-z)) 0 := by
    exact (show AnalyticAt ℂ H (-(0:ℂ)) from by simpa using hHa).comp analyticAt_id.neg
  have hka : AnalyticAt ℂ k 0 := (hHneg.sub analyticAt_const).inv (by simpa using hpa)
  have hkder : HasDerivAt k (deriv H 0/(H 0-a)^2) 0 := by
    have hdn := (show HasDerivAt H (deriv H 0) (-(0:ℂ)) from by simpa using hHa.differentiableAt.hasDerivAt).comp 0 (hasDerivAt_id (0:ℂ)).neg
    convert! (hdn.sub_const a).inv (by simpa using hpa) using 1 ; simp
  have hkdn : deriv k 0 ≠ 0 := by rw [hkder.deriv]; exact div_ne_zero hHd (pow_ne_zero _ hpa)
  have hkP : ∀ᶠ z in 𝓝 (0:ℂ), k z ∈ inverseExterior (expLevel v b) a ↔ 0 < z.im := by
    have ht : Tendsto (fun z : ℂ => -z) (𝓝 0) (𝓝 0) := by simpa using continuous_neg.tendsto (0:ℂ)
    have hne : ∀ᶠ z in 𝓝 (0:ℂ), H (-z)-a ≠ 0 :=
      (hHneg.continuousAt.sub continuousAt_const).eventually_ne (by simpa using hpa)
    filter_upwards [ht.eventually hside,hne] with z hz hzne
    rw [mem_inverseExterior_iff (show k z ≠ 0 from inv_ne_zero hzne)]
    dsimp only [k]
    rw [inv_inv,add_sub_cancel]
    simpa only [Complex.neg_im,neg_lt_zero] using hz.2
  obtain ⟨C,hC,hC0,hCa,hCi,hCd,hCP⟩ := analytic_complex_chart hka hkdn hkP
  exact ⟨⟨C,hC0,by rw [hC,hk0],hCa,hCi,by rwa [hk0] at hCd,by simpa only [hC] using hCP⟩⟩

end DirectCrouzeix.Geometry

namespace DirectCrouzeix.Geometry

theorem exists_expLevel_exterior {ι : Type u_139} [Fintype ι]
    (v : ι → ℂ) (b : ι → ℝ) (hc : IsCompact {z | expLevel v b z ≤ 1})
    {a : ℂ} (ha : expLevel v b a < 1) :
    ∃ R > 1, ∃ (c : ℂ) (g : ℂ → ℂ), c ≠ 0 ∧ AnalyticOnNhd ℂ g (ball 0 R) ∧
      InjOn (fun ζ => c*ζ+g ζ⁻¹) (Inv.inv ⁻¹' ball 0 R \ {0}) ∧
      (∀ ζ : ℂ, ζ ≠ 0 → ζ⁻¹ ∈ ball 0 R → deriv (fun ζ => c*ζ+g ζ⁻¹) ζ ≠ 0) ∧
      (∀ ζ : ℂ, ‖ζ‖ = 1 → expLevel v b (c*ζ+g ζ⁻¹) = 1) ∧
      (∀ ζ : ℂ, 1 < ‖ζ‖ → 1 < expLevel v b (c*ζ+g ζ⁻¹)) := by
  let U := inverseExterior (expLevel v b) a
  have hct := (expLevel_contDiff v b).continuous
  have hU : IsOpen U := inverseExterior_isOpen hct hc a
  obtain ⟨R,hR,f,hfa,hfi,hopen,hclosed,hf0,hfd⟩ := Conformal.exists_riemann_collar hU
    (inverseExterior_simplyConnected (expLevel_convex v b) ha)
    (inverseExterior_proper hct ha) (inverseExterior_compact_closure hct ha)
    (inverseExterior_analytic_boundary v b hc ha) (zero_mem_inverseExterior _ a)
  obtain ⟨c,g,hc0,hg,he,hi,hd⟩ := exterior_laurent_form (by linarith : 0 < R) hfa hfi hf0 hfd a
  refine ⟨R,hR,c,g,hc0,hg,hi,hd,?_,?_⟩
  · intro ζ hζ
    have hζ0 : ζ ≠ 0 := by intro hh; norm_num [hh] at hζ
    have hη : ‖ζ⁻¹‖ = 1 := by simp [norm_inv,hζ]
    have hηR : ζ⁻¹ ∈ ball 0 R := mem_ball_zero_iff.mpr (by rw [hη]; exact hR)
    have hfu : f ζ⁻¹ ∈ frontier U := by
      rw [frontier,hU.interior_eq]
      refine ⟨?_,?_⟩
      · rw [← hclosed]
        exact mem_image_of_mem f (mem_closedBall_zero_iff.mpr (by rw [hη]))
      · intro hh
        rw [← hopen] at hh
        obtain ⟨z,hz,hze⟩ := hh
        have hzR := ball_subset_ball hR.le hz
        have hez : z = ζ⁻¹ := hfi hzR hηR hze
        have hzlt := mem_ball_zero_iff.mp hz
        rw [hez,hη] at hzlt
        exact lt_irrefl _ hzlt
    obtain ⟨hfn,hfl⟩ := inverseExterior_frontier_level hct hc hfu
    rw [he ζ hζ0]
    exact hfl
  · intro ζ hζ
    have hζ0 : ζ ≠ 0 := by intro hh; norm_num [hh] at hζ
    have hηB : ζ⁻¹ ∈ ball 0 1 := by
      rw [mem_ball_zero_iff,norm_inv]
      exact inv_lt_one_of_one_lt₀ hζ
    have hηR := ball_subset_ball hR.le hηB
    have hfn : f ζ⁻¹ ≠ 0 := by
      intro hh
      have hη0 := hfi hηR (mem_ball_self (by linarith)) (hh.trans hf0.symm)
      exact (inv_ne_zero hζ0) hη0
    have hfu : f ζ⁻¹ ∈ U := by rw [← hopen]; exact mem_image_of_mem f hηB
    rw [he ζ hζ0]
    exact (mem_inverseExterior_iff hfn).mp hfu

end DirectCrouzeix.Geometry

noncomputable section

open Set Filter Metric

open scoped Topology ComplexConjugate

namespace DirectCrouzeix.Geometry

end DirectCrouzeix.Geometry

end

end

end

end

end

end

end

end

end OAI

-- ---- platform node ----
open OAI OAI.DirectCrouzeix OAI.DirectCrouzeix.Geometry
open scoped Matrix Matrix.Norms.L2Operator Kronecker
open MeasureTheory Set Filter Metric
open scoped Topology Interval ENNReal NNReal ComplexConjugate
open Filter Metric Set
open scoped Topology ComplexConjugate
open Set Filter Metric
open scoped Topology ComplexConjugate
open Set Filter Metric
open scoped Topology ComplexConjugate
open Set Filter Metric
open scoped Topology ComplexConjugate
open Set Filter Metric
open scoped Topology ComplexConjugate


theorem solution : type_of% @_root_.OAI.DirectCrouzeix.Geometry.exists_expLevel_exterior := @_root_.OAI.DirectCrouzeix.Geometry.exists_expLevel_exterior
