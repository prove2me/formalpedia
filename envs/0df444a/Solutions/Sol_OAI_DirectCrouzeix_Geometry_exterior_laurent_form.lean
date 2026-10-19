-- Prove2me | solution 1 for OAI.DirectCrouzeix.Geometry.exterior_laurent_form
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T08:29:15.110146+00:00
-- url     : https://prove2.me/submissions/d537cdb4-25f7-4d60-aed1-b33dd8451291

-- Generated from openai/math@1581d4c lean/OAI/Analysis/DirectCrouzeix/ExteriorMapping.lean:L49-L109
-- (upload_full_project.md Phase 4): solution for node OAI.DirectCrouzeix.Geometry.exterior_laurent_form. The node keeps its source
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

theorem exterior_laurent_form {R : ℝ} (hR : 0 < R) {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (ball 0 R)) (hinj : InjOn f (ball 0 R))
    (hf0 : f 0 = 0) (hd : ∀ u ∈ ball 0 R, deriv f u ≠ 0) (a : ℂ) :
    ∃ (c : ℂ) (g : ℂ → ℂ), c ≠ 0 ∧ AnalyticOnNhd ℂ g (ball 0 R) ∧
      (∀ ζ : ℂ, ζ ≠ 0 → c*ζ+g ζ⁻¹ = a+(f ζ⁻¹)⁻¹) ∧
      InjOn (fun ζ => c*ζ+g ζ⁻¹) (Inv.inv ⁻¹' ball 0 R \ {0}) ∧
      (∀ ζ : ℂ, ζ ≠ 0 → ζ⁻¹ ∈ ball 0 R → deriv (fun ζ => c*ζ+g ζ⁻¹) ζ ≠ 0) := by
  have h0 : (0:ℂ) ∈ ball 0 R := mem_ball_self hR
  let J := dslope f 0
  have hJ : AnalyticOnNhd ℂ J (ball 0 R) :=
    (Complex.differentiableOn_dslope (ball_mem_nhds (0:ℂ) hR)).mpr hf.differentiableOn |>.analyticOnNhd isOpen_ball
  have hJ0 : J 0 = deriv f 0 := dslope_same _ _
  have hfn (u : ℂ) (hu : u ∈ ball 0 R) (hu0 : u ≠ 0) : f u ≠ 0 := by
    intro he
    exact hu0 (hinj hu h0 (he.trans hf0.symm))
  have hJn (u : ℂ) (hu : u ∈ ball 0 R) : J u ≠ 0 := by
    by_cases hu0 : u = 0
    · subst u; rw [hJ0]; exact hd 0 h0
    · dsimp only [J]
      rw [dslope_of_ne _ hu0]
      simp only [slope_def_field,hf0,sub_zero]
      exact div_ne_zero (hfn u hu hu0) hu0
  let F := fun u => (J u)⁻¹
  have hF : AnalyticOnNhd ℂ F (ball 0 R) := fun u hu => (hJ u hu).inv (hJn u hu)
  let c := F 0
  have hc : c ≠ 0 := inv_ne_zero (hJn 0 h0)
  let g := fun u => a+dslope F 0 u
  have hg : AnalyticOnNhd ℂ g (ball 0 R) := by
    have hs : AnalyticOnNhd ℂ (dslope F 0) (ball 0 R) :=
      (Complex.differentiableOn_dslope (ball_mem_nhds (0:ℂ) hR)).mpr hF.differentiableOn |>.analyticOnNhd isOpen_ball
    exact analyticOnNhd_const.add hs
  have he (ζ : ℂ) (hζ : ζ ≠ 0) : c*ζ+g ζ⁻¹ = a+(f ζ⁻¹)⁻¹ := by
    have hu : ζ⁻¹ ≠ 0 := inv_ne_zero hζ
    dsimp only [g]
    rw [dslope_of_ne _ hu,slope_def_field]
    dsimp only [F,J,c]
    rw [dslope_of_ne _ hu,slope_def_field,hf0]
    simp only [sub_zero,div_inv_eq_mul]
    field_simp
    ring
  have hder (ζ : ℂ) (hζ : ζ ≠ 0) (hu : ζ⁻¹ ∈ ball 0 R) :
      HasDerivAt (fun ζ => a+(f ζ⁻¹)⁻¹)
        (- (deriv f ζ⁻¹ * (-1/ζ^2))/(f ζ⁻¹)^2) ζ := by
    have hi : HasDerivAt (fun ζ : ℂ => ζ⁻¹) (-1/ζ^2) ζ := by
      convert! (hasDerivAt_id ζ).inv hζ using 1
    have hh := ((hf _ hu).differentiableAt.hasDerivAt.comp ζ hi).inv (hfn _ hu (inv_ne_zero hζ))
    convert! hh.const_add a using 1
  refine ⟨c,g,hc,hg,he,?_,?_⟩
  · intro ζ hζ η hη hh
    have hζ0 : ζ ≠ 0 := hζ.2
    have hη0 : η ≠ 0 := hη.2
    change c*ζ+g ζ⁻¹ = c*η+g η⁻¹ at hh
    rw [he ζ hζ0,he η hη0,add_right_inj] at hh
    exact inv_injective (hinj hζ.1 hη.1 (inv_injective hh))
  · intro ζ hζ hu
    have hev : (fun ζ => c*ζ+g ζ⁻¹) =ᶠ[𝓝 ζ] (fun ζ => a+(f ζ⁻¹)⁻¹) := by
      filter_upwards [continuousAt_id.eventually_ne hζ] with z hz
      exact he z hz
    rw [((hder ζ hζ hu).congr_of_eventuallyEq hev).deriv]
    exact div_ne_zero (neg_ne_zero.mpr (mul_ne_zero (hd _ hu)
      (div_ne_zero (by norm_num) (pow_ne_zero _ hζ)))) (pow_ne_zero _ (hfn _ hu (inv_ne_zero hζ)))

end DirectCrouzeix.Geometry

namespace DirectCrouzeix.Geometry

end DirectCrouzeix.Geometry

namespace DirectCrouzeix.Geometry

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


theorem solution : type_of% @_root_.OAI.DirectCrouzeix.Geometry.exterior_laurent_form := @_root_.OAI.DirectCrouzeix.Geometry.exterior_laurent_form
