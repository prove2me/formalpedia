-- Prove2me | solution 1 for OAI.DirectCrouzeix.Geometry.expLevel_holomorphic_support
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T08:45:20.68706+00:00
-- url     : https://prove2.me/submissions/0c5e3762-8edc-4581-a29e-55d3a5b1abfa

-- Generated from openai/math@1581d4c lean/OAI/Analysis/DirectCrouzeix/ExponentialSupport.lean:L87-L149
-- (upload_full_project.md Phase 4): solution for node OAI.DirectCrouzeix.Geometry.expLevel_holomorphic_support. The node keeps its source
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
import Definitions.Def_OAI_Analysis_DirectCrouzeix_SupportNets
import Definitions.Def_OAI_Analysis_DirectCrouzeix_Convexity
import Theorems.Thm_OAI_DirectCrouzeix_Geometry_expLevel_first_order

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

theorem expLevel_hasFDerivAt (v : ι → ℂ) (b : ι → ℝ) (z : ℂ) :
    HasFDerivAt (expLevel v b) (innerSL ℝ (expGradient v b z)) z := by
  have hh := HasFDerivAt.fun_sum (x := z) (u := Finset.univ) (fun i _ =>
    (((innerSL ℝ (v i)).hasFDerivAt).add_const (b i)).exp)
  convert! hh using 1
  ext w
  simp only [expGradient,innerSL_apply_apply,sum_inner,real_inner_smul_left,sum_apply,smul_apply,smul_eq_mul]

theorem expGradient_ne_zero (v : ι → ℂ) (b : ι → ℝ) {p a : ℂ}
    (hp : expLevel v b p = 1) (ha : expLevel v b a < 1) : expGradient v b p ≠ 0 := by
  intro he
  have hh := expLevel_first_order v b p a
  rw [he,inner_zero_left,hp,add_zero] at hh
  linarith

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

-- ---- from OAI.Analysis.DirectCrouzeix.ExponentialSupport ----
namespace OAI

universe u_143

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

noncomputable section

open Set Filter Metric

open scoped Topology ComplexConjugate

noncomputable section

open Set

open scoped ComplexConjugate Matrix

namespace DirectCrouzeix.Geometry

theorem positive_parallel_of_complex_inner {G q : ℂ} (hG : G ≠ 0) (hq : q ≠ 0)
    (horth : inner ℝ G (Complex.I*q) = 0) (hpos : 0 ≤ inner ℝ G q) :
    ∃ t : ℝ, 0 < t ∧ q = t • G := by
  have him : (conj G*q).im = 0 := by
    rw [real_inner_eq_re_inner ℂ,RCLike.inner_apply] at horth
    change ((Complex.I*q)*conj G).re = 0 at horth
    simp only [Complex.mul_re,Complex.mul_im,Complex.I_re,Complex.I_im,Complex.conj_re,Complex.conj_im] at horth ⊢
    nlinarith
  have hre : (conj G*q).re = inner ℝ G q := by
    simp [real_inner_eq_re_inner ℂ,RCLike.inner_apply,mul_comm]
  have hnon : inner ℝ G q ≠ 0 := by
    intro hh
    have he : conj G*q = 0 := Complex.ext (by simpa [hre] using hh) (by simpa using him)
    exact mul_ne_zero ((map_ne_zero (starRingEnd ℂ)).mpr hG) hq he
  have hp : 0 < inner ℝ G q := lt_of_le_of_ne hpos (Ne.symm hnon)
  let t := inner ℝ G q/‖G‖^2
  refine ⟨t,div_pos hp (sq_pos_of_pos (norm_pos_iff.mpr hG)),?_⟩
  have hprod : conj G*q = (inner ℝ G q:ℂ) := by
    apply Complex.ext <;> simp [hre,him]
  have hGG : conj G*G = ((‖G‖^2:ℝ):ℂ) := by
    rw [← Complex.normSq_eq_conj_mul_self,Complex.normSq_eq_norm_sq]
  apply mul_left_cancel₀ ((map_ne_zero (starRingEnd ℂ)).mpr hG : conj G ≠ 0)
  rw [hprod,Complex.real_smul,mul_left_comm,hGG]
  dsimp only [t]
  rw [Complex.ofReal_div,Complex.ofReal_pow,div_mul_cancel₀ _ (pow_ne_zero _ (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hG)))]

theorem expLevel_holomorphic_support {ι : Type u_143} [Fintype ι]
    (v : ι → ℂ) (b : ι → ℝ) {a : ℂ} (ha : expLevel v b a < 1)
    {ψ : ℂ → ℂ} {ζ : ℂ} (hζ : ‖ζ‖ = 1)
    (hd : HasDerivAt ψ (deriv ψ ζ) ζ) (hdn : deriv ψ ζ ≠ 0)
    (hcircle : ∀ η : ℂ, ‖η‖ = 1 → expLevel v b (ψ η) = 1)
    (hout : ∀ η : ℂ, 1 ≤ ‖η‖ → 1 ≤ expLevel v b (ψ η))
    {w : ℂ} (hw : expLevel v b w ≤ 1) :
    0 ≤ inner ℝ (ζ*deriv ψ ζ) (ψ ζ-w) := by
  let G := expGradient v b (ψ ζ)
  let q := ζ*deriv ψ ζ
  have hζ0 : ζ ≠ 0 := by intro hh; simp [hh] at hζ
  have hq : q ≠ 0 := mul_ne_zero hζ0 hdn
  have hlevel : expLevel v b (ψ ζ) = 1 := hcircle ζ hζ
  have hG : G ≠ 0 := expGradient_ne_zero v b hlevel ha
  have hφd : HasFDerivAt (expLevel v b) (innerSL ℝ G) (ψ ζ) := expLevel_hasFDerivAt v b (ψ ζ)
  have horth : inner ℝ G (Complex.I*q) = 0 := by
    let e := fun t : ℝ => ζ*Complex.exp ((t:ℂ)*Complex.I)
    have he0 : e 0 = ζ := by simp [e]
    have hed : HasDerivAt e (ζ*Complex.I) 0 := by
      have hi : HasDerivAt (fun t : ℝ => (t:ℂ)) 1 0 := by
        simpa only [Complex.ofRealCLM_apply,Complex.ofReal_one] using! (Complex.ofRealCLM.hasDerivAt (x := (0:ℝ)))
      convert! ((hi.mul_const Complex.I).cexp).const_mul ζ using 1 ; simp
    have hψd := (show HasDerivAt ψ (deriv ψ ζ) (e 0) from he0 ▸ hd).scomp 0 hed
    have hcomp := (show HasFDerivAt (expLevel v b) (innerSL ℝ G) (ψ (e 0)) from he0 ▸ hφd).comp_hasDerivAt 0 hψd
    have hc : (fun t : ℝ => expLevel v b (ψ (e t))) = fun _ => 1 := by
      funext t
      apply hcircle
      simp [e,hζ,Complex.norm_exp]
    have hv : deriv (fun t : ℝ => expLevel v b (ψ (e t))) 0 = 0 := by rw [hc]; simp
    have heval : inner ℝ G (Complex.I*q) = (innerSL ℝ G) ((ζ*Complex.I) • deriv ψ ζ) := by
      simp only [innerSL_apply_apply,smul_eq_mul,q]; congr 1; ring
    rw [heval,← hcomp.deriv]
    exact hv
  have hpos : 0 ≤ inner ℝ G q := by
    let r := fun t : ℝ => (t:ℂ)*ζ
    have hr1 : r 1 = ζ := by simp [r]
    have hrd : HasDerivAt r ζ 1 := by
      have hi : HasDerivAt (fun t : ℝ => (t:ℂ)) 1 1 := by
        simpa only [Complex.ofRealCLM_apply,Complex.ofReal_one] using! (Complex.ofRealCLM.hasDerivAt (x := (1:ℝ)))
      convert! hi.mul_const ζ using 1 ; simp
    have hψd := (show HasDerivAt ψ (deriv ψ ζ) (r 1) from hr1 ▸ hd).scomp 1 hrd
    have hcomp := (show HasFDerivAt (expLevel v b) (innerSL ℝ G) (ψ (r 1)) from hr1 ▸ hφd).comp_hasDerivAt 1 hψd
    have hmin : IsMinOn (fun t : ℝ => expLevel v b (ψ (r t))) (Ici 1) 1 := by
      intro t ht
      change expLevel v b (ψ (r 1)) ≤ expLevel v b (ψ (r t))
      rw [hr1,hlevel]
      apply hout
      have ht0 : 0 ≤ t := le_trans (by norm_num) ht
      simpa [r,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg ht0,hζ] using ht
    have htan : (1:ℝ) ∈ posTangentConeAt (Ici 1) 1 := by
      apply mem_posTangentConeAt_of_segment_subset
      exact (convex_Ici (1:ℝ)).segment_subset (by norm_num) (by norm_num)
    have hh := hmin.localize.hasFDerivWithinAt_nonneg hcomp.hasFDerivAt.hasFDerivWithinAt htan
    simpa [q] using hh
  obtain ⟨t,ht,hqeq⟩ := positive_parallel_of_complex_inner hG hq horth hpos
  have hs := expLevel_first_order v b (ψ ζ) w
  rw [hlevel,show expGradient v b (ψ ζ) = G from rfl] at hs
  have hsupport : 0 ≤ inner ℝ G (ψ ζ-w) := by
    rw [inner_sub_right] at hs ⊢
    linarith
  change 0 ≤ inner ℝ q (ψ ζ-w)
  rw [hqeq,real_inner_smul_left]
  exact mul_nonneg (le_of_lt ht) hsupport

end DirectCrouzeix.Geometry

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
open Set Filter Metric
open scoped Topology ComplexConjugate
open Set
open scoped ComplexConjugate Matrix


theorem solution : type_of% @_root_.OAI.DirectCrouzeix.Geometry.expLevel_holomorphic_support := @_root_.OAI.DirectCrouzeix.Geometry.expLevel_holomorphic_support
