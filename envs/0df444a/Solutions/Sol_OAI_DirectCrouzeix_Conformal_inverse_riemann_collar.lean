-- Prove2me | solution 1 for OAI.DirectCrouzeix.Conformal.inverse_riemann_collar
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T08:07:53.702859+00:00
-- url     : https://prove2.me/submissions/d2903099-62cb-4cb1-9754-857a0de9d43e

-- Generated from openai/math@1581d4c lean/OAI/Analysis/DirectCrouzeix/ConformalCollar.lean:L129-L228
-- (upload_full_project.md Phase 4): solution for node OAI.DirectCrouzeix.Conformal.inverse_riemann_collar. The node keeps its source
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
import Theorems.Thm_OAI_DirectCrouzeix_Conformal_local_riemann_extension
import Theorems.Thm_OAI_DirectCrouzeix_Conformal_patch_boundary_germs
import Theorems.Thm_OAI_DirectCrouzeix_Conformal_univalent_neighborhood_of_disk_side

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

theorem inverse_riemann_collar {U : Set ℂ} (hU : IsOpen U)
    (hUc : IsCompact (closure U)) (hUB : HasAnalyticBoundary U)
    {a : ℂ} (ha : a ∈ U) {f : ℂ → ℂ} (hf : NormalizedEmbedding U a f)
    (hs : f '' U = ball 0 1) :
    ∃ R > 1, ∃ g : ℂ → ℂ, AnalyticOnNhd ℂ g (ball 0 R) ∧ InjOn g (ball 0 R) ∧
      g '' ball 0 1 = U ∧ g '' closedBall 0 1 = closure U ∧ g 0 = a ∧
      (∀ z ∈ ball 0 R, deriv g z ≠ 0) := by
  have hloc : ∀ p ∈ closure U, ∃ r > 0, ∃ E : ℂ → ℂ,
      AnalyticOnNhd ℂ E (ball p (3*r)) ∧ EqOn E f (ball p (3*r) ∩ U) ∧
      (∀ z ∈ ball p (3*r), ‖E z‖ < 1 ↔ z ∈ U) ∧ deriv E p ≠ 0 := by
    intro p hp
    by_cases hpin : p ∈ U
    · obtain ⟨r,hr,hrU⟩ := Metric.isOpen_iff.mp hU p hpin
      refine ⟨r/3,by positivity,f,?_,fun _ _ => rfl,?_,hf.derivative p hpin⟩
      · simpa only [show 3*(r/3)=r by ring] using
          (hf.holomorphic.analyticOnNhd hU).mono hrU
      · intro z hz
        have hzU : z ∈ U := hrU (by simpa only [show 3*(r/3)=r by ring] using hz)
        exact iff_of_true (mem_ball_zero_iff.mp (hf.disk hzU)) hzU
    · have hpB : p ∈ frontier U := by
        rw [frontier, hU.interior_eq]
        exact ⟨hp,hpin⟩
      obtain ⟨C⟩ := hUB p hpB
      exact local_riemann_extension hU ha hf hs hpin C
  obtain ⟨V,F,hV,hUV,hF,hFf,hside,hd⟩ := patch_boundary_germs hU hloc
  have hi : InjOn F U := by
    intro x hx y hy he
    apply hf.injective hx hy
    simpa only [hFf hx,hFf hy] using he
  have hm : F '' U = ball 0 1 := hFf.image_eq.trans hs
  obtain ⟨W,hW,hUW,hWV,hiW,hFW,hmW⟩ :=
    univalent_neighborhood_of_disk_side hV hUV hUc hF hi hm hside hd
  let Z := W ∩ interior {z | deriv F z ≠ 0}
  have hZ : IsOpen Z := hW.inter isOpen_interior
  have hUZ : closure U ⊆ Z := by
    intro z hz
    refine ⟨hUW hz,mem_interior_iff_mem_nhds.mpr ?_⟩
    exact ((hF z (hUV hz)).deriv.continuousAt).eventually
      (isClosed_singleton.isOpen_compl.mem_nhds (hd z hz))
  have hZF : AnalyticOnNhd ℂ F Z := hFW.mono inter_subset_left
  have hdZ : ∀ z ∈ Z, deriv F z ≠ 0 := fun z hz => interior_subset hz.2
  have hiZ : InjOn F Z := hiW.mono inter_subset_left
  have hImage : IsOpen (F '' Z) := by
    rw [isOpen_iff_mem_nhds]
    rintro w ⟨z,hz,rfl⟩
    rw [← (hZF z hz).hasStrictDerivAt.map_nhds_eq (hdZ z hz)]
    exact Filter.image_mem_map (hZ.mem_nhds hz)
  have hSmall : closedBall (0 : ℂ) 1 ⊆ F '' Z := by
    rw [← hmW]
    exact image_mono hUZ
  obtain ⟨δ,hδ,hδsub⟩ := (isCompact_closedBall (0 : ℂ) 1).exists_thickening_subset_open hImage hSmall
  rw [thickening_closedBall hδ (by norm_num : (0 : ℝ) ≤ 1)] at hδsub
  let R := δ + 1
  have hR : 1 < R := by dsimp [R]; linarith
  have hball : ball (0 : ℂ) R ⊆ F '' Z := hδsub
  let g := Function.invFunOn F Z
  have hgr : ∀ z ∈ F '' Z, F (g z) = z := fun z hz => Function.invFunOn_eq hz
  have hgl : ∀ z ∈ Z, g (F z) = z := fun z hz => hiZ.leftInvOn_invFunOn hz
  have hgm : ∀ z ∈ F '' Z, g z ∈ Z := fun z hz => Function.invFunOn_mem hz
  have hgder : ∀ z ∈ ball (0 : ℂ) R,
      HasStrictDerivAt g (deriv F (g z))⁻¹ z := by
    intro z hz
    have hzI := hball hz
    have hh := inverse_hasStrictDerivAt hZ hZF.differentiableOn hiZ (hgm z hzI) (hdZ _ (hgm z hzI))
    simpa only [g,hgr z hzI] using hh
  have hg : AnalyticOnNhd ℂ g (ball (0 : ℂ) R) := by
    apply DifferentiableOn.analyticOnNhd _ isOpen_ball
    exact fun z hz => (hgder z hz).hasDerivAt.differentiableAt.differentiableWithinAt
  refine ⟨R,hR,g,hg,?_,?_,?_,?_,?_⟩
  · intro x hx y hy he
    calc
      x = F (g x) := (hgr x (hball hx)).symm
      _ = F (g y) := congrArg F he
      _ = y := hgr y (hball hy)
  · apply Subset.antisymm
    · rintro w ⟨z,hz,rfl⟩
      have hzR := ball_subset_ball hR.le hz
      have hzI := hball hzR
      apply (hside _ (hWV (hgm z hzI).1)).mp
      rw [hgr z hzI]
      exact mem_ball_zero_iff.mp hz
    · intro z hz
      refine ⟨F z,?_,hgl z (hUZ (subset_closure hz))⟩
      rw [← hm]
      exact mem_image_of_mem F hz
  · apply Subset.antisymm
    · rintro w ⟨z,hz,rfl⟩
      rw [← hmW] at hz
      obtain ⟨y,hy,rfl⟩ := hz
      simpa only [hgl y (hUZ hy)] using hy
    · intro z hz
      refine ⟨F z,?_,hgl z (hUZ hz)⟩
      rw [← hmW]
      exact mem_image_of_mem F hz
  · have haZ := hUZ (subset_closure ha)
    have hFa : F a = 0 := (hFf ha).trans hf.normalized
    simpa only [hFa] using hgl a haZ
  · intro z hz
    rw [(hgder z hz).hasDerivAt.deriv]
    exact inv_ne_zero (hdZ _ (hgm z (hball hz)))

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


theorem solution : type_of% @_root_.OAI.DirectCrouzeix.Conformal.inverse_riemann_collar := @_root_.OAI.DirectCrouzeix.Conformal.inverse_riemann_collar
