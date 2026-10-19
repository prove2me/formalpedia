-- Prove2me | solution 1 for OAI.DirectCrouzeix.Conformal.univalent_neighborhood_of_disk_side
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T08:04:06.775446+00:00
-- url     : https://prove2.me/submissions/ba4a8e35-6b66-45b6-a3fb-59cd70e48b07

-- Generated from openai/math@1581d4c lean/OAI/Analysis/DirectCrouzeix/Continuation.lean:L143-L171
-- (upload_full_project.md Phase 4): solution for node OAI.DirectCrouzeix.Conformal.univalent_neighborhood_of_disk_side. The node keeps its source
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

-- ---- from OAI.Analysis.DirectCrouzeix.Continuation ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
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

theorem injective_closure_of_disk_side {U V : Set ℂ} (hV : IsOpen V)
    (hUV : closure U ⊆ V) {F : ℂ → ℂ} (hF : AnalyticOnNhd ℂ F V)
    (hi : InjOn F U) (hm : F '' U = ball 0 1)
    (hside : ∀ z ∈ V, ‖F z‖ < 1 ↔ z ∈ U)
    (hd : ∀ p ∈ closure U, deriv F p ≠ 0) : InjOn F (closure U) := by
  intro p hp q hq he
  by_contra hpq
  obtain ⟨S,T,hS,hT,hpS,hqT,hST⟩ := t2_separation hpq
  have hpN : S ∩ V ∈ 𝓝 p := (hS.inter hV).mem_nhds ⟨hpS,hUV hp⟩
  have hqN : T ∩ V ∈ 𝓝 q := (hT.inter hV).mem_nhds ⟨hqT,hUV hq⟩
  have hpI : F '' (S ∩ V) ∈ 𝓝 (F p) := by
    rw [← (hF p (hUV hp)).hasStrictDerivAt.map_nhds_eq (hd p hp)]
    exact Filter.image_mem_map hpN
  have hqI : F '' (T ∩ V) ∈ 𝓝 (F p) := by
    rw [he, ← (hF q (hUV hq)).hasStrictDerivAt.map_nhds_eq (hd q hq)]
    exact Filter.image_mem_map hqN
  have hpCl : F p ∈ closure (ball (0 : ℂ) 1) := by
    rw [← hm]
    exact mem_closure_image (hF p (hUV hp)).continuousAt hp
  obtain ⟨w,hwI,hwD⟩ := mem_closure_iff_nhds.mp hpCl _ (inter_mem hpI hqI)
  obtain ⟨a,haS,haw⟩ := hwI.1
  obtain ⟨b,hbT,hbw⟩ := hwI.2
  have haU : a ∈ U := (hside a haS.2).mp (by rw [haw]; exact mem_ball_zero_iff.mp hwD)
  have hbU : b ∈ U := (hside b hbT.2).mp (by rw [hbw]; exact mem_ball_zero_iff.mp hwD)
  have hab : a = b := hi haU hbU (haw.trans hbw.symm)
  exact Set.disjoint_left.mp hST haS.1 (hab ▸ hbT.1)

theorem univalent_neighborhood_of_disk_side {U V : Set ℂ} (hV : IsOpen V)
    (hUV : closure U ⊆ V) (hUc : IsCompact (closure U))
    {F : ℂ → ℂ} (hF : AnalyticOnNhd ℂ F V)
    (hi : InjOn F U) (hm : F '' U = ball 0 1)
    (hside : ∀ z ∈ V, ‖F z‖ < 1 ↔ z ∈ U)
    (hd : ∀ p ∈ closure U, deriv F p ≠ 0) :
    ∃ W, IsOpen W ∧ closure U ⊆ W ∧ W ⊆ V ∧
      InjOn F W ∧ AnalyticOnNhd ℂ F W ∧ F '' closure U = closedBall 0 1 := by
  have hic := injective_closure_of_disk_side hV hUV hF hi hm hside hd
  have hlocal : ∀ p ∈ closure U, ∃ S ∈ 𝓝 p, InjOn F S := by
    intro p hp
    let d := (hF p (hUV hp)).hasStrictDerivAt.hasStrictFDerivAt_equiv (hd p hp)
    exact ⟨(d.toOpenPartialHomeomorph F).source,
      (d.toOpenPartialHomeomorph F).open_source.mem_nhds d.mem_toOpenPartialHomeomorph_source,
      (d.toOpenPartialHomeomorph F).injOn⟩
  obtain ⟨W,hW,hUW,hiW⟩ := hic.exists_isOpen_superset hUc
    (fun p hp => (hF p (hUV hp)).continuousAt) hlocal
  refine ⟨W ∩ V,hW.inter hV,fun z hz => ⟨hUW hz,hUV hz⟩,inter_subset_right,
    hiW.mono inter_subset_left,hF.mono inter_subset_right,?_⟩
  apply Subset.antisymm
  · rintro w ⟨z,hz,rfl⟩
    rw [← closure_ball (0 : ℂ) (by norm_num : (1 : ℝ) ≠ 0), ← hm]
    exact mem_closure_image (hF z (hUV hz)).continuousAt hz
  · have hc : IsClosed (F '' closure U) :=
      (hUc.image_of_continuousOn (hF.continuousOn.mono hUV)).isClosed
    rw [← closure_ball (0 : ℂ) (by norm_num : (1 : ℝ) ≠ 0)]
    apply hc.closure_subset_iff.mpr
    rw [← hm]
    exact image_mono subset_closure

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


theorem solution : type_of% @_root_.OAI.DirectCrouzeix.Conformal.univalent_neighborhood_of_disk_side := @_root_.OAI.DirectCrouzeix.Conformal.univalent_neighborhood_of_disk_side
