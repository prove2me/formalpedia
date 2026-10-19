-- Prove2me | solution 1 for OAI.DirectCrouzeix.Conformal.bounded_holomorphic_compact
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T07:41:43.14929+00:00
-- url     : https://prove2.me/submissions/c26fef74-d674-4880-bc72-f24d0b0b5d0b

-- Generated from openai/math@1581d4c lean/OAI/Analysis/DirectCrouzeix/NormalFamilies.lean:L179-L201
-- (upload_full_project.md Phase 4): solution for node OAI.DirectCrouzeix.Conformal.bounded_holomorphic_compact. The node keeps its source
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

theorem bounded_holomorphic_equicontinuous {U : Set ℂ} (hU : IsOpen U)
    {ι : Type u_131} (F : ι → ℂ → ℂ)
    (hF : ∀ i, DifferentiableOn ℂ (F i) U)
    (hbound : ∀ i z, z ∈ U → ‖F i z‖ ≤ 1) :
    Equicontinuous (fun i (z : U) => F i z) := by
  intro x
  rw [Metric.equicontinuousAt_iff]
  intro ε hε
  obtain ⟨R, hR, hBR⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hU.mem_nhds x.property)
  let r := R / 2
  have hr : 0 < r := half_pos hR
  have hd (i : ι) (z : ℂ) (hz : z ∈ ball (x : ℂ) r) : ‖deriv (F i) z‖ ≤ 1 / r := by
    have hsub : closedBall z r ⊆ U := by
      intro w hw
      apply hBR
      have ht := dist_triangle w z (x : ℂ)
      have hw' := mem_closedBall.mp hw
      have hz' := mem_ball.mp hz
      change dist w (x : ℂ) ≤ R
      dsimp [r] at hw' hz'
      linarith
    apply Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hr
    · apply DifferentiableOn.diffContOnCl
      rw [closure_ball z hr.ne']
      exact (hF i).mono hsub
    · intro w hw
      exact hbound i w (hsub (sphere_subset_closedBall hw))
  have hbU : ball (x : ℂ) r ⊆ U := by
    intro z hz
    apply hBR
    exact mem_closedBall.mpr ((mem_ball.mp hz).le.trans (by dsimp [r]; linarith))
  refine ⟨min r (ε * r), lt_min hr (mul_pos hε hr), ?_⟩
  intro y hy i
  have hy' : dist (y : ℂ) (x : ℂ) < r := lt_of_lt_of_le hy (min_le_left _ _)
  have hxy : ‖F i y - F i x‖ ≤ (1 / r) * ‖(y : ℂ) - x‖ :=
    Convex.norm_image_sub_le_of_norm_deriv_le
      (fun z hz => (hF i).differentiableAt (hU.mem_nhds (hbU hz)))
      (hd i) (convex_ball (x : ℂ) r) (mem_ball_self hr) hy'
  rw [dist_comm, dist_eq_norm]
  apply lt_of_le_of_lt hxy
  rw [one_div, ← div_eq_inv_mul, div_lt_iff₀ hr]
  rw [← dist_eq_norm]
  exact lt_of_lt_of_le hy (min_le_right _ _)

theorem bounded_holomorphic_compact {U : Set ℂ} (hU : IsOpen U)
    (S : Set C(U, ℂ))
    (hS : ∀ f ∈ S, DifferentiableOn ℂ (extend U f) U ∧ ∀ z : U, ‖f z‖ ≤ 1) :
    IsCompact (closure S) := by
  let : LocallyCompactSpace U := hU.locallyCompactSpace
  let : T2Space (UniformOnFun U ℂ {K | IsCompact K}) :=
    UniformOnFun.t2Space_of_covering (by
      ext x
      simp only [mem_sUnion, mem_ofPred_eq, mem_univ, iff_true]
      exact ⟨{x}, isCompact_singleton, mem_singleton x⟩)
  apply ArzelaAscoli.isCompact_closure_of_isClosedEmbedding
    (F := fun f : C(U, ℂ) => (f : U → ℂ)) (𝔖 := {K | IsCompact K})
    (fun _ hK => hK)
    ContinuousMap.isUniformEmbedding_toUniformOnFunIsCompact.isClosedEmbedding
  · intro K hK
    have he := bounded_holomorphic_equicontinuous hU
      (fun f : S => extend U (f : C(U, ℂ)))
      (fun f => (hS f f.property).1)
      (fun f z hz => by simpa [extend, hz] using (hS f f.property).2 ⟨z, hz⟩)
    simpa only [Function.comp_def, extend_coe] using he.equicontinuousOn K
  · intro K hK z hz
    exact ⟨closedBall 0 1, isCompact_closedBall _ _, fun f hf => by
      simpa using (hS f hf).2 z⟩

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


theorem solution : type_of% @_root_.OAI.DirectCrouzeix.Conformal.bounded_holomorphic_compact := @_root_.OAI.DirectCrouzeix.Conformal.bounded_holomorphic_compact
