-- Prove2me | solution 1 for OAI.RuledApproximation.orthogonal_closedBall_square
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T08:12:20.210843+00:00
-- url     : https://prove2.me/submissions/252ed58e-f7d5-462a-82d8-856d9cc842e6

-- Generated from openai/math@1581d4c lean/OAI/Geometry/RuledCovering/NilpotentLattice.lean:L140-L173
-- (upload_full_project.md Phase 4): solution for node OAI.RuledApproximation.orthogonal_closedBall_square. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_RuledCovering
import Definitions.Def_OAI_Geometry_RuledCovering_Projection
import Definitions.Def_OAI_Geometry_RuledCovering_Frames
import Definitions.Def_OAI_Geometry_RuledCovering_OuterApproximation
import Definitions.Def_OAI_Geometry_RuledCovering_Lattice
import Definitions.Def_OAI_Geometry_RuledCovering_LocalApproximation
import Definitions.Def_OAI_Geometry_RuledCovering_HyperbolicLattice
import Definitions.Def_OAI_Geometry_RuledCovering_HyperbolicCover
import Definitions.Def_OAI_Geometry_RuledCovering_Isometries
import Definitions.Def_OAI_Geometry_RuledCovering_Hyperbolic
import Definitions.Def_OAI_Geometry_RuledCovering_NilpotentLattice

-- ---- from OAI.Geometry.RuledCovering.Frames ----
namespace OAI

noncomputable section

open Set MeasureTheory Filter Metric
open scoped Topology ContDiff Pointwise

namespace RuledApproximation

lemma coordinates_closedBall (b : Coordinates) {a : ℝ} (ha : 0 ≤ a) :
    closedBall b a = Set.pi univ (fun i => Icc (b i - a) (b i + a)) := by
  ext x
  simp only [mem_closedBall, dist_eq_norm, pi_norm_le_iff_of_nonneg ha, Real.norm_eq_abs,
    Pi.sub_apply, Set.mem_pi, mem_univ, true_implies, mem_Icc, abs_le]
  constructor <;> intro h i <;> obtain ⟨h₁, h₂⟩ := h i <;> constructor <;> linarith

end RuledApproximation

end

end OAI

-- ---- from OAI.Geometry.RuledCovering.NilpotentLattice ----
namespace OAI

noncomputable section

open Set MeasureTheory Filter Metric
open scoped Topology ContDiff Pointwise

namespace RuledApproximation

lemma orthogonal_closedBall_square (R : Plane ≃ₗᵢ[ℝ] Plane) (b : Coordinates)
    {a : ℝ} (ha : 0 < a) :
    IsSquareTile (orthogonalFrame R '' closedBall b a) := by
  let M := orthogonalFrame R
  refine ⟨M b,R,2*a,by positivity,?_⟩
  ext p
  constructor
  · rintro ⟨x,hx,rfl⟩
    let q : Coordinates := fun i => (x i-b i)/(2*a)
    refine ⟨WithLp.toLp 2 q, ?_, ?_⟩
    · rw [mem_closedBall, dist_eq_norm, pi_norm_le_iff_of_nonneg ha.le] at hx
      intro i
      change |(x i-b i)/(2*a)| ≤ 1/2
      rw [abs_div, abs_of_pos (by positivity : 0 < 2*a)]
      apply (div_le_iff₀ (by positivity : 0 < 2*a)).mpr
      have hi := hx i
      change |x i-b i| ≤ a at hi
      linarith
    · change M b+(2*a) • M q = M x
      rw [← map_smul, ← map_add]
      congr 1
      ext i
      simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,q]
      rw [mul_div_cancel₀ _ (mul_ne_zero (by norm_num) ha.ne')]
      ring
  · rintro ⟨x,hx,rfl⟩
    refine ⟨b+(2*a) • WithLp.ofLp x, ?_, ?_⟩
    · rw [coordinates_closedBall b ha.le]
      intro i _
      change b i-a ≤ b i+(2*a)*x i ∧ b i+(2*a)*x i ≤ b i+a
      have hi := abs_le.mp (hx i)
      constructor <;> nlinarith [hi.1,hi.2]
    · change M (b+(2*a) • WithLp.ofLp x) = M b + (2*a) • R x
      simp [M,orthogonalFrame]

end RuledApproximation

end

end OAI

-- ---- platform node ----
open OAI OAI.RuledApproximation
open Set MeasureTheory Filter Metric
open scoped Topology ContDiff


theorem solution : type_of% @_root_.OAI.RuledApproximation.orthogonal_closedBall_square := @_root_.OAI.RuledApproximation.orthogonal_closedBall_square
