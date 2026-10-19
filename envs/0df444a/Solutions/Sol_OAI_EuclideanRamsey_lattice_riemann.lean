-- Prove2me | solution 1 for OAI.EuclideanRamsey.lattice_riemann
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T03:18:58.910963+00:00
-- url     : https://prove2.me/submissions/9d51f8e0-6152-4956-b81a-8e1cc756fc66

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/EuclideanRamsey/Discretization.lean:L168-L188
-- (upload_full_project.md Phase 4): solution for node OAI.EuclideanRamsey.lattice_riemann. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_EuclideanRamsey
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_TensorNecessity
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_TensorDescent
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_SmoothingKernel
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_Hessian
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_DifferentialSplitting
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_SmoothingMatrix
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_LatticeMoments
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_Discretization
import Theorems.Thm_OAI_EuclideanRamsey_lattice_tsum_eq_grid

-- ---- from OAI.Combinatorics.EuclideanRamsey.Discretization ----
namespace OAI

universe uDomain uIndex

noncomputable section

open scoped TensorProduct RealInnerProductSpace
open scoped BigOperators
open Real Filter Topology MeasureTheory Polynomial
open Matrix MeasureTheory
open MeasureTheory
open Matrix
open scoped MatrixOrder Matrix.Norms.L2Operator
open MeasureTheory Matrix
open scoped TensorProduct

open MeasureTheory
open scoped BigOperators
namespace EuclideanRamsey

end EuclideanRamsey

open scoped BigOperators
namespace EuclideanRamsey

end EuclideanRamsey

open scoped BigOperators Pointwise Topology
open MeasureTheory Filter
namespace EuclideanRamsey

theorem lattice_riemann {k : ℕ} {f : (Fin k → ℝ) → ℝ}
    (hf : Continuous f) (hfc : HasCompactSupport f) :
    Tendsto (fun n : ℕ => (∑' γ : Fin k → ℤ, f (latticeSample n γ))/(n:ℝ)^k)
      atTop (𝓝 (∫ x, f x)) := by
  obtain ⟨R,hR,hfR⟩ := hfc.exists_pos_le_norm
  let s := Metric.closedBall (0 : Fin k → ℝ) R
  have hs : Function.support f ⊆ s := by
    intro x hx
    rw [show s = Metric.closedBall 0 R from rfl, Metric.mem_closedBall,dist_zero_right]
    exact le_of_lt (lt_of_not_ge (fun h => hx (hfR x h)))
  have hfront : volume (frontier s) = 0 :=
    measure_mono_null Metric.frontier_closedBall_subset_sphere
      (volume.addHaar_sphere_of_ne_zero 0 hR.ne')
  have h := tendsto_tsum_div_pow_atTop_integral s f hf Metric.isBounded_closedBall
    measurableSet_closedBall hfront
  have hi : (∫ x in s,f x) = ∫ x,f x := by
    rw [← integral_indicator measurableSet_closedBall, Set.indicator_eq_self.mpr hs]
  simp only [Fintype.card_fin,hi] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  rw [lattice_tsum_eq_grid (by omega) s f hs]

end EuclideanRamsey

end

end OAI

-- ---- platform node ----
open OAI OAI.EuclideanRamsey
open scoped TensorProduct RealInnerProductSpace
open scoped BigOperators
open Real Filter Topology MeasureTheory Polynomial
open Matrix MeasureTheory
open MeasureTheory
open Matrix
open scoped MatrixOrder Matrix.Norms.L2Operator
open MeasureTheory Matrix
open scoped TensorProduct
open MeasureTheory
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators Pointwise Topology
open MeasureTheory Filter


theorem solution : type_of% @_root_.OAI.EuclideanRamsey.lattice_riemann := @_root_.OAI.EuclideanRamsey.lattice_riemann
