-- Prove2me | solution 1 for OAI.EuclideanRamsey.lattice_riemann_perturb
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T03:22:06.691778+00:00
-- url     : https://prove2.me/submissions/775d2e72-7096-4ec0-b320-3bda98dedf7b

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/EuclideanRamsey/RationalConvolution.lean:L55-L82
-- (upload_full_project.md Phase 4): solution for node OAI.EuclideanRamsey.lattice_riemann_perturb. The node keeps its source
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
import Theorems.Thm_OAI_EuclideanRamsey_lattice_riemann
import Theorems.Thm_OAI_EuclideanRamsey_lattice_tsum_eq_grid

-- ---- from OAI.Combinatorics.EuclideanRamsey.RationalConvolution ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe uGroup uIndex

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
open scoped BigOperators Pointwise Topology
open MeasureTheory Filter

namespace EuclideanRamsey
open MeasureTheory Filter
open scoped BigOperators Pointwise Topology

lemma bounded_grid_finite {k n : ℕ} (hn : n ≠ 0) {s : Set (Fin k → ℝ)}
    (hs : Bornology.IsBounded s) :
    (s ∩ (n:ℝ)⁻¹ • (realLattice k : Set (Fin k → ℝ))).Finite := by
  rw [← Submodule.coe_pointwise_smul, ZSpan.smul _ (inv_ne_zero (by exact_mod_cast hn))]
  exact ZSpan.setFinite_inter _ hs

lemma lattice_sum_perturb_bound {k n : ℕ} (hn : n ≠ 0) {s : Set (Fin k → ℝ)}
    (hs : Bornology.IsBounded s) (f g : (Fin k → ℝ) → ℝ)
    (hf : Function.support f ⊆ s) (hg : Function.support g ⊆ s)
    (ε : ℝ) (hb : ∀ x, |f x-g x| ≤ ε) :
    |((∑' γ : Fin k → ℤ, f (latticeSample n γ))/(n:ℝ)^k)-
      ((∑' γ : Fin k → ℤ, g (latticeSample n γ))/(n:ℝ)^k)| ≤
      ε * ((Nat.card ↑(s ∩ (n:ℝ)⁻¹ • (realLattice k : Set (Fin k → ℝ))) : ℝ)/(n:ℝ)^k) := by
  let G := ↑(s ∩ (n:ℝ)⁻¹ • (realLattice k : Set (Fin k → ℝ)))
  let : Fintype G := (bounded_grid_finite hn hs).fintype
  rw [lattice_tsum_eq_grid hn s f hf,lattice_tsum_eq_grid hn s g hg,
    ← sub_div,abs_div,abs_of_nonneg (by positivity : 0 ≤ (n:ℝ)^k)]
  have hsum : |(∑' x : G,f x)-(∑' x : G,g x)| ≤ (Nat.card G : ℝ)*ε := by
    rw [tsum_fintype,tsum_fintype,← Finset.sum_sub_distrib]
    calc
      _ ≤ ∑ x : G, |f x-g x| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _x : G, ε := Finset.sum_le_sum (fun x hx => hb x)
      _ = _ := by simp [Nat.card_eq_fintype_card]
  calc
    _ ≤ ((Nat.card G : ℝ)*ε)/(n:ℝ)^k := div_le_div_of_nonneg_right hsum (by positivity)
    _ = _ := by ring

theorem lattice_riemann_perturb {k : ℕ} (f : (Fin k → ℝ) → ℝ)
    (g : ℕ → (Fin k → ℝ) → ℝ) (hf : Continuous f) (hfc : HasCompactSupport f)
    {R : ℝ} (hR : 0 < R)
    (hfs : Function.support f ⊆ Metric.closedBall 0 R)
    (hgs : ∀ n, Function.support (g n) ⊆ Metric.closedBall 0 R)
    (ε : ℕ → ℝ) (hε : Tendsto ε atTop (𝓝 0))
    (hbound : ∀ n, 1 ≤ n → ∀ x, |g n x-f x| ≤ ε n) :
    Tendsto (fun n : ℕ => (∑' γ : Fin k → ℤ, g n (latticeSample n γ))/(n:ℝ)^k)
      atTop (𝓝 (∫ x, f x)) := by
  let s := Metric.closedBall (0 : Fin k → ℝ) R
  have hfront : volume (frontier s) = 0 :=
    measure_mono_null Metric.frontier_closedBall_subset_sphere
      (volume.addHaar_sphere_of_ne_zero 0 hR.ne')
  have hc := tendsto_card_div_pow_atTop_volume s Metric.isBounded_closedBall
    measurableSet_closedBall hfront
  have hlim := hε.mul hc
  rw [zero_mul] at hlim
  have hdiff : Tendsto (fun n : ℕ =>
      (∑' γ : Fin k → ℤ, g n (latticeSample n γ))/(n:ℝ)^k-
      (∑' γ : Fin k → ℤ, f (latticeSample n γ))/(n:ℝ)^k) atTop (𝓝 0) := by
    apply squeeze_zero_norm' _ hlim
    filter_upwards [eventually_ge_atTop 1] with n hn
    simpa only [Real.norm_eq_abs,Fintype.card_fin] using
      lattice_sum_perturb_bound (by omega : n ≠ 0) Metric.isBounded_closedBall
        (g n) f (hgs n) hfs (ε n) (hbound n hn)
  convert hdiff.add (lattice_riemann hf hfc) using 1
  · ext n; ring
  · simp

end EuclideanRamsey

open scoped BigOperators Pointwise
namespace EuclideanRamsey

end EuclideanRamsey

open scoped BigOperators Topology
namespace EuclideanRamsey

end EuclideanRamsey

namespace EuclideanRamsey
open scoped BigOperators Pointwise

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
open scoped BigOperators Pointwise Topology
open MeasureTheory Filter
open MeasureTheory Filter
open scoped BigOperators Pointwise Topology


theorem solution : type_of% @_root_.OAI.EuclideanRamsey.lattice_riemann_perturb := @_root_.OAI.EuclideanRamsey.lattice_riemann_perturb
