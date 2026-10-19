-- Prove2me | solution 1 for OAI.EuclideanRamsey.stencil_weighted_riemann
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T03:26:44.7407+00:00
-- url     : https://prove2.me/submissions/0431f927-f777-472d-abff-61dc6559cb28

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/EuclideanRamsey/StencilConvolution.lean:L107-L201
-- (upload_full_project.md Phase 4): solution for node OAI.EuclideanRamsey.stencil_weighted_riemann. The node keeps its source
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
import Theorems.Thm_OAI_EuclideanRamsey_lattice_riemann_perturb
import Theorems.Thm_OAI_EuclideanRamsey_stencil_taylor_uniform

-- ---- from OAI.Combinatorics.EuclideanRamsey.StencilConvolution ----
namespace OAI

universe uIndex

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
open scoped BigOperators Pointwise
open scoped BigOperators Topology

namespace EuclideanRamsey
open scoped BigOperators

end EuclideanRamsey

namespace EuclideanRamsey
open MeasureTheory Filter
open scoped BigOperators Topology

lemma stencilDifferential_continuous {k : ℕ} (C : Matrix (Fin k) (Fin k) ℝ)
    {b : (Fin k → ℝ) → ℝ} (hb : ContDiff ℝ (⊤ : ℕ∞) b) :
    Continuous (stencilDifferential C b) := by
  have hh := hb.continuous_iteratedFDeriv (m := 2) (by norm_cast)
  unfold stencilDifferential
  fun_prop

lemma stencilDifferential_support {k : ℕ} (C : Matrix (Fin k) (Fin k) ℝ)
    (b : (Fin k → ℝ) → ℝ) : Function.support (stencilDifferential C b) ⊆ tsupport b := by
  intro x hx
  by_contra h
  have hi : x ∉ tsupport (iteratedFDeriv ℝ 2 b) := fun hx => h (tsupport_iteratedFDeriv_subset 2 hx)
  have hz := image_eq_zero_of_notMem_tsupport hi
  exact hx (by simp [stencilDifferential,hz])

lemma stencil_weighted_riemann {ι : Type uIndex} {k d : ℕ} (S : Finset ι)
    (q : ι → ℝ) (v : ι → (Fin k → ℝ)) (C : Matrix (Fin k) (Fin k) ℝ)
    (U : Matrix (Fin d) (Fin k) ℝ)
    (hzero : ∑ γ ∈ S,q γ = 0) (hfirst : ∀ j,∑ γ ∈ S,q γ*v γ j = 0)
    (hsecond : ∀ j l,∑ γ ∈ S,q γ*v γ j*v γ l = C j l)
    {b : (Fin k → ℝ) → ℝ} (hb : ContDiff ℝ (⊤ : ℕ∞) b)
    (hbc : HasCompactSupport b) :
    Tendsto (fun n : ℕ => (∑' δ : Fin k → ℤ,
      max (-((n:ℝ)^2*∑ γ ∈ S,q γ*b (latticeSample n δ+(-(n:ℝ)⁻¹) • v γ))) 0 *
        gradientWeight U (latticeSample n δ))/(n:ℝ)^k) atTop
      (𝓝 (∫ x,max (-stencilDifferential C b x) 0*gradientWeight U x)) := by
  classical
  let f := fun x => max (-stencilDifferential C b x) 0*gradientWeight U x
  let g := fun (n : ℕ) x => max (-((n:ℝ)^2*∑ γ ∈ S,q γ*b (x+(-(n:ℝ)⁻¹) • v γ))) 0*
    gradientWeight U x
  have hc : Continuous f := by
    have hh := stencilDifferential_continuous C hb
    unfold f gradientWeight
    fun_prop
  have hs : Function.support f ⊆ tsupport b := by
    intro x hx
    by_contra h
    have hd : stencilDifferential C b x = 0 := by
      by_contra hh
      exact h (stencilDifferential_support C b hh)
    exact hx (by simp [f,hd])
  have hfc : HasCompactSupport f := HasCompactSupport.of_support_subset_isCompact hbc hs
  obtain ⟨r,hr,hbr⟩ := hbc.exists_pos_le_norm
  let V := ∑ γ ∈ S,‖v γ‖
  have hV : 0 ≤ V := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hv (γ : ι) (hγ : γ ∈ S) : ‖v γ‖ ≤ V := Finset.single_le_sum (fun _ _ => norm_nonneg _) hγ
  let R := r+V+1
  have hR : 0 < R := by dsimp [R]; linarith
  have hfr : Function.support f ⊆ Metric.closedBall 0 R := by
    intro x hx
    rw [Metric.mem_closedBall,dist_zero_right]
    by_contra h
    have hxr : r < ‖x‖ := by dsimp [R] at h; linarith
    have hnb : x ∉ tsupport b := by
      apply notMem_tsupport_iff_eventuallyEq.mpr
      filter_upwards [(continuous_norm.continuousAt.eventually (eventually_gt_nhds hxr))] with y hy
      exact hbr y hy.le
    exact hnb (hs hx)
  have hgr (n : ℕ) : Function.support (g n) ⊆ Metric.closedBall 0 R := by
    intro x hx
    rw [Metric.mem_closedBall,dist_zero_right]
    by_contra h
    have hRx : R < ‖x‖ := lt_of_not_ge h
    have hz : g n x = 0 := by
      by_cases hn : n = 0
      · simp [g,hn]
      have hn1 : (1:ℝ) ≤ n := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hn)
      have hni : |(n:ℝ)⁻¹| ≤ 1 := by rw [abs_inv,abs_of_nonneg (by positivity)]; exact inv_le_one_of_one_le₀ hn1
      have hsum : ∑ γ ∈ S,q γ*b (x+(-(n:ℝ)⁻¹) • v γ) = 0 := by
        apply Finset.sum_eq_zero
        intro γ hγ
        have hnorm : r ≤ ‖x+(-(n:ℝ)⁻¹) • v γ‖ := by
          have hshift : ‖(-(n:ℝ)⁻¹) • v γ‖ ≤ V := by
            rw [norm_smul,Real.norm_eq_abs,abs_neg]
            exact (mul_le_mul_of_nonneg_right hni (norm_nonneg _)).trans (by simpa using hv γ hγ)
          have hx' : ‖x‖ ≤ ‖x+(-(n:ℝ)⁻¹) • v γ‖+‖(-(n:ℝ)⁻¹) • v γ‖ := by
            simpa only [add_sub_cancel_left] using norm_le_norm_add_norm_sub (x+(-(n:ℝ)⁻¹) • v γ) x
          dsimp [R] at hRx
          linarith
        rw [hbr _ hnorm,mul_zero]
      dsimp only [g]
      rw [hsum]
      simp
    exact hx hz
  obtain ⟨W,hW⟩ := (isCompact_closedBall (0 : Fin k → ℝ) R).exists_bound_of_continuousOn
    (show Continuous (gradientWeight U) by unfold gradientWeight; fun_prop).continuousOn
  obtain ⟨K,hK,hTaylor⟩ := stencil_taylor_uniform S q v C hzero hfirst hsecond hb hbc
  have hW0 : 0 ≤ W := (norm_nonneg _).trans (hW 0 (by simp [hR.le]))
  apply lattice_riemann_perturb f g hc hfc hR hfr hgr (fun n => K*W/(n:ℝ))
  · exact tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  · intro n hn x
    by_cases hx : x ∈ Metric.closedBall (0 : Fin k → ℝ) R
    · have hw : |gradientWeight U x| ≤ W := by simpa [Real.norm_eq_abs] using hW x hx
      have hn0 : (0:ℝ) < n := by exact_mod_cast (by omega : 0 < n)
      have he := hTaylor n hn0 x
      have hm := abs_max_sub_max_le_abs
        (-((n:ℝ)^2*∑ γ ∈ S,q γ*b (x+(-(n:ℝ)⁻¹) • v γ))) (-stencilDifferential C b x) 0
      have hm' : |max (-((n:ℝ)^2*∑ γ ∈ S,q γ*b (x+(-(n:ℝ)⁻¹) • v γ))) 0-
          max (-stencilDifferential C b x) 0| ≤ K/n := by
        apply hm.trans
        simpa only [neg_sub_neg,abs_sub_comm] using he
      dsimp [g,f]
      rw [← sub_mul,abs_mul]
      calc
        _ ≤ (K/n)*W := mul_le_mul hm' hw (abs_nonneg _) (by positivity)
        _ = _ := by ring
    · have hf0 : f x = 0 := by by_contra hh; exact hx (hfr hh)
      have hg0 : g n x = 0 := by by_contra hh; exact hx (hgr n hh)
      rw [hf0,hg0,sub_self,abs_zero]
      positivity

end EuclideanRamsey

namespace EuclideanRamsey
open Filter MeasureTheory
open scoped BigOperators Topology

end EuclideanRamsey

namespace EuclideanRamsey
open scoped BigOperators

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
open scoped BigOperators Pointwise
open scoped BigOperators Topology
open MeasureTheory Filter
open scoped BigOperators Topology


theorem solution.{uIndex} : type_of% @_root_.OAI.EuclideanRamsey.stencil_weighted_riemann.{uIndex} := @_root_.OAI.EuclideanRamsey.stencil_weighted_riemann.{uIndex}
