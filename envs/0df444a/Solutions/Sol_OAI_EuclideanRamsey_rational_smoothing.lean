-- Prove2me | solution 1 for OAI.EuclideanRamsey.rational_smoothing
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T03:28:12.585959+00:00
-- url     : https://prove2.me/submissions/cb4b6474-bc34-4908-a0ef-8c2ec0f3bc9b

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/EuclideanRamsey/StencilConvolution.lean:L266-L308
-- (upload_full_project.md Phase 4): solution for node OAI.EuclideanRamsey.rational_smoothing. The node keeps its source
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
import Theorems.Thm_OAI_EuclideanRamsey_compact_smoothing
import Theorems.Thm_OAI_EuclideanRamsey_latticeSample_finite_support
import Theorems.Thm_OAI_EuclideanRamsey_lattice_riemann
import Theorems.Thm_OAI_EuclideanRamsey_rationalize_convolution
import Theorems.Thm_OAI_EuclideanRamsey_stencil_weighted_riemann

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

end EuclideanRamsey

namespace EuclideanRamsey
open Filter MeasureTheory
open scoped BigOperators Topology

theorem exists_discrete_smoothing {k d : ℕ} (S : Finset (Fin k → ℤ))
    (q : (Fin k → ℤ) → ℝ) (C : Matrix (Fin k) (Fin k) ℝ) (U : Matrix (Fin d) (Fin k) ℝ)
    (hzero : ∑ γ ∈ S,q γ = 0) (hfirst : ∀ j,∑ γ ∈ S,q γ*(γ j:ℝ) = 0)
    (hsecond : ∀ j l,∑ γ ∈ S,q γ*(γ j:ℝ)*(γ l:ℝ) = C j l)
    {b : (Fin k → ℝ) → ℝ} (hb : ContDiff ℝ (⊤ : ℕ∞) b)
    (hbc : HasCompactSupport b) (hI : 0 < ∫ x,b x)
    {η : ℝ} (hη : (∫ x,max (-stencilDifferential C b x) 0*gradientWeight U x) < η*∫ x,b x) :
    ∃ (n : ℕ) (a : (Fin k → ℤ) → ℝ), 1 ≤ n ∧ Function.HasFiniteSupport a ∧
      0 < (∑' γ,a γ)/(n:ℝ)^2 ∧
      (∑' δ,max (-(∑ γ ∈ S,q γ*a (δ-γ))) 0*gradientWeight U (latticeSample n δ)) <
        η*((∑' γ,a γ)/(n:ℝ)^2) := by
  have hZ := lattice_riemann hb.continuous hbc
  have hN := stencil_weighted_riemann S q (fun γ j => (γ j:ℝ)) C U hzero hfirst hsecond hb hbc
  have he := hN.eventually_lt (tendsto_const_nhds.mul hZ) hη
  have hp := (tendsto_const_nhds.eventually_lt hZ hI)
  obtain ⟨n,hn,hp,he⟩ := (eventually_ge_atTop 1 |>.and (hp.and he)).exists
  let a := fun γ : Fin k → ℤ => b (latticeSample n γ)
  have hnf : (0:ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have ha : Function.HasFiniteSupport a := latticeSample_finite_support (by omega) hbc
  have hshift (δ γ : Fin k → ℤ) : latticeSample n δ+(-(n:ℝ)⁻¹) • (fun j => (γ j:ℝ)) =
      latticeSample n (δ-γ) := by
    ext j
    simp only [latticeSample,Pi.add_apply,Pi.smul_apply,smul_eq_mul,Pi.sub_apply,Int.cast_sub]
    ring
  simp only [hshift] at he
  have hscale (δ : Fin k → ℤ) :
      max (-((n:ℝ)^2*∑ γ ∈ S,q γ*a (δ-γ))) 0*gradientWeight U (latticeSample n δ) =
      (n:ℝ)^2*(max (-(∑ γ ∈ S,q γ*a (δ-γ))) 0*gradientWeight U (latticeSample n δ)) := by
    rw [← mul_neg,← mul_zero ((n:ℝ)^2),← mul_max_of_nonneg _ _ (sq_nonneg (n:ℝ))]
    rw [mul_assoc, mul_zero]
  change (∑' δ,max (-((n:ℝ)^2*∑ γ ∈ S,q γ*a (δ-γ))) 0*
    gradientWeight U (latticeSample n δ))/(n:ℝ)^k < η*((∑' γ,a γ)/(n:ℝ)^k) at he
  simp only [hscale,tsum_mul_left] at he
  have hp' : 0 < ∑' γ,a γ := (div_pos_iff_of_pos_right (pow_pos hnf k)).mp hp
  refine ⟨n,a,hn,ha,div_pos hp' (sq_pos_of_pos hnf),?_⟩
  have hh : (n:ℝ)^2*(∑' δ,max (-(∑ γ ∈ S,q γ*a (δ-γ))) 0*
      gradientWeight U (latticeSample n δ)) < η*(∑' γ,a γ) := by
    apply (div_lt_div_iff_of_pos_right (pow_pos hnf k)).mp
    simpa only [mul_div_assoc] using he
  rw [← mul_div_assoc]
  apply (lt_div_iff₀ (sq_pos_of_pos hnf)).mpr
  simpa only [mul_comm] using hh

end EuclideanRamsey

namespace EuclideanRamsey
open scoped BigOperators

lemma cosetPushforward_mul {k : ℕ} (Λ : AddSubgroup (Lattice k)) (ν b : LatticeRing k)
    (hν : cosetPushforward Λ ν = 0) : cosetPushforward Λ (ν*b) = 0 := by
  have he : AddMonoidAlgebra.mapDomain (QuotientAddGroup.mk' Λ) ν = 0 := by
    apply AddMonoidAlgebra.coeff_injective
    exact hν
  change (AddMonoidAlgebra.mapDomain (QuotientAddGroup.mk' Λ) (ν*b)).coeff = 0
  rw [AddMonoidAlgebra.mapDomain_mul,he,zero_mul]
  rfl

theorem rational_smoothing {k d s : ℕ} (hd : 1 ≤ d)
    (Λ : Fin s → AddSubgroup (Lattice k)) (ν : LatticeRing k)
    (C : Matrix (Fin k) (Fin k) ℚ) (U : Matrix (Fin d) (Fin k) ℝ)
    (hC : C.IsSymm) (hU : U*(C.map (Rat.cast : ℚ → ℝ))*U.transpose = (1 : Matrix (Fin d) (Fin d) ℝ))
    (hcos : ∀ i,cosetPushforward (Λ i) ν = 0)
    (hzero : mass ν = 0) (hfirst : ∀ j,firstMoment ν j = 0)
    (hsecond : ∀ j l,secondMoment ν j l = C j l)
    (η : ℝ) (hη : 0 < η) :
    ∃ (n : ℕ) (μ : LatticeRing k) (ζ : ℚ), 1 ≤ n ∧ 0 < ζ ∧
      (∀ i,cosetPushforward (Λ i) μ = 0) ∧ mass μ = 0 ∧
      (∀ j,firstMoment μ j = 0) ∧
      (∀ j l,secondMoment μ j l/(n:ℚ)^2 = ζ*C j l) ∧
      (∑' δ : Lattice k,max (-(μ.coeff δ:ℝ)) 0*gradientWeight U (latticeSample n δ)) < η*ζ := by
  classical
  have hC' : (C.map (Rat.cast : ℚ → ℝ)).IsSymm := by
    ext j l
    change (C l j:ℝ) = (C j l:ℝ)
    exact congrArg Rat.cast (congrFun (congrFun hC j) l)
  obtain ⟨b,hb,hbc,hb0,hbI,hbη⟩ := compact_smoothing k d hd (C.map (Rat.cast : ℚ → ℝ)) U hC' hU η hη
  have hz : ∑ γ ∈ ν.coeff.support,(ν.coeff γ:ℝ) = 0 := by
    exact_mod_cast hzero
  have hf (j : Fin k) : ∑ γ ∈ ν.coeff.support,(ν.coeff γ:ℝ)*(γ j:ℝ) = 0 := by
    exact_mod_cast hfirst j
  have hs (j l : Fin k) : ∑ γ ∈ ν.coeff.support,(ν.coeff γ:ℝ)*(γ j:ℝ)*(γ l:ℝ) = (C j l:ℝ) := by
    exact_mod_cast hsecond j l
  obtain ⟨n,a,hn,ha,hap,han⟩ := exists_discrete_smoothing ν.coeff.support
    (fun γ => (ν.coeff γ:ℝ)) (C.map (Rat.cast : ℚ → ℝ)) U hz hf hs hb hbc hbI hbη
  obtain ⟨p,hp0,hpη⟩ := rationalize_convolution ν (fun δ => gradientWeight U (latticeSample n δ))
    ((n:ℝ)^2) η ha hap han
  let ζ : ℚ := mass p/(n:ℚ)^2
  have hζ : (ζ:ℝ) = ((mass p : ℚ):ℝ)/(n:ℝ)^2 := by simp [ζ]
  have hζ0 : 0 < ζ := by
    have hp' : (0:ℝ) < (ζ:ℝ) := by simpa only [hζ,mass] using hp0
    exact_mod_cast hp'
  refine ⟨n,ν*p,ζ,hn,hζ0,fun i => cosetPushforward_mul (Λ i) ν p (hcos i),?_,?_,?_,?_⟩
  · simp [hzero]
  · intro j
    simp [firstMoment_mul,hzero,hfirst]
  · intro j l
    simp only [secondMoment_mul,hzero,hfirst,hsecond,zero_mul,zero_add,add_zero]
    dsimp [ζ]
    ring
  · simpa only [hζ,mass] using hpη

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
open scoped BigOperators


theorem solution : type_of% @_root_.OAI.EuclideanRamsey.rational_smoothing := @_root_.OAI.EuclideanRamsey.rational_smoothing
