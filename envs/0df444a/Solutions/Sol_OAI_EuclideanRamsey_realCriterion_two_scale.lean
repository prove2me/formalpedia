-- Prove2me | solution 1 for OAI.EuclideanRamsey.realCriterion_two_scale
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T03:36:45.057981+00:00
-- url     : https://prove2.me/submissions/91b5ff3e-61ce-471e-a8c4-92e845d7a08e

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/EuclideanRamsey/GramCompletion.lean:L251-L287
-- (upload_full_project.md Phase 4): solution for node OAI.EuclideanRamsey.realCriterion_two_scale. The node keeps its source
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
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_AdicLifting
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_TensorPresentation
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_SignedRows
import Theorems.Thm_OAI_EuclideanRamsey_finite_lattice_identity
import Theorems.Thm_OAI_EuclideanRamsey_rational_smoothing
import Theorems.Thm_OAI_EuclideanRamsey_realCriterion_lattice
import Theorems.Thm_OAI_EuclideanRamsey_two_scale_of_signed_rows

-- ---- from OAI.Combinatorics.EuclideanRamsey.GramCompletion ----
namespace OAI

universe uIndex uRow uColor

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
open scoped TensorProduct BigOperators

open Matrix
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator
namespace EuclideanRamsey
end EuclideanRamsey

namespace EuclideanRamsey
open Matrix
end EuclideanRamsey

namespace EuclideanRamsey
open scoped BigOperators
lemma evaluation_coset_pushforward {k : ℕ} (φ : Lattice k →+ ℝ)
    (μ : LatticeRing k) (hμ : cosetPushforward φ.ker μ=0) (n : ℝ) :
    μ.coeff.mapDomain (fun x => φ x/n)=0 := by
  let f := QuotientAddGroup.lift φ.ker φ le_rfl
  have he : (fun x => φ x/n) = (fun y => f y/n) ∘ QuotientAddGroup.mk' φ.ker := by
    funext x
    rfl
  rw [he,Finsupp.mapDomain_comp]
  change Finsupp.mapDomain _ (cosetPushforward φ.ker μ) = 0
  rw [hμ,Finsupp.mapDomain_zero]

lemma lattice_affine_evaluation {k d s : ℕ} (a : Fin s → Space d)
    (w : Fin k → AffineVector d) (i : Fin s) (γ : Lattice k) (n : ℝ) :
    ((rowEvaluation a i).comp (Fintype.linearCombination ℚ w)) (rationalize γ)/n =
      (∑ j,(γ j:ℝ)/n*w j none)+
        ∑ α,a i α*(∑ j,(γ j:ℝ)/n*w j (some α)) := by
  simp only [LinearMap.comp_apply,Fintype.linearCombination_apply,map_sum,map_smul,
    rationalize,AddMonoidHom.coe_mk,Rat.smul_def,rowEvaluation,LinearMap.coe_mk,
    AddHom.coe_mk,Fintype.sum_option,realAugmented,one_mul]
  change (∑ j,(γ j:ℝ)*(w j none+∑ α,a i α*w j (some α)))/n = _
  simp only [div_eq_mul_inv,mul_add,add_mul,Finset.sum_add_distrib,Finset.sum_mul,Finset.mul_sum]
  congr 1
  · apply Finset.sum_congr rfl
    intro j _
    ring
  · rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro α _
    apply Finset.sum_congr rfl
    intro j _
    ring

lemma scaled_second_moment {k d : ℕ} (μ : LatticeRing k) (n : ℕ)
    (C : Matrix (Fin k) (Fin k) ℚ) (U : Matrix (Fin d) (Fin k) ℝ)
    (ζ : ℚ) (hsecond : ∀ j l,secondMoment μ j l/(n:ℚ)^2 = ζ*C j l)
    (α β : Fin d) :
    μ.coeff.sum (fun γ q => (q:ℝ)*(∑ j,U α j*latticeSample n γ j)*
      (∑ l,U β l*latticeSample n γ l)) =
      (ζ:ℝ)*(U*(C.map (Rat.cast : ℚ → ℝ))*U.transpose) α β := by
  have hm (j l : Fin k) : ∑ γ ∈ μ.coeff.support,
      (μ.coeff γ:ℝ)*latticeSample n γ j*latticeSample n γ l = (ζ:ℝ)*(C j l:ℝ) := by
    have h := congrArg (Rat.cast : ℚ → ℝ) (hsecond j l)
    simp only [Rat.cast_div,Rat.cast_pow,Rat.cast_natCast,Rat.cast_mul,secondMoment,
      Finsupp.sum,Rat.cast_sum,Rat.cast_intCast] at h
    rw [← h,Finset.sum_div]
    apply Finset.sum_congr rfl
    intro γ hγ
    simp only [latticeSample]
    ring
  simp only [Finsupp.sum,Finset.mul_sum,Finset.sum_mul]
  rw [Finset.sum_comm]
  conv_lhs => arg 2; ext j; rw [Finset.sum_comm]
  have hr (j l : Fin k) : (∑ γ ∈ μ.coeff.support,
      (μ.coeff γ:ℝ)*(U α j*latticeSample n γ j)*(U β l*latticeSample n γ l)) =
      U α j*U β l*((ζ:ℝ)*(C j l:ℝ)) := by
    rw [← hm,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro γ hγ
    ring
  simp only [hr]
  change _ = (ζ:ℝ)*(∑ l,(∑ j,U α j*(C j l:ℝ))*U β l)
  simp only [Finset.mul_sum,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro l _
  ring

theorem realCriterion_two_scale {s d : ℕ} (a : Fin s → Space d)
    (hd : 1 ≤ d) (hs : 1 ≤ s) (h : RealCriterion a) (η : ℝ) (hη : 0 < η) :
    ∃ (ℓ : ℕ),1 ≤ ℓ ∧ ∃ (f g : Fin s → Space ℓ),
      (∀ i j,‖f i-f j‖^2=‖a i-a j‖^2) ∧
      (∀ i j,‖g i-g j‖^2=(η/(1+η))*‖a i-a j‖^2) ∧
      ∀ i,∃ σ : Equiv.Perm (Fin ℓ),∀ x,g i (σ x)=f i x := by
  classical
  obtain ⟨k,w,C,hk,hC,hU,hquot⟩ := realCriterion_lattice a hd h
  let U : Matrix (Fin d) (Fin k) ℝ := fun α j => w j (some α)
  let φ (i : Fin s) : Lattice k →+ ℝ :=
    ((rowEvaluation a i).comp (Fintype.linearCombination ℚ w)).toAddMonoidHom.comp rationalize
  let Λ (i : Fin s) := (φ i).ker
  obtain ⟨ν,hcos,hzero,hfirst,hsecond⟩ :=
    finite_lattice_identity k s hk hs Λ C hC hquot
  obtain ⟨n,μ,ζ,hn,hζ,hcos,_,_,hmom,hneg⟩ :=
    rational_smoothing hd Λ ν C U hC hU hcos hzero hfirst hsecond η hη
  let v (γ : Lattice k) : ℝ := ∑ j,(γ j:ℝ)/(n:ℝ)*w j none
  let g (γ : Lattice k) (α : Fin d) : ℝ := ∑ j,U α j*latticeSample n γ j
  have heval (i : Fin s) : μ.coeff.mapDomain (fun γ => v γ+∑ α,a i α*g γ α)=0 := by
    have he := evaluation_coset_pushforward (φ i) μ (hcos i) (n:ℝ)
    have heq : (fun γ => φ i γ/(n:ℝ)) = (fun γ => v γ+∑ α,a i α*g γ α) := by
      funext γ
      simpa only [φ,v,g,U,latticeSample,mul_comm,AddMonoidHom.comp_apply,LinearMap.toAddMonoidHom_coe] using lattice_affine_evaluation a w i γ (n:ℝ)
    rwa [heq] at he
  have hmoment (α β : Fin d) : μ.coeff.sum (fun γ q => (q:ℝ)*g γ α*g γ β) =
      (ζ:ℝ)*(if α=β then 1 else 0) := by
    have he := scaled_second_moment μ n C U ζ hmom α β
    rw [hU] at he
    exact he
  have hnegative : μ.coeff.sum (fun γ q => max (-(q:ℝ)) 0*(∑ α,(g γ α)^2)) < η*(ζ:ℝ) := by
    rw [tsum_eq_sum (s := μ.coeff.support)] at hneg
    · exact hneg
    · intro γ hγ
      have hz := Finsupp.notMem_support_iff.mp hγ
      simp [hz]
  exact two_scale_of_signed_rows hd hs a v g μ.coeff (ζ:ℝ) η
    (by exact_mod_cast hζ) hη heval hmoment hnegative

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
open scoped TensorProduct BigOperators
open Matrix
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator
open scoped BigOperators


theorem solution : type_of% @_root_.OAI.EuclideanRamsey.realCriterion_two_scale := @_root_.OAI.EuclideanRamsey.realCriterion_two_scale
