-- Prove2me | solution 1 for GlobalTheory.schwartz_eq_gaussian_of_fderiv_eq_mulVec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:32:42.545707+00:00
-- url     : https://prove2.me/submissions/0fa56912-5f33-4234-b993-7f5bb5e2782e

import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_MetaplecticRepresentation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IteratedLineDerivMemWeylAlg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsEqTransposeMulDiagonalMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzEqGaussianOfFderivEqMulVec

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix Complex GlobalTheory.RealWeil
open scoped Real SchwartzMap ComplexConjugate
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ (l : Type) [Fintype l] [DecidableEq l] (τ : Matrix l l ℂ) (f : Sch l), τ.IsSymm →
      (∀ (a : l) (x : EuclideanSpace ℝ l),
        fderiv ℝ f x (EuclideanSpace.single a 1) = 2 * π * I * (τ *ᵥ fun i => (x i : ℂ)) a * f x) →
      ∀ x : EuclideanSpace ℝ l,
        f x = f 0 * cexp (π * I * ((fun i => (x i : ℂ)) ⬝ᵥ τ *ᵥ fun i => (x i : ℂ))) := by
  intro l _ _ τ f _hτ H x
  set v : l → ℂ := fun i => (x i : ℂ) with hv
  set c : ℂ := v ⬝ᵥ τ *ᵥ v with hc
  have hx : x = ∑ a, x a • EuclideanSpace.single a (1 : ℝ) := by
    conv_lhs => rw [← (EuclideanSpace.basisFun l ℝ).toBasis.sum_repr x]
    simp
  have hD : ∀ t : ℝ, fderiv ℝ f (t • x) x = 2 * π * I * (t * c) * f (t • x) := by
    intro t
    rw [show fderiv ℝ f (t • x) x = fderiv ℝ f (t • x) (∑ a, x a • EuclideanSpace.single a (1 : ℝ)) from
      congrArg _ hx]
    simp only [map_sum, map_smul, H, Complex.real_smul]
    have hvt : (fun i => ((t • x) i : ℂ)) = (t : ℂ) • v := by
      funext i; simp [hv]
    rw [hvt, Matrix.mulVec_smul, hc, dotProduct]
    simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum, Finset.sum_mul, hv]
    refine Finset.sum_congr rfl fun a _ => ?_
    ring
  set φ : ℝ → ℂ := fun t => f (t • x) * cexp (-(π * I * c) * ((t ^ 2 : ℝ) : ℂ)) with hφ
  have hφd : ∀ t : ℝ, HasDerivAt φ 0 t := by
    intro t
    have h1 : HasDerivAt (fun t : ℝ => f (t • x)) (fderiv ℝ f (t • x) ((1 : ℝ) • x)) t :=
      (f.differentiableAt (x := t • x)).hasFDerivAt.comp_hasDerivAt t ((hasDerivAt_id t).smul_const x)
    have h2 : HasDerivAt (fun t : ℝ => cexp (-(π * I * c) * ((t ^ 2 : ℝ) : ℂ)))
        (cexp (-(π * I * c) * ((t ^ 2 : ℝ) : ℂ)) * (-(π * I * c) * (((2 : ℕ) * t ^ (2 - 1) : ℝ) : ℂ))) t :=
      (((hasDerivAt_pow 2 t).ofReal_comp).const_mul _).cexp
    refine (h1.mul h2).congr_deriv ?_
    rw [one_smul, hD]
    push_cast
    ring
  have hconst := is_const_of_deriv_eq_zero (fun t => (hφd t).differentiableAt) (fun t => (hφd t).deriv) 1 0
  simp only [hφ, one_smul, zero_smul, one_pow, ofReal_one, mul_one] at hconst
  norm_num at hconst
  rw [← hconst, mul_assoc, ← Complex.exp_add]
  simp
end GlobalTheory
