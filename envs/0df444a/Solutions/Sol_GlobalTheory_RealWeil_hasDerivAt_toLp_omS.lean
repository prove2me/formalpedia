-- Prove2me | solution 1 for GlobalTheory.RealWeil.hasDerivAt_toLp_omS
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:13:33.639793+00:00
-- url     : https://prove2.me/submissions/ac02c8a9-691e-414b-84fc-d96e7ca446c0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_RealMetaplecticRepresentation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IteratedLineDerivMemWeylAlg
import Theorems.Thm_GlobalTheory_RealWeil_weylAlg_induction
import Theorems.Thm_GlobalTheory_RealWeil_schwartzToL2_apply
import Theorems.Thm_GlobalTheory_RealWeil_toLp_dRho_omS
import Theorems.Thm_GlobalTheory_RealWeil_hasDerivAt_exp_apply
import Theorems.Thm_GlobalTheory_RealWeil_dRho_eq_sum
import Theorems.Thm_GlobalTheory_RealWeil_mul_J_symm
import Theorems.Thm_GlobalTheory_RealWeil_quad_comm


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Complex SchwartzMap LineDeriv Matrix
open scoped Real RealInnerProductSpace ContDiff FourierTransform
open GlobalTheory GlobalTheory.RealWeil
variable {l : Type} [Fintype l]
variable [DecidableEq l]
variable {G : Type} [Group G] {pr : G →* Matrix.symplecticGroup l ℝ} {om : G →* (L2 l ≃ₗᵢ[ℂ] L2 l)}
  {omS : G →* (Sch l →L[ℂ] Sch l)}
namespace GlobalTheory.RealWeil
theorem _root_.solution
    (h3 : ∀ (g : G) (w : l ⊕ l → ℝ) (f : L2 l),
      om g (rho w f) = rho ((pr g : Matrix (l ⊕ l) (l ⊕ l) ℝ) *ᵥ w) (om g f))
    (h4 : ∀ (g : G) (f : Sch l), om g (f.toLp 2 volume) = (omS g f).toLp 2 volume)
    {X : Matrix (l ⊕ l) (l ⊕ l) ℝ} (hX : X ∈ LieAlgebra.Symplectic.sp l ℝ) {γ : ℝ → G} (h0 : γ 0 = 1)
    (hγ : ∀ t, (pr (γ t) : Matrix (l ⊕ l) (l ⊕ l) ℝ) = NormedSpace.exp (t • X))
    (h6 : ∀ f : Sch l, HasDerivAt (fun t => om (γ t) (f.toLp 2 volume)) ((quad X f).toLp 2 volume) 0)
    {A : Sch l →L[ℂ] Sch l} (hA : A ∈ weylAlg l) (f : Sch l) :
    HasDerivAt (fun t => schwartzToL2 l (A (omS (γ t) f))) (schwartzToL2 l (A (quad X f))) 0 := by
  revert f
  refine weylAlg_induction
    (P := fun A => ∀ f, HasDerivAt (fun t => schwartzToL2 l (A (omS (γ t) f))) (schwartzToL2 l (A (quad X f))) 0) ?_ ?_ ?_ ?_ ?_ hA
  · intro f
    simpa only [h4, ContinuousLinearMap.one_apply, schwartzToL2_apply] using h6 f
  · intro A w ih f
    simp only [toLp_dRho_omS h3 h4, hγ, coe_smul]
    have hJ : Matrix.J l ℝ * Xᵀ * Matrix.J l ℝ = X := by
      have h := mul_J_symm hX
      rw [transpose_mul, J_transpose, neg_mul, neg_eq_iff_eq_neg] at h
      rw [h, neg_mul, Matrix.mul_assoc, J_squared]
      simp
    have hd : ∀ a, HasDerivAt
        (fun t : ℝ => ((-(Matrix.J l ℝ * (NormedSpace.exp (t • X))ᵀ * Matrix.J l ℝ)) *ᵥ w) a) (-(X *ᵥ w) a) 0 := by
      intro a
      conv => enter [2]; rw [← hJ]
      simp only [mulVec, dotProduct, Matrix.neg_apply, Matrix.mul_apply, transpose_apply, ← Finset.sum_neg_distrib,
        ← neg_mul]
      exact HasDerivAt.fun_sum fun b _ => HasDerivAt.mul_const (HasDerivAt.fun_sum fun c _ => HasDerivAt.mul_const
        (HasDerivAt.fun_sum fun d _ => (hasDerivAt_exp_apply X _ _).const_mul _) _) _
    refine (HasDerivAt.fun_sum fun a _ => (hd a).fun_smul (ih (dRho (Pi.single a 1) f))).congr_deriv ?_
    have e : dRho w * quad X = quad X * dRho w - dRho (X *ᵥ w) := by
      rw [← quad_comm hX, sub_sub_cancel]
    rw [ContinuousLinearMap.mul_apply, ← ContinuousLinearMap.mul_apply (dRho w), e, dRho_eq_sum w,
      dRho_eq_sum (X *ᵥ w)]
    simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply, map_sum,
      map_smul, ofReal_neg, ofReal_zero, zero_smul, NormedSpace.exp_zero, transpose_one, mul_one, J_squared, neg_neg, one_mulVec,
      h0, map_one, ContinuousLinearMap.one_apply, ContinuousLinearMap.sub_apply, ContinuousLinearMap.mul_apply,
      map_sub, neg_smul, ← sub_eq_add_neg, Finset.sum_sub_distrib]
    simp only [coe_smul]
    rfl
  · intro f
    simp only [ContinuousLinearMap.zero_apply, map_zero]
    exact hasDerivAt_const _ _
  · intro A B hA hB f
    simp only [ContinuousLinearMap.add_apply, map_add]
    exact (hA f).add (hB f)
  · intro c A hA f
    simp only [ContinuousLinearMap.smul_apply, map_smul]
    exact (hA f).const_smul c
end GlobalTheory.RealWeil
