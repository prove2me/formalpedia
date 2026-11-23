-- Prove2me | solution 1 for GlobalTheory.RealWeil.dRho_comm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:21:19.724872+00:00
-- url     : https://prove2.me/submissions/a31c03ec-296c-4f7f-a33e-bf29e4fe2a32

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_RealMetaplecticRepresentation
import Theorems.Thm_GlobalTheory_RealWeil_dRho_apply

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
open scoped Real RealInnerProductSpace ContDiff
open GlobalTheory GlobalTheory.RealWeil
variable {l : Type} [Fintype l]
namespace GlobalTheory.RealWeil
theorem _root_.solution (w w' : l ⊕ l → ℝ) :
    dRho w * dRho w' - dRho w' * dRho w = (2 * π * I * sympl w w' : ℂ) • (1 : Sch l →L[ℂ] Sch l) := by
  have key : ∀ (u v : l ⊕ l → ℝ) (f : Sch l) (x : EuclideanSpace ℝ l), fderiv ℝ (dRho v f) x (pPart u) =
      fderiv ℝ (fderiv ℝ f) x (pPart u) (pPart v) + (2 * π * I * (⟪qPart v, pPart u⟫ : ℝ) * f x +
        2 * π * I * (⟪qPart v, x⟫ : ℝ) * fderiv ℝ f x (pPart u)) := by
    intro u v f x
    have e : ⇑(dRho v f) = fun y => fderiv ℝ f y (pPart v) + 2 * π * I * (⟪qPart v, y⟫ : ℝ) * f y :=
      funext (dRho_apply v f)
    have d1 : HasFDerivAt (fderiv ℝ f) (fderiv ℝ (fderiv ℝ f) x) x :=
      (fderivCLM ℂ _ _ f).differentiableAt.hasFDerivAt
    have d2 := d1.clm_apply (hasFDerivAt_const (pPart v) x)
    have d3 := ((ofRealCLM.comp (innerSL ℝ (qPart v))).hasFDerivAt (x := x)).const_mul (2 * π * I : ℂ)
    have d4 := d2.add (d3.mul (f.hasFDerivAt x))
    rw [e]
    refine (congrArg (fun L : EuclideanSpace ℝ l →L[ℝ] ℂ => L (pPart u)) d4.fderiv).trans ?_
    simp
    ring
  ext f x
  have hs : fderiv ℝ (fderiv ℝ f) x (pPart w) (pPart w') = fderiv ℝ (fderiv ℝ f) x (pPart w') (pPart w) :=
    ((f.smooth 2).contDiffAt.isSymmSndFDerivAt (by simp)) _ _
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.mul_apply, SchwartzMap.sub_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.one_apply, SchwartzMap.smul_apply, smul_eq_mul]
  rw [dRho_apply w (dRho w' f), dRho_apply w' (dRho w f), key, key, dRho_apply, dRho_apply, hs]
  simp only [sympl, real_inner_comm (pPart w) (qPart w'), ofReal_sub]
  ring
end GlobalTheory.RealWeil
