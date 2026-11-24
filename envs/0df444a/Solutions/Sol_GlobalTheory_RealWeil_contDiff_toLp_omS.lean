-- Prove2me | solution 1 for GlobalTheory.RealWeil.contDiff_toLp_omS
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:13:32.983149+00:00
-- url     : https://prove2.me/submissions/cdb0e9c0-6250-4092-a898-94b528597a47

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_RealMetaplecticRepresentation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IteratedLineDerivMemWeylAlg
import Theorems.Thm_GlobalTheory_RealWeil_weylAlg_induction
import Theorems.Thm_GlobalTheory_RealWeil_schwartzToL2_apply
import Theorems.Thm_GlobalTheory_RealWeil_toLp_dRho_omS

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
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {γ : E → G}
    (hγ : ∀ a b, ContDiff ℝ ∞ fun t => (pr (γ t) : Matrix (l ⊕ l) (l ⊕ l) ℝ) a b)
    (h5 : ∀ f : Sch l, ContDiff ℝ ∞ fun t => om (γ t) (f.toLp 2 volume)) {A : Sch l →L[ℂ] Sch l} (hA : A ∈ weylAlg l)
    (f : Sch l) : ContDiff ℝ ∞ fun t => schwartzToL2 l (A (omS (γ t) f)) := by
  revert f
  refine weylAlg_induction (P := fun A => ∀ f, ContDiff ℝ ∞ fun t => schwartzToL2 l (A (omS (γ t) f))) ?_ ?_ ?_ ?_ ?_ hA
  · intro f
    simpa only [h4, ContinuousLinearMap.one_apply, schwartzToL2_apply] using h5 f
  · intro A w ih f
    simp only [toLp_dRho_omS h3 h4, coe_smul]
    refine ContDiff.sum fun a _ => ContDiff.fun_smul ?_ (ih _)
    simp only [mulVec, dotProduct, Matrix.neg_apply, Matrix.mul_apply, transpose_apply]
    exact ContDiff.sum fun b _ => ContDiff.mul (ContDiff.neg (ContDiff.sum fun c _ => ContDiff.mul
      (ContDiff.sum fun d _ => contDiff_const.mul (hγ _ _)) contDiff_const)) contDiff_const
  · intro f
    simp only [ContinuousLinearMap.zero_apply]
    exact contDiff_const
  · intro A B hA hB f
    simp only [ContinuousLinearMap.add_apply, map_add]
    exact (hA f).add (hB f)
  · intro c A hA f
    simp only [ContinuousLinearMap.smul_apply, map_smul]
    exact (hA f).const_smul c
end GlobalTheory.RealWeil
