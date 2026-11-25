-- Prove2me | solution 1 for GlobalTheory.metaplecticGaussianNormalised
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T07:55:28.196564+00:00
-- url     : https://prove2.me/submissions/42e1ee27-855a-4c14-9c73-9c54f3869c36

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_MetaplecticRepresentation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IteratedLineDerivMemWeylAlg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsEqTransposeMulDiagonalMul
import Definitions.Def_CompanionTheory_ThickeningEstimates_LieGroupReduction_MetaplecticRepresentation_RealMetaplecticRepresentationHolds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MetaplecticGaussianNormalised
import Theorems.Thm_CompanionTheory_ThKF_E_Impl_dRho
import Theorems.Thm_CompanionTheory_ThKR_Mp_MpA_ann_gs
import Theorems.Thm_CompanionTheory_ThKR_Mp_MpA_dd_one
import Theorems.Thm_CompanionTheory_ThKR_Mp_MpA_gs_zero
import Theorems.Thm_CompanionTheory_ThKR_Mp_continuous_om
import Theorems.Thm_CompanionTheory_ThKR_Mp_cover_of
import Theorems.Thm_CompanionTheory_ThKR_Mp_ddNe
import Theorems.Thm_CompanionTheory_ThKR_Mp_ker
import Theorems.Thm_CompanionTheory_ThKR_Mp_mkElt
import Theorems.Thm_CompanionTheory_ThKR_Mp_nrmUp
import Theorems.Thm_CompanionTheory_ThKR_Mp_omS_nrm
import Theorems.Thm_CompanionTheory_ThKR_Mp_om_rho
import Theorems.Thm_CompanionTheory_ThKR_Mp_om_sch
import Theorems.Thm_CompanionTheory_ThKR_Mp_secDer
import Theorems.Thm_CompanionTheory_ThKR_Mp_secEx_of
import Theorems.Thm_CompanionTheory_ThKR_Mp_surj_of
import Theorems.Thm_CompanionTheory_ThKR_Mp_topG
import Theorems.Thm_GroundTheory_Global_gaussianSchwartz_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Global.gaussianSchwartz_apply



set_option autoImplicit false
open MeasureTheory Matrix Complex GlobalTheory.RealWeil
open scoped Real SchwartzMap ComplexConjugate
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : ∀ (l : Type) [Fintype l] [DecidableEq l], ∃ (G : Type) (_ : Group G) (_ : TopologicalSpace G) (_ : IsTopologicalGroup G) (pr : G →* Matrix.symplecticGroup l ℝ) (om : G →* (L2 l ≃ₗᵢ[ℂ] L2 l)) (omS : G →* (Sch l →L[ℂ] Sch l)) (φ : Sch l), IsCoveringMap pr ∧ Function.Surjective pr ∧ (∃ ε : G, ε ≠ 1 ∧ (∀ g, pr g = 1 ↔ g = 1 ∨ g = ε) ∧ ∀ f, om ε f = -f) ∧ (∀ f : L2 l, Continuous fun g => om g f) ∧ (∀ (g : G) (w : l ⊕ l → ℝ) (f : L2 l), om g (rho w f) = rho ((pr g : Matrix (l ⊕ l) (l ⊕ l) ℝ) *ᵥ w) (om g f)) ∧ (∀ (g : G) (f : Sch l), om g (f.toLp 2) = (omS g f).toLp 2) ∧ (∀ x : EuclideanSpace ℝ l, φ x = cexp (-π * ((x.ofLp ⬝ᵥ x.ofLp : ℝ) : ℂ))) ∧ (∀ j : l, dRho (Pi.single (.inl j) 1) φ = I • dRho (Pi.single (.inr j) 1) φ) ∧ ∀ (g : G) (P : Matrix l l ℂ), (∀ a b, P a b = ((pr g).1 (.inl a) (.inl b) : ℂ) - I * ((pr g).1 (.inl a) (.inr b) : ℂ)) → omS g φ 0 ^ 2 * P.det = 1 := by
  intro l _ _
  have hS : CompanionTheory.ThKR.Mp.SecEx l := CompanionTheory.ThKR.Mp.secEx_of CompanionTheory.ThKR.Mp.mkElt CompanionTheory.ThKR.Mp.nrmUp
  have hO : CompanionTheory.ThKR.Mp.Surj l := CompanionTheory.ThKR.Mp.surj_of CompanionTheory.ThKR.Mp.ddNe hS
  have hC : CompanionTheory.ThKR.Mp.Cover l :=
    CompanionTheory.ThKR.Mp.cover_of CompanionTheory.ThKR.Mp.topG hO CompanionTheory.ThKR.Mp.ker hS CompanionTheory.ThKR.Mp.secDer
  haveI : IsTopologicalGroup (CompanionTheory.ThKR.Mp.G l) := CompanionTheory.ThKR.Mp.topG
  refine ⟨CompanionTheory.ThKR.Mp.G l, inferInstance, inferInstance, inferInstance, CompanionTheory.ThKR.Mp.pr, CompanionTheory.ThKR.Mp.om,
    CompanionTheory.ThKR.Mp.omS, CompanionTheory.ThKR.Mp.MpA.gs l, hC, hO, CompanionTheory.ThKR.Mp.ker, CompanionTheory.ThKR.Mp.continuous_om,
    CompanionTheory.ThKR.Mp.om_rho, CompanionTheory.ThKR.Mp.om_sch, ?_, ?_, ?_⟩
  · intro x
    rw [CompanionTheory.ThKR.Mp.MpA.gs, GroundTheory.Global.gaussianSchwartz_apply]
    have e : ‖x‖ ^ 2 = x.ofLp ⬝ᵥ x.ofLp := by
      rw [EuclideanSpace.norm_sq_eq]
      simp [dotProduct, sq]
    rw [e, Complex.ofReal_exp]
    push_cast
    ring_nf
  · intro j
    have h := CompanionTheory.ThKR.Mp.MpA.ann_gs (l := l) j
    have e1 : ((1 : CompanionTheory.ThKR.Mp.Sp l) : CompanionTheory.ThKR.Mp.Mat l) = 1 := rfl
    rw [e1, one_mulVec, one_mulVec] at h
    exact h
  · intro g P hP
    have h := CompanionTheory.ThKR.Mp.omS_nrm g 1 (CompanionTheory.ThKR.Mp.MpA.gs l) CompanionTheory.ThKR.Mp.MpA.ann_gs
    have e1 : ((1 : CompanionTheory.ThKR.Mp.Sp l) : CompanionTheory.ThKR.Mp.Mat l) = 1 := rfl
    rw [e1, Matrix.mul_one, CompanionTheory.ThKR.Mp.MpA.gs_zero, CompanionTheory.ThKR.Mp.MpA.dd_one, one_pow, one_mul] at h
    have eP : P = CompanionTheory.ThKR.Mp.upperParabolic (CompanionTheory.ThKR.Mp.pr g).1 := by
      ext a b; rw [hP]; rfl
    rw [eP]
    exact h
end GlobalTheory
