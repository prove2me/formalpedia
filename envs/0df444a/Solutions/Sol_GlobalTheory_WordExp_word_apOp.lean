-- Prove2me | solution 1 for GlobalTheory.WordExp.word_apOp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T01:11:53.040233+00:00
-- url     : https://prove2.me/submissions/a8268c50-6131-4726-838a-0eb3bb2d440a

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ZeroMemSolSet
import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllRegCheck
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_Casimir
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraRegularity_ExpHaar
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraInvariance_Compact
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CoefVFContDiffOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RightDerivWordExpCoordsDifferentialOperator
import Theorems.Thm_GlobalTheory_WordExp_isSmoothFun_foldr
import Theorems.Thm_GlobalTheory_HCA_apOp_zero_one
import Theorems.Thm_GlobalTheory_VFComp_vectorField_comp
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_AdL_apply
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_Ad_one
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_coe_Ad
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_coe_bracket
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_coe_rightDerivEnd
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_coe_rightTranslateEnd
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_contDiff_comp_coordEquiv
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_derivLie_apply
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_coe_restrict_apply
import Theorems.Thm_GroundTheory_Automorphic_conjCME_apply
import Theorems.Thm_P2M_GroundTheory_Automorphic_IsExpLieAlgebra_rightUAction___d9062316eb7b
import Theorems.Thm_P2M_GroundTheory_Automorphic_IsExpLieAlgebra_uAction___195cbae0e32a
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.IsExpLieAlgebra.AdL_apply
attribute [local simp] GroundTheory.Automorphic.IsExpLieAlgebra.Ad_one
attribute [local simp] GroundTheory.Automorphic.IsExpLieAlgebra.coe_Ad
attribute [local simp] GroundTheory.Automorphic.IsExpLieAlgebra.coe_bracket
attribute [local simp] GroundTheory.Automorphic.IsExpLieAlgebra.coe_rightDerivEnd
attribute [local simp] GroundTheory.Automorphic.IsExpLieAlgebra.coe_rightTranslateEnd
attribute [local simp] GroundTheory.Automorphic.IsExpLieAlgebra.derivLie_apply
attribute [local simp] GroundTheory.Automorphic.UnitaryRep.coe_restrict_apply
attribute [local simp] GroundTheory.Automorphic.conjCME_apply
attribute [local simp] P2M_GroundTheory_Automorphic_IsExpLieAlgebra_rightUAction___d9062316eb7b
attribute [local simp] P2M_GroundTheory_Automorphic_IsExpLieAlgebra_uAction___195cbae0e32a



set_option autoImplicit false
open ZetaZeros.D.EllReg GlobalTheory.HCA MeasureTheory GroundTheory.Automorphic
open scoped ContDiff
namespace GlobalTheory.WordExp
theorem _root_.solution : ∀ (𝔸 : Type) [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸] (G : Subgroup 𝔸ˣ) (𝔤 : Submodule ℝ 𝔸) (h : IsExpLieAlgebra G 𝔤) (d : ℕ) (b : Module.Basis (Fin d) ℝ 𝔤) (r : ℝ) (c : 𝔤 → Fin d → E d → ℝ), ((∀ X j, ContDiffOn ℝ ∞ (c X j) (Metric.ball 0 r)) ∧ (∀ x ∈ Metric.ball (0 : E d) r, ∀ ξ : E d, ξ ≠ 0 → ∃ i, ∑ j, c (b i) j x * ξ j ≠ 0) ∧ ∀ f : G → ℂ, h.IsSmoothFun f → ∀ X : 𝔤, ∀ x ∈ Metric.ball (0 : E d) r, h.rightDeriv X f (h.expG (coordEquiv b (x))) = ∑ j, (c X j x : ℂ) * fderiv ℝ (fun y => f (h.expG (coordEquiv b (y)))) x (ev j)) → ∀ l : List 𝔤, ∃ a : (n : ℕ) → (Fin n → Fin d) → E d → ℂ, (∀ n w, ContDiffOn ℝ ∞ (a n w) (Metric.ball 0 r)) ∧ ∀ f : G → ℂ, h.IsSmoothFun f → ∀ x ∈ Metric.ball (0 : E d) r, l.foldr h.rightDeriv f (h.expG (coordEquiv b (x))) = apOp l.length a (fun y => f (h.expG (coordEquiv b (y)))) x := by
  intro 𝔸 _ _ _ _ G 𝔤 h d b r c hyp l
  obtain ⟨hc, -, hX⟩ := hyp
  induction l with
  | nil =>
    refine ⟨fun _ _ _ => 1, fun _ _ => contDiffOn_const, fun f _ x _ => ?_⟩
    simp only [List.foldr_nil, List.length_nil]
    rw [apOp_zero_one]
  | cons X l ih =>
    obtain ⟨a, ha, hl⟩ := ih
    have hcX : ∀ j, ContDiffOn ℝ ∞ (fun x : E d => ((c X j x : ℝ) : ℂ)) (Metric.ball 0 r) := fun j =>
      Complex.ofRealCLM.contDiff.comp_contDiffOn (hc X j)
    obtain ⟨a', ha', -, hcomp⟩ := GlobalTheory.VFComp.vectorField_comp d l.length (Metric.ball 0 r)
      Metric.isOpen_ball a (fun j x => ((c X j x : ℝ) : ℂ)) ha hcX
    refine ⟨a', ha', fun f hf x hx => ?_⟩
    simp only [List.foldr_cons, List.length_cons]
    have hF := GlobalTheory.WordExp.isSmoothFun_foldr h hf l
    rw [hX _ hF X x hx]
    have heq : (fun y : E d => l.foldr h.rightDeriv f (h.expG (coordEquiv b y))) =ᶠ[nhds x]
        apOp l.length a (fun y => f (h.expG (coordEquiv b y))) := by
      filter_upwards [Metric.isOpen_ball.mem_nhds hx] with y hy using hl f hf y hy
    have hu : ContDiffOn ℝ ∞ (fun y : E d => f (h.expG (coordEquiv b y))) (Metric.ball 0 r) := by
      have := h.contDiff_comp_coordEquiv hf 1 b
      simp only [one_mul] at this
      exact this.contDiffOn
    rw [heq.fderiv_eq]
    exact hcomp _ hu x hx
end GlobalTheory.WordExp
