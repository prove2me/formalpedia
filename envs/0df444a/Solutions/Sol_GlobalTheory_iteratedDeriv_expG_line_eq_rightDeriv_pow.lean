-- Prove2me | solution 1 for GlobalTheory.iteratedDeriv_expG_line_eq_rightDeriv_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T01:22:34.78288+00:00
-- url     : https://prove2.me/submissions/ea23cc81-d5c9-4238-b85c-5341a6186edb

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_Casimir
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraRegularity_ExpHaar
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraInvariance_Compact
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavin
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_ParametricIntegral
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IteratedDerivExpGLineEqRightDerivPow
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_AdL_apply
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_Ad_one
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_coe_Ad
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_coe_bracket
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_coe_rightDerivEnd
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_coe_rightTranslateEnd
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_derivLie_apply
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_expG_add_smul
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
open MeasureTheory GroundTheory.Automorphic
open scoped ContDiff
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ (𝔸 : Type) [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸] (G : Subgroup 𝔸ˣ) (𝔤 : Submodule ℝ 𝔸) (h : IsExpLieAlgebra G 𝔤) (f : G → ℂ), h.IsSmoothFun f → ∀ (X : 𝔤) (g : G) (n : ℕ), ContDiff ℝ ∞ (fun t : ℝ => f (g * h.expG (t • X))) ∧ ∀ s : ℝ, iteratedDeriv n (fun t : ℝ => f (g * h.expG (t • X))) s = (List.replicate n X).foldr h.rightDeriv f (g * h.expG (s • X)) := by
  intro 𝔸 _ _ _ _ G 𝔤 h f hf X g n
  have hd : ∀ (f : G → ℂ), h.IsSmoothFun f → ∀ s : ℝ,
      HasDerivAt (fun t : ℝ => f (g * h.expG (t • X))) (h.rightDeriv X f (g * h.expG (s • X))) s := by
    intro f hf s
    have h1 := h.hasDerivAt_rightDeriv hf X (g * h.expG (s • X))
    have h2 : HasDerivAt (fun t : ℝ => f (g * h.expG ((s + t) • X)))
        (h.rightDeriv X f (g * h.expG (s • X))) (s - s) := by
      rw [sub_self]
      simpa only [h.expG_add_smul, mul_assoc] using h1
    have h3 := h2.comp_sub_const s s
    simpa only [add_sub_cancel] using h3
  have hi : ∀ (n : ℕ) (f : G → ℂ), h.IsSmoothFun f →
      iteratedDeriv n (fun t : ℝ => f (g * h.expG (t • X)))
        = fun s : ℝ => (List.replicate n X).foldr h.rightDeriv f (g * h.expG (s • X)) := by
    intro n
    induction n with
    | zero => intro f _; simp
    | succ n ih =>
      intro f hf
      rw [iteratedDeriv_succ']
      have hderiv : deriv (fun t : ℝ => f (g * h.expG (t • X)))
          = fun t : ℝ => h.rightDeriv X f (g * h.expG (t • X)) := by
        funext s; exact (hd f hf s).deriv
      rw [hderiv, ih _ (h.isSmoothFun_rightDeriv hf X)]
      funext s
      rw [List.replicate_succ', List.foldr_append]
      rfl
  refine ⟨?_, fun s => by rw [hi n f hf]⟩
  have hc := (h.isSmoothFun_iff).1 hf g
  exact hc.comp (contDiff_id.smul contDiff_const)
end GlobalTheory
