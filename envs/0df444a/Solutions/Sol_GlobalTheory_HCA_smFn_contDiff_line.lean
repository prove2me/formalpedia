-- Prove2me | solution 1 for GlobalTheory.HCA.smFn_contDiff_line
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T01:21:22.198532+00:00
-- url     : https://prove2.me/submissions/5ce62166-552b-4e3b-9134-8345fd5ca8df

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsExpLieAlgebraComplexUnits
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_Casimir
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraRegularity_ExpHaar
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraInvariance_Compact
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavin
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_ParametricIntegral
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_BoundedDerivFunctionalContDiffExpLine
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
open GlobalTheory.HCA MeasureTheory GroundTheory.Automorphic
open scoped ContDiff
open GlobalTheory GlobalTheory.HCA
namespace GlobalTheory.HCA
theorem _root_.solution :
    ∀ (𝔸 : Type) [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸] (G : Subgroup 𝔸ˣ) (𝔤 : Submodule ℝ 𝔸) (h : IsExpLieAlgebra G 𝔤) (d : ℕ) (b : Module.Basis (Fin d) ℝ 𝔤) [MeasurableSpace G] [BorelSpace G] (μ : Measure G), μ.IsHaarMeasure → ∀ (S : Submodule ℂ (G → ℂ)), (∀ f ∈ S, Continuous f) → (∀ f ∈ S, ∀ g, (fun y => f (g * y)) ∈ S) → ∀ K : Set G, IsCompact K → ∀ Λ : List (Fin d) → (G → ℂ) → ℂ, SmFn h b μ S K Λ → ∀ l i, ∀ f ∈ S, ContDiff ℝ ∞ (fun t : ℝ => Λ l fun y => f (h.expG (t • b i) * y)) ∧ ∀ (p : ℕ) (s : ℝ), iteratedDeriv p (fun t : ℝ => Λ l fun y => f (h.expG (t • b i) * y)) s = Λ (List.replicate p i ++ l) fun y => f (h.expG (s • b i) * y) := by
  intro 𝔸 _ _ _ _ G 𝔤 h d b _ _ μ _ S _ hS K _ Λ hΛ l i f hf
  have hd : ∀ (l : List (Fin d)) (s : ℝ), HasDerivAt (fun t : ℝ => Λ l fun y => f (h.expG (t • b i) * y))
      (Λ (i :: l) fun y => f (h.expG (s • b i) * y)) s := by
    intro l s
    have h1 := hΛ.der l i _ (hS f hf (h.expG (s • b i)))
    have h2 : HasDerivAt (fun t : ℝ => Λ l fun y => f (h.expG ((s + t) • b i) * y))
        (Λ (i :: l) fun y => f (h.expG (s • b i) * y)) (s - s) := by
      rw [sub_self]
      simpa only [h.expG_add_smul, mul_assoc] using h1
    have h3 := h2.comp_sub_const s s
    simpa only [add_sub_cancel] using h3
  have hi : ∀ p : ℕ, iteratedDeriv p (fun t : ℝ => Λ l fun y => f (h.expG (t • b i) * y))
      = fun s : ℝ => Λ (List.replicate p i ++ l) fun y => f (h.expG (s • b i) * y) := by
    intro p
    induction p with
    | zero => simp
    | succ p ih =>
      rw [iteratedDeriv_succ, ih]
      funext s
      rw [(hd _ s).deriv, List.replicate_succ, List.cons_append]
  refine ⟨contDiff_of_differentiable_iteratedDeriv fun m _ => ?_, fun p s => by rw [hi p]⟩
  rw [hi m]
  exact fun s => (hd _ s).differentiableAt
end GlobalTheory.HCA
