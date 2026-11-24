-- Prove2me | solution 1 for GlobalTheory.SmGL.IndDual.inductionContragredient
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:32:56.863502+00:00
-- url     : https://prove2.me/submissions/13f862c4-e2aa-4c73-a070-55214279ee5a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_HasFiniteLengthOfIsIrreducible
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IwahoriProjSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LeviIntegralFacts
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsOpenNormalisedSubgroupSubset
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsInvariantForm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IntegralIntegralGLMulRightComplexProductSigma
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_InductionContragredient
import Theorems.Thm_GlobalTheory_SmGL_IndDual_pair_bijective
import Theorems.Thm_GlobalTheory_SmGL_IndDual_exists_equiv
import Theorems.Thm_GlobalTheory_SmGL_IndDual_integral_KO_mul_right
import Theorems.Thm_GlobalTheory_SmGL_IsSmoothChar_comp
import Theorems.Thm_GlobalTheory_SmGL_IsSubquotient_trans
import Theorems.Thm_GlobalTheory_SmGL_LeviInt_levi_integral_facts
import Theorems.Thm_GlobalTheory_SmGL_continuous_leviEmb
import Theorems.Thm_GlobalTheory_SmGL_exists_open_normalised_subgroup_subset
import Theorems.Thm_GlobalTheory_SmGL_isSmoothChar_deltaHalf
import Theorems.Thm_GlobalTheory_SmGL_isSmooth_comp
import Theorems.Thm_GlobalTheory_SmGL_isSmooth_twist
import Theorems.Thm_GlobalTheory_SmGL_modulus_pos
import Theorems.Thm_GlobalTheory_SmGL_val_deltaHalf


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL Topology
open GlobalTheory GlobalTheory.SmGL GlobalTheory.SmGL.IndDual
namespace GlobalTheory.SmGL.IndDual
theorem _root_.solution : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k], GlobalTheory.SmGL.InductionContragredient k := by
  intro k _ _ _ _ α n m _ _ _ _ _ _ e _ _ μ _ W _ _ ρ hρ
  obtain ⟨-, hK1, hK2, -, -, hcont, hP, -, hPK⟩ := GlobalTheory.SmGL.LeviInt.levi_integral_facts k α n m e
  let σ : Representation ℂ (parab k e) W := (twist ρ (deltaHalf k m)).comp (leviProj k e)
  let τ : Representation ℂ (parab k e) (smoothPart ρ.dual) :=
    (twist (contra ρ) (deltaHalf k m)).comp (leviProj k e)
  let B : smoothPart ρ.dual →ₗ[ℂ] Module.Dual ℂ W := Submodule.subtype _
  have hσ : IsSmooth σ := isSmooth_comp (isSmooth_twist hρ (isSmoothChar_deltaHalf k)) _ hcont
  have hB : ∀ p w' w, B (τ p w') (σ p w) = (modulus k m (leviProj k e p) : ℂ) * B w' w := by
    intro p w' w
    show ((deltaHalf k m (leviProj k e p) : ℂ) • (contra ρ (leviProj k e p) w' : Module.Dual ℂ W))
      ((deltaHalf k m (leviProj k e p) : ℂ) • ρ (leviProj k e p) w) = _ * (w' : Module.Dual ℂ W) w
    rw [LinearMap.smul_apply, map_smul, contra_apply, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel,
      map_one, Module.End.one_apply, smul_smul, val_deltaHalf, ← Complex.ofReal_mul,
      Real.mul_self_sqrt (modulus_pos k _).le, smul_eq_mul]
  have hinv : ∀ g f' f, pair μ SplitFlip.isCompact_KO σ τ B (smInd _ τ g f') (smInd _ σ g f) =
      pair μ SplitFlip.isCompact_KO σ τ B f' f := fun g f' f =>
    GlobalTheory.SmGL.IndDual.integral_KO_mul_right k α n m e μ _ (continuous_pair σ τ B f' f)
      (fun p x => by rw [f'.1.2 p x, f.1.2 p x, hB]) g
  obtain ⟨hi, hs⟩ := pair_bijective μ SplitFlip.isCompact_KO σ τ B SplitFlip.isOpen_KO hP hPK
    (GlobalTheory.SmGL.exists_open_normalised_subgroup_subset k n) hσ (fun p hp w' w => by rw [hB, hK2 _ (hK1 p hp)]; simp) Subtype.val_injective
    (fun l hl => by
      rw [Submodule.range_subtype]
      have hc : Continuous fun g : Levi k m => (⟨leviEmb k e g⁻¹, leviEmb_mem_parab k e _⟩ : parab k e) :=
        ((continuous_leviEmb k e).comp continuous_inv).subtype_mk _
      refine mem_smoothPart_of_nhds ?_
      filter_upwards [(hc.tendsto' 1 1 (by simp)).eventually hl,
        IsOpen.mem_nhds (isSmoothChar_deltaHalf k (m := m)) (one_mem _)] with g h1 h2
      refine LinearMap.ext fun w => Eq.trans ?_ (h1 w)
      have h3 : deltaHalf k m g⁻¹ = 1 := inv_mem h2
      show l (ρ g⁻¹ w) = l (twist ρ (deltaHalf k m) (leviProj k e _) w)
      rw [leviProj_leviEmb, twist_apply, h3, Units.val_one, one_smul]) hinv
  exact exists_equiv μ SplitFlip.isCompact_KO σ τ B hinv hi hs
end GlobalTheory.SmGL.IndDual
