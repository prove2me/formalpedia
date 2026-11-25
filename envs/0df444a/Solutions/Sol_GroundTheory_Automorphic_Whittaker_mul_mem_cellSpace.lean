-- Prove2me | solution 1 for GroundTheory.Automorphic.Whittaker.mul_mem_cellSpace
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T02:28:38.793045+00:00
-- url     : https://prove2.me/submissions/6f79f2f8-8001-405c-8311-e024c9074e63

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerLSpace
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerOrbit
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerGroups
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerCells
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerRelevance
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerDistribution
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_bruhatCell_eq_of_mem
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_cellMinor_smul
import Theorems.Thm_GroundTheory_Automorphic_GLnLocal_quotientEquivLattice_mk
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_continuous_cellMinor
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_indicator_mul_mem
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_sub_mem_relSpan
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_transl_apply
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_transl_mem_supportedIn
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.GLnLocal.quotientEquivLattice_mk
attribute [local simp] GroundTheory.Automorphic.Whittaker.transl_apply



set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Whittaker
open Set Topology MulAction Matrix DoubleCoset ValuativeRel
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] {n : ℕ}
attribute [local instance] biAction
variable [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
attribute [local instance] totallyDisconnectedSpace_localField
attribute [local instance] continuousSMul_biAction
variable (ψ₀ : AddChar F ℂ)
namespace GroundTheory.Automorphic.Whittaker
theorem _root_.solution {g : GL (Fin n) F} {U : Set (GL (Fin n) F)}
    (hUinv : ∀ k : NN F n, ∀ x ∈ U, k • x ∈ U) (hUge : U ⊆ cellGe g)
    {V : Set (Fin n → F)} (hV : IsClopen V) {r : GL (Fin n) F → ℂ}
    (hr : r ∈ relSpan (chi (n := n) ψ₀) U ⊔ (supportedIn U ⊓ vanishingOn (cellLe g))) :
    (fun x => (cellMinor (bruhatCell g) ⁻¹' V).indicator 1 x * r x) ∈
      relSpan (chi (n := n) ψ₀) U ⊔ (supportedIn U ⊓ vanishingOn (cellLe g)) := by
  set w := bruhatCell g
  set A : Set (GL (Fin n) F) := cellMinor w ⁻¹' V
  have hA : IsClopen A := hV.preimage (continuous_cellMinor w)
  set φ : GL (Fin n) F → ℂ := A.indicator 1
  set W := relSpan (chi (n := n) ψ₀) U ⊔ (supportedIn U ⊓ vanishingOn (cellLe g))
  have hmul : ∀ f, (fun x => φ x * f x) = LinearMap.mulLeft ℂ φ f := fun f => rfl
  suffices h : W ≤ W.comap (LinearMap.mulLeft ℂ φ) by
    rw [hmul]
    exact h hr
  refine sup_le ?_ ?_
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨k, f, hf, rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_comap, map_sub, map_smul]
    have hφf : (fun x => φ x * f x) ∈ supportedIn U := indicator_mul_mem hA hf
    have e : LinearMap.mulLeft ℂ φ (transl k f) - chi ψ₀ k • LinearMap.mulLeft ℂ φ f =
        (transl k (fun x => φ x * f x) - chi ψ₀ k • (fun x => φ x * f x)) +
          (LinearMap.mulLeft ℂ φ (transl k f) - transl k (fun x => φ x * f x)) := by
      rw [← hmul]
      abel
    rw [e]
    refine add_mem (le_sup_left (b := supportedIn U ⊓ vanishingOn (cellLe g))
      (sub_mem_relSpan _ k hφf)) (le_sup_right (a := relSpan (chi (n := n) ψ₀) U) ⟨?_, ?_⟩)
    · exact sub_mem (indicator_mul_mem hA (transl_mem_supportedIn hUinv k hf))
        (transl_mem_supportedIn hUinv k hφf)
    · intro x hxC
      show φ x * transl k f x - transl k (fun x => φ x * f x) x = 0
      simp only [transl_apply]
      by_cases hxU : x ∈ U
      · have hxw : bruhatCell x = w := bruhatCell_eq_of_mem (hUge hxU) hxC
        have hp : cellMinor w (k⁻¹ • x) = cellMinor w x := cellMinor_smul hxw k⁻¹
        have hAx : (k⁻¹ • x ∈ A) ↔ (x ∈ A) := by
          show cellMinor w (k⁻¹ • x) ∈ V ↔ cellMinor w x ∈ V
          rw [hp]
        have : φ (k⁻¹ • x) = φ x := by
          show A.indicator 1 (k⁻¹ • x) = A.indicator 1 x
          by_cases hxA : x ∈ A
          · rw [Set.indicator_of_mem (hAx.2 hxA), Set.indicator_of_mem hxA]
            rfl
          · rw [Set.indicator_of_notMem (fun h => hxA (hAx.1 h)), Set.indicator_of_notMem hxA]
        rw [this, sub_self]
      · have hk : k⁻¹ • x ∉ U := fun h => hxU (by simpa using hUinv k _ h)
        have h0 : f (k⁻¹ • x) = 0 := Function.notMem_support.1 fun h => hk (hf.2 h)
        simp [h0]
  · rintro k ⟨hkU, hkC⟩
    refine le_sup_right (a := relSpan (chi (n := n) ψ₀) U) ⟨indicator_mul_mem hA hkU, ?_⟩
    intro x hx
    show φ x * k x = 0
    rw [hkC x hx, mul_zero]
end GroundTheory.Automorphic.Whittaker
