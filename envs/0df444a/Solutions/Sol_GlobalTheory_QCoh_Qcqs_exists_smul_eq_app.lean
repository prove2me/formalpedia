-- Prove2me | solution 1 for GlobalTheory.QCoh.Qcqs.exists_smul_eq_app
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T18:11:20.06473+00:00
-- url     : https://prove2.me/submissions/d4f39b00-9a21-4fc5-b163-21e0a785c915

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsQuasicoherentOfForallExistsAffine
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsSmulEqMapOfIsCompactOfIsQuasiSeparated
import Theorems.Thm_GlobalTheory_QCoh_Qcqs_exists_smul_eq_map_of_isCompact_of_isQuasiSeparated
import Theorems.Thm_GlobalTheory_QCoh_Qcqs_subsingleton_sections_of_eq_bot
import Theorems.Thm_P2M_GlobalTheory_QCoh_Qcqs_section_eq_zero_of_res__cd55f0c2510e
import Theorems.Thm_P2M_GlobalTheory_QCoh_Qcqs_exists_section_glue__f48d90dc2ee5
import Theorems.Thm_GlobalTheory_QCoh_Qcqs_app_res
import Theorems.Thm_GlobalTheory_QCoh_res_res
import Theorems.Thm_GlobalTheory_QCoh_res_self_ring


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
universe u
noncomputable section
open GlobalTheory GlobalTheory.QCoh GlobalTheory.QCoh.Qcqs
variable {X : Scheme.{u}} {F G : X.Modules} (φ : F ⟶ G) {U V W : X.Opens}
namespace GlobalTheory.QCoh.Qcqs
theorem _root_.solution (hU : IsCompact (U : Set X)) (hU' : IsQuasiSeparated (U : Set X))
    (S : Submonoid Γ(X, U))
    (hker : ∀ (V : X.Opens) (h : V ≤ U), IsAffineOpen V → ∀ a : Γ(F, V), φ.app V a = 0 →
      ∃ s ∈ S, X.presheaf.map (homOfLE h).op s • a = 0)
    (hsurj : ∀ (V : X.Opens) (h : V ≤ U), IsAffineOpen V → ∀ b : Γ(G, V),
      ∃ s ∈ S, ∃ a : Γ(F, V), X.presheaf.map (homOfLE h).op s • b = φ.app V a)
    (b : Γ(G, U)) : ∃ s ∈ S, ∃ a : Γ(F, U), s • b = φ.app U a := by
  letI (W : Set.Iic U) : Module Γ(X, U) Γ(F, W.1) := resModule F W.2
  letI (W : Set.Iic U) : Module Γ(X, U) Γ(G, W.1) := resModule G W.2
  obtain ⟨s, hs, a, e⟩ := exists_smul_eq_map_of_isCompact_of_isQuasiSeparated S U
    (A := fun W ↦ Γ(F, W.1)) (B := fun W ↦ Γ(G, W.1))
    (fun {W₁ W₂} h' ↦ resLinearOver F W₂.2 W₁.2 h')
    (fun {W₁ W₂} h' ↦ resLinearOver G W₂.2 W₁.2 h')
    (fun W ↦ appLinearOver φ W.2)
    (fun h' a ↦ app_res φ h' a)
    (fun h₁ h₂ b ↦ res_res G _ _ b)
    (fun W hW ↦ subsingleton_sections_of_eq_bot F hW)
    (fun W hW ↦ subsingleton_sections_of_eq_bot G hW)
    (fun h₁ h₂ h₃ ↦ section_eq_zero_of_res₂ F h₁ h₂ h₃)
    (fun h₁ h₂ h₃ ↦ section_eq_zero_of_res₂ G h₁ h₂ h₃)
    (fun h₁ h₂ h₃ ↦ exists_section_glue₂ F h₁ h₂ h₃)
    (fun W hW ↦ hker W.1 W.2 hW) (fun W hW ↦ hsurj W.1 W.2 hW) ⟨U, Set.self_mem_Iic⟩ hU hU' b
  refine ⟨s, hs, a, ?_⟩
  rw [← res_self_ring le_rfl s]
  exact e
end GlobalTheory.QCoh.Qcqs
