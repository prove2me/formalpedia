-- Prove2me | solution 1 for GlobalTheory.QCoh.Qcqs.exists_pow_smul_eq_res_of_qcqs
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:18:27.345969+00:00
-- url     : https://prove2.me/submissions/d70f62b4-3028-424c-929a-8fa3e27f59b5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsQuasicoherentOfForallExistsAffine
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsSmulEqMapOfIsCompactOfIsQuasiSeparated
import Theorems.Thm_GlobalTheory_QCoh_Qcqs_exists_smul_eq_map_of_isCompact_of_isQuasiSeparated
import Theorems.Thm_GlobalTheory_QCoh_Qcqs_subsingleton_sections_of_eq_bot
import Theorems.Thm_P2M_GlobalTheory_QCoh_Qcqs_section_eq_zero_of_res__cd55f0c2510e
import Theorems.Thm_P2M_GlobalTheory_QCoh_Qcqs_exists_section_glue__f48d90dc2ee5
import Theorems.Thm_GlobalTheory_QCoh_exists_pow_smul_eq_res
import Theorems.Thm_GlobalTheory_QCoh_exists_pow_smul_eq_zero
import Theorems.Thm_GlobalTheory_QCoh_germLinear_apply
import Theorems.Thm_GlobalTheory_QCoh_resBasicOpen_apply
import Theorems.Thm_GlobalTheory_QCoh_resLinear_apply
import Theorems.Thm_GlobalTheory_QCoh_res_res
import Theorems.Thm_GlobalTheory_QCoh_res_res_ring
import Theorems.Thm_GlobalTheory_QCoh_res_self
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.QCoh.germLinear_apply
attribute [local simp] GlobalTheory.QCoh.resBasicOpen_apply
attribute [local simp] GlobalTheory.QCoh.resLinear_apply



set_option autoImplicit false
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
universe u
noncomputable section
open GlobalTheory GlobalTheory.QCoh GlobalTheory.QCoh.Qcqs
variable {X : Scheme.{u}} (F : X.Modules) {U V W : X.Opens}
variable [F.IsQuasicoherent]
namespace GlobalTheory.QCoh.Qcqs
theorem _root_.solution (hU : IsCompact (U : Set X))
    (hU' : IsQuasiSeparated (U : Set X)) (f : Γ(X, U)) (h : V ≤ U) (hV : V = X.basicOpen f)
    (s : Γ(F, V)) : ∃ (n : ℕ) (t : Γ(F, U)),
      X.presheaf.map (homOfLE h).op f ^ n • s = F.presheaf.map (homOfLE h).op t := by
  letI (W : Set.Iic U) : Module Γ(X, U) Γ(F, W.1) := resModule F W.2
  letI (W : Set.Iic U) : Module Γ(X, U) Γ(F, W.1 ⊓ V) := resModule F (inf_le_right.trans h)
  obtain ⟨_, ⟨n, rfl⟩, t, e⟩ := exists_smul_eq_map_of_isCompact_of_isQuasiSeparated (.powers f) U
    (A := fun W ↦ Γ(F, W.1)) (B := fun W ↦ Γ(F, W.1 ⊓ V))
    (fun {W₁ W₂} h' ↦ resLinearOver F W₂.2 W₁.2 h')
    (fun {W₁ W₂} h' ↦ resLinearOver F _ _ (inf_le_inf_right V h'))
    (fun W ↦ resLinearOver F W.2 _ inf_le_left)
    (fun h' a ↦ (res_res F _ _ a).trans (res_res F _ _ a).symm)
    (fun h₁ h₂ b ↦ res_res F _ _ b)
    (fun W hW ↦ subsingleton_sections_of_eq_bot F hW)
    (fun W hW ↦ subsingleton_sections_of_eq_bot F (by simp [hW]))
    (fun h₁ h₂ h₃ ↦ section_eq_zero_of_res₂ F h₁ h₂ h₃)
    (fun h₁ h₂ h₃ ↦ section_eq_zero_of_res₂ F (inf_le_inf_right V h₁) (inf_le_inf_right V h₂)
      ((inf_le_inf_right V h₃).trans (inf_sup_right _ _ _).le))
    (fun h₁ h₂ h₃ ↦ exists_section_glue₂ F h₁ h₂ h₃)
    (fun W hW a ha ↦ by
      obtain ⟨n, hn⟩ := exists_pow_smul_eq_zero F hW (X.presheaf.map (homOfLE (W.2 : W.1 ≤ U)).op f)
        inf_le_left (by rw [X.basicOpen_res, hV]) a ha
      exact ⟨f ^ n, ⟨n, rfl⟩, by rw [← map_pow] at hn; exact hn⟩)
    (fun W hW b ↦ by
      obtain ⟨n, a, hn⟩ := exists_pow_smul_eq_res F hW (X.presheaf.map (homOfLE (W.2 : W.1 ≤ U)).op f)
        (V := W.1 ⊓ V) inf_le_left (by rw [X.basicOpen_res, hV]) b
      exact ⟨f ^ n, ⟨n, rfl⟩, a, by rw [res_res_ring (show W.1 ≤ U from W.2), ← map_pow] at hn; exact hn⟩)
    ⟨U, Set.self_mem_Iic⟩ hU hU' (F.presheaf.map (homOfLE inf_le_right).op s)
  refine ⟨n, t, ?_⟩
  have e' : X.presheaf.map (homOfLE (inf_le_left : U ⊓ V ≤ U)).op (f ^ n) •
      F.presheaf.map (homOfLE inf_le_right).op s =
      F.presheaf.map (homOfLE inf_le_left).op t := e
  have := congr(F.presheaf.map (homOfLE (le_inf h le_rfl)).op $e')
  rwa [F.map_smul, res_res, res_res, res_res_ring, res_self, map_pow] at this
end GlobalTheory.QCoh.Qcqs
