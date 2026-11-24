-- Prove2me | solution 1 for GlobalTheory.QCoh.Qcqs.exists_pow_smul_eq_zero_of_isCompact
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:18:28.040252+00:00
-- url     : https://prove2.me/submissions/10081ac0-76b6-4814-9b9a-165301c68568

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsQuasicoherentOfForallExistsAffine
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsSmulEqMapOfIsCompactOfIsQuasiSeparated
import Theorems.Thm_GlobalTheory_QCoh_Qcqs_exists_smul_eq_zero_of_isCompact
import Theorems.Thm_GlobalTheory_QCoh_Qcqs_subsingleton_sections_of_eq_bot
import Theorems.Thm_P2M_GlobalTheory_QCoh_Qcqs_section_eq_zero_of_res__cd55f0c2510e
import Theorems.Thm_GlobalTheory_QCoh_exists_pow_smul_eq_zero
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
variable {X : Scheme.{u}} (F : X.Modules) {U V W : X.Opens}
variable [F.IsQuasicoherent]
namespace GlobalTheory.QCoh.Qcqs
theorem _root_.solution (hU : IsCompact (U : Set X)) (f : Γ(X, U))
    (h : V ≤ U) (hV : V = X.basicOpen f) (t : Γ(F, U))
    (ht : F.presheaf.map (homOfLE h).op t = 0) : ∃ n : ℕ, f ^ n • t = 0 := by
  letI (W : Set.Iic U) : Module Γ(X, U) Γ(F, W.1) := resModule F W.2
  letI (W : Set.Iic U) : Module Γ(X, U) Γ(F, W.1 ⊓ V) := resModule F (inf_le_right.trans h)
  obtain ⟨_, ⟨n, rfl⟩, e⟩ := exists_smul_eq_zero_of_isCompact (.powers f) U
    (A := fun W ↦ Γ(F, W.1)) (B := fun W ↦ Γ(F, W.1 ⊓ V))
    (fun {W₁ W₂} h' ↦ resLinearOver F W₂.2 W₁.2 h')
    (fun {W₁ W₂} h' ↦ resLinearOver F _ _ (inf_le_inf_right V h'))
    (fun W ↦ resLinearOver F W.2 _ inf_le_left)
    (fun h' a ↦ (res_res F _ _ a).trans (res_res F _ _ a).symm)
    (fun W hW ↦ subsingleton_sections_of_eq_bot F hW)
    (fun h₁ h₂ h₃ ↦ section_eq_zero_of_res₂ F h₁ h₂ h₃)
    (fun W hW a ha ↦ by
      obtain ⟨n, hn⟩ := exists_pow_smul_eq_zero F hW (X.presheaf.map (homOfLE (W.2 : W.1 ≤ U)).op f)
        inf_le_left (by rw [X.basicOpen_res, hV]) a ha
      exact ⟨f ^ n, ⟨n, rfl⟩, by rw [← map_pow] at hn; exact hn⟩)
    ⟨U, Set.self_mem_Iic⟩ hU t (by
      change F.presheaf.map (homOfLE inf_le_left).op t = 0
      rw [← res_res F h inf_le_right, ht, map_zero])
  refine ⟨n, ?_⟩
  rw [← res_self_ring le_rfl (f ^ n)]
  exact e
end GlobalTheory.QCoh.Qcqs
