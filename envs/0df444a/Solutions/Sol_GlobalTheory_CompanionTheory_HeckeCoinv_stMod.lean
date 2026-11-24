-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HeckeCoinv.stMod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T13:29:27.688818+00:00
-- url     : https://prove2.me/submissions/e7489e9b-fed8-4c50-a4e6-2fd30f2694a9

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_InhabitedFinite
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_ModularityStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_HeckeCoinv_cnt_self_pos
import Theorems.Thm_GlobalTheory_CompanionTheory_HeckeCoinv_exists_phi
import Theorems.Thm_GlobalTheory_CompanionTheory_HeckeCoinv_inner_phi
import Theorems.Thm_GlobalTheory_CompanionTheory_HeckeCoinv_adj
import Theorems.Thm_GlobalTheory_CompanionTheory_HeckeCoinv_exists_rho
import Theorems.Thm_CompanionTheory_D_gk_admitted_word_cons
import Theorems.Thm_CompanionTheory_D_gk_admitted_word_nil
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] CompanionTheory.D.gk.admitted.word_cons
attribute [local simp] CompanionTheory.D.gk.admitted.word_nil



set_option autoImplicit false
open CompanionTheory.Rg.Fl
open scoped InnerProductSpace ComplexConjugate
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HeckeCoinv
namespace GlobalTheory.CompanionTheory.HeckeCoinv
theorem _root_.solution : StMod := by
  intro G _ K hp hsep h
  classical
  obtain ⟨Γ, hfin, hstab, hS⟩ := hsep (h.1 (Finsupp.single ((1 : G) : G ⧸ K) 1)).support
  obtain ⟨N, φ, hs, hφ⟩ := exists_phi (Γ := Γ) (X := G ⧸ K)
  obtain ⟨ρ, hstar, hρ⟩ := exists_rho hp φ hs (adj Γ hp φ hφ)
  refine ⟨N, ρ, hstar, fun h0 => ?_⟩
  set f := h.1 (Finsupp.single ((1 : G) : G ⧸ K) 1) with hf
  have hφf : φ f = 0 := by
    rw [hf, ← hρ, h0]
    rfl
  have hf0 : f = 0 := by
    ext z
    by_contra hz
    have hzS : z ∈ f.support := Finsupp.mem_support_iff.2 hz
    have h1 := inner_phi Γ φ hφ z f
    rw [hφf, inner_zero_right, Finsupp.sum, Finset.sum_eq_single z] at h1
    · have h2 : (cnt Γ z z : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (cnt_self_pos z).ne'
      exact mul_ne_zero hz h2 h1.symm
    · intro y hy hyz
      have : IsEmpty {γ : Γ // γ • z = y} := ⟨fun γ => hyz (hS z hzS y hy γ.1 γ.2).symm⟩
      have h0 : cnt Γ z y = 0 := Nat.card_of_isEmpty
      simp [h0]
    · intro hnot
      exact absurd hzS hnot
  apply Subtype.ext
  refine Finsupp.lhom_ext fun a b => ?_
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective a
  have h1 : Finsupp.single (g : G ⧸ K) b = b • lam K g (Finsupp.single ((1 : G) : G ⧸ K) 1) := by
    rw [lam_single]
    have : g • ((1 : G) : G ⧸ K) = (g : G ⧸ K) := by
      show ((g * 1 : G) : G ⧸ K) = _
      simp
    rw [this]
    simp
  rw [h1, map_smul, comm_lam, ← hf, hf0]
  simp
end GlobalTheory.CompanionTheory.HeckeCoinv
