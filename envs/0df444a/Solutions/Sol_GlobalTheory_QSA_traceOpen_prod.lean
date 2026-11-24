-- Prove2me | solution 1 for GlobalTheory.QSA.traceOpen_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T20:17:54.588675+00:00
-- url     : https://prove2.me/submissions/e393302e-c8fa-4e01-bb1e-10e89ca7fc2d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TraceOpen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_QuaternionNormOneTraceOpenProd
import Theorems.Thm_GlobalTheory_QSA_TraceOpenProd_glue_fst_snd
import Theorems.Thm_GlobalTheory_QSA_TraceOpenProd_nrm_glue
import Theorems.Thm_GlobalTheory_QSA_TraceOpenProd_nrm_fst
import Theorems.Thm_GlobalTheory_QSA_TraceOpenProd_nrm_snd
import Theorems.Thm_GlobalTheory_QSA_TraceOpenProd_continuous_glue

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain GlobalTheory.QSA
open scoped Quaternion Topology
open GlobalTheory GlobalTheory.QSA
open TraceOpenProd
namespace GlobalTheory.QSA
theorem _root_.solution : ∀ (R₁ R₂ : Type) [CommRing R₁] [TopologicalSpace R₁] [CommRing R₂] [TopologicalSpace R₂]
    (a₁ b₁ : R₁) (a₂ b₂ : R₂), TraceOpen R₁ a₁ b₁ → TraceOpen R₂ a₂ b₂ → TraceOpen (R₁ × R₂) (a₁, a₂) (b₁, b₂) := by
  intro R₁ R₂ _ _ _ _ a₁ b₁ a₂ b₂ h₁ h₂ g hg W hW
  have hW' : glue ⁻¹' W ∈ 𝓝 (fst g, snd g) := by
    apply continuous_glue.continuousAt.preimage_mem_nhds
    rw [glue_fst_snd]; exact hW
  obtain ⟨W₁, hW₁, W₂, hW₂, hsub⟩ := mem_nhds_prod_iff.1 hW'
  have hg₁ : nrm (fst g) = 1 := by rw [nrm_fst, hg]; rfl
  have hg₂ : nrm (snd g) = 1 := by rw [nrm_snd, hg]; rfl
  obtain ⟨O₁, hO₁, hne₁, hO₁t⟩ := h₁ _ hg₁ W₁ hW₁
  obtain ⟨O₂, hO₂, hne₂, hO₂t⟩ := h₂ _ hg₂ W₂ hW₂
  refine ⟨O₁ ×ˢ O₂, hO₁.prod hO₂, hne₁.prod hne₂, ?_⟩
  rintro ⟨t₁, t₂⟩ ⟨ht₁, ht₂⟩
  obtain ⟨u₁, hu₁W, hu₁n, hu₁r⟩ := hO₁t t₁ ht₁
  obtain ⟨u₂, hu₂W, hu₂n, hu₂r⟩ := hO₂t t₂ ht₂
  refine ⟨glue (u₁, u₂), hsub ⟨hu₁W, hu₂W⟩, ?_, ?_⟩
  · rw [nrm_glue, hu₁n, hu₂n]; rfl
  · simp [glue, hu₁r, hu₂r]
end GlobalTheory.QSA
