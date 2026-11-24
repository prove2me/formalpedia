-- Prove2me | solution 1 for GlobalTheory.UnitLemma.InvAlg.lin_fst_snd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:10:32.103201+00:00
-- url     : https://prove2.me/submissions/500c4cee-ebdb-428a-a047-6281854d3123

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ClearDenominators
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_LieLatticeProdComapInlAndMapSnd
import Theorems.Thm_GlobalTheory_UnitLemma_LinPair_exists_smul_mem_of_mem_span

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma Polynomial
open GlobalTheory.UnitLemma.LinPair
namespace GlobalTheory.UnitLemma.InvAlg
theorem _root_.solution : ∀ (K : UQ) (B₁ B₂ : InvAlg K) (M : Submodule K.O (B₁.A × B₂.A)),
    M ∈ (B₁.prod B₂).Lin →
    M.comap (LinearMap.inl K.O B₁.A B₂.A) ∈ B₁.Lin ∧ M.map (LinearMap.snd K.O B₁.A B₂.A) ∈ B₂.Lin := by
  intro K B₁ B₂ M hM
  obtain ⟨⟨hfg, hspan⟩, hg, hσ⟩ := hM
  have hg' : ∀ y ∈ M, ((B₁.g * y.1, B₂.g * y.2) : B₁.A × B₂.A) ∈ M := fun y hy => hg y hy
  have hσ' : ∀ y ∈ M, ((B₁.σ y.1, B₂.σ y.2) : B₁.A × B₂.A) ∈ M := fun y hy => hσ y hy
  replace hspan : Submodule.span K.E (M : Set (B₁.A × B₂.A)) = ⊤ := hspan
  refine ⟨⟨⟨?_, ?_⟩, ?_, ?_⟩, ⟨⟨hfg.map _, ?_⟩, ?_, ?_⟩⟩
  ·
    apply Submodule.fg_of_fg_map_injective (LinearMap.inl K.O B₁.A B₂.A) LinearMap.inl_injective
    exact isNoetherian_submodule.1 (isNoetherian_of_fg_of_noetherian M hfg) _ (Submodule.map_comap_le _ _)
  ·
    rw [eq_top_iff]
    intro a _
    have hx : ((a, 0) : B₁.A × B₂.A) ∈ Submodule.span K.E (M : Set (B₁.A × B₂.A)) := by
      rw [hspan]; exact Submodule.mem_top
    obtain ⟨d, hd, hdm⟩ := exists_smul_mem_of_mem_span K M hx
    have hda : d • a ∈ M.comap (LinearMap.inl K.O B₁.A B₂.A) := by
      rw [Submodule.mem_comap]; simpa using hdm
    have hdE : algebraMap K.O K.E d ≠ 0 := by
      rw [Ne, ← map_zero (algebraMap K.O K.E)]
      exact fun h => hd (IsFractionRing.injective K.O K.E h)
    have : a = (algebraMap K.O K.E d)⁻¹ • (d • a) := by
      rw [← algebraMap_smul (A := K.E) d a, smul_smul, inv_mul_cancel₀ hdE, one_smul]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hda)
  · intro y hy
    have := hg' _ hy
    simpa [Submodule.mem_comap] using this
  · intro y hy
    have := hσ' _ hy
    simpa [Submodule.mem_comap] using this
  · rw [Submodule.map_coe]
    have : ⇑(LinearMap.snd K.O B₁.A B₂.A) = ⇑(LinearMap.snd K.E B₁.A B₂.A) := rfl
    rw [this, ← Submodule.map_span, hspan, Submodule.map_top, LinearMap.range_eq_top]
    exact LinearMap.snd_surjective
  · rintro _ ⟨m, hm, rfl⟩
    exact ⟨_, hg' m hm, rfl⟩
  · rintro _ ⟨m, hm, rfl⟩
    exact ⟨_, hσ' m hm, rfl⟩
end GlobalTheory.UnitLemma.InvAlg
