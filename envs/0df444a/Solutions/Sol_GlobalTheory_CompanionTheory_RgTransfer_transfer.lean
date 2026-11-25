-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RgTransfer.transfer
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T02:38:02.4578+00:00
-- url     : https://prove2.me/submissions/c066c136-2b5c-44b8-862f-7a508acbd50b

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_StripEntire
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CorrESymmCoe
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_TransferOfSectionAndWallLaws
import Theorems.Thm_GlobalTheory_CompanionTheory_RgTransfer_hOf_eq
import Theorems.Thm_GlobalTheory_CompanionTheory_RgTransfer_isCh_one
import Theorems.Thm_GlobalTheory_CompanionTheory_RgTransfer_isPar_pull
import Theorems.Thm_GlobalTheory_CompanionTheory_RgTransfer_leftGood_comp
import Theorems.Thm_GlobalTheory_CompanionTheory_RgTransfer_mem_secSp_iff
import Theorems.Thm_GlobalTheory_CompanionTheory_RgTransfer_resRep_cont
import Theorems.Thm_GlobalTheory_CompanionTheory_RgTransfer_sec_pull
import Theorems.Thm_GlobalTheory_CompanionTheory_RgTransfer_wall_pull


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Filter Topology PositivityTheory.RgEis
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.RgTransfer
namespace GlobalTheory.CompanionTheory.RgTransfer
theorem _root_.solution : SecLaw → WallLaw → Transfer := by
  intro hSec hWall G _ _ _ _ _ W _ _ _ K ρ hK hρ G' _ _ _ _ _ Γ Q S P₁ P₂ Γ' K' S' P₁' P₂' π ι c₀ c c'
    η₁ η₂ β ξ η₁' η₂' β' ξ' N hK' hL hS hP₁ hP₂ hS' hR₁ hR₂ hη₁ hη₂ hβ hp₁ hp₂ hpβ hpξ
  have hcont := resRep_cont hL hρ
  have c1 : c' 1 = 1 := isCh_one hR₁.ch
  have corr : ∀ {P : Subgroup G} {P' : Subgroup G'}, IsPull Q P P' π c₀ c c' →
      Corr ρ (secSp K P c ρ) (secSp K' P' c' (resRep hL ρ)) :=
    fun h w => mem_secSp_iff hL h c1 ρ w
  have lawG : ∀ {P : Subgroup G} {P' : Subgroup G'}, IsPull Q P P' π c₀ c c' →
      IsPar Γ' K' P' c' → Law K P c ρ :=
    fun h hp => (hSec G W K ρ hK hρ (Γ ⊓ Q) _ c (isPar_pull hL h hp)).1
  have lawG' : ∀ {P' : Subgroup G'}, IsPar Γ' K' P' c' → Law K' P' c' (resRep hL ρ) :=
    fun hp => (hSec G' _ K' (resRep hL ρ) hK' hcont Γ' _ c' hp).1
  obtain ⟨M₁, bd₁⟩ := (hSec G' _ K' (resRep hL ρ) hK' hcont Γ' _ c' hR₁).2.2
  obtain ⟨M₂, bd₂⟩ := (hSec G' _ K' (resRep hL ρ) hK' hcont Γ' _ c' hR₂).2.2
  have equi : ∀ {L' : Submodule ℂ (fixSp K Q π c₀ ρ)} {R : ℝ} {D : ℂ → ℂ}
      {Op' : ℂ → (L' →L[ℂ] secSp K' P₂' c' (resRep hL ρ))}
      {H' : ℂ → G' → (L' →L[ℂ] fixSp K Q π c₀ ρ)},
      Wall Γ' K' P₁' P₂' c' η₁' η₂' β' (resRep hL ρ) L' R D Op' H' →
      ∀ z (g : G') (k : K') (w : L'), H' z (g * k) w = resRep hL ρ k⁻¹ (H' z g w) :=
    fun hw => (hWall G' _ K' (resRep hL ρ) hK' hcont Γ' P₁' P₂' c' η₁' η₂' β' _ _ _ _ _ hR₁ hR₂
      hη₁ hη₂ hβ hw).2.1
  have key : ∀ {L : Submodule ℂ W} {L' : Submodule ℂ (fixSp K Q π c₀ ρ)} (hLL : Corr ρ L L')
      {R : ℝ} {D : ℂ → ℂ} {Op' : ℂ → (L' →L[ℂ] secSp K' P₂' c' (resRep hL ρ))}
      {H' : ℂ → G' → (L' →L[ℂ] fixSp K Q π c₀ ρ)},
      Wall Γ' K' P₁' P₂' c' η₁' η₂' β' (resRep hL ρ) L' R D Op' H' →
      Wall (Γ ⊓ Q) K P₁ P₂ c η₁ η₂ β ρ L R D (fun z => cj (corrE hLL) (corrE (corr hP₂)) (Op' z))
        (hOf hL ρ (corrE hLL) H') :=
    fun hLL _ _ _ _ hw => wall_pull hK hL hρ hP₁ hP₂ hR₁ hR₂ hη₁ hη₂ hβ hp₁ hp₂ hpβ (lawG hP₁ hR₁)
      (lawG hP₂ hR₂) (lawG' hR₁) (lawG' hR₂) bd₁ bd₂ hLL (corr hP₁) (corr hP₂) hw (equi hw)
  have hCS := corr hS
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
  · obtain ⟨R, D, Op', H', hw⟩ := h _ (resRep hL ρ) hcont
    exact ⟨R, D, _, _, key (corr hP₁) hw⟩
  · obtain ⟨R, D, Op', H', hw, ⟨a, ha, hH0⟩, O', hO, hOp⟩ := h _ (resRep hL ρ) hcont
    refine ⟨R, D, _, _, key hCS hw, ⟨a, ha, fun g w => ?_⟩,
      fun z => cj (corrE hCS) (corrE (corr hP₂)) (O' z),
      leftGood_comp (cj (corrE hCS) (corrE (corr hP₂))) hO, fun z hz => ?_⟩
    · obtain ⟨q, k, rfl⟩ := exists_qk hL g
      rw [hOf_eq hL ρ _ (equi hw), hH0, map_smul]
      have := sec_pull hL hS hS'.iwa (lawG hS hS') (lawG' hS') (corrE hCS w).2 w.2 q k
      exact congrArg (fun u => a • u) this.symm
    · show cj (corrE hCS) (corrE (corr hP₂)) (Op' z) = z • cj (corrE hCS) (corrE (corr hP₂)) (O' z)
      rw [hOp z hz, map_smul]
  · obtain ⟨R, D, Op', H', hw, hd, T', hT⟩ := h _ (resRep hL ρ) hcont
    refine ⟨R, D, _, _, key (corr hP₁) hw, hd, cj (corrE (corr hP₁)) (corrE hCS) T', fun g w => ?_⟩
    obtain ⟨q, k, rfl⟩ := exists_qk hL g
    rw [hOf_eq hL ρ _ (equi hw), hT, map_smul, hpξ q k k.2]
    have := sec_pull hL hS hS'.iwa (lawG hS hS') (lawG' hS') (T' (corrE (corr hP₁) w)).2
      (cj (corrE (corr hP₁)) (corrE hCS) T' w).2 q k
    exact congrArg (fun u => Complex.exp (ξ' (π q)) • u) this.symm
end GlobalTheory.CompanionTheory.RgTransfer
