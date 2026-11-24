-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.FlDecomp.stDecomp_of_frame_witt_tor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T13:21:24.150488+00:00
-- url     : https://prove2.me/submissions/da7ffadb-19b9-438f-9d4f-dabae994f96f

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_StSandwich
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_DecompositionOfFrameWittTorus
import Theorems.Thm_GlobalTheory_CompanionTheory_FlDecomp_isIso_mul
import Theorems.Thm_GlobalTheory_CompanionTheory_FlDecomp_isIso_inv
import Theorems.Thm_GlobalTheory_CompanionTheory_FlDecomp_adapted_unique
import Theorems.Thm_GlobalTheory_CompanionTheory_FlDecomp_adapted_pull
import Theorems.Thm_GlobalTheory_CompanionTheory_FlDecomp_adapted_reindex
import Theorems.Thm_GlobalTheory_CompanionTheory_FlDecomp_adapted_tor
import Theorems.Thm_GlobalTheory_CompanionTheory_FlDecomp_norm_discrete
import Theorems.Thm_GlobalTheory_CompanionTheory_FlDecomp_exists_antitone_perm
import Theorems.Thm_GlobalTheory_CompanionTheory_FlDecomp_isMax_pull
import Theorems.Thm_GlobalTheory_CompanionTheory_FlDecomp_frame_perm
import Theorems.Thm_GlobalTheory_CompanionTheory_FlDecomp_frame_flip

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.FlDecomp
open CompanionTheory.Rg.FlB
namespace GlobalTheory.CompanionTheory.FlDecomp
theorem _root_.solution : StFrame → StWitt → StTor → StDecomp := by
  intro hFr hWi hT L _ _ _ _ s hs δ hδ V _ _ _ h hh l e f W Λ hF hM hA p hp0 hp1 hpu g hg
  have hδ0 : δ ≠ 0 := hδ.1
  have hM' := isMax_pull hM hg
  obtain ⟨l', e₁, f₁, W₁, u, hu, hF₁, hA₁, hA₂⟩ := hFr L s hs δ hδ V h hh Λ (pull g⁻¹ Λ) hM hM'
  choose n hn using fun i => norm_discrete hp0 hp1 hpu (hu i)
  obtain ⟨e₂, f₂, m, hF₂, hA₃, hA₄⟩ := frame_flip hs hδ0 hh hF₁ hA₁ hA₂ p n hn hp0
  obtain ⟨q, k₀, hk₀, hke, hkf, hkW⟩ := hWi L s hs δ hδ V h hh l l' e f W e₂ f₂ W₁ hF hF₂
  obtain ⟨σ, hσ⟩ := exists_antitone_perm (m ∘ q)
  obtain ⟨P, hP, hPe, hPf, hPW⟩ := frame_perm hδ0 hh hF σ
  have hk : IsIso h (k₀ * P) := isIso_mul hk₀ hP
  have he' : ∀ i, (k₀ * P) (e i) = (e₂ ∘ (σ.trans q)) i := fun i => by
    simp [LinearEquiv.mul_apply, hPe, hke]
  have hf' : ∀ i, (k₀ * P) (f i) = (f₂ ∘ (σ.trans q)) i := fun i => by
    simp [LinearEquiv.mul_apply, hPf, hkf]
  have hW' : ∀ w ∈ W, (k₀ * P) w ∈ W₁ := fun w hw => by
    simpa [LinearEquiv.mul_apply, hPW w hw] using (hkW w).1 hw
  have hu' : ∀ i, p ^ (m ∘ q ∘ σ) i ≠ 0 := fun i => pow_ne_zero _ hp0
  obtain ⟨t, ht, hTt, -⟩ := hT L s hs δ hδ V h hh l e f W hF (fun i => p ^ (m ∘ q ∘ σ) i) hu'
  have hKΛ := adapted_pull (W := W) hk he' hf' hW' (adapted_reindex hA₃ (σ.trans q))
  have hKΛ' := adapted_pull (W := W) hk he' hf' hW' (adapted_reindex hA₄ (σ.trans q))
  have hTΛ' := adapted_tor hs hu' hTt hKΛ'
  have hkeep : ∀ x, (k₀ * P) x ∈ Λ ↔ x ∈ Λ := fun x =>
    adapted_unique hF hKΛ hA (fun _ => rfl) x
  have hfin : ∀ x, g⁻¹ ((k₀ * P) (t x)) ∈ Λ ↔ x ∈ Λ := fun x =>
    adapted_unique hF hTΛ' hA (fun _ => rfl) x
  have hgg : ∀ x, g⁻¹ (g x) = x := fun x => by
    change (g⁻¹ * g) x = x
    simp
  refine ⟨k₀ * P, t, (k₀ * P * t)⁻¹ * g, m ∘ q ∘ σ, hσ, hk, isIso_mul (isIso_inv (isIso_mul hk ht)) hg, hkeep, ?_, hTt, by group⟩
  intro x
  have h3 : (k₀ * P) (t (((k₀ * P * t)⁻¹ * g) x)) = g x := by
    change ((k₀ * P * t) * ((k₀ * P * t)⁻¹ * g)) x = g x
    rw [mul_inv_cancel_left]
  rw [← hfin, h3, hgg]
end GlobalTheory.CompanionTheory.FlDecomp
