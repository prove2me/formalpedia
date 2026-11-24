-- Prove2me | solution 1 for GlobalTheory.SmGL.IndCoinv.mem_of_fixed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:41:28.124336+00:00
-- url     : https://prove2.me/submissions/8af13a71-6f84-4645-b721-4dff7c9117d5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_InductionContragredient
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SmIndCoinvariants
import Theorems.Thm_GlobalTheory_SmGL_DualAverage_exists_invariant_form
import Theorems.Thm_GlobalTheory_SmGL_IndDual_dual_ext
import Theorems.Thm_GlobalTheory_SmGL_IsSubquotient_trans


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SmGL.IndDual
open GlobalTheory GlobalTheory.SmGL GlobalTheory.SmGL.IndCoinv
variable {G X U : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup X] [Module ℂ X]
  [AddCommGroup U] [Module ℂ U] {P : Subgroup G} {σ : Representation ℂ P X} {ρ : Representation ℂ P U}
namespace GlobalTheory.SmGL.IndCoinv
theorem _root_.solution [T2Space G] {σ : Representation ℂ G X} (hσ : IsSmooth σ) {H : Subgroup G}
    (hH : IsCompact (H : Set G)) {Γ : Type} (T : Γ → σ.IntertwiningMap σ) (M : Submodule ℂ (fixed σ H))
    (hM : ∀ γ (z : fixed σ H), (⟨T γ z, map_mem_fixed (T γ) z.2⟩ : fixed σ H) - z ∈ M) (w : fixed σ H)
    (hw : w.1 ∈ Submodule.span ℂ {y : X | ∃ γ z, y = T γ z - z}) : w ∈ M := by
  by_contra hn
  obtain ⟨l, hl, hl0⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hn inferInstance
  obtain ⟨l₀, hl₀⟩ := LinearMap.exists_extend l
  obtain ⟨l₁, h1, h2⟩ := GlobalTheory.SmGL.DualAverage.exists_invariant_form G X σ hσ _ hH l₀
  have h3 : ∀ v : fixed σ H, l₁ v = l v := fun v =>
    (h2 _ (mem_fixed_iff.1 v.2)).trans (LinearMap.congr_fun hl₀ v)
  have h4 : ∀ γ, l₁ ∘ₗ (T γ).toLinearMap = l₁ := fun γ =>
    dual_ext hσ hH (fun h hh v => by
      show l₁ (T γ _) = l₁ (T γ _)
      rw [(T γ).isIntertwining, h1 h hh]) h1 fun v hv => by
      have h5 : l (_ - _) ∈ M.map l := Submodule.mem_map_of_mem (hM γ ⟨v, hv⟩)
      rw [hl0, Submodule.mem_bot, map_sub, ← h3, ← h3, sub_eq_zero] at h5
      exact h5
  apply hl
  rw [← h3]
  refine (Submodule.span_le (p := LinearMap.ker l₁)).2 ?_ hw
  rintro _ ⟨γ, z, rfl⟩
  have h5 : l₁ (T γ z) = l₁ z := LinearMap.congr_fun (h4 γ) z
  simp [h5]
end GlobalTheory.SmGL.IndCoinv
