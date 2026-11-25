-- Prove2me | solution 1 for GlobalTheory.RealWeil.SchrFamily.seminorm_rhoSch_sub_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:19:19.723246+00:00
-- url     : https://prove2.me/submissions/5ec6cc35-f444-4a3c-8182-bffd7ec15c65

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_RealMetaplecticRepresentation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsSchwartzTranslate
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzTranslationSeminormBound
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzCharacterSeminormBound
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchrodingerRepSchwartzPolynomialBound
import Theorems.Thm_GlobalTheory_RealWeil_SchrFamily_rhoSch_eq
import Theorems.Thm_GlobalTheory_PhaseLipschitz_seminorm_smulLeft_eChar_sub_le
import Theorems.Thm_GlobalTheory_SchwartzTranslateLip_translate_sub_le


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory GlobalTheory.RealWeil Filter Topology
open scoped SchwartzMap RealInnerProductSpace
noncomputable section
open GlobalTheory GlobalTheory.RealWeil GlobalTheory.RealWeil.SchrFamily
variable {l : Type} [Fintype l]
namespace GlobalTheory.RealWeil.SchrFamily
theorem _root_.solution (p : Seminorm ℂ (Sch l)) (hp : Continuous p) :
    ∃ (q₁ q₂ q₃ : Seminorm ℂ (Sch l)) (M₁ M₂ M₃ : ℕ), ∀ (w : l ⊕ l → ℝ) (g : Sch l),
      p (rhoSch w g - g) ≤ (‖qPart w‖ + |⟪pPart w, qPart w⟫ / 2|) * (1 + ‖qPart w‖) ^ M₁ *
          (‖pPart w‖ * (1 + ‖pPart w‖) ^ M₃ * q₃ g + q₁ g) + ‖pPart w‖ * (1 + ‖pPart w‖) ^ M₂ * q₂ g := by
  obtain ⟨q₁, M₁, hq₁, hb₁⟩ := GlobalTheory.PhaseLipschitz.seminorm_smulLeft_eChar_sub_le (EuclideanSpace ℝ l) p hp
  obtain ⟨q₂, M₂, -, hb₂⟩ := GlobalTheory.SchwartzTranslateLip.translate_sub_le (EuclideanSpace ℝ l) p hp
  obtain ⟨q₃, M₃, -, hb₃⟩ := GlobalTheory.SchwartzTranslateLip.translate_sub_le (EuclideanSpace ℝ l) q₁ hq₁
  refine ⟨q₁, q₂, q₃, M₁, M₂, M₃, fun w g => ?_⟩
  set T := SchwartzMap.compSubConstCLM ℂ (-pPart w) g with hT
  have hL : ‖innerSL ℝ (qPart w)‖ = ‖qPart w‖ := innerSL_apply_norm _ _
  have h1 := map_add_le_add p (SchwartzMap.smulLeftCLM ℂ
    (fun y => GlobalTheory.Published.Metaplectic.eChar (innerSL ℝ (qPart w) y + ⟪pPart w, qPart w⟫ / 2)) T - T) (T - g)
  rw [sub_add_sub_cancel] at h1
  rw [rhoSch_eq]
  refine le_trans h1 (add_le_add ((hb₁ _ _ T).trans ?_) (hb₂ _ g))
  rw [hL]
  have h2 := map_add_le_add q₁ (T - g) g
  rw [sub_add_cancel] at h2
  have h3 := hb₃ (pPart w) g
  gcongr
  linarith
end GlobalTheory.RealWeil.SchrFamily
