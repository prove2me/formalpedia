-- Prove2me | solution 1 for GlobalTheory.T.blowup_of_agreeing_ideal_cartier
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T18:12:14.572607+00:00
-- url     : https://prove2.me/submissions/0e65822e-6914-4482-bbf9-248a50b0f647

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_BlowupOfAgreeingIdealCartier
import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__GeometricallyConnectedOfIsIsoRestrict_f3ea578707b0384e
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_BlowupOfAgreeingIdealCartierStatement
import Theorems.Thm_P2M_GlobalTheory_CompanionTheory_Hypotheses__BlowupGlue_blowup_of_eq_on_open_2be0684b2feb


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ {X₁ X₂ : Scheme.{0}} (π : X₂ ⟶ X₁) (Z Z' : X₁.IdealSheafData) (O₁ O₂ : X₁.Opens), FinalTheorems.Blowup π Z → O₁ ⊔ O₂ = ⊤ → Z'.comap O₁.ι = Z.comap O₁.ι → (∀ x ∈ O₂, x ∉ Z'.support) → FinalTheorems.EffCartier (Z.comap O₂.ι) → FinalTheorems.Blowup π Z' := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.BlowupGlue.blowup_of_eq_on_open | exact GlobalTheory.CompanionTheory.Hypotheses₂.BlowupGlue.blowup_of_eq_on_open | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.BlowupGlue.blowup_of_eq_on_open <;> assumption)
end _root_.GlobalTheory.T
