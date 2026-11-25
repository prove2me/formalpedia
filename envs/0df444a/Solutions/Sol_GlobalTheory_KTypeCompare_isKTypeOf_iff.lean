-- Prove2me | solution 1 for GlobalTheory.KTypeCompare.isKTypeOf_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T07:02:30.956078+00:00
-- url     : https://prove2.me/submissions/d8c73b23-9518-4702-a203-41176bb6618d

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UpqRep
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_JetGauges_HarishChandraParameters
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_IsWtOnIffOfTorus
import Theorems.Thm_GlobalTheory_KTypeCompare_cDom_iff
import Theorems.Thm_GlobalTheory_KTypeCompare_isWtOn_iff
import Theorems.Thm_GlobalTheory_KTypeCompare_isKStableOn_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
noncomputable section
open GlobalTheory GlobalTheory.KTypeCompare
open GlobalTheory.IndefiniteRowSideFullHecke
variable {n : ℕ}
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
namespace GlobalTheory.KTypeCompare
theorem _root_.solution (ε : Fin n → Bool)
    (σ : Matrix (Fin n) (Fin n) ℂ → H →L[ℂ] H) (Λ : Fin n → ℝ) (S : Submodule ℂ H) :
    PI.UpqRep.IsKTypeOf ε σ Λ S ↔ HarishChandraRootData.IsKType ε σ S Λ := by
  simp only [PI.UpqRep.IsKTypeOf, isKStableOn_iff, isWtOn_iff, cDom_iff]
  constructor
  · rintro ⟨h1, h2, h3, ⟨v, hv, hv0, hw⟩, h5⟩
    exact ⟨h1, h2, h3, ⟨v, hv, hv0, hw⟩, fun ω v hv hw => h5 ω v hv hw.1 hw.2⟩
  · rintro ⟨h1, h2, h3, ⟨v, hv, hv0, hw⟩, h5⟩
    exact ⟨h1, h2, h3, ⟨v, hv, hv0, hw⟩, fun ω v hv hv0 hw => h5 ω v hv ⟨hv0, hw⟩⟩
end GlobalTheory.KTypeCompare
