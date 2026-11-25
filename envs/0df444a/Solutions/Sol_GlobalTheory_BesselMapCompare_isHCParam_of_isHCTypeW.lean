-- Prove2me | solution 1 for GlobalTheory.BesselMapCompare.isHCParam_of_isHCTypeW
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T07:32:19.156549+00:00
-- url     : https://prove2.me/submissions/0ced558e-bf33-4101-ab9d-eb880a3972aa

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_BesselMapUniq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_IsWtOnIffOfTorus
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_IsBesselMapSmBesselCharIff
import Theorems.Thm_GlobalTheory_KTypeCompare_isHCParam_iff
import Theorems.Thm_GlobalTheory_KTypeCompare_isHCTypeU_iff


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open GlobalTheory GlobalTheory.BesselMapCompare
open PI.UpqRep GlobalTheory.IndefiniteRowSideFullHecke
variable {k r : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
namespace GlobalTheory.BesselMapCompare
theorem _root_.solution {z : Fin (2 * r + k + 1) → ℂ} {u : Fin k → ℝ}
    {π : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (V →L[ℂ] V)}
    (h : IsHCTypeW k r z u π) : PI.UpqRep.IsHCParam u := by
  obtain ⟨g, -, hg⟩ := h
  exact (KTypeCompare.isHCParam_iff u).2 ((KTypeCompare.isHCTypeU_iff u _).1 hg).param
end GlobalTheory.BesselMapCompare
