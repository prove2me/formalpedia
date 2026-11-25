-- Prove2me | solution 1 for GlobalTheory.KTypeCompare.isHCTypeU_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T07:16:13.907952+00:00
-- url     : https://prove2.me/submissions/03cf966c-8c56-462b-a6dc-f4170e9523d5

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UpqRep
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_JetGauges_HarishChandraParameters
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_IsWtOnIffOfTorus
import Theorems.Thm_GlobalTheory_KTypeCompare_isURepOn_iff
import Theorems.Thm_GlobalTheory_KTypeCompare_isKTypeOf_iff
import Theorems.Thm_GlobalTheory_KTypeCompare_weight_integral
import Theorems.Thm_GlobalTheory_KTypeCompare_highest_dominant
import Theorems.Thm_GlobalTheory_KTypeCompare_UJset_allPos
import Theorems.Thm_GlobalTheory_KTypeCompare_lowK_allPos
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_HarishChandraRootData_grpK_const


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
namespace GlobalTheory.KTypeCompare
theorem _root_.solution {k : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (u : Fin k → ℝ) (π : Matrix (Fin k) (Fin k) ℂ → H →L[ℂ] H) :
    PI.UpqRep.IsHCTypeU k u π ↔ HarishChandraRootData.IsCompactIrrep π u := by
  have hc : PI.UpqRep.allPos k = fun _ => true := rfl
  unfold PI.UpqRep.IsHCTypeU
  rw [isURepOn_iff, UJset_allPos, isKTypeOf_iff, lowK_allPos, hc]
  constructor
  · rintro ⟨-, -, hrep, htype⟩
    have hrep' : HarishChandraRootData.IsUnitaryRepOn (HarishChandraRootData.grpK (fun _ : Fin k => true)) π := by
      rw [HarishChandraRootData.grpK_const]
      exact hrep
    obtain ⟨v, -, hv⟩ := htype.exists_highest
    refine ⟨⟨fun a b hab => ?_, fun i => ?_⟩, hrep, htype⟩
    · have hd := highest_dominant hrep' htype hab rfl
      simp only [Pi.sub_apply, HarishChandraRootData.rhoU] at hd
      have hab' : ((a : ℕ) : ℝ) < ((b : ℕ) : ℝ) := by exact_mod_cast hab
      linarith
    · obtain ⟨m, hm⟩ := weight_integral hv i
      refine ⟨m - ((i : ℕ) : ℤ), ?_⟩
      simp only [Pi.sub_apply, HarishChandraRootData.rhoU] at hm
      push_cast
      linarith
  · rintro ⟨-, hrep, htype⟩
    obtain ⟨v, -, hv0, -⟩ := htype.exists_highest
    have := htype.finDim
    exact ⟨nontrivial_of_ne v 0 hv0, LinearEquiv.finiteDimensional Submodule.topEquiv, hrep, htype⟩
end GlobalTheory.KTypeCompare
