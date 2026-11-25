-- Prove2me | solution 1 for GlobalTheory.CuspCharCheck.isIrrChar_of_hom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:10:44.483253+00:00
-- url     : https://prove2.me/submissions/e1091544-7b90-4a5f-8e76-274f66097d56

import Mathlib
import Definitions.Def_Formalism_UnipotentAdelicQuotients_CuspEllipticValues
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_CentralIdempotentIrreducibleCharacterProps
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_SubgroupCharacterSums_SumSubgroupEqZeroIff
import Theorems.Thm_GlobalTheory_CuspCharCheck_isChar_iff
import Theorems.Thm_GlobalTheory_BadShare_ZCalc_character_inv
import Theorems.Thm_PI_CharIdemW_scalar


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory CuspElliptic
open GlobalTheory GlobalTheory.CuspCharCheck
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
namespace GlobalTheory.CuspCharCheck
theorem _root_.solution {G : Type} [Group G] [Fintype G] (c : G →* ℂˣ) : IsIrrChar (fun x => (c x : ℂ)) := by
  have hc : IsChar (fun x => (c x : ℂ)) :=
    ⟨1, (Units.map (Matrix.scalar (Fin 1) : ℂ →+* _).toMonoidHom).comp c, fun x => by simp⟩
  refine ⟨hc, ?_⟩
  obtain ⟨V, hV⟩ := (isChar_iff _).1 hc
  have : ∀ x, (c x : ℂ) * star (c x : ℂ) = 1 := fun x => by
    have h := GlobalTheory.BadShare.ZCalc.character_inv V x
    rw [hV, starRingEnd_apply] at h
    rw [← h, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]
  rw [Finset.sum_congr rfl fun x _ => this x]
  simp
end GlobalTheory.CuspCharCheck
