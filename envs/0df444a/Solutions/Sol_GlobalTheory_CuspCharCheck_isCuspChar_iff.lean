-- Prove2me | solution 1 for GlobalTheory.CuspCharCheck.isCuspChar_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T14:41:00.65508+00:00
-- url     : https://prove2.me/submissions/b6432996-967f-4de1-b66e-ed35dcffb8ff

import Mathlib
import Definitions.Def_Formalism_UnipotentAdelicQuotients_CuspEllipticValues
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_CentralIdempotentIrreducibleCharacterProps
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_SubgroupCharacterSums_SumSubgroupEqZeroIff
import Theorems.Thm_GlobalTheory_CuspCharCheck_isIrrChar_iff
import Theorems.Thm_GlobalTheory_CuspCharCheck_sum_subgroup_eq_zero_iff

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
theorem _root_.solution {d : ℕ} (χ : GL (Fin d) F → ℂ) :
    IsCuspChar χ ↔ ∃ V : FDRep ℂ (GL (Fin d) F), Simple V ∧ V.character = χ ∧
      ∀ a, 0 < a → a < d → ∀ v : V, (∀ u ∈ (unipSubgroup d a : Subgroup (GL (Fin d) F)), V.ρ u v = v) → v = 0 := by
  classical
  unfold IsCuspChar
  rw [isIrrChar_iff]
  constructor
  · rintro ⟨⟨V, hV, rfl⟩, h⟩
    refine ⟨V, hV, rfl, fun a h0 h1 => (sum_subgroup_eq_zero_iff V _).1 ?_⟩
    convert h a h0 h1 using 3
    rfl
  · rintro ⟨V, hV, rfl, h⟩
    refine ⟨⟨V, hV, rfl⟩, fun a h0 h1 => ?_⟩
    convert (sum_subgroup_eq_zero_iff V _).2 (h a h0 h1) using 3
    rfl
end GlobalTheory.CuspCharCheck
