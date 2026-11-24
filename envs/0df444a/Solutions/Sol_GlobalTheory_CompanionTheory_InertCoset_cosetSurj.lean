-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.InertCoset.cosetSurj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:19:36.2514+00:00
-- url     : https://prove2.me/submissions/6d175190-2bb6-49cd-b5fb-a592198acc32

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitaryLeviNormalizesUnipotentRadical
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitaryBlockTriangularLeviPartUnitary
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_TwistedProofs_CosetSurjectiveOfLevi
import Theorems.Thm_GlobalTheory_CompanionTheory_InertCoset_exists_col
import Theorems.Thm_GlobalTheory_CompanionTheory_InertCoset_levi_step

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism.UG Matrix GlobalTheory.SatakeWeyl GlobalTheory.InertZeta
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.InertCoset
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L} {n : ℕ}
namespace GlobalTheory.CompanionTheory.InertCoset
theorem _root_.solution : LeviExists → CosetSurj := by
  intro hLE L _ _ ϖ σ q N hU g
  obtain ⟨s, k, hk, hcol⟩ := exists_col hU g
  obtain ⟨y, hy⟩ := levi_step hLE hU (g * k) hcol
  refine ⟨s, y, fun m hm => ?_⟩
  obtain ⟨u, hu, k', hk', he⟩ := hy m hm
  refine ⟨u, hu, k' * k⁻¹, Subgroup.mul_mem _ hk' (Subgroup.inv_mem _ hk), ?_⟩
  rw [← mul_assoc, ← he, mul_inv_cancel_right]
end GlobalTheory.CompanionTheory.InertCoset
