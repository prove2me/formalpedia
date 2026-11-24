-- Prove2me | solution 1 for GlobalTheory.Ex.QStr.root_over
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T15:35:00.910955+00:00
-- url     : https://prove2.me/submissions/2fc9f498-f119-42c7-a618-a04528133e0e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_SepticCharacterInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_DegenerationWeilPairingPropertiesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_DegenerationDataTorsionStructureAlgClosed
import Theorems.Thm_GlobalTheory_Ex_QStr_exists_lift
import Theorems.Thm_GlobalTheory_Ex_QStr_tor_div
import Theorems.Thm_GlobalTheory_Ex_NumD_exists_tor_iff


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Ex
open scoped BigOperators
noncomputable section
open GlobalTheory GlobalTheory.Ex GlobalTheory.Ex.QStr
variable {C : Type} [Field C] [IsAlgClosed C] (N : NumD C) {k : ℕ}
namespace GlobalTheory.Ex.QStr
theorem _root_.solution (hk : k ≠ 0) (γ : N.Gt) (b : N.A) (hb : b ^ k = γ.b) : ∃ γ' : N.Gt, γ'.b = b ∧ γ' ^ k = γ := by
  obtain ⟨γ₀, h₀⟩ := exists_lift N b
  obtain ⟨t, ht⟩ := (N.exists_tor_iff (γ * (γ₀ ^ k)⁻¹)).2 (by simp [h₀, hb])
  obtain ⟨t', rfl⟩ := tor_div N hk t
  refine ⟨N.tor t' * γ₀, by simp [h₀], ?_⟩
  rw [mul_pow, ← N.tor_pow, ht, inv_mul_cancel_right]
end GlobalTheory.Ex.QStr
