-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.TyFin.intwIp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T14:06:47.877688+00:00
-- url     : https://prove2.me/submissions/ebdb70e5-4e36-4458-afc0-befeeccca021

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IntertwinerInnerProduct
import Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_intw_eq_invariants

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.Ty.Fin
open Formalism.IrreducibleCountingLemmas.TYPES hiding zIdem IsCuspidal
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.TyFin
namespace GlobalTheory.CompanionTheory.TyFin
theorem _root_.solution : ReciprocityTheory.Ty.Fin.St.IntwIp := by
  intro Γ _ _ V _ _ _ W _ _ _ ρ σ
  have hc : (Nat.card Γ : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  have := invertibleOfNonzero hc
  have h := Representation.card_inv_mul_sum_char_eq_finrank (Representation.linHom ρ σ)
  rw [intw_eq_invariants, ← h]
  simp [ip, Set.ncard_univ, Representation.char_linHom]
end GlobalTheory.CompanionTheory.TyFin
