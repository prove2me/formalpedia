-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.TyFin.hcDim
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T20:15:34.162196+00:00
-- url     : https://prove2.me/submissions/745995b7-0775-4aa3-88c4-e40ef78b97a9

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_HarishChandraCharacterStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_HarishChandraDimension
import Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_blkGL_one_eq
import Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_indF_one_eq
import Theorems.Thm_GlobalTheory_T_harish_chandra_character


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.Ty.Fin
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.TyFin
namespace GlobalTheory.CompanionTheory.TyFin
theorem _root_.solution : ReciprocityTheory.Ty.Fin.St.HCDim := by
  intro K _ _ _ ι _ _ s b lam
  have h := congrFun (GlobalTheory.T.harish_chandra_character K ι s b lam).1 1
  rw [Representation.char_one, indF_one_eq] at h
  have hf : hcFun b (fun c => (lam c).character) (1 : GL ι K)
      = ((∏ c, Module.finrank ℂ (lam c) : ℕ) : ℂ) := by
    unfold hcFun
    push_cast
    refine Finset.prod_congr rfl fun c _ => ?_
    rw [blkGL_one_eq, FDRep.char_one]
  rw [hf] at h
  have hP : (Nat.card (Formalism.IrreducibleCountingLemmas.TYPES.parab K b) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have h2 : ((Module.finrank ℂ (Formalism.IrreducibleCountingLemmas.TYPES.hcSpace K b lam) *
      Nat.card (Formalism.IrreducibleCountingLemmas.TYPES.parab K b) : ℕ) : ℂ) =
      ((Nat.card (GL ι K) * ∏ c, Module.finrank ℂ (lam c) : ℕ) : ℂ) := by
    rw [Nat.cast_mul, h, Nat.cast_mul]
    field_simp
  exact_mod_cast h2
end GlobalTheory.CompanionTheory.TyFin
