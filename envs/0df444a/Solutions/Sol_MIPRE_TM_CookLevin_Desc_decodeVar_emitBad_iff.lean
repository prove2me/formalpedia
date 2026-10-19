-- Prove2me | solution 1 for MIPRE.TM.CookLevin.Desc.decodeVar_emitBad_iff
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T01:47:19.922281+00:00
-- url     : https://prove2.me/submissions/452403a4-b6cf-4df0-ad74-3f8e06ef05c8

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/TM/CookLevin/Kinds.lean (solution of MIPRE.TM.CookLevin.Desc.decodeVar_emitBad_iff);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Computability.Language
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Int.Interval
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Set.Basic
import Mathlib.Data.Sign.Defs
import Mathlib.Logic.Relation
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_SAT_Circuit
import Definitions.Def_MIPRE_Foundations_SAT_Cnf
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Loops_B
import Definitions.Def_MIPRE_Foundations_Cost_Fold
import Definitions.Def_MIPRE_Foundations_Cost_Unary
import Definitions.Def_MIPRE_Foundations_Cost_Numeric_B
import Definitions.Def_MIPRE_Foundations_Cost_Binary
import Definitions.Def_MIPRE_Foundations_SAT_Formula
import Definitions.Def_MIPRE_Foundations_SAT_FmlLib
import Definitions.Def_MIPRE_Cslib_Foundations_Data_RelatesInSteps
import Definitions.Def_MIPRE_Cslib_Computability_Machines_Turing_MultiTape_Deterministic
import Definitions.Def_MIPRE_TM_MultiInput_Deterministic
import Definitions.Def_MIPRE_TM_CookLevin_Local
import Definitions.Def_MIPRE_Foundations_SAT_Tseitin
import Definitions.Def_MIPRE_TM_CookLevin_Tableau
import Definitions.Def_MIPRE_TM_Interp_Instr
import Definitions.Def_MIPRE_TM_Interp_Machine
import Definitions.Def_MIPRE_TM_CookLevin_Layout
import Definitions.Def_MIPRE_TM_CookLevin_FieldFml
import Definitions.Def_MIPRE_TM_CookLevin_Kinds

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.TM.CookLevin.Desc
open SAT Cost Fml
variable (e G : ℕ)
theorem _root_.solution (F : Fields) (t : Fin (Sof e)) :
    decodeVar e G F = some (.emitBad t) ↔ IsEmitBad e F ∧ F.t = t := by
  constructor
  · intro h
    unfold decodeVar at h
    split at h
    · rename_i hflag
      split at h
      · exfalso; split_ifs at h <;> (try split at h) <;> cases h
      · split at h
        · exfalso; split_ifs at h <;> (try split at h) <;> cases h
        · split at h
          · exfalso; split_ifs at h <;> (try split at h) <;> cases h
          · split at h
            · exfalso; split_ifs at h <;> (try split at h) <;> cases h
            · split at h
              · rename_i htag
                split at h
                · rename_i hb
                  cases h
                  exact ⟨⟨hflag, htag, hb⟩, rfl⟩
                · cases h
              · exfalso; split_ifs at h <;> (try split at h) <;> cases h
    · exfalso; split_ifs at h <;> (try split at h) <;> cases h
  · rintro ⟨⟨hf, htag, hb⟩, ht⟩
    unfold decodeVar
    rw [if_pos hf, if_neg (by rw [htag]; decide), if_neg (by rw [htag]; decide),
      if_neg (by rw [htag]; decide), if_neg (by rw [htag]; decide), if_pos htag, dif_pos hb]
    simp only [Option.some.injEq]
    congr 1; ext; simp [ht]
end MIPRE.TM.CookLevin.Desc
