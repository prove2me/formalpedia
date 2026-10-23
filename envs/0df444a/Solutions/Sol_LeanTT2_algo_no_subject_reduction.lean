-- Prove2me | solution 1 for LeanTT2.algo_no_subject_reduction
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T10:27:44.437389+00:00
-- url     : https://prove2.me/submissions/54334618-35a7-4c95-a12b-f0477c198d19

import Mathlib
import Definitions.Def_LeanTT2_frag
import Definitions.Def_LeanTT2_spec
import Definitions.Def_LeanTT2_counter

universe u

open LeanTT2

theorem solution (F : Frag.{u}) (Γ : F.Ctx)
    (α β γ e : F.E)
    (hab : F.alg Γ α β) (hbc : F.alg Γ β γ) (hnac : ¬ F.alg Γ α γ)
    (he : F.aty Γ e γ) :
    F.aty Γ (F.app (F.idf β) e) β ∧
    F.aty Γ (F.app (F.idf α) (F.app (F.idf β) e)) α ∧
    F.red Γ (F.app (F.idf β) e) e ∧
    ¬ F.aty Γ (F.app (F.idf α) e) α := by
  have h1 : F.aty Γ (F.app (F.idf β) e) β :=
    (F.aty_idf Γ β e γ he).mpr (F.alg_symm Γ β γ hbc)
  refine ⟨h1, (F.aty_idf Γ α _ β h1).mpr (F.alg_symm Γ α β hab), F.red_idf Γ β e, ?_⟩
  intro h
  exact hnac (F.alg_symm Γ γ α ((F.aty_idf Γ α e γ he).mp h))
