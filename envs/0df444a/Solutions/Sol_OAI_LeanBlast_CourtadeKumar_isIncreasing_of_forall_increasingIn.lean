-- Prove2me | solution 1 for OAI.LeanBlast.CourtadeKumar.isIncreasing_of_forall_increasingIn
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T11:50:54.076994+00:00
-- url     : https://prove2.me/submissions/26feef9d-43ef-4f4e-b92a-be33af613450

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/BooleanNoise/Rearrangement.lean:L86-L105
-- (upload_full_project.md Phase 4): solution for node OAI.LeanBlast.CourtadeKumar.isIncreasing_of_forall_increasingIn. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_CourtadeKumar
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_Model__CourtadeKumar
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_Statement__CourtadeKumar
import Definitions.Def_OAI_InformationTheory_BooleanNoise_Basic
import Definitions.Def_OAI_InformationTheory_BooleanNoise_FiniteNoise
import Definitions.Def_OAI_InformationTheory_BooleanNoise_Statement
import Definitions.Def_OAI_InformationTheory_BooleanNoise_EntropyScalars
import Definitions.Def_OAI_InformationTheory_BooleanNoise_FiniteDistribution
import Definitions.Def_OAI_InformationTheory_BooleanNoise_Attainment
import Definitions.Def_OAI_InformationTheory_BooleanNoise_Rearrangement

-- ---- from OAI.InformationTheory.BooleanNoise.Rearrangement ----
namespace OAI

noncomputable section

open scoped BigOperators

namespace LeanBlast.CourtadeKumar

variable {n : ℕ}

theorem increasingIn_setBit_mono {F : Cube n → ℝ} {i : Fin n}
    (hF : IsIncreasingIn i F) (x : Cube n) (a b : Bool) (hab : a ≤ b) :
    F (setBit i a x) ≤ F (setBit i b x) := by
  cases a <;> cases b
  · exact le_rfl
  · exact hF x
  · exact False.elim ((by decide : ¬ ((true : Bool) ≤ false)) hab)
  · exact le_rfl

theorem isIncreasing_of_forall_increasingIn {F : Cube n → ℝ}
    (hF : ∀ i, IsIncreasingIn i F) : IsIncreasing F := by
  intro x y hxy
  let fill (s : Finset (Fin n)) : Cube n := fun i => if i ∈ s then y i else x i
  have hfill : ∀ s : Finset (Fin n), F x ≤ F (fill s) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp [fill]
    | @insert i s hi ih =>
      have hstep : F (fill s) ≤ F (setBit i (y i) (fill s)) := by
        have horder : fill s i ≤ y i := by simp [fill, hi, hxy i]
        simpa only [setBit_self] using
          increasingIn_setBit_mono (hF i) (fill s) (fill s i) (y i) horder
      have heq : setBit i (y i) (fill s) = fill (insert i s) := by
        funext j
        by_cases hji : j = i
        · subst j; simp [fill]
        · simp [setBit, fill, hji]
      exact ih.trans (heq ▸ hstep)
  simpa [fill] using hfill Finset.univ

end LeanBlast.CourtadeKumar

end

end OAI

-- ---- platform node ----
open OAI OAI.LeanBlast OAI.LeanBlast.CourtadeKumar
open scoped BigOperators


theorem solution : type_of% @_root_.OAI.LeanBlast.CourtadeKumar.isIncreasing_of_forall_increasingIn := @_root_.OAI.LeanBlast.CourtadeKumar.isIncreasing_of_forall_increasingIn
