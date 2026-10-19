-- Prove2me | solution 1 for OAI.LeanBlast.CourtadeKumar.noiseOperator_dictator
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T11:46:39.538079+00:00
-- url     : https://prove2.me/submissions/9e11fef0-eb90-4366-bc75-9047799a1494

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/BooleanNoise/Attainment.lean:L16-L37
-- (upload_full_project.md Phase 4): solution for node OAI.LeanBlast.CourtadeKumar.noiseOperator_dictator. The node keeps its source
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

-- ---- from OAI.InformationTheory.BooleanNoise.FiniteNoise ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

open scoped BigOperators

noncomputable section

universe u

namespace LeanBlast.CourtadeKumar

variable {n : ℕ}

theorem noiseOperator_prod (u : ℝ) (f : Fin n → Bool → ℝ) (x : Cube n) :
    noiseOperator u (fun y => ∏ i, f i (y i)) x =
      ∏ i, ∑ b : Bool, (if x i = b then (1 + u) / 2 else (1 - u) / 2) * f i b := by
  unfold noiseOperator noiseKernel
  simp_rw [← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun (i : Fin n) (b : Bool) =>
    (if x i = b then (1 + u) / 2 else (1 - u) / 2) * f i b)).symm

end LeanBlast.CourtadeKumar

end

end OAI

-- ---- from OAI.InformationTheory.BooleanNoise.Attainment ----
namespace OAI

open scoped BigOperators

noncomputable section

namespace LeanBlast.CourtadeKumar

variable {n : ℕ}

theorem noiseOperator_dictator (u : ℝ) (i : Fin n) (x : Cube n) :
    noiseOperator u (signEncoding (dictator i)) x =
      u * signEncoding (dictator i) x := by
  let a : Fin n → Bool → ℝ :=
    fun j b => if j = i then (if b then 1 else -1) else 1
  have hprod : (fun y : Cube n => ∏ j, a j (y j)) = signEncoding (dictator i) := by
    funext y
    simp [a, signEncoding, dictator]
    rfl
  have hfactor (j : Fin n) :
      (∑ b : Bool, (if x j = b then (1 + u) / 2 else (1 - u) / 2) * a j b) =
        if j = i then u * signEncoding (dictator i) x else 1 := by
    by_cases hji : j = i
    · subst j
      cases hx : x i <;> simp [a, hx, signEncoding, dictator] <;> ring
    · cases hx : x j <;> simp [a, hji] <;> ring
  calc
    _ = noiseOperator u (fun y => ∏ j, a j (y j)) x := by rw [hprod]
    _ = ∏ j, ∑ b : Bool,
        (if x j = b then (1 + u) / 2 else (1 - u) / 2) * a j b :=
      noiseOperator_prod u a x
    _ = u * signEncoding (dictator i) x := by simp_rw [hfactor]; simp

end LeanBlast.CourtadeKumar

end

end OAI

-- ---- platform node ----
open OAI OAI.LeanBlast OAI.LeanBlast.CourtadeKumar
open scoped BigOperators


theorem solution : type_of% @_root_.OAI.LeanBlast.CourtadeKumar.noiseOperator_dictator := @_root_.OAI.LeanBlast.CourtadeKumar.noiseOperator_dictator
