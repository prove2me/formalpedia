-- Prove2me | solution 1 for OAI.LeanBlast.CourtadeKumar.informationDeficit_noise_dictator
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T11:49:11.4392+00:00
-- url     : https://prove2.me/submissions/78d6f867-e511-4773-bfb0-56b8a8d4800b

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/BooleanNoise/Attainment.lean:L106-L119
-- (upload_full_project.md Phase 4): solution for node OAI.LeanBlast.CourtadeKumar.informationDeficit_noise_dictator. The node keeps its source
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
import Theorems.Thm_OAI_LeanBlast_CourtadeKumar_noiseOperator_dictator

-- ---- from OAI.InformationTheory.BooleanNoise.FiniteNoise ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

open scoped BigOperators

noncomputable section

universe u

namespace LeanBlast.CourtadeKumar

variable {n : ℕ}

theorem noiseKernel_symm (u : ℝ) (x y : Cube n) :
    noiseKernel u x y = noiseKernel u y x := by
  apply Finset.prod_congr rfl
  intro i _
  by_cases h : x i = y i
  · rw [ite_eq_left h, ite_eq_left h.symm]
  · rw [ite_eq_right h, ite_eq_right (Ne.symm h)]

theorem noiseKernel_col_sum (u : ℝ) (y : Cube n) :
    ∑ x, noiseKernel u x y = 1 := by
  simp_rw [noiseKernel_symm u]
  exact noiseKernel_row_sum u y

theorem cubeAverage_noiseOperator (u : ℝ) (g : Cube n → ℝ) :
    cubeAverage (noiseOperator u g) = cubeAverage g := by
  unfold cubeAverage noiseOperator
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul, noiseKernel_col_sum, one_mul]

end LeanBlast.CourtadeKumar

end

end OAI

-- ---- from OAI.InformationTheory.BooleanNoise.Attainment ----
namespace OAI

open scoped BigOperators

noncomputable section

namespace LeanBlast.CourtadeKumar

variable {n : ℕ}

theorem cubeAverage_dictator (i : Fin n) : cubeAverage (signEncoding (dictator i)) = 0 := by
  simpa only [noiseOperator_zero_correlation, zero_mul] using
    noiseOperator_dictator 0 i (fun _ => false)

theorem informationDeficit_noise_dictator (u : ℝ) (i : Fin n) :
    informationDeficit (noiseOperator u (signEncoding (dictator i))) = psi u := by
  have he : entropyAverage (noiseOperator u (signEncoding (dictator i))) = entropy u := by
    have hpoint :
        (fun x => entropy (noiseOperator u (signEncoding (dictator i)) x)) =
          fun _ : Cube n => entropy u := by
      funext x
      rw [noiseOperator_dictator]
      cases hx : x i <;> simp [signEncoding, dictator, hx]
    unfold entropyAverage
    rw [hpoint, cubeAverage_const]
  rw [informationDeficit, cubeAverage_noiseOperator, cubeAverage_dictator,
    entropy_zero, he]
  simp [entropy]

end LeanBlast.CourtadeKumar

end

end OAI

-- ---- platform node ----
open OAI OAI.LeanBlast OAI.LeanBlast.CourtadeKumar
open scoped BigOperators


theorem solution : type_of% @_root_.OAI.LeanBlast.CourtadeKumar.informationDeficit_noise_dictator := @_root_.OAI.LeanBlast.CourtadeKumar.informationDeficit_noise_dictator
