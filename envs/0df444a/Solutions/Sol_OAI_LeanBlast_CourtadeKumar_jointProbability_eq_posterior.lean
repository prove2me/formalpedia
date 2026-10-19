-- Prove2me | solution 1 for OAI.LeanBlast.CourtadeKumar.jointProbability_eq_posterior
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T11:45:13.58251+00:00
-- url     : https://prove2.me/submissions/67098c6d-dbb3-45da-899a-b9bb7f9b155e

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/BooleanNoise/FiniteDistribution.lean:L70-L85
-- (upload_full_project.md Phase 4): solution for node OAI.LeanBlast.CourtadeKumar.jointProbability_eq_posterior. The node keeps its source
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

theorem noiseOperator_add (u : ℝ) (g h : Cube n → ℝ) (x : Cube n) :
    noiseOperator u (fun y => g y + h y) x = noiseOperator u g x + noiseOperator u h x := by
  simp [noiseOperator, mul_add, Finset.sum_add_distrib]

theorem noiseOperator_sub (u : ℝ) (g h : Cube n → ℝ) (x : Cube n) :
    noiseOperator u (fun y => g y - h y) x = noiseOperator u g x - noiseOperator u h x := by
  simp [noiseOperator, mul_sub, Finset.sum_sub_distrib]

theorem noiseOperator_smul (u c : ℝ) (g : Cube n → ℝ) (x : Cube n) :
    noiseOperator u (fun y => c * g y) x = c * noiseOperator u g x := by
  simp [noiseOperator, Finset.mul_sum, mul_left_comm]

end LeanBlast.CourtadeKumar

end

end OAI

-- ---- from OAI.InformationTheory.BooleanNoise.FiniteDistribution ----
namespace OAI

noncomputable section

open scoped BigOperators

namespace LeanBlast.CourtadeKumar

variable {n : ℕ}

theorem signProbability_signEncoding (f : Cube n → Bool) (x : Cube n) (b : Bool) :
    signProbability (signEncoding f x) b = if f x = b then 1 else 0 := by
  cases b <;> cases hfx : f x <;> simp [signProbability, signEncoding, hfx]

theorem noiseOperator_signProbability (u : ℝ) (g : Cube n → ℝ) (b : Bool) (x : Cube n) :
    noiseOperator u (fun y => signProbability (g y) b) x =
      signProbability (noiseOperator u g x) b := by
  cases b
  · change noiseOperator u (fun y => (1 - g y) / 2) x = (1 - noiseOperator u g x) / 2
    have hfun : (fun y => (1 - g y) / 2) = (fun y => (1 / 2 : ℝ) * (1 - g y)) := by
      funext y
      ring
    rw [hfun, noiseOperator_smul, noiseOperator_sub, noiseOperator_const]
    ring
  · change noiseOperator u (fun y => (1 + g y) / 2) x = (1 + noiseOperator u g x) / 2
    have hfun : (fun y => (1 + g y) / 2) = (fun y => (1 / 2 : ℝ) * (1 + g y)) := by
      funext y
      ring
    rw [hfun, noiseOperator_smul, noiseOperator_add, noiseOperator_const]
    ring

theorem bitFlipKernel_eq_noiseKernel (ε : ℝ) (x y : Cube n) :
    bitFlipKernel ε x y = noiseKernel (1 - 2 * ε) x y := by
  unfold bitFlipKernel noiseKernel
  apply Finset.prod_congr rfl
  intro i _
  split_ifs <;> ring

theorem jointProbability_eq_posterior (ε : ℝ) (f : Cube n → Bool) (b : Bool) (y : Cube n) :
    jointProbability ε f b y =
      signProbability (noiseOperator (1 - 2 * ε) (signEncoding f) y) b / (2 : ℝ) ^ n := by
  have hterm (x : Cube n) :
      (if f x = b then bitFlipKernel ε x y else 0) =
        noiseKernel (1 - 2 * ε) y x * signProbability (signEncoding f x) b := by
    rw [signProbability_signEncoding]
    by_cases h : f x = b
    · simp only [h, ite_true, mul_one, bitFlipKernel_eq_noiseKernel]
      exact noiseKernel_symm _ x y
    · simp [h]
  unfold jointProbability cubeAverage
  simp_rw [hterm]
  change noiseOperator (1 - 2 * ε) (fun x => signProbability (signEncoding f x) b) y /
    (2 : ℝ) ^ n = _
  rw [noiseOperator_signProbability]

end LeanBlast.CourtadeKumar

end

end OAI

-- ---- platform node ----
open OAI OAI.LeanBlast OAI.LeanBlast.CourtadeKumar
open scoped BigOperators


theorem solution : type_of% @_root_.OAI.LeanBlast.CourtadeKumar.jointProbability_eq_posterior := @_root_.OAI.LeanBlast.CourtadeKumar.jointProbability_eq_posterior
