-- Prove2me | solution 1 for OAI.LeanBlast.CourtadeKumar.noiseOperator_setBit
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T11:52:30.658599+00:00
-- url     : https://prove2.me/submissions/7bbf37a7-e2a2-4102-b475-090f840af610

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/BooleanNoise/Rearrangement.lean:L220-L238
-- (upload_full_project.md Phase 4): solution for node OAI.LeanBlast.CourtadeKumar.noiseOperator_setBit. The node keeps its source
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

-- ---- from OAI.Combinatorics.GotsmanLinial.Statement ----
namespace OAI

open scoped BigOperators

namespace LeanBlast.GotsmanLinial

theorem flip_involutive {n : ℕ} (i : Fin n) : Function.Involutive (flip i) :=
  flip_flip i

theorem flip_bijective {n : ℕ} (i : Fin n) : Function.Bijective (flip i) :=
  (flip_involutive i).bijective

end LeanBlast.GotsmanLinial

end OAI

-- ---- from OAI.InformationTheory.BooleanNoise.FiniteNoise ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

open scoped BigOperators

noncomputable section

universe u

namespace LeanBlast.CourtadeKumar

variable {n : ℕ}

theorem noiseKernel_split_coord (u : ℝ) (x y : Cube n) (i : Fin n) :
    noiseKernel u x y =
      (if x i = y i then (1 + u) / 2 else (1 - u) / 2) *
        ∏ j ∈ Finset.univ.erase i, if x j = y j then (1 + u) / 2 else (1 - u) / 2 := by
  exact (Finset.mul_prod_erase _ _ (Finset.mem_univ i)).symm

end LeanBlast.CourtadeKumar

end

end OAI

-- ---- from OAI.InformationTheory.BooleanNoise.Rearrangement ----
namespace OAI

noncomputable section

open scoped BigOperators

namespace LeanBlast.CourtadeKumar

variable {n : ℕ}

theorem pair_sum_setBit (i : Fin n) (F : Cube n → ℝ) (x : Cube n) :
    F (setBit i false x) + F (setBit i true x) = F x + F (flip i x) := by
  have hself := setBit_self i x
  cases hx : x i
  · simpa [setBit, flip, LeanBlast.GotsmanLinial.flip, hx] using
      congrArg (fun z => F z + F (setBit i true x)) hself
  · simpa [setBit, flip, LeanBlast.GotsmanLinial.flip, hx, add_comm] using
      congrArg (fun z => F (setBit i false x) + F z) hself

theorem sum_comp_flip (i : Fin n) (F : Cube n → ℝ) :
    (∑ x, F (flip i x)) = ∑ x, F x := by
  exact Fintype.sum_bijective (flip i) (LeanBlast.GotsmanLinial.flip_bijective i) _ _
    (fun _ => rfl)

theorem sum_setBit_pair (i : Fin n) (F : Cube n → ℝ) :
    (∑ x, (F (setBit i false x) + F (setBit i true x))) = 2 * ∑ x, F x := by
  simp_rw [pair_sum_setBit]
  rw [Finset.sum_add_distrib, sum_comp_flip]
  ring

theorem coordinateOffKernel_setBit_left (i : Fin n) (u : ℝ) (x y : Cube n) (b : Bool) :
    coordinateOffKernel i u (setBit i b x) y = coordinateOffKernel i u x y := by
  apply Finset.prod_congr rfl
  intro j hj
  simp only [setBit, Function.update_of_ne (Finset.mem_erase.mp hj).1]

theorem coordinateOffKernel_setBit_right (i : Fin n) (u : ℝ) (x y : Cube n) (b : Bool) :
    coordinateOffKernel i u x (setBit i b y) = coordinateOffKernel i u x y := by
  apply Finset.prod_congr rfl
  intro j hj
  simp only [setBit, Function.update_of_ne (Finset.mem_erase.mp hj).1]

theorem noiseKernel_setBit_pair (i : Fin n) (u : ℝ) (x y : Cube n) (a b : Bool) :
    noiseKernel u (setBit i a x) (setBit i b y) =
      (if a = b then (1 + u) / 2 else (1 - u) / 2) * coordinateOffKernel i u x y := by
  rw [noiseKernel_split_coord _ _ _ i]
  simp only [setBit_apply_same]
  change (if a = b then _ else _) *
    coordinateOffKernel i u (setBit i a x) (setBit i b y) = _
  rw [coordinateOffKernel_setBit_left, coordinateOffKernel_setBit_right]

theorem coordinateOffNoise_add (i : Fin n) (u : ℝ) (F G : Cube n → ℝ) (x : Cube n) :
    coordinateOffNoise i u (fun y => F y + G y) x =
      coordinateOffNoise i u F x + coordinateOffNoise i u G x := by
  simp only [coordinateOffNoise, mul_add, Finset.sum_add_distrib]

theorem coordinateOffNoise_smul (i : Fin n) (u c : ℝ) (F : Cube n → ℝ) (x : Cube n) :
    coordinateOffNoise i u (fun y => c * F y) x = c * coordinateOffNoise i u F x := by
  simp only [coordinateOffNoise, Finset.mul_sum, mul_left_comm]

theorem noiseOperator_setBit (i : Fin n) (u : ℝ) (F : Cube n → ℝ)
    (x : Cube n) (b : Bool) :
    noiseOperator u F (setBit i b x) =
      coordinateOffNoise i u (coordinatePairMean i F) x +
        (if b then u else -u) * coordinateOffNoise i u (coordinatePairDifference i F) x := by
  have h := sum_setBit_pair i (fun y => noiseKernel u (setBit i b x) y * F y)
  change _ = 2 * noiseOperator u F (setBit i b x) at h
  have heq : (∑ y, (noiseKernel u (setBit i b x) (setBit i false y) * F (setBit i false y) +
      noiseKernel u (setBit i b x) (setBit i true y) * F (setBit i true y))) =
      2 * coordinateOffNoise i u (fun y => coordinatePairMean i F y +
        (if b then u else -u) * coordinatePairDifference i F y) x := by
    rw [coordinateOffNoise, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro y _
    rw [noiseKernel_setBit_pair, noiseKernel_setBit_pair]
    cases b <;> simp only [Bool.false_eq_true, Bool.true_eq_false, ↓reduceIte,
      coordinatePairMean, coordinatePairDifference] <;> ring
  rw [heq, coordinateOffNoise_add, coordinateOffNoise_smul] at h
  linarith

end LeanBlast.CourtadeKumar

end

end OAI

-- ---- platform node ----
open OAI OAI.LeanBlast OAI.LeanBlast.CourtadeKumar
open scoped BigOperators


theorem solution : type_of% @_root_.OAI.LeanBlast.CourtadeKumar.noiseOperator_setBit := @_root_.OAI.LeanBlast.CourtadeKumar.noiseOperator_setBit
