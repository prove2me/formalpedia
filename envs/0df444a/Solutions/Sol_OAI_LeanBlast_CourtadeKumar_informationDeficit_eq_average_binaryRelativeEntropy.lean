-- Prove2me | solution 1 for OAI.LeanBlast.CourtadeKumar.informationDeficit_eq_average_binaryRelativeEntropy
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T12:39:52.292999+00:00
-- url     : https://prove2.me/submissions/cf31b20b-42bd-4183-a89d-0bb3df128140

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/BooleanNoise/CubeVariance.lean:L82-L102
-- (upload_full_project.md Phase 4): solution for node OAI.LeanBlast.CourtadeKumar.informationDeficit_eq_average_binaryRelativeEntropy. The node keeps its source
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
import Definitions.Def_OAI_InformationTheory_BooleanNoise_CurvatureCertificates
import Definitions.Def_OAI_InformationTheory_BooleanNoise_ComparisonEstimates
import Definitions.Def_OAI_InformationTheory_BooleanNoise_InverseScalars
import Definitions.Def_OAI_InformationTheory_BooleanNoise_EntropySeries
import Definitions.Def_OAI_InformationTheory_BooleanNoise_EntropyBounds
import Definitions.Def_OAI_InformationTheory_BooleanNoise_MediumCurvature
import Definitions.Def_OAI_InformationTheory_BooleanNoise_CurvatureBounds
import Definitions.Def_OAI_InformationTheory_BooleanNoise_LRegularity
import Definitions.Def_OAI_InformationTheory_BooleanNoise_SemigroupFlow
import Definitions.Def_OAI_InformationTheory_BooleanNoise_CubeSplits
import Definitions.Def_OAI_InformationTheory_BooleanNoise_PairEntropy
import Definitions.Def_OAI_InformationTheory_BooleanNoise_LambdaScalars
import Definitions.Def_OAI_InformationTheory_BooleanNoise_JensenGaps
import Definitions.Def_OAI_InformationTheory_BooleanNoise_CubeVariance

-- ---- from OAI.InformationTheory.BooleanNoise.FiniteNoise ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

open scoped BigOperators

noncomputable section

universe u

namespace LeanBlast.CourtadeKumar

variable {n : ℕ}

theorem cubeAverage_sub (g h : Cube n → ℝ) :
    cubeAverage (fun x => g x - h x) = cubeAverage g - cubeAverage h := by
  simp [cubeAverage, Finset.sum_sub_distrib, sub_div]

theorem cubeAverage_smul (c : ℝ) (g : Cube n → ℝ) :
    cubeAverage (fun x => c * g x) = c * cubeAverage g := by
  simp [cubeAverage, ← Finset.mul_sum, mul_div_assoc]

theorem cubeAverage_strict_mono {g h : Cube n → ℝ} (hgh : ∀ x, g x ≤ h x)
    (hlt : ∃ x, g x < h x) : cubeAverage g < cubeAverage h := by
  apply (div_lt_div_iff_of_pos_right (cube_denominator_pos n)).2
  apply Finset.sum_lt_sum (fun x _ => hgh x)
  obtain ⟨x, hx⟩ := hlt
  exact ⟨x, Finset.mem_univ x, hx⟩

theorem cubeAverage_lt {g h : Cube n → ℝ} (hgh : ∀ x, g x < h x) :
    cubeAverage g < cubeAverage h := by
  exact cubeAverage_strict_mono (fun x => (hgh x).le) ⟨fun _ => false, hgh _⟩

theorem IsInterior.cubeAverage {g : Cube n → ℝ} (hg : IsInterior g) :
    -1 < cubeAverage g ∧ cubeAverage g < 1 := by
  constructor
  · simpa using cubeAverage_lt (fun x => (hg x).1)
  · simpa using cubeAverage_lt (fun x => (hg x).2)

end LeanBlast.CourtadeKumar

end

end OAI

-- ---- from OAI.InformationTheory.BooleanNoise.CubeVariance ----
namespace OAI

open scoped BigOperators

noncomputable section

namespace LeanBlast.CourtadeKumar

variable {n : ℕ}

theorem binaryRelativeEntropy_eq {a m : ℝ}
    (ha : -1 < a ∧ a < 1) (hm : -1 < m ∧ m < 1) :
    binaryRelativeEntropy a m = psi a - psi m -
      (a - m) / 2 * (Real.log (1 + m) - Real.log (1 - m)) := by
  have hap : 1 + a ≠ 0 := ne_of_gt (by linarith)
  have ham : 1 - a ≠ 0 := ne_of_gt (by linarith)
  have hmp : 1 + m ≠ 0 := ne_of_gt (by linarith)
  have hmm : 1 - m ≠ 0 := ne_of_gt (by linarith)
  unfold binaryRelativeEntropy psi
  rw [Real.log_div hap hmp, Real.log_div ham hmm]
  ring

theorem informationDeficit_eq_average_psi (g : Cube n → ℝ) :
    informationDeficit g = cubeAverage (fun x => psi (g x)) - psi (cubeAverage g) := by
  unfold informationDeficit entropyAverage entropy
  rw [cubeAverage_sub, cubeAverage_const]
  ring

theorem informationDeficit_eq_average_binaryRelativeEntropy
    {g : Cube n → ℝ} (hg : IsInterior g) :
    informationDeficit g =
      cubeAverage (fun x => binaryRelativeEntropy (g x) (cubeAverage g)) := by
  let m := cubeAverage g
  let c := Real.log (1 + m) - Real.log (1 - m)
  have hlin : cubeAverage (fun x => (g x - m) / 2 * c) = 0 := by
    have heq : (fun x => (g x - m) / 2 * c) = (fun x => (c / 2) * (g x - m)) := by
      funext x
      ring
    rw [heq, cubeAverage_smul, cubeAverage_sub, cubeAverage_const]
    dsimp [m]
    ring
  have heq : (fun x => binaryRelativeEntropy (g x) m) =
      (fun x => psi (g x) - psi m - (g x - m) / 2 * c) := by
    funext x
    exact binaryRelativeEntropy_eq (hg x) hg.cubeAverage
  rw [show (fun x => binaryRelativeEntropy (g x) (cubeAverage g)) =
      (fun x => binaryRelativeEntropy (g x) m) from rfl, heq]
  rw [cubeAverage_sub, cubeAverage_sub, cubeAverage_const, hlin, sub_zero]
  exact informationDeficit_eq_average_psi g

end LeanBlast.CourtadeKumar

end

end OAI

-- ---- platform node ----
open OAI OAI.LeanBlast OAI.LeanBlast.CourtadeKumar
open scoped BigOperators


theorem solution : type_of% @_root_.OAI.LeanBlast.CourtadeKumar.informationDeficit_eq_average_binaryRelativeEntropy := @_root_.OAI.LeanBlast.CourtadeKumar.informationDeficit_eq_average_binaryRelativeEntropy
