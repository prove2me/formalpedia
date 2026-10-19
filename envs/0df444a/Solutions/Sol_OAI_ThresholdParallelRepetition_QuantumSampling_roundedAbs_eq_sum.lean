-- Prove2me | solution 1 for OAI.ThresholdParallelRepetition.QuantumSampling.roundedAbs_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T11:54:07.424351+00:00
-- url     : https://prove2.me/submissions/27ddb2fc-a636-4995-a373-7bbbed26f648

-- Generated from openai/math@1581d4c lean/OAI/Probability/EntangledGames/CoherentFilters.lean:L271-L285
-- (upload_full_project.md Phase 4): solution for node OAI.ThresholdParallelRepetition.QuantumSampling.roundedAbs_eq_sum. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_EntangledGames
import Definitions.Def_OAI_Probability_EntangledGames_Basic
import Definitions.Def_OAI_Probability_EntangledGames_Resolvent
import Definitions.Def_OAI_Probability_EntangledGames_SpectralEntropy
import Definitions.Def_OAI_Probability_EntangledGames_Purification
import Definitions.Def_OAI_Probability_EntangledGames_MeasurementTransport
import Definitions.Def_OAI_Probability_EntangledGames_HilbertSchmidt
import Definitions.Def_OAI_Probability_EntangledGames_SpectralBins
import Definitions.Def_OAI_Probability_EntangledGames_CoherentFilters

-- ---- from OAI.Probability.EntangledGames.CoherentFilters ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e
namespace OAI

universe u_m u_n u_p u_ι u_q

open scoped BigOperators ComplexOrder
open scoped MatrixOrder
open Matrix
open MeasureTheory Filter Set
open scoped Topology
open scoped Matrix.Norms.Elementwise
open scoped Interval

noncomputable section
open scoped BigOperators MatrixOrder ComplexOrder
open Matrix
namespace ThresholdParallelRepetition.QuantumSampling
open ThresholdParallelRepetition.MeasurementTransport
variable {m : Type u_m} {n : Type u_n} [Fintype m] [Fintype n] [DecidableEq n]

end ThresholdParallelRepetition.QuantumSampling

noncomputable section
open scoped BigOperators MatrixOrder ComplexOrder
open Matrix
namespace ThresholdParallelRepetition.QuantumSampling
variable {n : Type u_n} [Fintype n] [DecidableEq n]

end ThresholdParallelRepetition.QuantumSampling

noncomputable section
open scoped BigOperators MatrixOrder ComplexOrder
open Matrix
namespace ThresholdParallelRepetition.QuantumSampling
variable {m : Type u_m} {n : Type u_n} {p : Type u_p} [Fintype m] [Fintype n] [Fintype p]

variable [DecidableEq m]
end ThresholdParallelRepetition.QuantumSampling

noncomputable section
open scoped BigOperators MatrixOrder ComplexOrder
open Matrix
namespace ThresholdParallelRepetition.QuantumSampling
variable {n : Type u_n} [Fintype n] [DecidableEq n]

lemma sum_binScale_indicator (L : Finset ℤ) (ε s a : ℝ)
    (h : 0 < a → ⌊Real.log a/ε+s⌋ ∈ L) :
    (∑ l ∈ L, binScale ε s l * binIndicator ε s l a) = binWeight a ε s := by
  by_cases ha : 0 < a
  · simp only [binIndicator, ha, true_and, binWeight, ite_true, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq, ite_eq_left (h ha)]
    rfl
  · simp [binIndicator, binWeight, ha]

lemma roundedAbs_eq_sum (L : Finset ℤ) {A : Matrix n n ℂ} (ε s : ℝ)
    (hL : CoversBins L A ε s) :
    roundedAbs A ε s = ∑ l : L, binScale ε s l • binProjection A ε s l := by
  unfold roundedAbs binProjection
  calc
    _ = cfc (∑ l : L, fun a => binScale ε s l * binIndicator ε s l a) A := by
      apply cfc_congr; intro a ha
      simp only [Finset.sum_apply]
      rw [Finset.sum_coe_sort L (fun l => binScale ε s l * binIndicator ε s l a)]
      exact (sum_binScale_indicator L ε s a (hL a ha)).symm
    _ = _ := by
      erw [cfc_sum_univ (fun l : L => fun a => binScale ε s l * binIndicator ε s l a) A
        (fun _ => A.finite_real_spectrum.continuousOn _)]
      apply Finset.sum_congr rfl; intro l _
      exact cfc_const_mul _ _ _ (A.finite_real_spectrum.continuousOn _)

end ThresholdParallelRepetition.QuantumSampling

noncomputable section
open scoped BigOperators MatrixOrder ComplexOrder Kronecker
open Matrix
namespace ThresholdParallelRepetition.QuantumSampling

variable {m : Type u_m} {n : Type u_n} {p : Type u_p} {q : Type u_q} [Fintype m] [Fintype n] [Fintype p] [Fintype q]

end ThresholdParallelRepetition.QuantumSampling

end
end
end
end
end

end OAI

-- ---- platform node ----
open OAI OAI.ThresholdParallelRepetition OAI.ThresholdParallelRepetition.QuantumSampling
open scoped BigOperators ComplexOrder
open scoped MatrixOrder
open Matrix
open MeasureTheory Filter Set
open scoped Topology
open scoped Matrix.Norms.Elementwise
open scoped Interval
open scoped BigOperators MatrixOrder ComplexOrder
open Matrix
open scoped BigOperators MatrixOrder ComplexOrder
open Matrix
open scoped BigOperators MatrixOrder ComplexOrder
open Matrix
open scoped BigOperators MatrixOrder ComplexOrder
open Matrix


theorem solution.{u_n} : type_of% @_root_.OAI.ThresholdParallelRepetition.QuantumSampling.roundedAbs_eq_sum.{u_n} := @_root_.OAI.ThresholdParallelRepetition.QuantumSampling.roundedAbs_eq_sum.{u_n}
