-- Prove2me | solution 1 for OAI.ThresholdParallelRepetition.FiniteProbability.Law.pi_avg_left
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T12:13:36.997413+00:00
-- url     : https://prove2.me/submissions/7112eb26-bc5b-4662-8b13-9f8be8e7580f

-- Generated from openai/math@1581d4c lean/OAI/Probability/EntangledGames/Resampling.lean:L147-L162
-- (upload_full_project.md Phase 4): solution for node OAI.ThresholdParallelRepetition.FiniteProbability.Law.pi_avg_left. The node keeps its source
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
import Definitions.Def_OAI_Probability_EntangledGames_SamplingStrategy
import Definitions.Def_OAI_Probability_EntangledGames_CorrelatedSampling
import Definitions.Def_OAI_Probability_EntangledGames_FiniteProbability
import Definitions.Def_OAI_Probability_EntangledGames_RelativeEntropy
import Definitions.Def_OAI_Probability_EntangledGames_Resampling

-- ---- from OAI.Probability.EntangledGames.FiniteProbability ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe u_α u_β u_γ u_E u_F u_ι

noncomputable section
open scoped BigOperators
namespace ThresholdParallelRepetition.FiniteProbability

namespace Law
variable {α : Type u_α} {β : Type u_β} {γ : Type u_γ} {E : Type u_E} [Fintype α] [Fintype β] [Fintype γ]
  [AddCommMonoid E] [Module ℝ E]

lemma normalize_weight [DecidableEq α] (w : α → ℝ) (hw : ∀ x, 0 ≤ w x) (a₀ x : α) :
    (∑ y, w y)*(normalize w hw a₀).weight x = w x := by
  rw [normalize]
  split_ifs with h
  · have hx : w x = 0 := (Finset.sum_eq_zero_iff_of_nonneg (fun y _ => hw y)).mp h x (Finset.mem_univ x)
    simp [h, hx]
  · simp only
    field_simp

section Pair
variable [DecidableEq α] [DecidableEq β]

omit [DecidableEq β] in
lemma second_given (p : Law (α×β)) (a₀ : α) (x : α) (y : β) :
    p.second.weight y*(p.givenSecond a₀ y).weight x = p.weight (x,y) :=
  normalize_weight _ _ _ _

omit [DecidableEq β] in
lemma disintegrate_second (p : Law (α×β)) (a₀ : α) (f : α×β → E) :
    p.avg f = p.second.avg (fun y => (p.givenSecond a₀ y).avg (fun x => f (x,y))) := by
  simp only [avg, Fintype.sum_prod_type, Finset.smul_sum, ← mul_smul, second_given]
  exact Finset.sum_comm
end Pair

section Pi
variable {ι : Type u_ι} [Fintype ι] [DecidableEq ι]

end Pi

section Information

variable {ι : Type u_ι} [Fintype ι] [DecidableEq ι] [DecidableEq α]
end Information

end Law
end ThresholdParallelRepetition.FiniteProbability

end

end OAI

-- ---- from OAI.Probability.EntangledGames.Resampling ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem dite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α} {e : ¬c → α} : (dite c t e) = t hc := @dif_pos c h hc α t e

namespace OAI

universe u_X u_Y u_I u_E u_F u_R

noncomputable section
open scoped BigOperators
namespace ThresholdParallelRepetition.FiniteProbability
namespace Law
variable {X : Type u_X} {Y : Type u_Y} {I : Type u_I} {E : Type u_E} [Fintype X] [Fintype Y] [Fintype I] [DecidableEq I]
  [DecidableEq X] [DecidableEq Y] [AddCommMonoid E] [Module ℝ E]

omit [DecidableEq Y] in
lemma pair_avg_left (μ : Law (X×Y)) (x₀ : X) (f : X×Y → E) :
    μ.avg (fun z => (μ.givenSecond x₀ z.2).avg (fun x => f (x,z.2))) = μ.avg f := by
  rw [disintegrate_second μ x₀, disintegrate_second μ x₀ f]
  simp only [avg_const]
omit [DecidableEq Y] in
lemma pi_avg_left (μ : Law (X×Y)) (x₀ : X) (i : I) (f : Profile I X Y → E) :
    (pi (fun _ : I => μ)).avg (μ.left x₀ i f) = (pi (fun _ : I => μ)).avg f := by
  rw [pi_avg_split _ i, pi_avg_split _ i f]
  rw [avg_comm, avg_comm μ]
  congr 1
  funext r
  change μ.avg (fun z => (μ.givenSecond x₀ _).avg _) = _
  have he (z : X×Y) (x : X) :
      updateLeft ((Equiv.funSplitAt i (X×Y)).symm (z,r)) i x =
        (Equiv.funSplitAt i (X×Y)).symm ((x,z.2),r) := by
    simpa only [updateLeft, Equiv.funSplitAt_symm_apply, dite_eq_left] using
      update_split i r z (x,z.2)
  simp_rw [he]
  simpa only [Equiv.funSplitAt_symm_apply, dite_eq_left] using
    (pair_avg_left μ x₀ (fun z => f ((Equiv.funSplitAt i (X×Y)).symm (z,r))))
section Linear
variable {F : Type u_F} [AddCommMonoid F] [Module ℝ F]
end Linear

section Folds

variable {F : Type u_F} [AddCommMonoid F] [Module ℝ F]
end Folds

section FixedCoordinate
variable {F : Type u_F} [AddCommMonoid F] [Module ℝ F]
end FixedCoordinate

section FoldLinear
variable {R : Type u_R} {F : Type u_F} [Fintype R] [AddCommMonoid F] [Module ℝ F]
end FoldLinear

end Law
end ThresholdParallelRepetition.FiniteProbability

end

end OAI

-- ---- platform node ----
open OAI OAI.ThresholdParallelRepetition OAI.ThresholdParallelRepetition.FiniteProbability OAI.ThresholdParallelRepetition.FiniteProbability.Law
open scoped BigOperators


theorem solution.{u_X,u_Y,u_I,u_E} : type_of% @_root_.OAI.ThresholdParallelRepetition.FiniteProbability.Law.pi_avg_left.{u_X,u_Y,u_I,u_E} := @_root_.OAI.ThresholdParallelRepetition.FiniteProbability.Law.pi_avg_left.{u_X,u_Y,u_I,u_E}
