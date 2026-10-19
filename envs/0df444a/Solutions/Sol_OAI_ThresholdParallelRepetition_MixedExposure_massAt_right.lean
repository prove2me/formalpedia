-- Prove2me | solution 1 for OAI.ThresholdParallelRepetition.MixedExposure.massAt_right
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T12:23:13.356268+00:00
-- url     : https://prove2.me/submissions/978711a6-bfaf-4d45-9ca6-a0fc1876add1

-- Generated from openai/math@1581d4c lean/OAI/Probability/EntangledGames/ExposureChain.lean:L312-L337
-- (upload_full_project.md Phase 4): solution for node OAI.ThresholdParallelRepetition.MixedExposure.massAt_right. The node keeps its source
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
import Definitions.Def_OAI_Probability_EntangledGames_EffectExposure
import Definitions.Def_OAI_Probability_EntangledGames_ExposureChain

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

lemma avg_smul (p : Law α) (r : ℝ) (f : α → E) :
    p.avg (fun x => r • f x) = r • p.avg f := by
  simp only [avg, Finset.smul_sum, smul_comm (p.weight _) r]
lemma avg_linear (p : Law α) (f : α → E) {F : Type u_F} [AddCommMonoid F] [Module ℝ F]
    (L : E →ₗ[ℝ] F) : L (p.avg f) = p.avg (fun x => L (f x)) := by
  simp [avg]

section Pair
variable [DecidableEq α] [DecidableEq β]

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

-- ---- from OAI.Probability.EntangledGames.ExposureChain ----
namespace OAI

universe u_I u_X u_Y u_R u_m u_n u_E u_Z

noncomputable section
open scoped BigOperators MatrixOrder ComplexOrder
open Matrix
namespace ThresholdParallelRepetition.MixedExposure
open QuantumSampling Resolvent OperatorEntropy FiniteProbability Law

variable {X : Type u_X} {Y : Type u_Y} {I : Type u_I} {R : Type u_R} {m : Type u_m} {n : Type u_n} [Fintype X] [Fintype Y] [Fintype I]
  [DecidableEq X] [DecidableEq Y] [DecidableEq I]
  [Fintype R] [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]

variable {E : Type u_E} [AddCommMonoid E] [Module ℝ E]
end ThresholdParallelRepetition.MixedExposure

end

noncomputable section
open scoped BigOperators MatrixOrder ComplexOrder
open Matrix
namespace ThresholdParallelRepetition.MixedExposure
open QuantumSampling Resolvent OperatorEntropy FiniteProbability Law
variable {R : Type u_R} {Z : Type u_Z} {m : Type u_m} {n : Type u_n} [Fintype R] [Nonempty R] [Fintype Z]
  [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]

end ThresholdParallelRepetition.MixedExposure

end

noncomputable section
open scoped BigOperators MatrixOrder ComplexOrder
open Matrix
namespace ThresholdParallelRepetition.MixedExposure
open QuantumSampling Resolvent OperatorEntropy FiniteProbability Law
variable {X : Type u_X} {Y : Type u_Y} {I : Type u_I} {R : Type u_R} {m : Type u_m} {n : Type u_n} [Fintype X] [Fintype Y] [Fintype I]
  [DecidableEq X] [DecidableEq Y] [DecidableEq I] [Nonempty X] [Nonempty Y]
  [Fintype R] [DecidableEq R] [Nonempty R]
  [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]

end ThresholdParallelRepetition.MixedExposure

end

noncomputable section
open scoped BigOperators MatrixOrder ComplexOrder
open Matrix
namespace ThresholdParallelRepetition.MixedExposure
open QuantumSampling OperatorEntropy FiniteProbability Law
variable {X : Type u_X} {Y : Type u_Y} {I : Type u_I} {R : Type u_R} {m : Type u_m} {n : Type u_n} [Fintype X] [Fintype Y] [Fintype I] [DecidableEq I]
  [Fintype R] [DecidableEq X] [DecidableEq Y]
  [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

omit [Fintype n] [Fintype I] [Fintype R] [DecidableEq X] [DecidableEq n] [DecidableEq m] in
lemma right_update_eq (μ : Law (X×Y)) (y₀ : Y) (i : I)
    (H : Profile I X Y → Matrix n n ℂ) (z : Profile I X Y) (q : X×Y) :
    μ.right y₀ i H (Function.update z i q) =
      (μ.givenFirst y₀ q.1).avg (fun y => H (Function.update z i (q.1,y))) := by
  simp only [right, Function.update_self, updateRight, Function.update_idem]
omit [DecidableEq X] [DecidableEq m] [DecidableEq n] in
lemma massAt_right (μ : Law (X×Y)) (y₀ : Y) (θ : R → Profile I X Y → ℝ) (p : ℝ) (i : I)
    (C : Matrix m n ℂ) (F : R → Profile I X Y → Matrix m m ℂ)
    (H : R → Profile I X Y → Matrix n n ℂ) (hF : ∀ r, IgnoresRight (F r) i) (q : X×Y) :
    massAt μ θ p i C F (fun r => μ.right y₀ i (H r)) q =
      (μ.givenFirst y₀ q.1).avg (fun y => massAt μ θ p i C F H (q.1,y)) := by
  unfold massAt
  rw [show (fun y => (1/p)*∑ r, (pi (fun _ : I => μ)).avg (fun z => θ r z *
      prob C (F r (Function.update z i (q.1,y))) (H r (Function.update z i (q.1,y))))) =
        (fun y => (1/p) • ∑ r, (pi (fun _ : I => μ)).avg (fun z => θ r z *
      prob C (F r (Function.update z i (q.1,y))) (H r (Function.update z i (q.1,y))))) from rfl,
    avg_smul, avg_sum]
  congr 1
  apply Finset.sum_congr rfl; intro r _
  rw [avg_comm]
  congr 1; funext z
  rw [show (fun y => θ r z*prob C (F r (Function.update z i (q.1,y))) (H r (Function.update z i (q.1,y)))) =
      (fun y => θ r z • prob C (F r (Function.update z i (q.1,y))) (H r (Function.update z i (q.1,y)))) from rfl,
    avg_smul]
  dsimp only
  rw [right_update_eq]
  congr 1
  have he (y : Y) : F r (Function.update z i (q.1,y)) = F r (Function.update z i q) := by
    simpa only [updateRight, Function.update_self, Function.update_idem] using hF r (Function.update z i q) y
  simp_rw [he]
  exact (μ.givenFirst y₀ q.1).avg_linear _ (probRight C (F r (Function.update z i q)))

end ThresholdParallelRepetition.MixedExposure

end

end OAI

-- ---- platform node ----
open OAI OAI.ThresholdParallelRepetition OAI.ThresholdParallelRepetition.MixedExposure
open scoped BigOperators MatrixOrder ComplexOrder
open Matrix
open QuantumSampling OperatorEntropy FiniteProbability Law


theorem solution.{u_I,u_X,u_Y,u_R,u_m,u_n} : type_of% @_root_.OAI.ThresholdParallelRepetition.MixedExposure.massAt_right.{u_I,u_X,u_Y,u_R,u_m,u_n} := @_root_.OAI.ThresholdParallelRepetition.MixedExposure.massAt_right.{u_I,u_X,u_Y,u_R,u_m,u_n}
