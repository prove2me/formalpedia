-- Prove2me | solution 1 for OAI.ThresholdParallelRepetition.MixedExposure.massAt_left
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T12:25:30.227344+00:00
-- url     : https://prove2.me/submissions/1872e051-b3a2-4195-81c6-fe627131b608

-- Generated from openai/math@1581d4c lean/OAI/Probability/EntangledGames/ExposureChain.lean:L339-L364
-- (upload_full_project.md Phase 4): solution for node OAI.ThresholdParallelRepetition.MixedExposure.massAt_left. The node keeps its source
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

omit [Fintype m] [Fintype I] [Fintype R] [DecidableEq Y] [DecidableEq n] [DecidableEq m] in
lemma left_update_eq (μ : Law (X×Y)) (x₀ : X) (i : I)
    (F : Profile I X Y → Matrix m m ℂ) (z : Profile I X Y) (q : X×Y) :
    μ.left x₀ i F (Function.update z i q) =
      (μ.givenSecond x₀ q.2).avg (fun x => F (Function.update z i (x,q.2))) := by
  simp only [left, Function.update_self, updateLeft, Function.update_idem]

omit [DecidableEq Y] [DecidableEq m] [DecidableEq n] in
lemma massAt_left (μ : Law (X×Y)) (x₀ : X) (θ : R → Profile I X Y → ℝ) (p : ℝ) (i : I)
    (C : Matrix m n ℂ) (F : R → Profile I X Y → Matrix m m ℂ)
    (H : R → Profile I X Y → Matrix n n ℂ) (hH : ∀ r, IgnoresLeft (H r) i) (q : X×Y) :
    massAt μ θ p i C (fun r => μ.left x₀ i (F r)) H q =
      (μ.givenSecond x₀ q.2).avg (fun x => massAt μ θ p i C F H (x,q.2)) := by
  unfold massAt
  rw [show (fun x => (1/p)*∑ r, (pi (fun _ : I => μ)).avg (fun z => θ r z *
      prob C (F r (Function.update z i (x,q.2))) (H r (Function.update z i (x,q.2))))) =
        (fun x => (1/p) • ∑ r, (pi (fun _ : I => μ)).avg (fun z => θ r z *
      prob C (F r (Function.update z i (x,q.2))) (H r (Function.update z i (x,q.2))))) from rfl,
    avg_smul, avg_sum]
  congr 1
  apply Finset.sum_congr rfl; intro r _
  rw [avg_comm]
  congr 1; funext z
  rw [show (fun x => θ r z*prob C (F r (Function.update z i (x,q.2))) (H r (Function.update z i (x,q.2)))) =
      (fun x => θ r z • prob C (F r (Function.update z i (x,q.2))) (H r (Function.update z i (x,q.2)))) from rfl,
    avg_smul]
  dsimp only
  rw [left_update_eq]
  congr 1
  have he (x : X) : H r (Function.update z i (x,q.2)) = H r (Function.update z i q) := by
    simpa only [updateLeft, Function.update_self, Function.update_idem] using hH r (Function.update z i q) x
  simp_rw [he]
  exact (μ.givenSecond x₀ q.2).avg_linear _ (probLeft C (H r (Function.update z i q)))
end ThresholdParallelRepetition.MixedExposure

end

end OAI

-- ---- platform node ----
open OAI OAI.ThresholdParallelRepetition OAI.ThresholdParallelRepetition.MixedExposure
open scoped BigOperators MatrixOrder ComplexOrder
open Matrix
open QuantumSampling OperatorEntropy FiniteProbability Law


theorem solution.{u_I,u_X,u_Y,u_R,u_m,u_n} : type_of% @_root_.OAI.ThresholdParallelRepetition.MixedExposure.massAt_left.{u_I,u_X,u_Y,u_R,u_m,u_n} := @_root_.OAI.ThresholdParallelRepetition.MixedExposure.massAt_left.{u_I,u_X,u_Y,u_R,u_m,u_n}
