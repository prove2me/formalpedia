-- Prove2me | solution 1 for OAI.NoiselessRegression.Learner.riesz_success
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T23:25:22.644909+00:00
-- url     : https://prove2.me/submissions/51fff767-e654-497b-97e0-877f1992788b

-- Generated from openai/math@1581d4c lean/OAI/Probability/ProjectionMoments/Streaming.lean:L15-L77
-- (upload_full_project.md Phase 4): solution for node OAI.NoiselessRegression.Learner.riesz_success. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Model
import Definitions.Def_OAI_Probability_GaussianRegression_Nets__ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Gram__ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_ReplicaMoments__ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Smoothing__ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Projection__ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Support__ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Blocks__ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Sphere__ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Stream__ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Caps__ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Execution__ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Rotational__ProjectionMoments
import Definitions.Def_OAI_Probability_ProjectionMoments_Graph
import Definitions.Def_OAI_Probability_ProjectionMoments_Frames
import Definitions.Def_OAI_Probability_ProjectionMoments_SphereDensity
import Definitions.Def_OAI_Probability_ProjectionMoments_FrameMoments
import Definitions.Def_OAI_Probability_ProjectionMoments_RieszPotential
import Definitions.Def_OAI_Probability_ProjectionMoments_Polar
import Definitions.Def_OAI_Probability_ProjectionMoments_BallMoments
import Definitions.Def_OAI_Probability_ProjectionMoments_CapTests
import Definitions.Def_OAI_Probability_ProjectionMoments_CapDuality
import Definitions.Def_OAI_Probability_ProjectionMoments_WeightedCover
import Definitions.Def_OAI_Probability_ProjectionMoments_Stopping
import Definitions.Def_OAI_Probability_ProjectionMoments_BorelRules
import Definitions.Def_OAI_Probability_ProjectionMoments_Kernels
import Definitions.Def_OAI_Probability_ProjectionMoments_Realization
import Definitions.Def_OAI_Probability_ProjectionMoments_StoppingKernel
import Theorems.Thm_OAI_NoiselessRegression_Learner_streaming_success_bound_tagged

-- ---- from OAI.Probability.ProjectionMoments.Stopping ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace
namespace NoiselessRegression

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable {J : Type*} [Fintype J] [MeasurableSpace J] [MeasurableSingletonClass J]

variable [Nontrivial E] [Nonempty J]

end

namespace Learner
universe u
variable {d M T : ℕ} {Ω : Type u}

lemma card_taggedState (M T : ℕ) : Fintype.card (TaggedState M T) = (T+2)*2^M := by
  simp only [TaggedState, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, State]
  ring

end Learner
end NoiselessRegression

end

end OAI

-- ---- from OAI.Probability.ProjectionMoments.Streaming ----
namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace
namespace NoiselessRegression

section
namespace Learner
universe u

theorem riesz_success :
    ∃ C₀ : ℝ, 1 ≤ C₀ ∧ ∀ d M T : ℕ, 16 ≤ d → ∀ ε : ℝ,
      0 < ε → ε ≤ 1/10 →
      ∀ (Ω : Type u) [MeasurableSpace Ω] (ρ : Measure Ω), IsProbabilityMeasure ρ →
      ∀ L : Learner d M T Ω, L.Admissible ρ →
      let q := d/8
      let W : ℝ := ((T:ℝ)+2)*2^M
      L.uniformSuccess ρ ε ≤ ENNReal.ofReal
        (C₀^d*ε^((d:ℝ)/2-1)*(1+C₀^d*(1+Real.log (1/ε))*W^(1/(q:ℝ)))^((T+q-1)/q)) := by
  refine ⟨32768,by norm_num,?_⟩
  intro d M T hd ε hε hε10 Ω _ ρ hρ L hL q W
  let : IsProbabilityMeasure ρ := hρ
  let a := (d-1)/2
  have hq : 2 ≤ q := by dsimp [q]; omega
  have ha : 2*a ≤ d-1 := by dsimp [a]; omega
  have hqa : 2*q ≤ a := by dsimp [a,q]; omega
  have hb := L.streaming_success_bound_tagged ρ hL (by omega) hε ha hq hqa
  have hW : 0 ≤ W := by dsimp [W]; positivity
  have hqn : 0 ≤ 1/(q:ℝ) := by positivity
  have he : ((T+2)*2^M:ℝ≥0∞)^(1/(q:ℝ)) = ENNReal.ofReal (W^(1/(q:ℝ))) := by
    rw [← ENNReal.ofReal_rpow_of_nonneg hW hqn]
    congr 1
    dsimp [W]
    rw [ENNReal.ofReal_mul (by positivity : 0 ≤ (T:ℝ)+2),
      ENNReal.ofReal_add (by positivity : 0 ≤ (T:ℝ)) (by norm_num : (0:ℝ) ≤ 2),
      ENNReal.ofReal_pow (by norm_num : (0:ℝ) ≤ 2),ENNReal.ofReal_natCast,ENNReal.ofReal_ofNat]
  have hfactor : streamFactor (E := Vector d) (J := TaggedState M T) q =
      ENNReal.ofReal ((32768:ℝ)^d*W^(1/(q:ℝ))) := by
    unfold streamFactor
    rw [finrank_euclideanSpace_fin,card_taggedState,Nat.cast_mul,Nat.cast_add,Nat.cast_pow,Nat.cast_ofNat,he]
    rw [ENNReal.ofReal_mul (by positivity),ENNReal.ofReal_pow (by norm_num),ENNReal.ofReal_ofNat]
  rw [hfactor, ← ENNReal.ofReal_pow (by positivity : 0 ≤ (32768:ℝ)^d*W^(1/(q:ℝ))),
    ← ENNReal.ofReal_mul (by positivity : 0 ≤ (3:ℝ)*4^d),
    ← ENNReal.ofReal_mul (by positivity : 0 ≤ (3:ℝ)*4^d*ε^a)] at hb
  apply hb.trans
  apply ENNReal.ofReal_le_ofReal
  have hε1 : ε ≤ 1 := by linarith
  have hexp : (d:ℝ)/2-1 ≤ a := by
    have hh : d-1 ≤ 2*a+1 := by dsimp [a]; omega
    have hd1 : 1 ≤ d := by omega
    have hh' : (d:ℝ) ≤ 2*(a:ℝ)+2 := by
      exact_mod_cast (show d ≤ 2*a+2 by omega)
    linarith
  have heps : ε^a ≤ ε^((d:ℝ)/2-1) := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_ge hε hε1 hexp
  have hconst : (3:ℝ)*4^d ≤ (32768:ℝ)^d := by
    have hp' : (3:ℝ)^1 ≤ 3^d := pow_le_pow_right₀ (by norm_num) (by omega)
    have hsmall : (12:ℝ)^d ≤ (32768:ℝ)^d := pow_le_pow_left₀ (by norm_num) (by norm_num) d
    calc
      (3:ℝ)*4^d ≤ 3^d*4^d := mul_le_mul_of_nonneg_right (by simpa using hp') (by positivity)
      _ = 12^d := by rw [← mul_pow]; norm_num
      _ ≤ _ := hsmall
  have hlog : 0 ≤ Real.log (1/ε) := Real.log_nonneg ((one_le_div hε).mpr hε1)
  have hstep : (32768:ℝ)^d*W^(1/(q:ℝ)) ≤
      1+(32768:ℝ)^d*(1+Real.log (1/ε))*W^(1/(q:ℝ)) := by
    have hm : (32768:ℝ)^d*W^(1/(q:ℝ)) ≤
        (32768:ℝ)^d*(1+Real.log (1/ε))*W^(1/(q:ℝ)) := by
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hW _)
      nlinarith [pow_nonneg (by norm_num : (0:ℝ) ≤ 32768) d]
    linarith
  exact mul_le_mul (mul_le_mul hconst heps (by positivity) (by positivity))
    (pow_le_pow_left₀ (by positivity) hstep _) (by positivity) (by positivity)

end Learner

universe u
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E]

namespace Learner
variable {d M T : ℕ} {Ω : Type u}

end Learner
end

namespace Learner

section
universe u

end

universe u
variable {d M T : ℕ} {Ω : Type u}

end Learner
end NoiselessRegression

end

end OAI

-- ---- platform node ----
open OAI OAI.NoiselessRegression OAI.NoiselessRegression.Learner
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace


theorem solution.{u} : type_of% @_root_.OAI.NoiselessRegression.Learner.riesz_success.{u} := @_root_.OAI.NoiselessRegression.Learner.riesz_success.{u}
