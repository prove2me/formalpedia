-- Prove2me | solution 1 for OAI.NoiselessRegression.Learner.haar_success
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T23:33:08.03113+00:00
-- url     : https://prove2.me/submissions/7b0101a4-a2d7-4fea-afef-efa6e7430b72

-- Generated from openai/math@1581d4c lean/OAI/Probability/ProjectionMoments/Streaming.lean:L365-L393
-- (upload_full_project.md Phase 4): solution for node OAI.NoiselessRegression.Learner.haar_success. The node keeps its source
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
import Theorems.Thm_OAI_NoiselessRegression_Learner_frozen_success_bound_local

-- ---- from OAI.Probability.GaussianRegression.Rotational ----
namespace OAI

/-!
Fubini bounds and rotational lower bounds for sequential estimation.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
open InnerProductSpace
open scoped Pointwise

noncomputable section

universe u

namespace NoiselessRegression

section FubiniAux
variable {X Y Z : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
  {μ : Measure X} {ν : Measure Y} [SFinite μ] [SFinite ν]
lemma ae_fiber_aemeasurable {f : X × Y → Z} (hf : AEMeasurable f (μ.prod ν)) :
    ∀ᵐ y ∂ν, AEMeasurable (fun x => f (x,y)) μ := by
  have he := Measure.ae_ae_of_ae_prod hf.prod_swap.ae_eq_mk
  filter_upwards [he] with y hy
  have hm : Measurable (fun x => hf.prod_swap.mk _ (y,x)) :=
    hf.prod_swap.measurable_mk.comp (measurable_const.prodMk measurable_id)
  exact hm.aemeasurable.congr (Filter.EventuallyEq.symm hy)

lemma prod_null_set_bound {S : Set (X × Y)} (hS : NullMeasurableSet S (μ.prod ν))
    {c : ℝ≥0∞} (h : ∀ᵐ y ∂ν, μ {x | (x,y) ∈ S} ≤ c) :
    (μ.prod ν) S ≤ c * ν univ := by
  have hm : AEMeasurable (S.indicator (fun _ => (1 : ℝ≥0∞))) (μ.prod ν) :=
    aemeasurable_const.indicator₀ hS
  rw [← one_mul ((μ.prod ν) S), ← lintegral_indicator_const₀ hS 1, lintegral_prod_symm _ hm]
  apply (lintegral_mono_ae ?_).trans_eq (lintegral_const c)
  filter_upwards [h, ae_fiber_aemeasurable hm] with y hy hmy
  have hs : NullMeasurableSet {x | (x,y) ∈ S} μ := by
    have heq : {x | (x,y) ∈ S} = {x | S.indicator (fun _ => (1 : ℝ≥0∞)) (x,y) = 1} := by
      ext x
      by_cases hx : (x,y) ∈ S <;> simp [hx]
    rw [heq]
    exact nullMeasurableSet_eq_fun hmy aemeasurable_const
  change (∫⁻ x, ({x | (x,y) ∈ S}).indicator (fun _ => (1 : ℝ≥0∞)) x ∂μ) ≤ c
  simpa [lintegral_indicator_const₀ hs] using hy
end FubiniAux

namespace Learner
lemma angularSuccess_nullMeasurable {d M T : ℕ} {Ω : Type u} [MeasurableSpace Ω]
    (L : Learner d M T Ω) (ρ : Measure Ω) (ε : ℝ) (hL : L.Admissible ρ) :
    NullMeasurableSet {z : UnitSphere d × (Ω × Samples d T) |
      angularError z.1 (L.estimate z.1 z.2.1 z.2.2) ≤ ε}
      ((uniformSphere d).prod (ρ.prod (sampleLaw d T))) := by
  apply nullMeasurableSet_le _ aemeasurable_const
  exact Real.continuous_arccos.measurable.comp_aemeasurable
    ((measurable_subtype_coe.comp_aemeasurable hL.uniform_experiment).inner
      (measurable_subtype_coe.comp measurable_fst).aemeasurable)

end Learner

end NoiselessRegression

end

end OAI

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

end Learner

universe u
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E]

namespace Learner
variable {d M T : ℕ} {Ω : Type u}

end Learner
end

lemma streamFactor_ofReal {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {J : Type*} [Fintype J] (q : ℕ) :
    streamFactor (E := E) (J := J) q = ENNReal.ofReal
      ((32768:ℝ)^Module.finrank ℝ E*(Fintype.card J:ℝ)^(1/(q:ℝ))) := by
  unfold streamFactor
  rw [ENNReal.ofReal_mul (by positivity),ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_ofNat,
    ← ENNReal.ofReal_rpow_of_nonneg (Nat.cast_nonneg _) (by positivity : 0 ≤ 1/(q:ℝ)),
    ENNReal.ofReal_natCast]

lemma three_mul_four_pow_le (d : ℕ) (hd : 1 ≤ d) : (3:ℝ)*4^d ≤ (32768:ℝ)^d := by
  have hp : (3:ℝ)^1 ≤ 3^d := pow_le_pow_right₀ (by norm_num) hd
  calc
    (3:ℝ)*4^d ≤ 3^d*4^d := mul_le_mul_of_nonneg_right (by simpa using hp) (by positivity)
    _ = 12^d := by rw [← mul_pow]; norm_num
    _ ≤ _ := pow_le_pow_left₀ (by norm_num) (by norm_num) d

namespace Learner

section
universe u

end

universe u
variable {d M T : ℕ} {Ω : Type u}

lemma streaming_success_bound_local [MeasurableSpace Ω]
    (L : Learner d M T Ω) (ρ : Measure Ω) [IsProbabilityMeasure ρ]
    (hL : L.Admissible ρ) (hd : 3 ≤ d) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    {a q : ℕ} {b : ℝ} (hb : 0 ≤ b) (hab : (a:ℝ)+b ≤ (d-1:ℕ)) (hq : 2 ≤ q) (hqa : 2*q ≤ a) :
    L.uniformSuccess ρ ε ≤
      (ENNReal.ofReal ((3 : ℝ)*4^d) * ENNReal.ofReal (ε^b)) *
        streamFactor (E := Vector d) (J := TaggedState M q) q ^ ((T+q-1)/q) := by
  let : NeZero d := ⟨by omega⟩
  let : SigmaFinite (observationReference d) := by unfold observationReference; infer_instance
  have hω : ∀ᵐ ω ∂ρ, ∀ t j,
      AEMeasurable (L.transition t ω j) (observationReference d) := by
    simp only [ae_all_iff]
    intro t j
    exact ae_fiber_aemeasurable (hL.transition t j).prod_swap
  have hp := ((MeasurePreserving.id (uniformSphere d)).prod
      (Measure.measurePreserving_swap (μ := sampleLaw d T) (ν := ρ))).comp
    (measurePreserving_prodAssoc (uniformSphere d) (sampleLaw d T) ρ)
  let S := {z : UnitSphere d × (Ω × Samples d T) |
    angularError z.1 (L.estimate z.1 z.2.1 z.2.2) ≤ ε}
  have hS : NullMeasurableSet S ((uniformSphere d).prod (ρ.prod (sampleLaw d T))) :=
    L.angularSuccess_nullMeasurable ρ ε hL
  have he := hp.measure_preimage hS
  have hb := prod_null_set_bound (hS.preimage hp.quasiMeasurePreserving)
    (c := (ENNReal.ofReal ((3 : ℝ)*4^d) * ENNReal.ofReal (ε^b)) *
      streamFactor (E := Vector d) (J := TaggedState M q) q ^ ((T+q-1)/q))
    (by
      filter_upwards [hω] with ω hω
      exact L.frozen_success_bound_local ω hd hω hε hε1 hb hab hq hqa)
  simpa only [he,measure_univ,mul_one,S,uniformSuccess] using hb

theorem haar_success :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ d M T : ℕ, 16 ≤ d → ∀ ε : ℝ,
      0 < ε → ε ≤ 1/10 →
      ∀ (Ω : Type u) [MeasurableSpace Ω] (ρ : Measure Ω), IsProbabilityMeasure ρ →
      ∀ L : Learner d M T Ω, L.Admissible ρ →
      let k := d/4
      let Nstar : ℝ := ((k:ℝ)+2)*2^M
      L.uniformSuccess ρ ε ≤ ENNReal.ofReal
        (C^d*ε^k*(C^d*Nstar^(1/(k:ℝ)))^((T+k-1)/k)) := by
  refine ⟨32768,by norm_num,?_⟩
  intro d M T hd ε hε hε10 Ω _ ρ hρ L hL k Nstar
  let : IsProbabilityMeasure ρ := hρ
  let a := d-1-k
  have hk : 2 ≤ k := by dsimp [k]; omega
  have hka : 2*k ≤ a := by dsimp [k,a]; omega
  have hab : (a:ℝ)+(k:ℝ) ≤ (d-1:ℕ) := by
    exact_mod_cast (show a+k ≤ d-1 by dsimp [a,k]; omega)
  have hb := L.streaming_success_bound_local ρ hL (by omega) hε (by linarith)
    (Nat.cast_nonneg k) hab hk hka
  have hcard : (Fintype.card (TaggedState M k):ℝ) = Nstar := by
    rw [card_taggedState]; simp [Nstar,Nat.cast_mul,Nat.cast_add,Nat.cast_pow]
  rw [Real.rpow_natCast,streamFactor_ofReal,finrank_euclideanSpace_fin,hcard,
    ← ENNReal.ofReal_pow (by positivity : 0 ≤ (32768:ℝ)^d*Nstar^(1/(k:ℝ))),
    ← ENNReal.ofReal_mul (by positivity : 0 ≤ (3:ℝ)*4^d),
    ← ENNReal.ofReal_mul (by positivity : 0 ≤ (3:ℝ)*4^d*ε^k)] at hb
  apply hb.trans
  apply ENNReal.ofReal_le_ofReal
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (three_mul_four_pow_le d (by omega)) (by positivity)) (by positivity)

end Learner
end NoiselessRegression

end

end OAI

-- ---- platform node ----
open OAI OAI.NoiselessRegression OAI.NoiselessRegression.Learner
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace


theorem solution.{u} : type_of% @_root_.OAI.NoiselessRegression.Learner.haar_success.{u} := @_root_.OAI.NoiselessRegression.Learner.haar_success.{u}
