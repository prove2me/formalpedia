-- Prove2me | solution 1 for OAI.SubsphereCurrent.full_current_main_scope
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T10:00:13.611994+00:00
-- url     : https://prove2.me/submissions/1d6fd942-9d54-4584-8d35-cc696ccbcf90

-- Generated from openai/math@1581d4c lean/OAI/Probability/Subsphere/Main.lean:L15-L18
-- (upload_full_project.md Phase 4): solution for the platform mission target OAI.SubsphereCurrent.full_current_main_scope.
-- The source declaration is kept inside its namespace next to the proof-only helpers it needs;
-- `theorem solution` restates the platform stub (Theorems.Thm_OAI_SubsphereCurrent_full_current_main_scope) verbatim and is proved by it.
import Mathlib
import Definitions.Def_SubsphereCurrent
import Definitions.Def_OAI_Probability_Subsphere_Models
import Definitions.Def_OAI_Probability_Subsphere_Regression_Geometry
import Definitions.Def_OAI_Probability_Subsphere_Regression_Gram
import Definitions.Def_OAI_Probability_Subsphere_Regression_Gaussian
import Definitions.Def_OAI_Probability_Subsphere_Regression_Projection
import Definitions.Def_OAI_Probability_Subsphere_Regression_Model
import Definitions.Def_OAI_Probability_Subsphere_Regression_Spheres
import Definitions.Def_OAI_Probability_Subsphere_Regression_Blocks
import Definitions.Def_OAI_Probability_Subsphere_Regression_Streaming
import Definitions.Def_OAI_Probability_Subsphere_Kernels_Precision
import Definitions.Def_OAI_Probability_Subsphere_Geometry_Integration
import Definitions.Def_OAI_Probability_Subsphere_Geometry_MassBounds
import Definitions.Def_OAI_Probability_Subsphere_Geometry_Affine
import Definitions.Def_OAI_Probability_Subsphere_Estimates_FixedPrecision
import Definitions.Def_OAI_Probability_Subsphere_Mixture_Haar
import Definitions.Def_OAI_Probability_Subsphere_Mixture_BetaTheory
import Definitions.Def_OAI_Probability_Subsphere_Mixture_Latitude
import Definitions.Def_OAI_Probability_Subsphere_Mixture_Domination
import Theorems.Thm_OAI_SubsphereCurrent_Affine_Simulation_average_le_of_simulated
import Theorems.Thm_OAI_SubsphereCurrent_Affine_affine_raw_bound
import Theorems.Thm_OAI_SubsphereCurrent_Fixed_Stream_average_euclideanSuccess_bound
import Theorems.Thm_OAI_SubsphereCurrent_Fixed_Stream_average_euclideanSuccess_zero_bound
import Theorems.Thm_OAI_SubsphereCurrent_Fixed_parameters
import Theorems.Thm_OAI_SubsphereCurrent_Fixed_raw_bound_le
import Theorems.Thm_OAI_SubsphereCurrent_KernelLearner_asTape_admissible
import Theorems.Thm_OAI_SubsphereCurrent_KernelLearner_borelVersion_success_ae
import Theorems.Thm_OAI_SubsphereCurrent_KernelLearner_uniformSuccess_asTape
import Theorems.Thm_OAI_SubsphereCurrent_Mixture_directionLaw_domination
import Theorems.Thm_OAI_SubsphereCurrent_Mixture_haar_eval_preserving
import Theorems.Thm_OAI_SubsphereCurrent_Polar_measurable_radial
import Theorems.Thm_OAI_SubsphereCurrent_Polar_sphereMap_preserving
import Theorems.Thm_OAI_SubsphereCurrent_SeededLearner_exists_good_seed
import Theorems.Thm_OAI_SubsphereCurrent_Slice_controlled_cap_bound
import Theorems.Thm_OAI_SubsphereCurrent_Weighted_block_reconstruct
import Theorems.Thm_OAI_SubsphereCurrent_Weighted_nested_average
import Theorems.Thm_OAI_SubsphereCurrent_Weighted_weighted_terminal
import Theorems.Thm_OAI_SubsphereCurrent_finiteSample_map
import Theorems.Thm_OAI_SubsphereCurrent_measurable_finiteSample
import Theorems.Thm_OAI_SubsphereRegression_Learner_half_linear_success_bound
import Theorems.Thm_OAI_SubsphereRegression_Learner_streaming_success_bound
import Theorems.Thm_OAI_SubsphereRegression_explicit_precision_old_model
import Theorems.Thm_OAI_SubsphereRegression_localized_routing_bound
import Theorems.Thm_OAI_SubsphereRegression_precision_from_stream_bound_half_aux

-- ---- from OAI.Probability.Subsphere.Regression.Spheres ----
namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
universe u
namespace SubsphereRegression
open scoped Topology
open InnerProductSpace
section SphereBounds
open scoped Pointwise
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

end SphereBounds

open scoped Pointwise
section MoreSphere
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma ambientSphereLaw_support : (ambientSphereLaw (E := E)).support ⊆ Metric.sphere 0 1 := by
  apply Measure.support_subset_of_isClosed Metric.isClosed_sphere
  rw [mem_ae_iff, ambientSphereLaw, Measure.map_apply (by fun_prop)
    Metric.isClosed_sphere.measurableSet.compl]
  have h : (Subtype.val : Metric.sphere (0 : E) 1 → E) ⁻¹' (Metric.sphere 0 1)ᶜ = ∅ := by
    ext x
    simp
  rw [h, measure_empty]

lemma ambientSphereLaw_ae_norm [Nontrivial E] :
    ∀ᵐ x : E ∂ambientSphereLaw, ‖x‖ = 1 := by
  filter_upwards [Measure.support_mem_ae (μ := ambientSphereLaw (E := E))] with x hx
  exact mem_sphere_zero_iff_norm.mp (ambientSphereLaw_support hx)

end MoreSphere

section FubiniAux
variable {X Y Z : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
  {μ : Measure X} {ν : Measure Y} [SFinite μ] [SFinite ν]
end FubiniAux

end SubsphereRegression
end
end

end OAI

-- ---- from OAI.Probability.Subsphere.Regression.Streaming ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
universe u
namespace SubsphereRegression
open scoped Topology
open InnerProductSpace
open scoped Pointwise
section StreamAux
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable {J : Type*} [Fintype J] [MeasurableSpace J] [MeasurableSingletonClass J]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [MeasurableSpace J] [MeasurableSingletonClass J] in
lemma streamFactor_ne_top (q : ℕ) : streamFactor (E := E) (J := J) q ≠ ∞ := by
  exact ENNReal.mul_ne_top (by simp) (ENNReal.rpow_ne_top_of_nonneg (by positivity) (by simp))

end StreamAux

namespace Learner
variable {d M T : ℕ} {Ω : Type u} (L : Learner d M T Ω)

end Learner

section StreamCaps
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E]
variable {J : Type*} [Fintype J] [MeasurableSpace J] [MeasurableSingletonClass J] [Nonempty J]

end StreamCaps

section ObservationAC
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

end ObservationAC

end SubsphereRegression
end
end

end OAI

-- ---- from OAI.Probability.Subsphere.Kernels.Precision ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
namespace SubsphereCurrent

section FiniteVersion
variable {X A : Type*} [MeasurableSpace X] [Fintype A] [Nonempty A]
variable {μ : Measure X} (p : X → PMF A)

lemma measurable_borelPMF (hp : ∀ a, AEMeasurable (fun x => p x a) μ) (a : A) :
    Measurable (fun x => borelPMF p hp x a) := by
  classical
  have hm (b : A) := (hp b).measurable_mk
  have hs : MeasurableSet {x | ∑ b, (hp b).mk (fun x => p x b) x = 1} :=
    measurableSet_eq_fun (Finset.measurable_sum _ (fun b _ => hm b)) measurable_const
  have he : (fun x => borelPMF p hp x a) = fun x =>
      if ∑ b, (hp b).mk (fun x => p x b) x = 1
      then (hp a).mk (fun x => p x a) x else PMF.pure (Classical.arbitrary A) a := by
    funext x
    unfold borelPMF
    split_ifs <;> rfl
  rw [he]
  exact Measurable.ite hs (hm a) measurable_const

end FiniteVersion

namespace KernelLearner

lemma borelVersion_rules {d M T : ℕ} (L : KernelLearner d M T) (hL : L.CompletedRules) :
    (L.borelVersion hL).BorelRules := by
  intro t q a
  exact measurable_borelPMF _ _ a

end KernelLearner
end SubsphereCurrent
end
end
section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
noncomputable section
namespace SubsphereCurrent

lemma lintegral_finiteSample {n : ℕ} [NeZero n] (p : PMF (Fin n))
    (f : Fin n → ℝ≥0∞) :
    (∫⁻ r, f (finiteSample p r) ∂coinLaw) = ∑ i, p i * f i := by
  have hm : Measurable (finiteSample p) :=
    measurable_finiteSample (fun _ => measurable_const) measurable_id
  rw [← lintegral_map (measurable_of_finite f) hm, finiteSample_map, lintegral_countable']
  simp only [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _),
    tsum_fintype, mul_comm]

section EquivSampling
variable {A B : Type*}
lemma pmf_map_equiv_apply (e : A ≃ B) (p : PMF A) (b : B) :
    p.map e b = p (e.symm b) := by
  classical
  have he (a : A) : b = e a ↔ e.symm b = a := by
    constructor
    · intro h; simp [h]
    · intro h; rw [← h, e.apply_symm_apply]
  simp only [PMF.map_apply, he]
  simp

variable [Fintype A] [Nonempty A]

lemma measurable_samplePMF {X : Type*} [MeasurableSpace X] [MeasurableSpace A]
    {p : X → PMF A} {r : X → ℝ}
    (hp : ∀ a, Measurable (fun x => p x a)) (hr : Measurable r) :
    Measurable (fun x => samplePMF (p x) (r x)) := by
  let : NeZero (Fintype.card A) := ⟨Fintype.card_ne_zero⟩
  apply (measurable_of_finite (Fintype.equivFin A).symm).comp
  exact measurable_finiteSample (fun i => by simpa only [pmf_map_equiv_apply] using hp _) hr

lemma lintegral_samplePMF (p : PMF A) (f : A → ℝ≥0∞) :
    (∫⁻ r, f (samplePMF p r) ∂coinLaw) = ∑ a, p a * f a := by
  let : NeZero (Fintype.card A) := ⟨Fintype.card_ne_zero⟩
  change (∫⁻ r, (fun i => f ((Fintype.equivFin A).symm i))
    (finiteSample (p.map (Fintype.equivFin A)) r) ∂coinLaw) = _
  rw [lintegral_finiteSample (p.map (Fintype.equivFin A))
    (fun i => f ((Fintype.equivFin A).symm i))]
  simp_rw [pmf_map_equiv_apply]
  exact Equiv.sum_comp (Fintype.equivFin A).symm (fun a => p a * f a)

end EquivSampling

end SubsphereCurrent
end
end
section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
noncomputable section
namespace SubsphereCurrent

section CountableBind
variable {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
  [Countable A] [Countable B] [MeasurableSingletonClass A] [MeasurableSingletonClass B]

end CountableBind

section Chain
variable {A : Type*} [MeasurableSpace A] [Countable A] [MeasurableSingletonClass A]

end Chain
end SubsphereCurrent
end
end
section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section

namespace SubsphereCurrent
end SubsphereCurrent

namespace SubsphereRegression.Learner
-- [generator] dropped: open SubsphereCurrent (measurable_countable_select)

end SubsphereRegression.Learner

namespace SubsphereCurrent
namespace KernelLearner
end KernelLearner
end SubsphereCurrent
end
end
section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
universe u v w
namespace SubsphereCurrent

lemma measurePreserving_swapFirstTwo {A : Type u} {B : Type v} {C : Type w}
    [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C]
    (μ : Measure A) (ν : Measure B) (ρ : Measure C)
    [SFinite μ] [SFinite ν] [SFinite ρ] :
    MeasurePreserving (swapFirstTwo A B C) (μ.prod (ν.prod ρ)) (ν.prod (μ.prod ρ)) := by
  exact (measurePreserving_prodAssoc ν μ ρ).comp
    (((MeasureTheory.Measure.measurePreserving_swap (μ := μ) (ν := ν)).prod (MeasurePreserving.id ρ)).comp
      (MeasurePreserving.symm MeasurableEquiv.prodAssoc (measurePreserving_prodAssoc μ ν ρ)))

namespace KernelLearner
end KernelLearner

namespace SeededLearner
lemma uniformSuccess_of_pointwise {d M T : ℕ} {Ω : Type u} [MeasurableSpace Ω]
    (L : SeededLearner d M T Ω) (ρ : Measure Ω) [IsProbabilityMeasure ρ]
    (hL : L.Admissible ρ) (ε : ℝ) [NeZero d] (c : ℝ≥0∞)
    (hc : ∀ s, c ≤ L.success ρ ε s) : c ≤ L.uniformSuccess ρ ε := by
  rw [uniformSuccess, lintegral_prod _ (hL.uniform_experiment ε)]
  calc
    c = ∫⁻ _ : UnitSphere d, c ∂uniformSphere d := by simp
    _ ≤ _ := lintegral_mono hc

end SeededLearner
end SubsphereCurrent
end
end
section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
universe u
namespace SubsphereCurrent

theorem explicit_precision : ExplicitPrecision.{u} := by
  intro M hM
  obtain ⟨d₁, hd₁⟩ := SubsphereRegression.explicit_precision_old_model.{0} M hM
  refine ⟨max 3 d₁, ?_⟩
  intro d hd T ε hε hε10 Ω _ ρ hρ L hL hs
  let : IsProbabilityMeasure ρ := hρ
  let : NeZero d := ⟨by omega⟩
  have hs' : (2/3 : ℝ≥0∞) ≤ L.uniformSuccess ρ ε := by
    rcases hs with hs | hs
    · exact hs
    · exact L.uniformSuccess_of_pointwise ρ hL ε _ hs
  obtain ⟨ω, hω, hgood⟩ := L.exists_good_seed ρ hL ε
  let K := (L.rules ω).borelVersion hω
  have hK : K.BorelRules := (L.rules ω).borelVersion_rules hω
  have hsuccess : (2/3 : ℝ≥0∞) ≤ K.asTape.uniformSuccess K.tapeLaw ε := by
    rw [K.uniformSuccess_asTape hK ε]
    calc
      (2/3 : ℝ≥0∞) ≤ L.uniformSuccess ρ ε := hs'
      _ ≤ ∫⁻ z : UnitSphere d × Samples d T, (L.rules ω).conditionalSuccess ε z.1 z.2
          ∂(uniformSphere d).prod (sampleLaw d T) := hgood
      _ = ∫⁻ z : UnitSphere d × Samples d T, K.conditionalSuccess ε z.1 z.2
          ∂(uniformSphere d).prod (sampleLaw d T) :=
        lintegral_congr_ae ((L.rules ω).borelVersion_success_ae hω (by omega) ε)
  exact hd₁ d (by omega) T ε hε hε10 (KernelLearner.Tape d (M d) T)
    K.tapeLaw inferInstance K.asTape (K.asTape_admissible hK) (Or.inl hsuccess)

end SubsphereCurrent
end
end

end OAI

-- ---- from OAI.Probability.Subsphere.Geometry.Integration ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem dite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t : c → α} {e : ¬c → α} : (dite c t e) = e hc := @dif_neg c h hc α t e

namespace OAI

section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
namespace SubsphereCurrent.Polar
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E]

end SubsphereCurrent.Polar
end
end
section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
namespace SubsphereCurrent.Polar
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E] in
lemma radial_smul (g : Metric.sphere (0 : E) 1 → ℝ≥0∞)
    (s : Metric.sphere (0 : E) 1) {r : ℝ} (hr : 0 < r) : radial g (r • s.val) = g s := by
  have hs : s.val ≠ 0 := by
    intro hs
    have hn := mem_sphere_zero_iff_norm.mp s.property
    rw [hs,norm_zero] at hn
    norm_num at hn
  rw [radial,dite_eq_right (smul_ne_zero hr.ne' hs)]
  congr 1
  apply Subtype.ext
  exact (NormedSpace.normalize_smul_of_pos hr _).trans
    (NormedSpace.normalize_eq_self_of_norm_eq_one (mem_sphere_zero_iff_norm.mp s.property))

end SubsphereCurrent.Polar
end
end
section
/-! Isometric naturality of the exact normalized Haar spherical law. -/
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace Pointwise
noncomputable section
namespace SubsphereCurrent.Polar
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F]

end SubsphereCurrent.Polar
end
end
section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
namespace SubsphereCurrent.Slice
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

end SubsphereCurrent.Slice
end
end
section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
namespace SubsphereCurrent.Weighted

lemma borel_onTest {d n : ℕ} (A : Affine.Test d n) : Measurable (onTest A) := by
  apply Measurable.subtype_mk
  change Measurable (fun s : Affine.Sphere A.space => A.center+A.radius • (s.val : Vector d))
  fun_prop

lemma radius_le_one {d n : ℕ} (A : Affine.Test d n) : A.radius ≤ 1 := by
  nlinarith [A.unit,sq_nonneg ‖A.center‖,A.radius_positive]

end SubsphereCurrent.Weighted
end
end
section
open MeasureTheory Set
open scoped ENNReal NNReal
noncomputable section
namespace SubsphereCurrent.Polar

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E]

end SubsphereCurrent.Polar
end
end
section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
namespace SubsphereCurrent.Slice
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E]

end SubsphereCurrent.Slice
end
end
section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
namespace SubsphereCurrent.Slice
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E]

end SubsphereCurrent.Slice
end
end
section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
namespace SubsphereCurrent.Quarter
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
lemma subspace_dimension (U : Submodule ℝ E) {k : ℕ} (hk : k ≤ Module.finrank ℝ U) :
    ∃ F : Submodule ℝ E, F ≤ U ∧ Module.finrank ℝ F = k := by
  obtain ⟨v,hv⟩ := exists_linearIndependent_of_le_finrank (R := ℝ) (M := U) hk
  let w : Fin k → E := fun i => v i
  have hw : LinearIndependent ℝ w := hv.map' U.subtype (LinearMap.ker_eq_bot.mpr Subtype.val_injective)
  refine ⟨Submodule.span ℝ (Set.range w), ?_, ?_⟩
  · exact Submodule.span_le.mpr (by rintro _ ⟨i,rfl⟩; exact (v i).property)
  · simpa using finrank_span_eq_card hw

end SubsphereCurrent.Quarter
end
end

end OAI

-- ---- from OAI.Probability.Subsphere.Geometry.MassBounds ----
namespace OAI

noncomputable section

namespace SubsphereCurrent.Weighted
section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace

lemma measurable_weightedOnTest {d n : ℕ} (A : Affine.Test d n)
    {g : Sphere d → ℝ≥0∞} (hg : Measurable g) : Measurable (weightedOnTest A g) :=
  measurable_const.mul (hg.comp (borel_onTest A))

lemma weighted_control {d n k b : ℕ} (A : Affine.Test d n)
    {g : Sphere d → ℝ≥0∞} (hg : Measurable g) (hb : (d : ℝ)/16 ≤ b) :
    Slice.Controlled (weightedOnTest A g) k b (norm d k g) := by
  intro B
  have hB1 : B.radius ≤ 1 := by nlinarith [B.unit,sq_nonneg ‖B.center‖,B.positive]
  have hp : ENNReal.ofReal (B.radius^b) ≤ (ENNReal.ofReal B.radius)^((d : ℝ)/16) := by
    rw [ENNReal.ofReal_pow B.positive.le,← ENNReal.rpow_natCast]
    exact ENNReal.rpow_le_rpow_of_exponent_ge (ENNReal.ofReal_le_one.mpr hB1) hb
  change ENNReal.ofReal (B.radius^b) *
    (∫⁻ s, (ENNReal.ofReal A.radius)^((d : ℝ)/16)*g (onTest A (B.point s))
      ∂Affine.sphereLaw B.space) ≤ _
  rw [lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg (by positivity) ENNReal.ofReal_ne_top)]
  calc
    _ ≤ (ENNReal.ofReal B.radius)^((d : ℝ)/16)*
        ((ENNReal.ofReal A.radius)^((d : ℝ)/16)*
          ∫⁻ s, g (onTest A (B.point s)) ∂Affine.sphereLaw B.space) := mul_le_mul' hp le_rfl
    _ = (ENNReal.ofReal (nestedTest A B).radius)^((d : ℝ)/16)*
        ∫⁻ s, g (onTest (nestedTest A B) s) ∂Affine.sphereLaw (nestedTest A B).space := by
      rw [nested_average A B hg,← mul_assoc,mul_comm ((ENNReal.ofReal B.radius)^((d : ℝ)/16)),
        ← ENNReal.mul_rpow_of_nonneg _ _ (by positivity),← ENNReal.ofReal_mul A.radius_positive.le]
      rfl
    _ ≤ _ := le_iSup (fun D : Affine.Test d k => (ENNReal.ofReal D.radius)^((d : ℝ)/16)*
      ∫⁻ s, g (onTest D s) ∂Affine.sphereLaw D.space) (nestedTest A B)

lemma subspace_perpendicular {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (z : E) {k : ℕ} (hk : k+1 ≤ Module.finrank ℝ E) :
    ∃ K : Submodule ℝ E, Module.finrank ℝ K = k ∧ z ∈ Kᗮ := by
  let U := Submodule.span ℝ ({z} : Set E)
  have hU : Module.finrank ℝ U ≤ 1 := by
    simpa [U] using (finrank_span_le_card (R := ℝ) ({z} : Set E))
  have hd := U.finrank_add_finrank_orthogonal
  obtain ⟨K,hK,hkd⟩ := Quarter.subspace_dimension Uᗮ (k := k) (by omega)
  refine ⟨K,hkd,?_⟩
  apply (Submodule.mem_orthogonal _ _).mpr
  intro x hx
  exact Submodule.inner_left_of_mem_orthogonal (Submodule.subset_span (by simp : z ∈ ({z} : Set E))) (hK hx)

lemma weighted_cap {d n k b : ℕ} (A : Affine.Test d n) [Nontrivial A.space]
    {g : Sphere d → ℝ≥0∞} (hg : Measurable g)
    (hkn : k+1 ≤ n) (hb0 : b+1 ≤ k) (h2b : 2*b ≤ k) (hb : (d : ℝ)/16 ≤ b)
    (z : A.space) {t : ℝ} (ht : 0 < t) :
    (∫⁻ s, Slice.capFunction (weightedOnTest A g) z t s ∂Affine.sphereLaw A.space) ≤
      (2 : ℝ≥0∞)^(n+1)*norm d k g*ENNReal.ofReal (t^(k-b)) := by
  obtain ⟨K,hK,hz⟩ := subspace_perpendicular z (A.dimension ▸ hkn)
  let : Nontrivial K := Module.nontrivial_of_finrank_pos (hK ▸ (by omega : 0 < k))
  simpa only [A.dimension] using Slice.controlled_cap_bound
    (measurable_weightedOnTest A hg) (weighted_control A hg hb) K hK hb0 h2b hz ht

lemma radial_sphere {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E]
    (g : Metric.sphere (0 : E) 1 → ℝ≥0∞) (s : Metric.sphere (0 : E) 1) :
    Polar.radial g s.val = g s := by
  simpa using Polar.radial_smul g s (r := 1) zero_lt_one

lemma weightedOnTest_le_one {d n : ℕ} (A : Affine.Test d n)
    {g : Sphere d → ℝ≥0∞} (hg : ∀ s, g s ≤ 1) (s : Affine.Sphere A.space) :
    weightedOnTest A g s ≤ 1 := by
  refine (mul_le_of_le_one_left zero_le ?_).trans (hg _)
  exact ENNReal.rpow_le_one (ENNReal.ofReal_le_one.mpr (radius_le_one A)) (by positivity)

lemma weighted_norm_le_one {d n : ℕ} (hn : 0 < n)
    {g : Sphere d → ℝ≥0∞} (hg : ∀ s, g s ≤ 1) : norm d n g ≤ 1 := by
  apply iSup_le
  intro A
  let : Nontrivial A.space := Module.nontrivial_of_finrank_pos (A.dimension ▸ hn)
  let : IsProbabilityMeasure (Affine.sphereLaw A.space) := SubsphereRegression.sphereLaw_probability
  refine (mul_le_of_le_one_left zero_le ?_).trans
    (by simpa using (lintegral_mono (μ := Affine.sphereLaw A.space) (fun s => hg (onTest A s))))
  exact ENNReal.rpow_le_one (ENNReal.ofReal_le_one.mpr (radius_le_one A)) (by positivity)

section Ambient
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E]

lemma sphereDensity_integral {g : Metric.sphere (0 : E) 1 → ℝ≥0∞} (hg : Measurable g)
    {f : E → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ x, f x ∂sphereDensity g) = ∫⁻ s, g s*f s.val ∂Affine.sphereLaw E := by
  rw [sphereDensity,lintegral_withDensity_eq_lintegral_mul _ (Polar.measurable_radial hg) hf,
    SubsphereRegression.ambientSphereLaw,lintegral_map ((Polar.measurable_radial hg).mul hf) (by fun_prop)]
  apply lintegral_congr
  intro s
  change Polar.radial g s.val*f s.val = _
  rw [radial_sphere]

lemma sphereDensity_cap {g : Metric.sphere (0 : E) 1 → ℝ≥0∞} (hg : Measurable g)
    (z : E) (r : ℝ) :
    sphereDensity g (Metric.closedBall z r) =
      ∫⁻ s, Slice.capFunction g z r s ∂Affine.sphereLaw E := by
  rw [← one_mul (sphereDensity g _),← lintegral_indicator_const Metric.isClosed_closedBall.measurableSet 1,
    sphereDensity_integral hg ((measurable_const : Measurable (fun _ : E => (1 : ℝ≥0∞))).indicator
      Metric.isClosed_closedBall.measurableSet)]
  apply lintegral_congr
  intro s
  by_cases hs : dist s.val z ≤ r <;> simp [Slice.capFunction,Metric.mem_closedBall,hs]

omit [Nontrivial E] in
lemma sphereDensity_le {g : Metric.sphere (0 : E) 1 → ℝ≥0∞} (hg : ∀ s, g s ≤ 1) :
    sphereDensity g ≤ SubsphereRegression.ambientSphereLaw (E := E) := by
  rw [sphereDensity]
  conv_rhs => rw [← withDensity_one (μ := SubsphereRegression.ambientSphereLaw (E := E))]
  apply withDensity_mono
  filter_upwards [] with x
  unfold Polar.radial
  split_ifs <;> simp_all

lemma sphereDensity_finite {g : Metric.sphere (0 : E) 1 → ℝ≥0∞}
    (hg : ∀ s, g s ≤ 1) : IsFiniteMeasure (sphereDensity g) :=
  isFiniteMeasure_of_le _ (sphereDensity_le hg)

lemma sphereDensity_restrict_ball {g : Metric.sphere (0 : E) 1 → ℝ≥0∞}
    (hg : ∀ s, g s ≤ 1) : (sphereDensity g).restrict (Metric.closedBall 0 1) = sphereDensity g := by
  apply Measure.restrict_eq_self_of_ae_mem
  have hnorm : ∀ᵐ x ∂sphereDensity g, ‖x‖ = 1 :=
    MeasureTheory.ae_mono (sphereDensity_le hg) SubsphereRegression.ambientSphereLaw_ae_norm
  filter_upwards [hnorm] with x hx
  simp [Metric.mem_closedBall,dist_zero_right,hx]

end Ambient

lemma polynomialMass_weighted {d n k b : ℕ} (A : Affine.Test d n) [Nontrivial A.space]
    {g : Sphere d → ℝ≥0∞} (hg : Measurable g)
    (hkn : k+1 ≤ n) (hb0 : b+1 ≤ k) (h2b : 2*b ≤ k) (hb : (d : ℝ)/16 ≤ b) :
    SubsphereRegression.PolynomialMass (sphereDensity (weightedOnTest A g)) (k-b)
      ((2 : ℝ≥0∞)^(n+1)*norm d k g) := by
  intro z t ht
  rw [sphereDensity_cap (measurable_weightedOnTest A hg)]
  exact weighted_cap A hg hkn hb0 h2b hb z ht

variable {V : Type*} [Fintype V] [Nonempty V]

omit [Nonempty V] in
lemma completeRoute_ge (v₀ : V) (w : V → ℝ≥0∞) (hw : ∑ v, w v ≤ 1) (v : V) :
    w v ≤ completeRoute v₀ w hw v := by
  classical
  exact le_add_right le_rfl

omit [Nonempty V] in
lemma measurable_completeRoute {X : Type*} [MeasurableSpace X]
    (v₀ : V) (w : V → X → ℝ≥0∞) (hw : ∀ x, ∑ v, w v x ≤ 1)
    (hm : ∀ v, Measurable (w v)) (v : V) :
    Measurable (fun x => completeRoute v₀ (fun i => w i x) (hw x) v) := by
  classical
  change Measurable (fun x => w v x + if v = v₀ then 1-∑ i, w i x else 0)
  split_ifs
  · exact (hm v).add (measurable_const.sub (Finset.measurable_sum _ (fun i _ => hm i)))
  · simpa using hm v

lemma sample_mass_identity {X : Type*} [MeasurableSpace X]
    [MeasurableSpace V] [MeasurableSingletonClass V]
    (p : X → PMF V) (hp : ∀ v, Measurable (fun x => p x v))
    (μ : Measure X) [SFinite μ] (v : V) :
    (∫⁻ x, p x v ∂μ) = ∫⁻ r, μ {x | samplePMF (p x) r = v} ∂coinLaw := by
  classical
  have hf : Measurable (fun z : X × ℝ => samplePMF (p z.1) z.2) :=
    measurable_samplePMF (fun i => (hp i).comp measurable_fst) measurable_snd
  have hi : Measurable (fun z : X × ℝ => if samplePMF (p z.1) z.2 = v then (1 : ℝ≥0∞) else 0) :=
    Measurable.ite (measurableSet_eq_fun hf measurable_const) measurable_const measurable_const
  have he (x : X) : p x v = ∫⁻ r, (if samplePMF (p x) r = v then (1 : ℝ≥0∞) else 0) ∂coinLaw := by
    rw [lintegral_samplePMF (p x) (fun a => if a=v then (1 : ℝ≥0∞) else 0)]
    simp
  simp_rw [he]
  rw [lintegral_lintegral_swap hi.aemeasurable]
  apply lintegral_congr
  intro r
  have hr : Measurable (fun x : X => samplePMF (p x) r) :=
    measurable_samplePMF hp measurable_const
  change (∫⁻ x, {x | samplePMF (p x) r = v}.indicator (fun _ => (1 : ℝ≥0∞)) x ∂μ) = _
  rw [lintegral_indicator_const (measurableSet_eq_fun hr measurable_const),one_mul]

lemma measurable_sample_mass {X : Type*} [MeasurableSpace X]
    [MeasurableSpace V] [MeasurableSingletonClass V]
    (p : X → PMF V) (hp : ∀ v, Measurable (fun x => p x v))
    (μ : Measure X) [SFinite μ] (v : V) :
    Measurable (fun r : ℝ => μ {x | samplePMF (p x) r = v}) := by
  classical
  have hf : Measurable (fun z : ℝ × X => samplePMF (p z.2) z.1) :=
    measurable_samplePMF (fun i => (hp i).comp measurable_snd) measurable_fst
  have hi : Measurable (fun z : ℝ × X => if samplePMF (p z.2) z.1 = v then (1 : ℝ≥0∞) else 0) :=
    Measurable.ite (measurableSet_eq_fun hf measurable_const) measurable_const measurable_const
  have hmi : Measurable (fun r : ℝ => ∫⁻ x : X,
      (if samplePMF (p x) r = v then (1 : ℝ≥0∞) else 0) ∂μ) := hi.lintegral_prod_right
  convert hmi using 1
  ext r
  have hr : Measurable (fun x : X => samplePMF (p x) r) :=
    measurable_samplePMF hp measurable_const
  change _ = ∫⁻ x, {x | samplePMF (p x) r = v}.indicator (fun _ => (1 : ℝ≥0∞)) x ∂μ
  rw [lintegral_indicator_const (measurableSet_eq_fun hr measurable_const),one_mul]

lemma routing_mixture_bound {X : Type*} [MeasurableSpace X]
    [MeasurableSpace V] [MeasurableSingletonClass V]
    (μ : V → Measure X) [∀ v, SFinite (μ v)]
    (w : V → X → ℝ≥0∞) (hw : ∀ x, ∑ v, w v x ≤ 1) (hm : ∀ v, Measurable (w v))
    {B : ℝ≥0∞}
    (hb : ∀ φ : X → V, Measurable φ → ∑ v, μ v {x | φ x = v} ≤ B) :
    (∑ v, ∫⁻ x, w v x ∂μ v) ≤ B := by
  classical
  let v₀ : V := Classical.choice inferInstance
  let p (x : X) := completeRoute v₀ (fun v => w v x) (hw x)
  have hp (v : V) : Measurable (fun x => p x v) := measurable_completeRoute v₀ w hw hm v
  calc
    _ ≤ ∑ v, ∫⁻ x, p x v ∂μ v := Finset.sum_le_sum fun v _ => lintegral_mono fun x =>
      completeRoute_ge v₀ (fun i => w i x) (hw x) v
    _ = ∑ v, ∫⁻ r, μ v {x | samplePMF (p x) r = v} ∂coinLaw := by
      simp_rw [sample_mass_identity p hp]
    _ = ∫⁻ r, ∑ v, μ v {x | samplePMF (p x) r = v} ∂coinLaw :=
      (lintegral_finsetSum _ (fun v _ => measurable_sample_mass p hp (μ v) v)).symm
    _ ≤ ∫⁻ _ : ℝ, B ∂coinLaw := lintegral_mono fun r =>
      hb (fun x => samplePMF (p x) r) (measurable_samplePMF hp measurable_const)
    _ = B := by simp

end
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E]
variable {V : Type*} [Fintype V] [Nonempty V] [MeasurableSpace V] [MeasurableSingletonClass V]

lemma projection_sphere_integral {m : ℕ}
    {g : Metric.sphere (0 : E) 1 → ℝ≥0∞} (hg : Measurable g) (hg1 : ∀ s, g s ≤ 1)
    {f : ((Fin m → E) × (Fin m → ℝ)) → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ x, f x ∂SubsphereRegression.projectionLaw (sphereDensity g) m) =
      ∫⁻ s, g s * (∫⁻ X : Fin m → E, f (X,fun i => ⟪s.val,X i⟫)
        ∂Measure.pi (fun _ => stdGaussian E)) ∂Affine.sphereLaw E := by
  let : IsFiniteMeasure (sphereDensity g) := sphereDensity_finite hg1
  have hobs : Measurable (fun z : (Fin m → E) × E => (z.1,fun i => ⟪z.2,z.1 i⟫)) := by fun_prop
  have hi : Measurable (fun z : (Fin m → E) × E => f (z.1,fun i => ⟪z.2,z.1 i⟫)) := hf.comp hobs
  rw [SubsphereRegression.projectionLaw,lintegral_map hf hobs,
    lintegral_prod_symm _ hi.aemeasurable]
  exact sphereDensity_integral hg hi.lintegral_prod_left

lemma sphereDensity_zero_of_mass_zero
    {g : Metric.sphere (0 : E) 1 → ℝ≥0∞} (hg1 : ∀ s, g s ≤ 1)
    {a : ℕ} (hlocal : SubsphereRegression.PolynomialMass (sphereDensity g) a 0) :
    sphereDensity g = 0 := by
  have hz := hlocal 0 1 zero_lt_one
  simp only [zero_mul] at hz
  have hr := sphereDensity_restrict_ball hg1
  apply Measure.measure_univ_eq_zero.mp
  rw [← hr,Measure.restrict_apply MeasurableSet.univ,Set.univ_inter]
  exact le_zero_iff.mp hz

omit [Nonempty V] in
lemma deterministic_sphere_routing {m a q : ℕ} {C : ℝ≥0∞}
    {g : V → Metric.sphere (0 : E) 1 → ℝ≥0∞} (hg1 : ∀ v s, g v s ≤ 1)
    (hlocal : ∀ v, SubsphereRegression.PolynomialMass (sphereDensity (g v)) a C)
    (hCt : C ≠ ∞)
    (ha : a ≤ Module.finrank ℝ E) (hm : m ≤ Module.finrank ℝ E)
    (hq : 1 ≤ q) (hmargin : q+m ≤ a)
    (φ : ((Fin m → E) × (Fin m → ℝ)) → V) (hφ : Measurable φ) :
    (∑ v, SubsphereRegression.projectionLaw (sphereDensity (g v)) m {x | φ x=v}) ≤
      (32768 : ℝ≥0∞)^Module.finrank ℝ E*(Fintype.card V : ℝ≥0∞)^(1/((q : ℝ)+1))*C := by
  let (v : V) : IsFiniteMeasure (sphereDensity (g v)) := sphereDensity_finite (hg1 v)
  by_cases hC : C=0
  · subst C
    have hz (v : V) := sphereDensity_zero_of_mass_zero (hg1 v) (hlocal v)
    simp [hz,SubsphereRegression.projectionLaw]
  · have hb := SubsphereRegression.localized_routing_bound (fun v => sphereDensity (g v))
      hlocal hC hCt Module.finrank_pos ha hm hq hmargin φ hφ (0 : E) zero_lt_one
    simp only [sphereDensity_restrict_ball (hg1 _),one_pow,ENNReal.ofReal_one,mul_one] at hb
    exact hb

lemma sphere_routing_bound {m a q : ℕ} {C : ℝ≥0∞}
    {g : V → Metric.sphere (0 : E) 1 → ℝ≥0∞} (hg : ∀ v, Measurable (g v))
    (hg1 : ∀ v s, g v s ≤ 1)
    (hlocal : ∀ v, SubsphereRegression.PolynomialMass (sphereDensity (g v)) a C)
    (hCt : C ≠ ∞)
    (ha : a ≤ Module.finrank ℝ E) (hm : m ≤ Module.finrank ℝ E)
    (hq : 1 ≤ q) (hmargin : q+m ≤ a)
    (κ : V → ((Fin m → E) × (Fin m → ℝ)) → ℝ≥0∞)
    (hκ : ∀ v, Measurable (κ v)) (hκ1 : ∀ obs, ∑ v, κ v obs ≤ 1) :
    (∑ v, ∫⁻ s, g v s * (∫⁻ X : Fin m → E, κ v (X,fun i => ⟪s.val,X i⟫)
      ∂Measure.pi (fun _ => stdGaussian E)) ∂Affine.sphereLaw E) ≤
      (32768 : ℝ≥0∞)^Module.finrank ℝ E*(Fintype.card V : ℝ≥0∞)^(1/((q : ℝ)+1))*C := by
  let (v : V) : IsFiniteMeasure (sphereDensity (g v)) := sphereDensity_finite (hg1 v)
  let (v : V) : IsFiniteMeasure (SubsphereRegression.projectionLaw (sphereDensity (g v)) m) := by
    unfold SubsphereRegression.projectionLaw
    infer_instance
  simp_rw [← projection_sphere_integral (hg _) (hg1 _) (hκ _)]
  exact routing_mixture_bound (fun v => SubsphereRegression.projectionLaw (sphereDensity (g v)) m)
    κ hκ1 hκ (fun φ hφ => deterministic_sphere_routing hg1 hlocal hCt ha hm hq hmargin φ hφ)

end SubsphereCurrent.Weighted

end

end OAI

-- ---- from OAI.Probability.Subsphere.Geometry.Affine ----
-- Lean 4.33 compatibility: Measurable.of_eval is the renamed measurable_pi_lambda
-- (Mathlib/MeasureTheory/MeasurableSpace/Constructions.lean at d13f23b records the alias).
section Lean433MeasurableOfEval
end Lean433MeasurableOfEval

namespace OAI

section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
universe u v
namespace SubsphereCurrent.Affine

end SubsphereCurrent.Affine
end
end
section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
namespace SubsphereCurrent.Fixed
namespace Stream
variable {E J : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [MeasurableSpace J] [Fintype J] [MeasurableSingletonClass J] [Nonempty J]
  {T : ℕ}

end Stream
end SubsphereCurrent.Fixed
end
end
section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
namespace SubsphereCurrent.Fixed
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

namespace Stream
variable {J : Type*} [MeasurableSpace J] [Fintype J] [MeasurableSingletonClass J] [Nonempty J]
  {T : ℕ}

omit [Nonempty J] in
lemma average_euclideanSuccess_le_one [Nontrivial E] (L : Stream E J T) (η : ℝ) :
    (∫⁻ z : Sphere E × (Fin T → E), L.euclideanSuccess η z.1.val z.2
      ∂(sphereLaw E).prod (rowsLaw E T)) ≤ 1 := by
  calc
    _ ≤ ∫⁻ _ : Sphere E × (Fin T → E), (1 : ℝ≥0∞)
        ∂(sphereLaw E).prod (rowsLaw E T) := lintegral_mono fun _ => prob_le_one
    _ = _ := by simp

end Stream
end SubsphereCurrent.Fixed
end
end
section
/-! Exact Gaussian reconstruction for an affine-sphere test. The complementary
rows are independent random parameters, not an extra sample channel to a learner. -/
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
namespace SubsphereCurrent

end SubsphereCurrent
end
end
section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
namespace SubsphereCurrent.Affine
variable {d n : ℕ}
namespace Test
variable (A : Test d n)

end Test

namespace Simulation
variable {J : Type*} [Fintype J] [Nonempty J] [MeasurableSpace J] [MeasurableSingletonClass J]
  {T : ℕ} (A : Test d n) (L : Fixed.Stream (Vector d) J T)

omit [Fintype J] [Nonempty J] [MeasurableSpace J] [MeasurableSingletonClass J] in
lemma borel (hL : L.BorelRules) (w : Fin T → A.spaceᗮ) : (stream A L w).BorelRules := by
  intro t q a
  exact (hL t q a).comp (by fun_prop)

end Simulation
end SubsphereCurrent.Affine
end
end
section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
namespace SubsphereCurrent.Fixed
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

namespace Stream
variable {J : Type*} [Fintype J] [Nonempty J] [MeasurableSpace J] [MeasurableSingletonClass J]
  {T : ℕ}
end Stream
end SubsphereCurrent.Fixed
end
end
section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
namespace SubsphereCurrent.Affine
namespace Simulation
attribute [local instance] OAI.SubsphereCurrent.Affine.Simulation.affineSimulationSphereLaw_probability
variable {d n : ℕ} (A : Test d n) [Nontrivial A.space]
  {J : Type*} [Fintype J] [Nonempty J] [MeasurableSpace J] [MeasurableSingletonClass J]
  {T : ℕ} (L : Fixed.Stream (Vector d) J T)

end Simulation
end SubsphereCurrent.Affine
end
end
section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
namespace SubsphereCurrent.Weighted
variable {d n m : ℕ} (A : Affine.Test d n) [Nontrivial A.space]
variable {V : Type*} [Fintype V]

omit [Nontrivial A.space] in
lemma measurable_pullObservation (w : Fin m → A.spaceᗮ) : Measurable (pullObservation A w) := by
  unfold pullObservation
  fun_prop

end SubsphereCurrent.Weighted
end
end

end OAI

-- ---- from OAI.Probability.Subsphere.Estimates.Weighted ----
namespace OAI

noncomputable section

namespace SubsphereCurrent.Weighted
section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace

section
universe v

lemma block_parameters {d n : ℕ} (hd : 128 ≤ d) (hn : (d : ℝ)/2 ≤ n) :
    0 < n-2 ∧ (n-2)+1 ≤ n ∧ (d/16+1)+1 ≤ n-2 ∧
      2*(d/16+1) ≤ n-2 ∧ (d : ℝ)/16 ≤ (d/16+1 : ℕ) ∧
      1 ≤ d/16-1 ∧ (d/16-1)+d/16 ≤ (n-2)-(d/16+1) ∧
      d/16 ≤ n ∧ 0 < n := by
  have hdn : d ≤ 2*n := by exact_mod_cast (by linarith : (d : ℝ) ≤ 2*n)
  have hsmall : (d : ℝ)/16 ≤ (d/16+1 : ℕ) := by
    have hrem := Nat.mod_lt d (by norm_num : 0 < 16)
    have hdiv := Nat.mod_add_div d 16
    have hcast : (d : ℝ) < 16*((d/16 : ℕ)+1) := by exact_mod_cast (by omega : d < 16*(d/16+1))
    push_cast
    linarith
  exact ⟨by omega,by omega,by omega,by omega,hsmall,by omega,by omega,by omega,by omega⟩

lemma weighted_block_test {d n : ℕ} (hd : 128 ≤ d) (hn : (d : ℝ)/2 ≤ n) (hnd : n ≤ d)
    {V : Type v} [Fintype V] [Nonempty V] [MeasurableSpace V] [MeasurableSingletonClass V]
    (κ : V → Observation d (d/16) → ℝ≥0∞) (hκ : ∀ v, Measurable (κ v))
    (hκ1 : ∀ obs, ∑ v, κ v obs ≤ 1)
    (g : V → Sphere d → ℝ≥0∞) (hg : ∀ v, Measurable (g v)) (hg1 : ∀ v s, g v s ≤ 1)
    (A : Affine.Test d n) :
    (ENNReal.ofReal A.radius)^((d : ℝ)/16) *
      (∫⁻ s, blockInput κ g (onTest A s) ∂Affine.sphereLaw A.space) ≤
      (32768 : ℝ≥0∞)^n*(Fintype.card V : ℝ≥0∞)^(1/((d/16 : ℕ) : ℝ))*
        ((2 : ℝ≥0∞)^(n+1)*(⨆ v, norm d (n-2) (g v))) := by
  obtain ⟨hk,hkn,hb0,h2b,hb,hq,hmargin,hm,hn0⟩ := block_parameters hd hn
  let : Nontrivial A.space := Module.nontrivial_of_finrank_pos (A.dimension ▸ hn0)
  let C := (2 : ℝ≥0∞)^(n+1)*(⨆ v, norm d (n-2) (g v))
  have hC : C ≠ ∞ := by
    apply ENNReal.mul_ne_top (by finiteness)
    exact ne_top_of_le_ne_top (by norm_num : (1 : ℝ≥0∞) ≠ ∞)
      (iSup_le fun v => weighted_norm_le_one hk (hg1 v))
  have hlocal (v : V) : SubsphereRegression.PolynomialMass (sphereDensity (weightedOnTest A (g v)))
      ((n-2)-(d/16+1)) C := by
    intro z t ht
    apply (polynomialMass_weighted A (hg v) hkn hb0 h2b hb z t ht).trans
    exact mul_le_mul' (mul_le_mul' le_rfl (le_iSup (fun v => norm d (n-2) (g v)) v)) le_rfl
  rw [block_reconstruct A κ hκ g hg]
  have he : (((d/16-1 : ℕ) : ℝ)+1) = ((d/16 : ℕ) : ℝ) := by
    rw [Nat.cast_sub (by omega : 1 ≤ d/16),Nat.cast_one]
    ring
  calc
    _ ≤ ∫⁻ _ : Fin (d/16) → A.spaceᗮ,
        (32768 : ℝ≥0∞)^n*(Fintype.card V : ℝ≥0∞)^(1/((d/16 : ℕ) : ℝ))*C
        ∂Measure.pi (fun _ => stdGaussian A.spaceᗮ) := by
      apply lintegral_mono
      intro w
      have hr := sphere_routing_bound (E := A.space) (fun v => measurable_weightedOnTest A (hg v))
        (fun v => weightedOnTest_le_one A (hg1 v)) hlocal hC
        (by rw [A.dimension]; omega) (by rwa [A.dimension]) hq hmargin
        (fun v obs => κ v (pullObservation A w obs))
        (fun v => (hκ v).comp (measurable_pullObservation A w))
        (fun obs => hκ1 (pullObservation A w obs))
      simpa only [A.dimension,he] using hr
    _ = _ := by simp [C]

lemma weighted_block {d n : ℕ} (hd : 128 ≤ d) (hn : (d : ℝ)/2 ≤ n) (hnd : n ≤ d)
    {W : ℝ} (_hW : 1 ≤ W)
    {V : Type v} [Fintype V] [Nonempty V] (hcard : (Fintype.card V : ℝ) ≤ W)
    (κ : V → Observation d (d/16) → ℝ≥0∞) (hκ : ∀ v, Measurable (κ v))
    (hκ1 : ∀ obs, ∑ v, κ v obs ≤ 1)
    (g : V → Sphere d → ℝ≥0∞) (hg : ∀ v, Measurable (g v)) (hg1 : ∀ v s, g v s ≤ 1) :
    norm d n (blockInput κ g) ≤
      (ENNReal.ofReal W)^(1/((d/16 : ℕ) : ℝ))*ENNReal.ofReal ((131072 : ℝ)^d)*
        (⨆ v, norm d (n-2) (g v)) := by
  classical
  let : MeasurableSpace V := ⊤
  let : MeasurableSingletonClass V := ⟨fun _ => trivial⟩
  apply iSup_le
  intro A
  apply (weighted_block_test hd hn hnd κ hκ hκ1 g hg hg1 A).trans
  have hc : (Fintype.card V : ℝ≥0∞)^(1/((d/16 : ℕ) : ℝ)) ≤
      (ENNReal.ofReal W)^(1/((d/16 : ℕ) : ℝ)) := by
    apply ENNReal.rpow_le_rpow _ (by positivity)
    exact_mod_cast ENNReal.ofReal_le_ofReal hcard
  have hp : (32768 : ℝ≥0∞)^n*2^(n+1) ≤ ENNReal.ofReal ((131072 : ℝ)^d) := by
    have hn1 : n+1 ≤ 2*d := by omega
    calc
      _ ≤ (32768 : ℝ≥0∞)^d*2^(2*d) := mul_le_mul'
        (pow_le_pow_right₀ (by norm_num) hnd) (pow_le_pow_right₀ (by norm_num) hn1)
      _ = _ := by rw [pow_mul,← mul_pow,ENNReal.ofReal_pow (by positivity)]; norm_num
  calc
    _ = (Fintype.card V : ℝ≥0∞)^(1/((d/16 : ℕ) : ℝ))*
        ((32768 : ℝ≥0∞)^n*2^(n+1))*(⨆ v, norm d (n-2) (g v)) := by ac_rfl
    _ ≤ _ := mul_le_mul' (mul_le_mul' hc hp) le_rfl

end

end
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace

theorem radius_weighted_full_estimate : RadiusWeightedFullEstimate := by
  refine ⟨131072,by norm_num,128,?_⟩
  intro d hd
  constructor
  · intro W hW V _ _ hcard κ hκ hκ1 g hg hg1 n hn hnd
    exact weighted_block hd hn hnd hW hcard κ hκ hκ1 g hg hg1
  · intro n hn hnd π hπ ε hε
    let := hπ
    apply (weighted_terminal (by omega : 4 ≤ d) hn hnd π hε).trans
    apply mul_le_mul' _ le_rfl
    apply ENNReal.ofReal_le_ofReal
    exact pow_le_pow_left₀ (by norm_num) (by norm_num) d

end SubsphereCurrent.Weighted

end

end OAI

-- ---- from OAI.Probability.Subsphere.Estimates.HalfPrecision ----
namespace OAI

noncomputable section

namespace SubsphereRegression
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
namespace Learner
end Learner
end SubsphereRegression
section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace
universe u
namespace SubsphereRegression
namespace Learner
lemma streaming_success_bound_half_real {d M T : ℕ} {Ω : Type u} [MeasurableSpace Ω]
    (L : Learner d M T Ω) (ρ : Measure Ω) [IsProbabilityMeasure ρ]
    (hL : L.Admissible ρ) (hd : 3 ≤ d) {ε : ℝ} (hε : 0 < ε)
    {a q : ℕ} (ha : 2*a ≤ d-1) (hq : 2 ≤ q) (hqa : 2*q ≤ a)
    (hs : (1/2 : ℝ≥0∞) ≤ L.uniformSuccess ρ ε) :
    (1/2 : ℝ) ≤ ((T : ℝ)+1) * ((3 : ℝ)*4^d * ε^a) *
      ((32768 : ℝ)^d * ((2 : ℝ)^M)^(1/(q : ℝ)))^(T/q+1) := by
  have hb := hs.trans (L.streaming_success_bound ρ hL hd hε ha hq hqa)
  have ht : (T+1 : ℝ≥0∞) *
      (ENNReal.ofReal ((3 : ℝ)*4^d) * ENNReal.ofReal (ε^a)) *
      streamFactor (E := Vector d) (J := State M) q ^ (T/q+1) ≠ ∞ := by
    apply ENNReal.mul_ne_top
    · apply ENNReal.mul_ne_top (by simp)
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
    · exact ENNReal.pow_ne_top (streamFactor_ne_top q)
  have hr := ENNReal.toReal_mono ht hb
  simpa [ENNReal.toReal_div, ENNReal.toReal_ofNat, ENNReal.toReal_mul,
    ENNReal.toReal_add, ENNReal.toReal_natCast, ENNReal.toReal_one,
    ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ 3*4^d),
    ENNReal.toReal_ofReal (by positivity : 0 ≤ ε^a), streamFactor,
    ENNReal.toReal_pow, ← ENNReal.toReal_rpow, finrank_euclideanSpace_fin,
    Fintype.card_fin, State, Nat.cast_pow, Nat.cast_ofNat, Vector] using hr

end Learner

theorem half_precision_old_model :
  ∀ M : ℕ → ℕ,
    Asymptotics.IsLittleO atTop (fun d => (M d : ℝ)) (fun d => (d : ℝ) ^ 2) →
    ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d → ∀ T : ℕ, ∀ ε : ℝ,
    0 < ε → ε ≤ 1 / 10 →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (ρ : Measure Ω), IsProbabilityMeasure ρ →
    ∀ L : Learner d (M d) T Ω, L.Admissible ρ →
    ((1 / 2 : ℝ≥0∞) ≤ L.uniformSuccess ρ ε) →
    (1 / (4 * (1024 + 512)) * Real.log 2 : ℝ) * (d : ℝ) * Real.logb 2 (1 / ε) ≤ (T : ℝ) := by
  intro M hM
  obtain ⟨d₂, hd₂⟩ := eventually_atTop.1 hM.eventuallyLE
  refine ⟨max 32 d₂, ?_⟩
  intro d hd T ε hε hε10 Ω _ ρ hρ L hL hs
  let : IsProbabilityMeasure ρ := hρ
  have hd32 : 32 ≤ d := by omega
  have hmem : (M d : ℝ) ≤ 1 * (d : ℝ)^2 := by
    have hm := hd₂ d (by omega)
    simpa only [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg (M d) : (0 : ℝ) ≤ M d),
      abs_of_nonneg (sq_nonneg (d : ℝ)), one_mul] using hm
  have hs' := hs
  have hT : d ≤ 32*T := by
    by_contra h
    have hb := hs'.trans (L.half_linear_success_bound ρ (by omega) (by omega) hε10 hL)
    have hr := ENNReal.toReal_mono ENNReal.ofReal_ne_top hb
    norm_num [ENNReal.toReal_div] at hr
  let q := (d-1)/4
  let a := 2*q
  have hq : 2 ≤ q := by dsimp [q]; omega
  have hqa : 2*q ≤ a := le_rfl
  have ha : 2*a ≤ d-1 := by dsimp [a, q]; omega
  have hdq : d ≤ 8*q := by dsimp [q]; omega
  have hda : d ≤ 4*a := by dsimp [a]; omega
  have hp := precision_from_stream_bound_half_aux hd32 hT (by omega) hdq hda hmem
    (by norm_num : (0 : ℝ) < 1) hε (by linarith : ε ≤ 1)
    (L.streaming_success_bound_half_real ρ hL (by omega) hε ha hq hqa hs')
  have hlog2 : Real.log (2 : ℝ) ≠ 0 := (Real.log_pos (by norm_num)).ne'
  calc
    _ = (1 / (4 * (1024 + 512))) * (d : ℝ) * Real.log (1 / ε) := by
      rw [Real.logb]
      field_simp
    _ ≤ T := by simpa only [mul_one] using hp

end SubsphereRegression
end
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace
universe u
namespace SubsphereCurrent

theorem half_precision : HalfPrecision.{u} := by
  refine ⟨1 / (4 * (1024 + 512)) * Real.log 2, mul_pos (by norm_num) (Real.log_pos (by norm_num)), ?_⟩
  intro M hM
  obtain ⟨d₁, hd₁⟩ := SubsphereRegression.half_precision_old_model.{0} M hM
  refine ⟨max 3 d₁, ?_⟩
  intro d hd T ε hε hε10 Ω _ ρ hρ L hL hs
  let : IsProbabilityMeasure ρ := hρ
  let : NeZero d := ⟨by omega⟩
  obtain ⟨ω, hω, hgood⟩ := L.exists_good_seed ρ hL ε
  let K := (L.rules ω).borelVersion hω
  have hK : K.BorelRules := (L.rules ω).borelVersion_rules hω
  have hsuccess : (1/2 : ℝ≥0∞) ≤ K.asTape.uniformSuccess K.tapeLaw ε := by
    rw [K.uniformSuccess_asTape hK ε]
    calc
      (1/2 : ℝ≥0∞) ≤ L.uniformSuccess ρ ε := hs
      _ ≤ ∫⁻ z : UnitSphere d × Samples d T, (L.rules ω).conditionalSuccess ε z.1 z.2
          ∂(uniformSphere d).prod (sampleLaw d T) := hgood
      _ = ∫⁻ z : UnitSphere d × Samples d T, K.conditionalSuccess ε z.1 z.2
          ∂(uniformSphere d).prod (sampleLaw d T) :=
        lintegral_congr_ae ((L.rules ω).borelVersion_success_ae hω (by omega) ε)
  exact hd₁ d (by omega) T ε hε hε10 (KernelLearner.Tape d (M d) T)
    K.tapeLaw inferInstance K.asTape (K.asTape_admissible hK) hsuccess

end SubsphereCurrent

end

end OAI

-- ---- from OAI.Probability.Subsphere.Estimates.AffinePrecision ----
namespace OAI

noncomputable section

namespace SubsphereCurrent.Affine
open scoped ENNReal NNReal

lemma affine_parameters {d n ell : ℕ} (hd : 128 ≤ d) (hn : (d+1)/2 + 2*ell ≤ n) :
    let q := (n-1)/4
    2 ≤ q ∧ n ≤ 5*q ∧ d ≤ 2*n ∧ d/16 ≤ q ∧ d/8 ≤ 2*q ∧
      2*(d/32) ≤ 2*q ∧ ell*(d/16)/q+1 ≤ ell+1 := by
  dsimp
  have hq : 2 ≤ (n-1)/4 := by omega
  have hm : d/16 ≤ (n-1)/4 := by omega
  refine ⟨hq,by omega,by omega,hm,by omega,by omega,?_⟩
  have := Nat.div_le_of_le_mul (by simpa [Nat.mul_comm] using Nat.mul_le_mul_left ell hm)
  omega

lemma log_card_of_width {d J : ℕ} {W : ℝ} (hd : 128 ≤ d) (hJ : 1 ≤ J)
    (hJW : (J : ℝ) ≤ W) (hbudget : W^(1/((d/8 : ℕ) : ℝ)) ≤ (2 : ℝ)^d) :
    Real.log (J : ℝ) ≤ ((d/8 : ℕ) : ℝ)*d*Real.log 2 := by
  have hp : (0 : ℝ) < (d/8 : ℕ) := by exact_mod_cast (by omega : 0 < d/8)
  have hJp : (0 : ℝ) < J := by exact_mod_cast (by omega : 0 < J)
  have hWp : 0 < W := hJp.trans_le hJW
  have hlog := Real.log_le_log (Real.rpow_pos_of_pos hWp _) hbudget
  rw [Real.log_rpow hWp,Real.log_pow] at hlog
  have hmul := mul_le_mul_of_nonneg_left hlog hp.le
  have he : ((d/8 : ℕ) : ℝ)*(1/((d/8 : ℕ) : ℝ)*Real.log W) = Real.log W := by
    field_simp
  rw [he] at hmul
  exact (Real.log_le_log hJp hJW).trans (by nlinarith [hmul])

lemma affine_zero_bound {n a : ℕ} {η : ℝ} (hn : 3 ≤ n) (ha : a ≤ n-1)
    (hη : 0 ≤ η) (hsmall : 16*η ≤ 1) :
    (3 : ℝ)*4^n * η^(n-1) ≤ (16*η)^a := by
  have he : n = (n-3)+3 := by omega
  have he' : n-1 = (n-3)+2 := by omega
  have hc : (3 : ℝ)*4^n ≤ 16^(n-1) := by
    calc
      (3 : ℝ)*4^n = 192*4^(n-3) := by
        conv_lhs => rw [he,pow_add]
        norm_num
        ring
      _ ≤ 256*16^(n-3) := by
        have hh : (4 : ℝ)^(n-3) ≤ 16^(n-3) := pow_le_pow_left₀ (by norm_num) (by norm_num) _
        have h0 : (0 : ℝ) ≤ 4^(n-3) := by positivity
        linarith
      _ = (16 : ℝ)^(n-1) := by rw [he',pow_add]; norm_num; ring
  calc
    _ ≤ 16^(n-1)*η^(n-1) := mul_le_mul_of_nonneg_right hc (pow_nonneg hη _)
    _ = (16*η)^(n-1) := by rw [mul_pow]
    _ ≤ _ := pow_le_pow_of_le_one (by positivity) hsmall ha

end SubsphereCurrent.Affine
section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
universe u v
namespace SubsphereCurrent.Affine

lemma simulated_numeric_bound {d n ell : ℕ} (hd : 128 ≤ d)
    (hn : (d+1)/2+2*ell ≤ n) (A : Test d n)
    {J : Type*} [Fintype J] [Nonempty J] [MeasurableSpace J] [MeasurableSingletonClass J]
    (hbudget : Real.log (Fintype.card J : ℝ) ≤ ((d/8 : ℕ) : ℝ)*d*Real.log 2)
    (L : Fixed.Stream A.space J (ell*(d/16))) (hL : L.BorelRules)
    {η : ℝ} (hη : 0 < η) (hsmall : 16*((1000 : ℝ)^32)^ell*η ≤ 1) :
    (∫⁻ z : Sphere A.space × (Fin (ell*(d/16)) → A.space),
      L.euclideanSuccess η z.1.val z.2
        ∂(sphereLaw A.space).prod (Fixed.rowsLaw A.space (ell*(d/16)))) ≤
      ENNReal.ofReal ((16*((1000 : ℝ)^32)^ell*η)^(2*(d/32))) := by
  have hnpos : 0 < n := by omega
  let : Nontrivial A.space := Module.nontrivial_of_finrank_pos (A.dimension ▸ hnpos)
  obtain ⟨hq,_,_,_,_,haq,_⟩ := affine_parameters hd hn
  by_cases hell : ell = 0
  · subst ell
    revert L
    rw [Nat.zero_mul]
    simp only [pow_zero,mul_one]
    intro L hL
    simp only [pow_zero,mul_one] at hsmall
    have hη1 : η ≤ 1 := by nlinarith
    have hb := Fixed.Stream.average_euclideanSuccess_zero_bound (E := A.space) (J := J)
      L hL hη hη1
    rw [A.dimension,← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 3*4^n)] at hb
    exact hb.trans (ENNReal.ofReal_le_ofReal (affine_zero_bound (a := 2*(d/32)) (n := n) (by omega) (by omega) hη.le hsmall))
  · let q := (n-1)/4
    let a := 2*q
    let b := ell*(d/16)/q+1
    have ha : 2*a ≤ Module.finrank ℝ A.space-1 := by rw [A.dimension]; dsimp [a,q]; omega
    have hb := L.average_euclideanSuccess_bound hL hη ha hq (le_refl a)
    have ht : (ENNReal.ofReal ((3 : ℝ)*4^Module.finrank ℝ A.space) * ENNReal.ofReal (η^a)) *
        SubsphereRegression.streamFactor (E := A.space) (J := J) q ^ b ≠ ∞ :=
      ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)
        (ENNReal.pow_ne_top (SubsphereRegression.streamFactor_ne_top q))
    have hr := ENNReal.toReal_mono ht hb
    have hr' : (∫⁻ z : Sphere A.space × (Fin (ell*(d/16)) → A.space),
        L.euclideanSuccess η z.1.val z.2
          ∂(sphereLaw A.space).prod (Fixed.rowsLaw A.space (ell*(d/16)))).toReal ≤
        ((3 : ℝ)*4^n * η^(2*((n-1)/4))) *
          ((32768 : ℝ)^n * (Fintype.card J : ℝ)^(1/(((n-1)/4 : ℕ) : ℝ)))^
            (ell*(d/16)/((n-1)/4)+1) := by
      simpa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ 3*4^n),
        ENNReal.toReal_ofReal (by positivity : 0 ≤ η^a),SubsphereRegression.streamFactor,
        ENNReal.toReal_pow,← ENNReal.toReal_rpow,A.dimension,a,q,b, sphereLaw,Fixed.sphereLaw] using hr
    apply (ENNReal.toReal_le_toReal (ne_top_of_le_ne_top ht hb) ENNReal.ofReal_ne_top).1
    rw [ENNReal.toReal_ofReal (by positivity)]
    exact hr'.trans (affine_raw_bound hd hn (by omega) Fintype.card_pos hbudget hη hsmall)

lemma estimate_one_seed {d n ell : ℕ} (hd : 128 ≤ d)
    (hn : (d+1)/2+2*ell ≤ n) (A : Test d n)
    {J : Type*} [Fintype J] [Nonempty J] [MeasurableSpace J] [MeasurableSingletonClass J]
    (hbudget : Real.log (Fintype.card J : ℝ) ≤ ((d/8 : ℕ) : ℝ)*d*Real.log 2)
    (L : Fixed.Stream (Vector d) J (ell*(d/16))) (hL : L.BorelRules)
    (hu : ∀ q, ∀ᵐ y ∂L.output q, ‖y‖ = 1) {ε : ℝ} (hε : 0 < ε) :
    (∫⁻ z : Sphere A.space × (Fin (ell*(d/16)) → Vector d),
      L.angularSuccess ε (A.point z.1) z.2
        ∂(sphereLaw A.space).prod (Fixed.rowsLaw (Vector d) (ell*(d/16)))) ≤
      ENNReal.ofReal (((16*((1000 : ℝ)^32)^ell*ε)/A.radius)^(2*(d/32))) := by
  have hnpos : 0 < n := by omega
  let : Nontrivial A.space := Module.nontrivial_of_finrank_pos (A.dimension ▸ hnpos)
  let : IsProbabilityMeasure (sphereLaw A.space) := Fixed.sphereLaw_probability
  by_cases hsmall : 16*((1000 : ℝ)^32)^ell*(ε/A.radius) ≤ 1
  · apply Simulation.average_le_of_simulated A L hL hu ε
    intro w
    simpa only [mul_div_assoc] using simulated_numeric_bound hd hn A hbudget
      (Simulation.stream A L w) (Simulation.borel A L hL w) (div_pos hε A.radius_positive) hsmall
  · calc
      _ ≤ ∫⁻ _ : Sphere A.space × (Fin (ell*(d/16)) → Vector d), (1 : ℝ≥0∞)
          ∂(sphereLaw A.space).prod (Fixed.rowsLaw (Vector d) (ell*(d/16))) :=
        lintegral_mono (fun _ => prob_le_one)
      _ = 1 := by simp
      _ ≤ _ := ENNReal.one_le_ofReal.2 (one_le_pow₀ (by simpa only [mul_div_assoc] using le_of_lt (lt_of_not_ge hsmall)))

end SubsphereCurrent.Affine
end
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
universe u v
namespace SubsphereCurrent.Affine

theorem all_affine_full_estimate : AllAffineFullEstimate.{u,v} := by
  refine ⟨128,?_⟩
  intro d hd k hk W hW J _ _ _ _ hJW hbudget ε hε hε1 Ω _ ρ hρ L hL ell hell state n hn A
  let : IsProbabilityMeasure ρ := hρ
  have hnpos : 0 < n := by omega
  let : Nontrivial A.space := Module.nontrivial_of_finrank_pos (A.dimension ▸ hnpos)
  let : IsProbabilityMeasure (sphereLaw A.space) := Fixed.sphereLaw_probability
  let : IsFiniteMeasure (Fixed.rowsLaw (Vector d) (ell*(d/16))) := inferInstance
  let : SFinite (Fixed.rowsLaw (Vector d) (ell*(d/16))) := by
    let : SigmaFinite (Fixed.rowsLaw (Vector d) (ell*(d/16))) := IsFiniteMeasure.toSigmaFinite _
    infer_instance
  have hlog := log_card_of_width hd Fintype.card_pos hJW hbudget
  let e := swapFirstTwo Ω (Sphere A.space) (Fin (ell*(d/16)) → Vector d)
  have hp := measurePreserving_swapFirstTwo ρ (sphereLaw A.space) (Fixed.rowsLaw (Vector d) (ell*(d/16)))
  have he := hp.lintegral_comp_emb e.measurableEmbedding
    (fun z : Sphere A.space × (Ω × (Fin (ell*(d/16)) → Vector d)) =>
      ((L z.2.1).suffix ((k-ell)*(d/16)) (ell*(d/16)) state).angularSuccess ε (A.point z.1) z.2.2)
  rw [← he]
  apply (lintegral_prod_le _).trans
  calc
    _ ≤ ∫⁻ _ : Ω, ENNReal.ofReal (((16*((1000 : ℝ)^32)^ell*ε)/A.radius)^(2*(d/32))) ∂ρ := by
      apply lintegral_mono_ae
      filter_upwards [hL] with ω hω
      exact estimate_one_seed hd hn A hlog
        ((L ω).suffix ((k-ell)*(d/16)) (ell*(d/16)) state)
        (fun t q a => hω.1 _ q a) hω.2 hε
    _ = _ := by simp

end SubsphereCurrent.Affine

end

end OAI

-- ---- from OAI.Probability.Subsphere.Estimates.FixedPrecision ----
namespace OAI

noncomputable section

namespace SubsphereCurrent.Fixed
section
open scoped ENNReal NNReal

lemma two_le_boundConstant : 2 ≤ boundConstant := by
  have h := Real.add_one_le_exp (2048 : ℝ)
  unfold boundConstant
  linarith

end
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
universe u

lemma dimension_bound_one_seed {d j m : ℕ} (hd : 64 ≤ d)
    (hm : (d : ℝ)/2 + 2*j ≤ m) (hmd : m ≤ d)
    (L : Stream (Vector m) (Fin (2^(d^2))) (j*(d/32))) (hL : L.BorelRules)
    {η : ℝ} (hη : 0 < η) :
    (∫⁻ z : Sphere (Vector m) × (Fin (j*(d/32)) → Vector m),
      L.euclideanSuccess η z.1.val z.2
        ∂(sphereLaw (Vector m)).prod (rowsLaw (Vector m) (j*(d/32)))) ≤
      ENNReal.ofReal ((boundConstant^(j+1)*η)^((d : ℝ)/32)) := by
  have hmpos : 0 < m := by
    have hdp : (64 : ℝ) ≤ d := by exact_mod_cast hd
    have : (0 : ℝ) < m := by nlinarith [Nat.cast_nonneg j (α := ℝ)]
    exact_mod_cast this
  let : NeZero m := ⟨by omega⟩
  let q := (m-1)/4
  let a := 2*q
  have hq : 2 ≤ q := (parameters hd hm).1
  have ha : 2*a ≤ Module.finrank ℝ (Vector m)-1 := by
    simp only [Vector,finrank_euclideanSpace_fin]
    dsimp [a,q]
    omega
  have hcpos : 0 < boundConstant := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) two_le_boundConstant
  have hP1 := L.average_euclideanSuccess_le_one η
  by_cases hη1 : η ≤ 1
  · have hb := L.average_euclideanSuccess_bound hL hη ha hq (le_refl a)
    have ht : (ENNReal.ofReal ((3 : ℝ)*4^Module.finrank ℝ (Vector m)) * ENNReal.ofReal (η^a)) *
        SubsphereRegression.streamFactor (E := Vector m) (J := Fin (2^(d^2))) q ^
          (j*(d/32)/q+1) ≠ ∞ :=
      ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)
        (ENNReal.pow_ne_top (SubsphereRegression.streamFactor_ne_top q))
    have hr := ENNReal.toReal_mono ht hb
    have hr' : (∫⁻ z : Sphere (Vector m) × (Fin (j*(d/32)) → Vector m),
        L.euclideanSuccess η z.1.val z.2
          ∂(sphereLaw (Vector m)).prod (rowsLaw (Vector m) (j*(d/32)))).toReal ≤
        ((3 : ℝ)*4^m * η^(2*((m-1)/4))) *
          ((32768 : ℝ)^m * ((2 : ℝ)^(d^2))^(1/(((m-1)/4 : ℕ) : ℝ)))^
            (j*(d/32)/((m-1)/4)+1) := by
      simpa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ 3*4^m),
        ENNReal.toReal_ofReal (by positivity : 0 ≤ η^a), SubsphereRegression.streamFactor,
        ENNReal.toReal_pow, ← ENNReal.toReal_rpow, finrank_euclideanSpace_fin,
        Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat, Vector,a,q] using hr
    apply (ENNReal.toReal_le_toReal (ne_top_of_le_ne_top (by simp) hP1) ENNReal.ofReal_ne_top).1
    rw [ENNReal.toReal_ofReal (Real.rpow_nonneg (by positivity) _)]
    exact hr'.trans (raw_bound_le hd hm hmd hη hη1)
  · apply hP1.trans
    apply ENNReal.one_le_ofReal.2
    apply Real.one_le_rpow _ (by positivity)
    have hc : 1 ≤ boundConstant^(j+1) := one_le_pow₀ (by linarith [two_le_boundConstant])
    nlinarith

theorem dimension_estimate : DimensionEstimate.{u} := by
  refine ⟨boundConstant,two_le_boundConstant,64,?_⟩
  intro d hd j m hm hmd η hη Ω _ ρ hρ L hL hmexp
  let : IsProbabilityMeasure ρ := hρ
  have hmpos : 0 < m := by
    have hdp : (64 : ℝ) ≤ d := by exact_mod_cast hd
    have : (0 : ℝ) < m := by nlinarith [Nat.cast_nonneg j (α := ℝ)]
    exact_mod_cast this
  let : NeZero m := ⟨by omega⟩
  let : IsProbabilityMeasure (rowsLaw (Vector m) (j*(d/32))) := rowsLaw_probability _
  let : IsFiniteMeasure (rowsLaw (Vector m) (j*(d/32))) := inferInstance
  let : SFinite (rowsLaw (Vector m) (j*(d/32))) := by
    let : SigmaFinite (rowsLaw (Vector m) (j*(d/32))) := IsFiniteMeasure.toSigmaFinite _
    infer_instance
  let e := swapFirstTwo Ω (Sphere (Vector m)) (Fin (j*(d/32)) → Vector m)
  have hp := measurePreserving_swapFirstTwo ρ (sphereLaw (Vector m)) (rowsLaw (Vector m) (j*(d/32)))
  have hm' := hmexp.comp_quasiMeasurePreserving hp.quasiMeasurePreserving
  have he := hp.lintegral_comp_emb e.measurableEmbedding
    (fun z : Sphere (Vector m) × (Ω × (Fin (j*(d/32)) → Vector m)) =>
      (L z.2.1).euclideanSuccess η z.1.val z.2.2)
  dsimp only [Function.comp_def] at hm'
  rw [← he,lintegral_prod _ hm']
  calc
    _ ≤ ∫⁻ _ : Ω, ENNReal.ofReal ((boundConstant^(j+1)*η)^((d : ℝ)/32)) ∂ρ := by
      apply lintegral_mono_ae
      filter_upwards [hL] with ω hω
      exact dimension_bound_one_seed hd hm hmd (L ω) hω hη
    _ = _ := by simp

end SubsphereCurrent.Fixed

end

end OAI

-- ---- from OAI.Probability.Subsphere.Mixture.Domination ----
-- Lean 4.33 compatibility: Measurable.of_eval is the renamed measurable_pi_lambda
-- (Mathlib/MeasureTheory/MeasurableSpace/Constructions.lean at d13f23b records the alias).
section Lean433MeasurableOfEval
private theorem Measurable.of_eval {α δ : Type*} {X : δ → Type*}
    [MeasurableSpace α] [∀ a, MeasurableSpace (X a)] {f : α → ∀ a, X a}
    (hf : ∀ a, Measurable fun c => f c a) : Measurable f :=
  measurable_pi_lambda f hf
end Lean433MeasurableOfEval

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
namespace SubsphereCurrent.Mixture
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

end SubsphereCurrent.Mixture
end
end
section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
noncomputable section
namespace SubsphereCurrent

end SubsphereCurrent
end
end
section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
namespace SubsphereCurrent.Mixture
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

end SubsphereCurrent.Mixture
end
end
section
open MeasureTheory Set
noncomputable section
namespace SubsphereCurrent.Mixture
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F]

lemma ambientSphereLaw_transport (e : E ≃ₗᵢ[ℝ] F) :
    MeasurePreserving e SubsphereRegression.ambientSphereLaw SubsphereRegression.ambientSphereLaw := by
  have hs : MeasurePreserving (Polar.sphereMap e) (SubsphereRegression.sphereLaw (E := E))
      (SubsphereRegression.sphereLaw (E := F)) := Polar.sphereMap_preserving e
  refine ⟨e.continuous.measurable,?_⟩
  rw [SubsphereRegression.ambientSphereLaw,SubsphereRegression.ambientSphereLaw,
    Measure.map_map e.continuous.measurable (by fun_prop),← hs.map_eq,
    Measure.map_map (by fun_prop) hs.measurable]
  rfl

end SubsphereCurrent.Mixture
end
end
section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
namespace SubsphereCurrent.Mixture
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

lemma block_bottom_haar [Nontrivial E] {x : E} (hx : ‖x‖ = 1) :
    MeasurePreserving (fun w : Orthogonal (⊥ : Submodule ℝ E)ᗮ => blockIso ⊥ 1 w x)
      orthogonalLaw SubsphereRegression.ambientSphereLaw := by
  let K : Submodule ℝ E := (⊥ : Submodule ℝ E)ᗮ
  have hK : K = ⊤ := Submodule.bot_orthogonal_eq_top
  let e := LinearIsometryEquiv.ofTop E K hK
  let : Nontrivial K := e.symm.injective.nontrivial
  let xK : K := ⟨x,by simp [K]⟩
  have h := (ambientSphereLaw_transport e).comp (haar_eval_preserving (show ‖xK‖ = 1 from hx))
  convert h using 1
  funext w
  exact blockIso_on_right ⊥ 1 w xK

lemma directionLaw_bottom (N : Submodule ℝ E) [Nontrivial N] [Nontrivial E] :
    directionLaw ⊥ N = SubsphereRegression.ambientSphereLaw := by
  apply Measure.ext_of_lintegral
  intro f hf
  have hm := measurable_directionSampler (⊥ : Submodule ℝ E) N
  rw [directionLaw,lintegral_map hf hm]
  rw [lintegral_prod_symm (fun z : Orthogonal (⊥ : Submodule ℝ E)ᗮ × N =>
    f (blockIso ⊥ 1 z.1 (z.2 : E))) (hf.comp hm).aemeasurable]
  calc
    _ = ∫⁻ _x : N, (∫⁻ y, f y ∂SubsphereRegression.ambientSphereLaw)
        ∂SubsphereRegression.ambientSphereLaw := by
      apply lintegral_congr_ae
      filter_upwards [SubsphereRegression.ambientSphereLaw_ae_norm (E := N)] with x hx
      exact (block_bottom_haar (show ‖(x : E)‖ = 1 from hx)).lintegral_comp hf
    _ = _ := by simp

lemma measurable_directionJointSampler (V N : Submodule ℝ E) (t : ℕ) :
    Measurable (fun z : Orthogonal Vᗮ × (Fin t → N) => fun i => blockIso V 1 z.1 (z.2 i : E)) := by
  apply Measurable.of_eval
  intro i
  exact ((continuous_blockIso V).comp
    ((continuous_const.prodMk continuous_fst).prodMk
      (continuous_subtype_val.comp ((continuous_apply i).comp continuous_snd)))).measurable

lemma directionJointLaw_top (V : Submodule ℝ E) (t : ℕ) [Nontrivial E] :
    directionJointLaw V ⊤ t = Measure.pi (fun _ : Fin t => SubsphereRegression.ambientSphereLaw) := by
  let : Nontrivial (⊤ : Submodule ℝ E) :=
    (LinearIsometryEquiv.ofTop E (⊤ : Submodule ℝ E) rfl).symm.injective.nontrivial
  apply Measure.ext_of_lintegral
  intro f hf
  have hm := measurable_directionJointSampler V (⊤ : Submodule ℝ E) t
  rw [directionJointLaw,lintegral_map hf hm]
  rw [lintegral_prod (fun z : Orthogonal Vᗮ × (Fin t → (⊤ : Submodule ℝ E)) =>
    f (fun i => blockIso V 1 z.1 (z.2 i : E))) (hf.comp hm).aemeasurable]
  have h (w : Orthogonal Vᗮ) :
      (∫⁻ x : Fin t → (⊤ : Submodule ℝ E), f (fun i => blockIso V 1 w (x i : E))
        ∂Measure.pi (fun _ => SubsphereRegression.ambientSphereLaw)) =
      ∫⁻ x : Fin t → E, f x ∂Measure.pi (fun _ => SubsphereRegression.ambientSphereLaw) := by
    let e := (LinearIsometryEquiv.ofTop E (⊤ : Submodule ℝ E) rfl).trans (blockIso V 1 w)
    exact (measurePreserving_pi (fun _ : Fin t => SubsphereRegression.ambientSphereLaw)
      (fun _ => SubsphereRegression.ambientSphereLaw)
      (fun _ => ambientSphereLaw_transport e)).lintegral_comp hf
  simp_rw [h]
  simp

end SubsphereCurrent.Mixture
end
end
section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
namespace SubsphereCurrent.Mixture

theorem mixture_estimate (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] : MixtureEstimate E := by
  refine ⟨directionLaw_domination,?_,?_⟩
  · intro N hN
    let : Nontrivial N := Module.nontrivial_of_finrank_pos (R := ℝ) (M := N) (by omega)
    have hNE := Submodule.finrank_le N
    let : Nontrivial E := Module.nontrivial_of_finrank_pos (R := ℝ) (M := E) (by omega)
    exact directionLaw_bottom N
  · intro V t hE
    let : Nontrivial E := Module.nontrivial_of_finrank_pos (R := ℝ) (M := E) (by omega)
    exact directionJointLaw_top V t

end SubsphereCurrent.Mixture
end
end

end OAI

-- ---- from OAI.Probability.Subsphere.Main ----
namespace OAI

section
noncomputable section
universe u v w
namespace SubsphereCurrent

theorem full_current_main_scope : CurrentMainScope.{u,v,w} := by
  exact ⟨explicit_precision, Weighted.radius_weighted_full_estimate,
    half_precision, Affine.all_affine_full_estimate, Fixed.dimension_estimate,
    Mixture.mixture_estimate⟩

end SubsphereCurrent
end
end

end OAI

-- ---- mission target ----
open OAI OAI.SubsphereCurrent
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
universe u v w

namespace OAI
namespace SubsphereCurrent
theorem _root_.solution : CurrentMainScope.{u,v,w} := by
  first
    | exact OAI.SubsphereCurrent.full_current_main_scope
    | (apply OAI.SubsphereCurrent.full_current_main_scope <;> assumption)
    | (intros; apply OAI.SubsphereCurrent.full_current_main_scope <;> assumption)
end SubsphereCurrent
end OAI
