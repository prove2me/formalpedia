-- Prove2me | solution 1 for OAI.SubsphereCurrent.Fixed.Stream.lintegral_tapeEstimate
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T09:07:41.894469+00:00
-- url     : https://prove2.me/submissions/5b909a88-90cc-4fb8-8d5d-72a9427d2f4e

-- Generated from openai/math@1581d4c lean/OAI/Probability/Subsphere/Geometry/Affine.lean:L130-L156
-- (upload_full_project.md Phase 4): solution for node OAI.SubsphereCurrent.Fixed.Stream.lintegral_tapeEstimate. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
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
import Theorems.Thm_OAI_SubsphereCurrent_detChain_lintegral
import Theorems.Thm_OAI_SubsphereCurrent_finiteSample_map
import Theorems.Thm_OAI_SubsphereCurrent_measurable_finiteSample

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

lemma measurable_select {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {h : J → X → Y} (hh : ∀ j, Measurable (h j)) {φ : X → J} (hφ : Measurable φ) :
    Measurable (fun x => h (φ x) x) :=
  (measurable_from_prod_countable_right (f := fun p : J × X => h p.1 p.2) hh).comp (hφ.prodMk measurable_id)

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

end FiniteVersion

namespace KernelLearner

end KernelLearner
end SubsphereCurrent
end
end
section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
noncomputable section
namespace SubsphereCurrent

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

lemma samplePMF_map [MeasurableSpace A] [MeasurableSingletonClass A] (p : PMF A) :
    coinLaw.map (samplePMF p) = p.toMeasure := by
  let : NeZero (Fintype.card A) := ⟨Fintype.card_ne_zero⟩
  let e := Fintype.equivFin A
  have hm : Measurable (finiteSample (p.map e)) :=
    measurable_finiteSample (fun _ => measurable_const) measurable_id
  change coinLaw.map (e.symm ∘ finiteSample (p.map e)) = _
  rw [← Measure.map_map (measurable_of_finite e.symm) hm, finiteSample_map,
    PMF.toMeasure_map _ _ (measurable_of_finite e.symm), PMF.map_comp]
  have he : e.symm ∘ e = id := by funext a; simp
  rw [he, PMF.map_id]
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

lemma pmf_toMeasure_bind (p : PMF A) (k : A → PMF B) :
    (p.bind k).toMeasure = p.toMeasure.bind (fun a => (k a).toMeasure) := by
  apply Measure.ext_of_singleton
  intro b
  rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton b),
    PMF.bind_apply, Measure.bind_apply (measurableSet_singleton b)
      (measurable_of_countable _).aemeasurable, lintegral_countable']
  simp only [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _), mul_comm]

lemma pmf_lintegral_bind (p : PMF A) (k : A → PMF B) (f : B → ℝ≥0∞) :
    (∫⁻ b, f b ∂(p.bind k).toMeasure) =
      ∫⁻ a, ∫⁻ b, f b ∂(k a).toMeasure ∂p.toMeasure := by
  rw [pmf_toMeasure_bind, Measure.lintegral_bind
    (measurable_of_countable _).aemeasurable (measurable_of_countable _).aemeasurable]
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

namespace KernelLearner
end KernelLearner

namespace SeededLearner
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

end SubsphereCurrent
end
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

omit [FiniteDimensional ℝ E] [BorelSpace E] [MeasurableSingletonClass J] in
lemma stepDet_measurable (L : Stream E J T) (s : E) (x : Fin T → E) (n : ℕ) (q : J) :
    Measurable (L.stepDet s x n q) :=
  measurable_samplePMF (fun _ => measurable_const) measurable_id

omit [FiniteDimensional ℝ E] [BorelSpace E] in
lemma stepDet_map (L : Stream E J T) (s : E) (x : Fin T → E) (n : ℕ) (q : J) :
    coinLaw.map (L.stepDet s x n q) = (L.stepPMF s x n q).toMeasure := samplePMF_map _

omit [FiniteDimensional ℝ E] [BorelSpace E] [MeasurableSpace J] [Fintype J]
  [MeasurableSingletonClass J] [Nonempty J] in
lemma run_eq_bind_chain (L : Stream E J T) (s : E) (x : Fin T → E) (n : ℕ) :
    L.run s x n = L.initial.bind (fun q => lawChain (L.stepPMF s x) q n) := by
  induction n with
  | zero => simp [run, lawChain]
  | succ n ih =>
    change (L.run s x n).bind (L.stepPMF s x n) = _
    rw [ih, PMF.bind_bind]
    rfl

lemma measurable_detChain_param (L : Stream E J T) (hL : L.BorelRules)
    {X : Type*} [MeasurableSpace X]
    {s : X → E} {x : X → Fin T → E} {q : X → J}
    (hs : Measurable s) (hx : Measurable x) (hq : Measurable q) (n : ℕ)
    {r : X → Fin n → ℝ} (hr : Measurable r) :
    Measurable (fun z => detChain (L.stepDet (s z) (x z)) (q z) n (r z)) := by
  induction n with
  | zero => exact hq
  | succ n ih =>
    have hp : Measurable (fun z => detChain (L.stepDet (s z) (x z)) (q z) n (Fin.init (r z))) :=
      ih (by fun_prop)
    have hstep (a : J) : Measurable (fun z => L.stepDet (s z) (x z) n a (r z (Fin.last n))) := by
      unfold stepDet stepPMF
      split_ifs with hn
      · exact measurable_samplePMF (fun b => (hL (n+1) a b).comp
          (by fun_prop)) (by fun_prop)
      · exact measurable_samplePMF (fun _ => measurable_const) (by fun_prop)
    exact SubsphereRegression.measurable_select hstep hp

lemma measurable_tapeEstimate (L : Stream E J T) (hL : L.BorelRules)
    {X : Type*} [MeasurableSpace X]
    {s : X → E} {ω : X → Tape E J T} {x : X → Fin T → E}
    (hs : Measurable s) (hω : Measurable ω) (hx : Measurable x) :
    Measurable (fun z => L.tapeEstimate (s z) (ω z) (x z)) := by
  unfold tapeEstimate
  exact SubsphereRegression.measurable_select (h := fun a z => (ω z).2.2 a) (fun a => by fun_prop)
    (L.measurable_detChain_param hL hs hx (measurable_fst.comp hω) T
      (measurable_fst.comp (measurable_snd.comp hω)))

lemma lintegral_tapeEstimate (L : Stream E J T) (hL : L.BorelRules)
    (s : E) (x : Fin T → E) (f : E → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ ω, f (L.tapeEstimate s ω x) ∂L.tapeLaw) = ∫⁻ u, f u ∂L.estimateLaw s x := by
  let : ∀ q, IsProbabilityMeasure (L.output q) := L.output_probability
  have hE : Measurable (fun ω => f (L.tapeEstimate s ω x)) :=
    hf.comp (L.measurable_tapeEstimate hL measurable_const measurable_id measurable_const)
  rw [tapeLaw, lintegral_prod _ hE.aemeasurable]
  calc
    _ = ∫⁻ q, ∫⁻ r : Fin T → ℝ, ∫⁻ u, f u
        ∂L.output (detChain (L.stepDet s x) q T r)
        ∂Measure.pi (fun _ => coinLaw) ∂L.initial.toMeasure := by
      apply lintegral_congr
      intro q
      rw [lintegral_prod (fun y : (Fin T → ℝ) × (J → E) => f (L.tapeEstimate s (q,y) x))
        (hE.comp (measurable_const.prodMk measurable_id)).aemeasurable]
      apply lintegral_congr
      intro r
      exact (measurePreserving_eval L.output (detChain (L.stepDet s x) q T r)).lintegral_comp hf
    _ = ∫⁻ q, ∫⁻ a, ∫⁻ u, f u ∂L.output a
        ∂(lawChain (L.stepPMF s x) q T).toMeasure ∂L.initial.toMeasure := by
      apply lintegral_congr
      intro q
      exact detChain_lintegral (L.stepDet_measurable s x) (L.stepDet_map s x) q T (fun a => ∫⁻ u, f u ∂L.output a)
    _ = ∫⁻ a, ∫⁻ u, f u ∂L.output a ∂(L.run s x T).toMeasure := by
      rw [run_eq_bind_chain, pmf_lintegral_bind]
    _ = _ := by
      rw [estimateLaw, Measure.lintegral_bind (measurable_of_countable _).aemeasurable hf.aemeasurable]

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

end SubsphereCurrent.Weighted
end
end

end OAI

-- ---- platform node ----
open OAI OAI.SubsphereCurrent OAI.SubsphereCurrent.Fixed OAI.SubsphereCurrent.Fixed.Stream
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace


theorem solution : type_of% @_root_.OAI.SubsphereCurrent.Fixed.Stream.lintegral_tapeEstimate := @_root_.OAI.SubsphereCurrent.Fixed.Stream.lintegral_tapeEstimate
