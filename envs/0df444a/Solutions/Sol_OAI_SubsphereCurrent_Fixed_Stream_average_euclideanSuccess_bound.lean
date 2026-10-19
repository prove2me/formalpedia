-- Prove2me | solution 1 for OAI.SubsphereCurrent.Fixed.Stream.average_euclideanSuccess_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T09:09:44.360761+00:00
-- url     : https://prove2.me/submissions/dd15d0af-a1b9-414e-96fb-0d47ac081b4a

-- Generated from openai/math@1581d4c lean/OAI/Probability/Subsphere/Geometry/Affine.lean:L237-L274
-- (upload_full_project.md Phase 4): solution for node OAI.SubsphereCurrent.Fixed.Stream.average_euclideanSuccess_bound. The node keeps its source
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
import Theorems.Thm_OAI_SubsphereCurrent_Fixed_Stream_lintegral_tapeEstimate
import Theorems.Thm_OAI_SubsphereCurrent_measurable_finiteSample
import Theorems.Thm_OAI_SubsphereRegression_route_cap_bound

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

lemma fin_tail_snoc {X : Type*} {k : ℕ} (A : Fin (k+1) → X) (x : X) :
    Fin.tail (Fin.snoc A x : Fin (k+2) → X) =
      (Fin.snoc (Fin.tail A : Fin k → X) x : Fin (k+1) → X) := by
  rw [← Fin.cons_self_tail A, ← Fin.cons_snoc_eq_snoc_cons, Fin.tail_cons, Fin.tail_cons]

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [Fintype J] [MeasurableSpace J] [MeasurableSingletonClass J] in
lemma streamRoute_snoc (δ : ℕ → J → (E × ℝ) → J) (n k : ℕ) (j : J)
    (A : Fin k → E) (b : Fin k → ℝ) (x : E) (y : ℝ) :
    streamRoute δ n (k+1) j (Fin.snoc A x, Fin.snoc b y) =
      δ (n+k+1) (streamRoute δ n k j (A,b)) (x,y) := by
  induction k generalizing n j with
  | zero => simp [streamRoute, Fin.snoc_zero]
  | succ k ih =>
    rw [streamRoute]
    simp only [Fin.snoc_apply_zero, fin_tail_snoc]
    rw [ih, streamRoute]
    congr 1; omega

end StreamAux

lemma fin_prefix_snoc {X : Type*} {n T : ℕ} (h : n+1 ≤ T) (x : Fin T → X) :
    (fun i : Fin (n+1) => x (Fin.castLE h i)) =
      (Fin.snoc (fun i : Fin n => x (Fin.castLE (by omega) i))
        (x ⟨n, by omega⟩) : Fin (n+1) → X) := by
  ext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [Fin.snoc_last]
    rfl
  · simp

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

omit [MeasurableSpace A] [Countable A] [MeasurableSingletonClass A] in
lemma detChain_snoc (F : ℕ → A → ℝ → A) (a : A) (n : ℕ)
    (r : Fin n → ℝ) (u : ℝ) :
    detChain F a (n+1) (Fin.snoc r u) = F n (detChain F a n r) u := by
  simp [detChain]

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

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [BorelSpace E] [MeasurableSingletonClass J] in
lemma tapeTransition_measurable (L : Stream E J T) (hL : L.BorelRules)
    (ω : Tape E J T) (n : ℕ) (q : J) : Measurable (L.tapeTransition ω n q) :=
  measurable_samplePMF (hL n q) measurable_const

omit [FiniteDimensional ℝ E] [BorelSpace E] [MeasurableSpace J] [MeasurableSingletonClass J] in
lemma streamRoute_eq_detChain (L : Stream E J T) (s : E) (ω : Tape E J T)
    (x : Fin T → E) {n : ℕ} (hn : n ≤ T) :
    SubsphereRegression.streamRoute (L.tapeTransition ω) 0 n ω.1
      ((fun i => x (Fin.castLE hn i)), fun i => ⟪s,x (Fin.castLE hn i)⟫) =
      detChain (L.stepDet s x) ω.1 n (fun i => ω.2.1 (Fin.castLE hn i)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [SubsphereRegression.fin_prefix_snoc hn x,
      SubsphereRegression.fin_prefix_snoc hn (fun i => ⟪s,x i⟫),
      SubsphereRegression.streamRoute_snoc, ih (by omega),
      SubsphereRegression.fin_prefix_snoc hn ω.2.1, detChain_snoc]
    simp [tapeTransition, stepDet, stepPMF, show n < T by omega, real_inner_comm]

omit [FiniteDimensional ℝ E] [BorelSpace E] [MeasurableSpace J] [MeasurableSingletonClass J] in
lemma tapeEstimate_eq_route (L : Stream E J T) (s : E) (ω : Tape E J T) (x : Fin T → E) :
    L.tapeEstimate s ω x = ω.2.2
      (SubsphereRegression.streamRoute (L.tapeTransition ω) 0 T ω.1 (x,fun i => ⟪s,x i⟫)) := by
  simpa [tapeEstimate] using congrArg ω.2.2 (L.streamRoute_eq_detChain s ω x le_rfl).symm

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

lemma measurable_euclideanTest {X : Type*} [MeasurableSpace X]
    {s y : X → E} (hs : Measurable s) (hy : Measurable y) (η : ℝ) :
    Measurable (fun x => euclideanTest η (s x) (y x)) := by
  simpa only [euclideanTest,Set.indicator_apply,Set.mem_ofPred_eq] using
    (Measurable.ite (measurableSet_le ((hy.sub hs).norm) measurable_const)
      measurable_const measurable_const :
      Measurable (fun x => if ‖y x-s x‖ ≤ η then (1 : ℝ≥0∞) else 0))

namespace Stream
variable {J : Type*} [MeasurableSpace J] [Fintype J] [MeasurableSingletonClass J] [Nonempty J]
  {T : ℕ}

lemma euclideanSuccess_eq_integral_tape (L : Stream E J T) (hL : L.BorelRules)
    (η : ℝ) (s : E) (x : Fin T → E) :
    L.euclideanSuccess η s x = ∫⁻ ω, euclideanTest η s (L.tapeEstimate s ω x) ∂L.tapeLaw := by
  rw [L.lintegral_tapeEstimate hL s x (euclideanTest η s)
    (measurable_euclideanTest measurable_const measurable_id η)]
  have hS : MeasurableSet {y : E | ‖y-s‖ ≤ η} :=
    measurableSet_le (by fun_prop) measurable_const
  simp only [euclideanTest,euclideanSuccess,lintegral_indicator_const hS,one_mul]

lemma average_euclideanSuccess_bound [Nontrivial E] (L : Stream E J T) (hL : L.BorelRules)
    {η : ℝ} (hη : 0 < η) {a q : ℕ}
    (ha : 2*a ≤ Module.finrank ℝ E-1) (hq : 2 ≤ q) (hqa : 2*q ≤ a) :
    (∫⁻ z : Sphere E × (Fin T → E), L.euclideanSuccess η z.1.val z.2
      ∂(sphereLaw E).prod (rowsLaw E T)) ≤
      (ENNReal.ofReal ((3 : ℝ)*4^Module.finrank ℝ E) * ENNReal.ofReal (η^a)) *
        SubsphereRegression.streamFactor (E := E) (J := J) q ^ (T/q+1) := by
  simp_rw [L.euclideanSuccess_eq_integral_tape hL η]
  have hm : Measurable (fun z : (Sphere E × (Fin T → E)) × Tape E J T =>
      euclideanTest η z.1.1.val (L.tapeEstimate z.1.1.val z.2 z.1.2)) :=
    measurable_euclideanTest (measurable_subtype_coe.comp (measurable_fst.comp measurable_fst))
      (L.measurable_tapeEstimate hL
        (measurable_subtype_coe.comp (measurable_fst.comp measurable_fst)) measurable_snd
        (measurable_snd.comp measurable_fst)) η
  rw [lintegral_lintegral_swap hm.aemeasurable]
  calc
    _ ≤ ∫⁻ _ : Tape E J T,
        (ENNReal.ofReal ((3 : ℝ)*4^Module.finrank ℝ E) * ENNReal.ofReal (η^a)) *
          SubsphereRegression.streamFactor (E := E) (J := J) q ^ (T/q+1) ∂L.tapeLaw := by
      apply lintegral_mono
      intro ω
      have hb := SubsphereRegression.route_cap_bound (L.tapeTransition_measurable hL ω)
        ω.2.2 hη ha hq hqa T ω.1
      have hS : MeasurableSet {z : Sphere E × (Fin T → E) |
          dist z.1.val (L.tapeEstimate z.1.val ω z.2) ≤ η} :=
        measurableSet_le ((measurable_subtype_coe.comp measurable_fst).dist
          (L.measurable_tapeEstimate hL (measurable_subtype_coe.comp measurable_fst) measurable_const measurable_snd))
          measurable_const
      have he : (fun z : Sphere E × (Fin T → E) => euclideanTest η z.1.val
          (L.tapeEstimate z.1.val ω z.2)) =
          {z : Sphere E × (Fin T → E) |
            dist z.1.val (L.tapeEstimate z.1.val ω z.2) ≤ η}.indicator (fun _ => 1) := by
        funext z
        simp [euclideanTest,Set.indicator_apply,dist_eq_norm,norm_sub_rev]
      dsimp only
      rw [he,lintegral_indicator_const hS,one_mul]
      simpa only [L.tapeEstimate_eq_route, sphereLaw,rowsLaw,SubsphereRegression.sphereLaw] using hb
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


theorem solution : type_of% @_root_.OAI.SubsphereCurrent.Fixed.Stream.average_euclideanSuccess_bound := @_root_.OAI.SubsphereCurrent.Fixed.Stream.average_euclideanSuccess_bound
