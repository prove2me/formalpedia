-- Prove2me | solution 1 for OAI.SubsphereCurrent.Weighted.block_reconstruct
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T09:16:00.760354+00:00
-- url     : https://prove2.me/submissions/7e5b142c-74f7-4a85-891e-182be1039a11

-- Generated from openai/math@1581d4c lean/OAI/Probability/Subsphere/Geometry/Affine.lean:L639-L710
-- (upload_full_project.md Phase 4): solution for node OAI.SubsphereCurrent.Weighted.block_reconstruct. The node keeps its source
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
variable [Fintype A] [Nonempty A]

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

-- ---- from OAI.Probability.Subsphere.Geometry.Integration ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
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

section Ambient
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E]

end Ambient

variable {V : Type*} [Fintype V] [Nonempty V]

end
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E]
variable {V : Type*} [Fintype V] [Nonempty V] [MeasurableSpace V] [MeasurableSingletonClass V]

end SubsphereCurrent.Weighted

end

end OAI

-- ---- from OAI.Probability.Subsphere.Geometry.Affine ----
-- Lean 4.33 compatibility: Measurable.of_eval is the renamed measurable_pi_lambda
-- (Mathlib/MeasureTheory/MeasurableSpace/Constructions.lean at d13f23b records the alias).
section Lean433MeasurableOfEval
private theorem Measurable.of_eval {α δ : Type*} {X : δ → Type*}
    [MeasurableSpace α] [∀ a, MeasurableSpace (X a)] {f : α → ∀ a, X a}
    (hf : ∀ a, Measurable fun c => f c a) : Measurable f :=
  measurable_pi_lambda f hf
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

lemma stdGaussian_prod_map {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    [MeasurableSpace F] [BorelSpace F] :
    ((stdGaussian E).prod (stdGaussian F)).map (WithLp.toLp 2) =
      stdGaussian (WithLp 2 (E × F)) := by
  apply Measure.ext_of_charFun
  funext t
  rw [charFun_prod,charFun_stdGaussian,charFun_stdGaussian,charFun_stdGaussian,
    ← Complex.exp_add, ← Complex.ofReal_pow, ← Complex.ofReal_pow, ← Complex.ofReal_pow,
    WithLp.prod_norm_sq_eq_of_L2]
  congr 1
  push_cast
  change -(↑‖t.fst‖ : ℂ)^2 / 2 + -↑‖t.snd‖^2 / 2 = _
  ring

lemma gaussian_orthogonal_sum {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (H : Submodule ℝ E) :
    MeasurePreserving (fun z : H × Hᗮ => (z.1 : E) + (z.2 : E))
      ((stdGaussian H).prod (stdGaussian Hᗮ)) (stdGaussian E) := by
  have hmap := stdGaussian_map H.orthogonalDecomposition.symm
  rw [← stdGaussian_prod_map,Measure.map_map (by fun_prop) (by fun_prop)] at hmap
  refine ⟨by fun_prop,?_⟩
  convert hmap using 1
  congr 1

lemma gaussian_orthogonal_rows {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (H : Submodule ℝ E) (T : ℕ) :
    MeasurePreserving (fun z : (Fin T → H) × (Fin T → Hᗮ) =>
      fun i => (z.1 i : E) + (z.2 i : E))
      ((Measure.pi (fun _ => stdGaussian H)).prod (Measure.pi (fun _ => stdGaussian Hᗮ)))
      (Measure.pi (fun _ : Fin T => stdGaussian E)) := by
  have h1 := (measurePreserving_arrowProdEquivProdArrow H Hᗮ (Fin T)
    (fun _ => stdGaussian H) (fun _ => stdGaussian Hᗮ)).symm
  exact (measurePreserving_pi (fun _ : Fin T => (stdGaussian H).prod (stdGaussian Hᗮ))
    (fun _ => stdGaussian E) (fun _ => gaussian_orthogonal_sum H)).comp h1

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

lemma measurable_point : Measurable A.point := by unfold point; fun_prop

lemma observation_identity (s : Sphere A.space) (x : A.space) (w : A.spaceᗮ) :
    ⟪(x : Vector d)+(w : Vector d),A.point s⟫ =
      ⟪(x : Vector d)+(w : Vector d),A.center⟫ + A.radius * ⟪x,s.val⟫ := by
  simp only [point,inner_add_right,real_inner_smul_right,inner_add_left]
  rw [Submodule.inner_left_of_mem_orthogonal s.val.property w.property]
  simp only [mul_zero,add_zero]
  rfl

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

lemma reconstruct_preserving :
    MeasurePreserving
      (fun z : (Fin T → A.spaceᗮ) × (Sphere A.space × (Fin T → A.space)) =>
        (z.2.1,fun i => (z.2.2 i : Vector d)+(z.1 i : Vector d)))
      ((Fixed.rowsLaw A.spaceᗮ T).prod ((sphereLaw A.space).prod (Fixed.rowsLaw A.space T)))
      ((sphereLaw A.space).prod (Fixed.rowsLaw (Vector d) T)) := by
  have h1 : MeasurePreserving
      (fun z : (Fin T → A.spaceᗮ) × (Fin T → A.space) =>
        fun i => (z.2 i : Vector d)+(z.1 i : Vector d))
      ((Fixed.rowsLaw A.spaceᗮ T).prod (Fixed.rowsLaw A.space T))
      (Fixed.rowsLaw (Vector d) T) :=
    (gaussian_orthogonal_rows A.space T).comp
      (Measure.measurePreserving_swap (μ := Fixed.rowsLaw A.spaceᗮ T) (ν := Fixed.rowsLaw A.space T))
  exact ((MeasurePreserving.id (sphereLaw A.space)).prod h1).comp
    (measurePreserving_swapFirstTwo (Fixed.rowsLaw A.spaceᗮ T) (sphereLaw A.space)
      (Fixed.rowsLaw A.space T))

lemma integral_reconstruct (f : Sphere A.space × (Fin T → Vector d) → ℝ≥0∞)
    (hf : Measurable f) :
    (∫⁻ z, f z ∂(sphereLaw A.space).prod (Fixed.rowsLaw (Vector d) T)) =
      ∫⁻ w : Fin T → A.spaceᗮ, ∫⁻ z : Sphere A.space × (Fin T → A.space),
        f (z.1,fun i => (z.2 i : Vector d)+(w i : Vector d))
          ∂(sphereLaw A.space).prod (Fixed.rowsLaw A.space T)
        ∂Fixed.rowsLaw A.spaceᗮ T := by
  have hp := reconstruct_preserving (T := T) A
  rw [← hp.lintegral_comp hf]
  exact lintegral_prod _ (hf.comp hp.measurable).aemeasurable

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

lemma block_reconstruct (κ : V → Observation d m → ℝ≥0∞) (hκ : ∀ v, Measurable (κ v))
    (g : V → Sphere d → ℝ≥0∞) (hg : ∀ v, Measurable (g v)) :
    (ENNReal.ofReal A.radius)^((d : ℝ)/16) *
      (∫⁻ s, blockInput κ g (onTest A s) ∂Affine.sphereLaw A.space) =
    ∫⁻ w : Fin m → A.spaceᗮ,
      (∑ v, ∫⁻ s : Affine.Sphere A.space, weightedOnTest A (g v) s *
        (∫⁻ X : Fin m → A.space, κ v (pullObservation A w (X,fun i => ⟪s.val,X i⟫))
          ∂Measure.pi (fun _ => stdGaussian A.space)) ∂Affine.sphereLaw A.space)
      ∂Measure.pi (fun _ => stdGaussian A.spaceᗮ) := by
  classical
  let f (z : Affine.Sphere A.space × (Fin m → Vector d)) :=
    ∑ v, κ v (z.2,fun i => ⟪z.2 i,A.point z.1⟫)*g v (onTest A z.1)
  have hf : Measurable f := by
    apply Finset.measurable_sum
    intro v _
    exact ((hκ v).comp (measurable_snd.prodMk (Measurable.of_eval (fun index =>
      ((measurable_pi_apply index).comp measurable_snd).inner (A.measurable_point.comp measurable_fst))))).mul
      ((hg v).comp ((borel_onTest A).comp measurable_fst))
  have he : (∫⁻ s, blockInput κ g (onTest A s) ∂Affine.sphereLaw A.space) =
      ∫⁻ z, f z ∂(Affine.sphereLaw A.space).prod (Fixed.rowsLaw (Vector d) m) :=
    (lintegral_prod _ hf.aemeasurable).symm
  rw [he,Affine.Simulation.integral_reconstruct A f hf]
  rw [← lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg (by positivity) ENNReal.ofReal_ne_top)]
  apply lintegral_congr
  intro w
  have hr : Measurable (fun z : Affine.Sphere A.space × (Fin m → A.space) =>
      f (z.1,fun i => (z.2 i : Vector d)+(w i : Vector d))) := by
    apply hf.comp
    fun_prop
  rw [lintegral_prod _ hr.aemeasurable,
    ← lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg (by positivity) ENNReal.ofReal_ne_top)]
  have hmeas (v : V) : Measurable (fun s : Affine.Sphere A.space =>
      weightedOnTest A (g v) s *
        ∫⁻ X : Fin m → A.space, κ v (pullObservation A w (X,fun i => ⟪s.val,X i⟫))
          ∂Measure.pi (fun _ => stdGaussian A.space)) := by
    apply (measurable_weightedOnTest A (hg v)).mul
    apply Measurable.lintegral_prod_right
    apply (hκ v).comp
    apply (measurable_pullObservation A w).comp
    fun_prop
  rw [← lintegral_finsetSum _ (fun v _ => hmeas v)]
  apply lintegral_congr
  intro s
  have hm (v : V) : Measurable (fun X : Fin m → A.space =>
      κ v ((fun i => (X i : Vector d)+(w i : Vector d)),
        fun i => ⟪(X i : Vector d)+(w i : Vector d),A.point s⟫)*g v (onTest A s)) := by
    apply Measurable.mul _ measurable_const
    apply (hκ v).comp
    fun_prop
  change (ENNReal.ofReal A.radius)^((d : ℝ)/16) *
    (∫⁻ X, ∑ v, κ v ((fun i => (X i : Vector d)+(w i : Vector d)),
      fun i => ⟪(X i : Vector d)+(w i : Vector d),A.point s⟫)*g v (onTest A s)
        ∂Measure.pi (fun _ => stdGaussian A.space)) = _
  rw [lintegral_finsetSum _ (fun v _ => hm v),Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v _
  have hroute : (fun X : Fin m → A.space => κ v ((fun i => (X i : Vector d)+(w i : Vector d)),
      fun i => ⟪(X i : Vector d)+(w i : Vector d),A.point s⟫)) =
    fun X => κ v (pullObservation A w (X,fun i => ⟪s.val,X i⟫)) := by
    funext X
    congr 2
    funext i
    rw [A.observation_identity]
    simp only [real_inner_comm]
  have hmroute : Measurable (fun X : Fin m → A.space => κ v
      ((fun i => (X i : Vector d)+(w i : Vector d)),
        fun i => ⟪(X i : Vector d)+(w i : Vector d),A.point s⟫)) := by
    apply (hκ v).comp
    fun_prop
  rw [lintegral_mul_const _ hmroute,hroute]
  simp only [weightedOnTest]
  ac_rfl

end SubsphereCurrent.Weighted
end
end

end OAI

-- ---- platform node ----
open OAI OAI.SubsphereCurrent OAI.SubsphereCurrent.Weighted
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace


theorem solution : type_of% @_root_.OAI.SubsphereCurrent.Weighted.block_reconstruct := @_root_.OAI.SubsphereCurrent.Weighted.block_reconstruct
