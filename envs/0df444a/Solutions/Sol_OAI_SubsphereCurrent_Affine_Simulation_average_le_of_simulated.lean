-- Prove2me | solution 1 for OAI.SubsphereCurrent.Affine.Simulation.average_le_of_simulated
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T09:13:45.576515+00:00
-- url     : https://prove2.me/submissions/def71cb0-a6c2-4ede-b0a8-6ae6da13dfd7

-- Generated from openai/math@1581d4c lean/OAI/Probability/Subsphere/Geometry/Affine.lean:L594-L615
-- (upload_full_project.md Phase 4): solution for node OAI.SubsphereCurrent.Affine.Simulation.average_le_of_simulated. The node keeps its source
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

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma chord_le_arccos (s t : Metric.sphere (0 : E) 1) :
    dist s.val t.val ≤ Real.arccos ⟪s.val,t.val⟫ := by
  have hs : ‖s.val‖ = 1 := mem_sphere_zero_iff_norm.mp s.property
  have ht : ‖t.val‖ = 1 := mem_sphere_zero_iff_norm.mp t.property
  have habs : |⟪s.val,t.val⟫| ≤ 1 := by
    simpa [hs, ht] using abs_real_inner_le_norm s.val t.val
  have hcos := Real.one_sub_sq_div_two_le_cos (x := Real.arccos ⟪s.val,t.val⟫)
  rw [Real.cos_arccos (abs_le.mp habs).1 (abs_le.mp habs).2] at hcos
  have hd : (dist s.val t.val)^2 = 2 - 2*⟪s.val,t.val⟫ := by
    rw [dist_eq_norm, norm_sub_sq_real, hs, ht]
    ring
  nlinarith [dist_nonneg (x := s.val) (y := t.val), Real.arccos_nonneg ⟪s.val,t.val⟫]

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

lemma norm_point (s : Sphere A.space) : ‖A.point s‖ = 1 := by
  have hs : ‖(s.val : Vector d)‖ = 1 := by
    rw [Submodule.norm_coe]
    exact mem_sphere_zero_iff_norm.mp s.property
  have ho : ⟪A.center, (s.val : Vector d)⟫ = 0 :=
    Submodule.inner_left_of_mem_orthogonal s.val.property A.perpendicular
  have hz : ‖A.point s‖^2 = 1 := by
    rw [point,norm_add_sq_real,real_inner_smul_right,ho,mul_zero,norm_smul,
      Real.norm_eq_abs,abs_of_pos A.radius_positive,hs,mul_one]
    nlinarith [A.unit]
  nlinarith [norm_nonneg (A.point s)]

lemma project_point (s : Sphere A.space) : A.project (A.point s) = s.val := by
  simp [project,point,map_smul,Submodule.orthogonalProjectionOnto_mem_subspace_eq_self,
    smul_smul,A.radius_positive.ne']

lemma project_error (s : Sphere A.space) (y : Vector d) :
    ‖A.project y-s.val‖ ≤ ‖y-A.point s‖/A.radius := by
  rw [← A.project_point s]
  have he : A.project y - A.project (A.point s) =
      A.radius⁻¹ • A.space.orthogonalProjectionOnto (y-A.point s) := by
    simp only [project,← smul_sub,← map_sub]
    congr 2
    abel
  rw [he,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr A.radius_positive),div_eq_mul_inv]
  exact (mul_le_mul_of_nonneg_left (A.space.norm_orthogonalProjectionOnto_apply_le _) (inv_nonneg.mpr A.radius_positive.le)).trans_eq (mul_comm _ _)

lemma angular_project_error {ε : ℝ} (s : Sphere A.space) (y : Vector d)
    (hy : ‖y‖ = 1) (h : Real.arccos ⟪y,A.point s⟫ ≤ ε) :
    ‖A.project y-s.val‖ ≤ ε/A.radius := by
  apply (A.project_error s y).trans
  apply div_le_div_of_nonneg_right _ A.radius_positive.le
  have hc : ‖y-A.point s‖ ≤ Real.arccos ⟪y,A.point s⟫ := by
    simpa only [dist_eq_norm] using (SubsphereRegression.chord_le_arccos
      (⟨y,mem_sphere_zero_iff_norm.mpr hy⟩ : Sphere (Vector d))
      ⟨A.point s,mem_sphere_zero_iff_norm.mpr (A.norm_point s)⟩)
  exact hc.trans h

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

omit [Fintype J] [Nonempty J] [MeasurableSpace J] [MeasurableSingletonClass J] in
lemma run_eq (w : Fin T → A.spaceᗮ) (s : Sphere A.space) (x : Fin T → A.space) (l : ℕ) :
    (stream A L w).run s.val x l =
      L.run (A.point s) (fun i => (x i : Vector d)+(w i : Vector d)) l := by
  induction l with
  | zero => rfl
  | succ l ih =>
    simp only [Fixed.Stream.run,ih]
    congr 1
    funext q
    split_ifs with hl
    · change L.transition (l+1) q _ = L.transition (l+1) q _
      congr 1
      simp [A.observation_identity s (x ⟨l,hl⟩) (w ⟨l,hl⟩),hl]
    · rfl

omit [Nonempty J] in
lemma success_le (w : Fin T → A.spaceᗮ) (s : Sphere A.space) (x : Fin T → A.space)
    (hu : ∀ q, ∀ᵐ y ∂L.output q, ‖y‖ = 1) (ε : ℝ) :
    L.angularSuccess ε (A.point s) (fun i => (x i : Vector d)+(w i : Vector d)) ≤
      (stream A L w).euclideanSuccess (ε/A.radius) s.val x := by
  have hA : MeasurableSet {y : Vector d | Real.arccos ⟪y,A.point s⟫ ≤ ε} :=
    measurableSet_le (by fun_prop) measurable_const
  have hB : MeasurableSet {y : A.space | ‖y-s.val‖ ≤ ε/A.radius} :=
    measurableSet_le (by fun_prop) measurable_const
  unfold Fixed.Stream.angularSuccess Fixed.Stream.euclideanSuccess Fixed.Stream.estimateLaw
  rw [Measure.bind_apply hA (measurable_of_countable _).aemeasurable,
    Measure.bind_apply hB (measurable_of_countable _).aemeasurable,run_eq]
  apply lintegral_mono
  intro q
  change L.output q _ ≤ (L.output q).map A.project _
  rw [Measure.map_apply A.measurable_project hB]
  apply measure_mono_ae
  filter_upwards [hu q] with y hy
  exact fun h => A.angular_project_error s y hy h

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

lemma measurable_angularTest {X : Type*} [MeasurableSpace X]
    {s y : X → E} (hs : Measurable s) (hy : Measurable y) (ε : ℝ) :
    Measurable (fun x => angularTest ε (s x) (y x)) := by
  have he := Real.continuous_arccos.measurable.comp (hy.inner hs)
  simpa only [angularTest,Set.indicator_apply,Set.mem_ofPred_eq] using
    (Measurable.ite (measurableSet_le he measurable_const) measurable_const measurable_const :
      Measurable (fun x => if Real.arccos ⟪y x,s x⟫ ≤ ε then (1 : ℝ≥0∞) else 0))

namespace Stream
variable {J : Type*} [Fintype J] [Nonempty J] [MeasurableSpace J] [MeasurableSingletonClass J]
  {T : ℕ}
lemma angularSuccess_eq_integral_tape (L : Stream E J T) (hL : L.BorelRules)
    (ε : ℝ) (s : E) (x : Fin T → E) :
    L.angularSuccess ε s x = ∫⁻ ω, angularTest ε s (L.tapeEstimate s ω x) ∂L.tapeLaw := by
  rw [L.lintegral_tapeEstimate hL s x (angularTest ε s)
    (measurable_angularTest measurable_const measurable_id ε)]
  have hS : MeasurableSet {y : E | Real.arccos ⟪y,s⟫ ≤ ε} :=
    measurableSet_le (by fun_prop) measurable_const
  simp only [angularTest,angularSuccess,lintegral_indicator_const hS,one_mul]

lemma measurable_angularSuccess (L : Stream E J T) (hL : L.BorelRules) (ε : ℝ) :
    Measurable (fun z : E × (Fin T → E) => L.angularSuccess ε z.1 z.2) := by
  simp_rw [L.angularSuccess_eq_integral_tape hL ε]
  exact (measurable_angularTest (measurable_fst.comp measurable_fst)
    (L.measurable_tapeEstimate hL (measurable_fst.comp measurable_fst)
      measurable_snd (measurable_snd.comp measurable_fst)) ε).lintegral_prod_right

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

omit [Nontrivial A.space] in
lemma measurable_angular_onTest (hL : L.BorelRules) (ε : ℝ) :
    Measurable (fun z : Sphere A.space × (Fin T → Vector d) =>
      L.angularSuccess ε (A.point z.1) z.2) := by
  have hm0 : Measurable (fun z : Vector d × (Fin T → Vector d) => L.angularSuccess ε z.1 z.2) :=
    L.measurable_angularSuccess hL ε
  have harg : Measurable (fun z : Sphere A.space × (Fin T → Vector d) => (A.point z.1,z.2)) :=
    (A.measurable_point.comp measurable_fst).prodMk measurable_snd
  exact Measurable.comp
    (g := fun z : Vector d × (Fin T → Vector d) => L.angularSuccess ε z.1 z.2)
    (f := fun z : Sphere A.space × (Fin T → Vector d) => (A.point z.1,z.2)) hm0 harg

lemma average_le_of_simulated (hL : L.BorelRules)
    (hu : ∀ q, ∀ᵐ y ∂L.output q, ‖y‖ = 1) (ε : ℝ) (B : ℝ≥0∞)
    (hb : ∀ w : Fin T → A.spaceᗮ,
      (∫⁻ z : Sphere A.space × (Fin T → A.space),
        (stream A L w).euclideanSuccess (ε/A.radius) z.1.val z.2
          ∂(sphereLaw A.space).prod (Fixed.rowsLaw A.space T)) ≤ B) :
    (∫⁻ z : Sphere A.space × (Fin T → Vector d),
      L.angularSuccess ε (A.point z.1) z.2
        ∂(sphereLaw A.space).prod (Fixed.rowsLaw (Vector d) T)) ≤ B := by
  calc
    _ = ∫⁻ w : Fin T → A.spaceᗮ, ∫⁻ z : Sphere A.space × (Fin T → A.space),
        L.angularSuccess ε (A.point z.1) (fun i => (z.2 i : Vector d)+(w i : Vector d))
          ∂(sphereLaw A.space).prod (Fixed.rowsLaw A.space T)
        ∂Fixed.rowsLaw A.spaceᗮ T :=
      integral_reconstruct A _ (measurable_angular_onTest A L hL ε)
    _ ≤ ∫⁻ _ : Fin T → A.spaceᗮ, B ∂Fixed.rowsLaw A.spaceᗮ T := by
      apply lintegral_mono
      intro w
      apply (lintegral_mono ?_).trans (hb w)
      intro z
      exact success_le A L w z.1 z.2 hu ε
    _ = _ := by simp

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
open OAI OAI.SubsphereCurrent OAI.SubsphereCurrent.Affine OAI.SubsphereCurrent.Affine.Simulation
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
attribute [local instance] OAI.SubsphereCurrent.Affine.Simulation.affineSimulationSphereLaw_probability


theorem solution : type_of% @_root_.OAI.SubsphereCurrent.Affine.Simulation.average_le_of_simulated := @_root_.OAI.SubsphereCurrent.Affine.Simulation.average_le_of_simulated
