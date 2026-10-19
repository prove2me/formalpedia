-- Prove2me | solution 1 for OAI.NoiselessRegression.route_mixed_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T20:38:52.819252+00:00
-- url     : https://prove2.me/submissions/d1de4992-84cb-4b3a-9628-e5de2b2eae72

-- Generated from openai/math@1581d4c lean/OAI/Probability/ProjectionMoments/StoppingKernel.lean:L72-L110
-- (upload_full_project.md Phase 4): solution for node OAI.NoiselessRegression.route_mixed_bound. The node keeps its source
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
import Theorems.Thm_OAI_NoiselessRegression_capWeight_mass_mixed
import Theorems.Thm_OAI_NoiselessRegression_continuation_mass_bound_ceil

-- ---- from OAI.Probability.GaussianRegression.Sphere ----
namespace OAI

/-!
Normalized spherical surface measure, cap bounds, and rotational symmetry.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
open InnerProductSpace

noncomputable section

universe u

namespace NoiselessRegression

section SphereBounds
open scoped Pointwise
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

end SphereBounds

open scoped Pointwise
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

end NoiselessRegression

end

end OAI

-- ---- from OAI.Probability.GaussianRegression.Stream ----
namespace OAI

/-!
Sequential routing and continuation mass propagation.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
open InnerProductSpace
open scoped Pointwise

noncomputable section

universe u

namespace NoiselessRegression

section StreamAux
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable {J : Type*} [Fintype J] [MeasurableSpace J] [MeasurableSingletonClass J]

lemma measurable_select {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {h : J → X → Y} (hh : ∀ j, Measurable (h j)) {φ : X → J} (hφ : Measurable φ) :
    Measurable (fun x => h (φ x) x) :=
  (measurable_from_prod_countable_right (f := fun p : J × X => h p.1 p.2) hh).comp (hφ.prodMk measurable_id)

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E] in
lemma lintegral_pi_cons (ν : Measure E) [SigmaFinite ν] {n : ℕ}
    (f : (Fin (n+1) → E) → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ v, f v ∂Measure.pi (fun _ => ν)) =
      ∫⁻ x, ∫⁻ v : Fin n → E, f (Fin.cons x v) ∂Measure.pi (fun _ => ν) ∂ν := by
  have hp := (measurePreserving_piFinSuccAbove (fun _ : Fin (n+1) => ν) (0 : Fin (n+1))).symm
  rw [← hp.lintegral_comp_emb (MeasurableEquiv.measurableEmbedding _) f, lintegral_prod]
  · congr 1
    ext x
    congr 1
    ext v
    congr 1
    simp only [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv]
    simp
  · exact (hf.comp hp.measurable).aemeasurable

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E] in
lemma measurable_streamRoute {δ : ℕ → J → (E × ℝ) → J}
    (hδ : ∀ n j, Measurable (δ n j)) (n k : ℕ) (j : J) :
    Measurable (streamRoute δ n k j) := by
  induction k generalizing n j with
  | zero => exact measurable_const
  | succ k ih =>
    change Measurable (fun x : (Fin (k+1) → E) × (Fin (k+1) → ℝ) => streamRoute δ (n+1) k (δ (n+1) j (x.1 0,x.2 0)) (Fin.tail x.1,Fin.tail x.2))
    have ht : Measurable (fun x : (Fin (k+1) → E) × (Fin (k+1) → ℝ) =>
        (Fin.tail x.1, Fin.tail x.2)) := by
      change Measurable (fun x : (Fin (k+1) → E) × (Fin (k+1) → ℝ) =>
        ((fun i : Fin k => x.1 i.succ), (fun i : Fin k => x.2 i.succ)))
      fun_prop
    have hd : Measurable (fun x : (Fin (k+1) → E) × (Fin (k+1) → ℝ) =>
        δ (n+1) j (x.1 0,x.2 0)) := (hδ (n+1) j).comp (by fun_prop)
    exact measurable_select (fun a => (ih (n+1) a).comp ht) hd

lemma measurable_continuation {δ : ℕ → J → (E × ℝ) → J} {w : ℕ → J → E → ℝ≥0∞}
    (hδ : ∀ n j, Measurable (δ n j)) (hw : ∀ n j, Measurable (w n j)) (n k : ℕ) (j : J) :
    Measurable (continuation δ w n k j) := by
  induction k generalizing n j with
  | zero => exact hw n j
  | succ k ih =>
    apply Measurable.lintegral_prod_left
    exact measurable_select (fun a => (ih (n+1) a).comp measurable_snd)
      ((hδ (n+1) j).comp (by fun_prop))

lemma continuation_unroll {δ : ℕ → J → (E × ℝ) → J} {w : ℕ → J → E → ℝ≥0∞}
    (hδ : ∀ n j, Measurable (δ n j))
    (n m k : ℕ) (j : J) (s : E) :
    continuation δ w n (m+k) j s =
      blockValue (fun a => continuation δ w (n+m) k a) (streamRoute δ n m j) s := by
  induction m generalizing n j with
  | zero =>
    simp [blockValue, streamRoute]
  | succ m ih =>
    rw [Nat.succ_add, continuation]
    simp_rw [ih]
    unfold blockValue
    have hf : Measurable (fun A : Fin (m+1) → E =>
        continuation δ w (n+(m+1)) k (streamRoute δ n (m+1) j (A,fun i => ⟪s,A i⟫)) s) := by
      exact (measurable_of_finite (fun a => continuation δ w (n+(m+1)) k a s)).comp
        ((measurable_streamRoute hδ n (m+1) j).comp (by fun_prop))
    rw [lintegral_pi_cons _ _ hf]
    apply lintegral_congr
    intro x
    apply lintegral_congr
    intro A
    have he : Fin.tail (fun i : Fin (m+1) => ⟪s,(Fin.cons x A : Fin (m+1) → E) i⟫) = (fun i => ⟪s,A i⟫) := by
      ext i
      simp [Fin.tail]
    simp [streamRoute, he, Nat.add_left_comm, Nat.add_comm]

end StreamAux

end NoiselessRegression

end

end OAI

-- ---- from OAI.Probability.GaussianRegression.Caps ----
namespace OAI

/-!
Spherical cap mass bounds along sequential routes.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
open InnerProductSpace
open scoped Pointwise

noncomputable section

universe u

namespace NoiselessRegression

section StreamCaps
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E]
variable {J : Type*} [Fintype J] [MeasurableSpace J] [MeasurableSingletonClass J] [Nonempty J]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [Nontrivial E] in
lemma measurable_capWeight (y : E) (ε : ℝ) : Measurable (capWeight y ε) :=
  measurable_const.indicator Metric.isClosed_closedBall.measurableSet

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E] in
lemma capWeight_le_one (y s : E) (ε : ℝ) : capWeight y ε s ≤ 1 := by
  classical
  simp only [capWeight, Set.indicator_apply]
  split <;> simp

lemma ambient_mass_bound {f : E → ℝ≥0∞} {a : ℕ} {C : ℝ≥0∞}
    (h : PolynomialMass ((ambientSphereLaw (E := E)).withDensity f) a C) :
    (∫⁻ s, f s ∂ambientSphereLaw) ≤ C := by
  rw [← setLIntegral_univ, ← withDensity_apply _ MeasurableSet.univ]
  apply (measure_mono_ae ?_).trans (by simpa using h 0 1 zero_lt_one)
  filter_upwards [(withDensity_absolutelyContinuous (ambientSphereLaw (E := E)) f).ae_le
    (ambientSphereLaw_ae_norm (E := E))] with s hs
  intro _
  change dist s 0 ≤ 1
  simp [dist_zero_right, hs]

end StreamCaps

end NoiselessRegression

end

end OAI

-- ---- from OAI.Probability.ProjectionMoments.StoppingKernel ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace
namespace NoiselessRegression

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E]

variable {J : Type*} [Fintype J] [MeasurableSpace J] [MeasurableSingletonClass J] [Nonempty J]

lemma continuation_mixed_integral_bound {δ : ℕ → J → (E × ℝ) → J}
    (hδ : ∀ n j, Measurable (δ n j)) (y : ℕ → J → E)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) {a q : ℕ} {b : ℝ}
    (hb : 0 ≤ b) (hab : (a:ℝ)+b ≤ (Module.finrank ℝ E-1:ℕ))
    (hq : 2 ≤ q) (hqa : 2*q ≤ a) (n k : ℕ) (j : J) :
    (∫⁻ s, continuation δ (fun n j => capWeight (y n j) ε) n k j s ∂ambientSphereLaw) ≤
      (ENNReal.ofReal ((3 : ℝ)*4^Module.finrank ℝ E) * ENNReal.ofReal (ε^b)) *
        streamFactor (E := E) (J := J) q ^ ((k+q-1)/q) := by
  have ha : a ≤ Module.finrank ℝ E := by
    have : (a:ℝ) ≤ (Module.finrank ℝ E:ℝ) := by
      have hh : ((Module.finrank ℝ E-1:ℕ):ℝ) ≤ Module.finrank ℝ E := by exact_mod_cast Nat.sub_le (Module.finrank ℝ E) 1
      linarith
    exact_mod_cast this
  apply ambient_mass_bound
  apply continuation_mass_bound_ceil _ hδ (fun n j => measurable_capWeight _ _)
    (fun n j s => capWeight_le_one _ _ _)
    (mul_ne_zero (by positivity) (by positivity)) (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)
    (fun n j => capWeight_mass_mixed (y n j) hε hε1 a hb hab)
    (Module.finrank_pos (R := ℝ) (M := E)) ha hq hqa

lemma route_mixed_bound {δ : ℕ → J → (E × ℝ) → J}
    (hδ : ∀ n j, Measurable (δ n j)) (y : J → E)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) {a q : ℕ} {b : ℝ}
    (hb : 0 ≤ b) (hab : (a:ℝ)+b ≤ (Module.finrank ℝ E-1:ℕ))
    (hq : 2 ≤ q) (hqa : 2*q ≤ a) (k : ℕ) (j : J) :
    ((sphereLaw (E := E)).prod (Measure.pi (fun _ : Fin k => stdGaussian E)))
      {z | dist z.1.val (y (streamRoute δ 0 k j (z.2,fun i => ⟪z.1.val,z.2 i⟫))) ≤ ε} ≤
      (ENNReal.ofReal ((3 : ℝ)*4^Module.finrank ℝ E) * ENNReal.ofReal (ε^b)) *
        streamFactor (E := E) (J := J) q ^ ((k+q-1)/q) := by
  let w : ℕ → J → E → ℝ≥0∞ := fun _ j => capWeight (y j) ε
  have hV := measurable_continuation (w := w) hδ (fun _ j => measurable_capWeight (y j) ε) 0 k j
  have he (s : E) : continuation δ w 0 k j s =
      ∫⁻ A : Fin k → E, capWeight (y (streamRoute δ 0 k j (A,fun i => ⟪s,A i⟫))) ε s
        ∂Measure.pi (fun _ => stdGaussian E) := by
    simpa [w, blockValue, continuation] using continuation_unroll (w := w) hδ 0 k 0 j s
  let S : Set ((Metric.sphere (0 : E) 1) × (Fin k → E)) :=
    {z | dist z.1.val (y (streamRoute δ 0 k j (z.2,fun i => ⟪z.1.val,z.2 i⟫))) ≤ ε}
  have hS : MeasurableSet S := by
    apply measurableSet_le _ measurable_const
    exact measurable_subtype_coe.comp measurable_fst |>.dist
      ((measurable_of_finite y).comp ((measurable_streamRoute hδ 0 k j).comp (by fun_prop)))
  change ((sphereLaw (E := E)).prod _) S ≤ _
  rw [← one_mul (((sphereLaw (E := E)).prod _) S), ← lintegral_indicator_const hS 1,
    lintegral_prod _ (measurable_const.indicator hS).aemeasurable]
  have hf : ∀ s : Metric.sphere (0 : E) 1,
      (∫⁻ A, S.indicator (fun _ => (1 : ℝ≥0∞)) (s,A) ∂Measure.pi (fun _ => stdGaussian E)) =
        continuation δ w 0 k j s.val := by
    intro s
    rw [he]
    apply lintegral_congr
    intro A
    classical
    change (if dist s.val (y (streamRoute δ 0 k j (A,fun i => ⟪s.val,A i⟫))) ≤ ε then 1 else 0) = _
    unfold capWeight
    rw [Set.indicator_apply]
    rfl
  simp_rw [hf]
  rw [← lintegral_map hV measurable_subtype_coe]
  exact continuation_mixed_integral_bound hδ (fun _ => y) hε hε1 hb hab hq hqa 0 k j

end

namespace Learner

section
variable {d M : ℕ}

end

variable {d M T : ℕ}

variable [NeZero d]

end Learner
end NoiselessRegression

end

end OAI

-- ---- platform node ----
open OAI OAI.NoiselessRegression
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace


theorem solution : type_of% @_root_.OAI.NoiselessRegression.route_mixed_bound := @_root_.OAI.NoiselessRegression.route_mixed_bound
