-- Prove2me | solution 1 for OAI.SubsphereRegression.Learner.streaming_success_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T08:30:45.470603+00:00
-- url     : https://prove2.me/submissions/98591631-7121-4034-8d9d-c986f333ea53

-- Generated from openai/math@1581d4c lean/OAI/Probability/Subsphere/Regression/Precision.lean:L128-L157
-- (upload_full_project.md Phase 4): solution for node OAI.SubsphereRegression.Learner.streaming_success_bound. The node keeps its source
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
import Theorems.Thm_OAI_SubsphereRegression_lintegral_pi_prefix
import Theorems.Thm_OAI_SubsphereRegression_measurable_streamRoute
import Theorems.Thm_OAI_SubsphereRegression_prod_null_set_bound
import Theorems.Thm_OAI_SubsphereRegression_route_cap_bound
import Theorems.Thm_OAI_SubsphereRegression_sphere_observation_quasi

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
lemma ae_fiber_aemeasurable {f : X × Y → Z} (hf : AEMeasurable f (μ.prod ν)) :
    ∀ᵐ y ∂ν, AEMeasurable (fun x => f (x,y)) μ := by
  have he := Measure.ae_ae_of_ae_prod hf.prod_swap.ae_eq_mk
  filter_upwards [he] with y hy
  have hm : Measurable (fun x => hf.prod_swap.mk _ (y,x)) :=
    hf.prod_swap.measurable_mk.comp (measurable_const.prodMk measurable_id)
  exact hm.aemeasurable.congr (Filter.EventuallyEq.symm hy)

end FubiniAux

end SubsphereRegression
end
end

end OAI

-- ---- from OAI.Probability.Subsphere.Regression.Blocks ----
namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace
universe u
namespace SubsphereRegression
open scoped Topology
open InnerProductSpace
open scoped Pointwise
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

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

end SubsphereRegression

end

end OAI

-- ---- from OAI.Probability.Subsphere.Regression.Streaming ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem dite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α} {e : ¬c → α} : (dite c t e) = t hc := @dif_pos c h hc α t e

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
lemma one_le_streamFactor [Nonempty J] {q : ℕ} (hq : 0 < q) :
    1 ≤ streamFactor (E := E) (J := J) q := by
  apply one_le_mul (one_le_pow₀ (by norm_num))
  exact ENNReal.one_le_rpow (by exact_mod_cast Fintype.card_pos (α := J)) (by positivity)

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

lemma forcedRun_eq_route (s : UnitSphere d) (ω : Ω) (x : Samples d T)
    {n : ℕ} (hn : n ≤ T) :
    L.forcedRun s ω x n =
      streamRoute (fun t j obs => (L.transition t ω j obs).2) 0 n (L.initialChoice ω).2
        ((fun i => x (Fin.castLE hn i)), (fun i => ⟪s.val,x (Fin.castLE hn i)⟫)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [forcedRun, dite_eq_left (by omega), ih (by omega)]
    rw [fin_prefix_snoc hn x, fin_prefix_snoc hn (fun i => ⟪s.val,x i⟫), streamRoute_snoc]
    simp only [zero_add, real_inner_comm]

lemma run_forced_witness (s : UnitSphere d) (ω : Ω) (x : Samples d T)
    (n : ℕ) (hn : n ≤ T) :
    (L.run s ω x n = .inl (L.forcedRun s ω x n)) ∨
      ∃ t ≤ n, L.run s ω x n = .inr (t, L.forcedRun s ω x t) := by
  induction n with
  | zero =>
    simp only [run, start, forcedRun]
    split
    · exact Or.inr ⟨0, le_rfl, rfl⟩
    · exact Or.inl rfl
  | succ n ih =>
    rcases ih (by omega) with h | ⟨t,ht,h⟩
    · have hnt : n < T := by omega
      rw [run, h]
      simp only [dite_eq_left hnt, forcedRun]
      split
      · exact Or.inr ⟨n+1, le_rfl, by simp [forcedRun, hnt]⟩
      · exact Or.inl rfl
    · right
      exact ⟨t, by omega, by rw [run, h]⟩

lemma terminal_forced_witness (s : UnitSphere d) (ω : Ω) (x : Samples d T) :
    ∃ t ≤ T, L.terminal s ω x = (t, L.forcedRun s ω x t) := by
  rcases L.run_forced_witness s ω x T le_rfl with h | ⟨t,ht,h⟩
  · exact ⟨T, le_rfl, by simp [terminal, h]⟩
  · exact ⟨t, ht, by simp [terminal, h]⟩

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

-- ---- from OAI.Probability.Subsphere.Regression.Precision ----
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
section StreamTransfer
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E] in
lemma measurePreserving_pi_prefix (ν : Measure E) [IsProbabilityMeasure ν]
    {t T : ℕ} (ht : t ≤ T) :
    MeasurePreserving (fun x : Fin T → E => fun i : Fin t => x (Fin.castLE ht i))
      (Measure.pi (fun _ => ν)) (Measure.pi (fun _ => ν)) := by
  refine ⟨by fun_prop, ?_⟩
  apply Measure.ext_of_lintegral
  intro f hf
  rw [lintegral_map hf (by fun_prop)]
  exact lintegral_pi_prefix ν ht f hf

lemma sphere_sample_observation_quasi [Nontrivial E] (hd : 3 ≤ Module.finrank ℝ E)
    {T : ℕ} (i : Fin T) :
    Measure.QuasiMeasurePreserving
      (fun z : (Metric.sphere (0 : E) 1) × (Fin T → E) => (z.2 i, ⟪z.1.val,z.2 i⟫))
      ((sphereLaw (E := E)).prod (Measure.pi (fun _ => stdGaussian E)))
      ((stdGaussian E).prod volume) := by
  exact (sphere_observation_quasi hd).comp
    ((MeasurePreserving.id (sphereLaw (E := E))).prod
      (measurePreserving_eval (fun _ : Fin T => stdGaussian E) i)).quasiMeasurePreserving

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] in
lemma streamRoute_congr {J : Type*} (δ δ' : ℕ → J → (E × ℝ) → J)
    (n k : ℕ) (j : J) (A : Fin k → E) (b : Fin k → ℝ)
    (h : ∀ t j i, δ t j (A i,b i) = δ' t j (A i,b i)) :
    streamRoute δ n k j (A,b) = streamRoute δ' n k j (A,b) := by
  induction k generalizing n j with
  | zero => rfl
  | succ k ih =>
    rw [streamRoute, streamRoute, h]
    exact ih (n+1) _ (Fin.tail A) (Fin.tail b) (fun t j i => h t j i.succ)

lemma prefix_route_cap_bound [Nontrivial E]
    {J : Type*} [Fintype J] [MeasurableSpace J] [MeasurableSingletonClass J] [Nonempty J]
    {δ : ℕ → J → (E × ℝ) → J} (hδ : ∀ n j, Measurable (δ n j)) (y : J → E)
    {ε : ℝ} (hε : 0 < ε) {a q : ℕ} (ha : 2*a ≤ Module.finrank ℝ E - 1)
    (hq : 2 ≤ q) (hqa : 2*q ≤ a) {k T : ℕ} (hk : k ≤ T) (j : J) :
    ((sphereLaw (E := E)).prod (Measure.pi (fun _ : Fin T => stdGaussian E)))
      {z | dist z.1.val (y (streamRoute δ 0 k j
        ((fun i => z.2 (Fin.castLE hk i)),fun i => ⟪z.1.val,z.2 (Fin.castLE hk i)⟫))) ≤ ε} ≤
      (ENNReal.ofReal ((3 : ℝ)*4^Module.finrank ℝ E) * ENNReal.ofReal (ε^a)) *
        streamFactor (E := E) (J := J) q ^ (T/q+1) := by
  have hp := (MeasurePreserving.id (sphereLaw (E := E))).prod
    (measurePreserving_pi_prefix (stdGaussian E) hk)
  have hs : MeasurableSet
      {z : (Metric.sphere (0 : E) 1) × (Fin k → E) |
        dist z.1.val (y (streamRoute δ 0 k j (z.2,fun i => ⟪z.1.val,z.2 i⟫))) ≤ ε} := by
    apply measurableSet_le _ measurable_const
    exact (measurable_subtype_coe.comp measurable_fst).dist
      ((measurable_of_finite y).comp ((measurable_streamRoute hδ 0 k j).comp (by fun_prop)))
  apply (le_of_eq (hp.measure_preimage hs.nullMeasurableSet)).trans
  apply (route_cap_bound hδ y hε ha hq hqa k j).trans
  apply mul_le_mul' le_rfl
  exact pow_le_pow_right₀ (one_le_streamFactor (by omega : 0 < q))
    (Nat.add_le_add_right (Nat.div_le_div_right hk) 1)

end StreamTransfer

namespace Learner

lemma frozen_success_bound {d M T : ℕ} {Ω : Type u} (L : Learner d M T Ω)
    (ω : Ω) (hd : 3 ≤ d)
    (htrans : ∀ t j, AEMeasurable (fun obs => (L.transition t ω j obs).2) (observationReference d))
    {ε : ℝ} (hε : 0 < ε) {a q : ℕ} (ha : 2*a ≤ d-1) (hq : 2 ≤ q) (hqa : 2*q ≤ a) :
    ((uniformSphere d).prod (sampleLaw d T))
      {z | angularError z.1 (L.estimate z.1 ω z.2) ≤ ε} ≤
      (T+1 : ℝ≥0∞) * (ENNReal.ofReal ((3 : ℝ)*4^d) * ENNReal.ofReal (ε^a)) *
        streamFactor (E := Vector d) (J := State M) q ^ (T/q+1) := by
  classical
  let : NeZero d := ⟨by omega⟩
  let δ : ℕ → State M → (Vector d × ℝ) → State M := fun t j => (htrans t j).mk _
  have hδ (t : ℕ) (j : State M) : Measurable (δ t j) := (htrans t j).measurable_mk
  let μ := (uniformSphere d).prod (sampleLaw d T)
  have hgood : ∀ᵐ z ∂μ, ∀ t j (i : Fin T),
      (L.transition t ω j (z.2 i,⟪z.1.val,z.2 i⟫)).2 = δ t j (z.2 i,⟪z.1.val,z.2 i⟫) := by
    simp only [ae_all_iff]
    intro t j i
    exact (sphere_sample_observation_quasi (by simpa using hd) i).ae (htrans t j).ae_eq_mk
  let S : Fin (T+1) → Set (UnitSphere d × Samples d T) := fun t =>
    {z | dist z.1.val (L.output t ω (streamRoute δ 0 t (L.initialChoice ω).2
      ((fun i => z.2 (Fin.castLE (by omega) i)),fun i => ⟪z.1.val,z.2 (Fin.castLE (by omega) i)⟫))).val ≤ ε}
  have hmono : {z : UnitSphere d × Samples d T | angularError z.1 (L.estimate z.1 ω z.2) ≤ ε}
      ≤ᵐ[μ] ⋃ t, S t := by
    filter_upwards [hgood] with z hz
    intro hs
    rcases L.terminal_forced_witness z.1 ω z.2 with ⟨t,ht,he⟩
    have hf : L.forcedRun z.1 ω z.2 t = streamRoute δ 0 t (L.initialChoice ω).2
        ((fun i => z.2 (Fin.castLE ht i)),fun i => ⟪z.1.val,z.2 (Fin.castLE ht i)⟫) := by
      rw [L.forcedRun_eq_route z.1 ω z.2 ht]
      exact streamRoute_congr _ _ 0 t _ _ _ (fun n j i => hz n j (Fin.castLE ht i))
    have hc : dist z.1.val (L.estimate z.1 ω z.2).val ≤ ε := by
      apply le_trans _ hs
      simpa only [angularError, dist_comm] using chord_le_arccos (L.estimate z.1 ω z.2) z.1
    refine Set.mem_iUnion.mpr ⟨⟨t,by omega⟩, ?_⟩
    change dist z.1.val (L.output t ω _) ≤ ε
    simpa only [estimate, he, hf] using hc
  let B : ℝ≥0∞ := (ENNReal.ofReal ((3 : ℝ)*4^d) * ENNReal.ofReal (ε^a)) *
    streamFactor (E := Vector d) (J := State M) q ^ (T/q+1)
  have hb (t : Fin (T+1)) : μ (S t) ≤ B := by
    simpa only [B, μ, S, uniformSphere, sphereLaw, sampleLaw, finrank_euclideanSpace_fin] using
      prefix_route_cap_bound hδ (fun j => (L.output t ω j).val) hε
        (by simpa using ha) hq hqa (by omega : (t : ℕ) ≤ T) (L.initialChoice ω).2
  calc
    _ ≤ μ (⋃ t, S t) := measure_mono_ae hmono
    _ ≤ ∑' t, μ (S t) := measure_iUnion_le S
    _ ≤ ∑' _ : Fin (T+1), B := ENNReal.tsum_le_tsum hb
    _ = _ := by simp [B, tsum_fintype, nsmul_eq_mul, mul_assoc]

lemma streaming_success_bound {d M T : ℕ} {Ω : Type u} [MeasurableSpace Ω]
    (L : Learner d M T Ω) (ρ : Measure Ω) [IsProbabilityMeasure ρ]
    (hL : L.Admissible ρ) (hd : 3 ≤ d) {ε : ℝ} (hε : 0 < ε)
    {a q : ℕ} (ha : 2*a ≤ d-1) (hq : 2 ≤ q) (hqa : 2*q ≤ a) :
    L.uniformSuccess ρ ε ≤
      (T+1 : ℝ≥0∞) * (ENNReal.ofReal ((3 : ℝ)*4^d) * ENNReal.ofReal (ε^a)) *
        streamFactor (E := Vector d) (J := State M) q ^ (T/q+1) := by
  let : NeZero d := ⟨by omega⟩
  let : SigmaFinite (observationReference d) := by unfold observationReference; infer_instance
  have hω : ∀ᵐ ω ∂ρ, ∀ t j,
      AEMeasurable (fun obs => (L.transition t ω j obs).2) (observationReference d) := by
    simp only [ae_all_iff]
    intro t j
    filter_upwards [ae_fiber_aemeasurable (hL.transition t j).prod_swap] with ω hω
    exact measurable_snd.comp_aemeasurable hω
  have hp := ((MeasurePreserving.id (uniformSphere d)).prod
      (Measure.measurePreserving_swap (μ := sampleLaw d T) (ν := ρ))).comp
    (measurePreserving_prodAssoc (uniformSphere d) (sampleLaw d T) ρ)
  let S := {z : UnitSphere d × (Ω × Samples d T) |
    angularError z.1 (L.estimate z.1 z.2.1 z.2.2) ≤ ε}
  have hS : NullMeasurableSet S ((uniformSphere d).prod (ρ.prod (sampleLaw d T))) :=
    L.angularSuccess_nullMeasurable ρ ε hL
  have he := hp.measure_preimage hS
  have hb := prod_null_set_bound (hS.preimage hp.quasiMeasurePreserving)
    (c := (T+1 : ℝ≥0∞) * (ENNReal.ofReal ((3 : ℝ)*4^d) * ENNReal.ofReal (ε^a)) *
      streamFactor (E := Vector d) (J := State M) q ^ (T/q+1))
    (by
      filter_upwards [hω] with ω hω
      exact L.frozen_success_bound ω hd hω hε ha hq hqa)
  simpa only [he, measure_univ, mul_one, S, uniformSuccess] using hb

end Learner

namespace Learner

end Learner

section LowerFubini
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  {μ : Measure X} {ν : Measure Y} [SFinite μ] [SFinite ν]
end LowerFubini

namespace Learner
end Learner

end SubsphereRegression

end
end

end OAI

-- ---- platform node ----
open OAI OAI.SubsphereRegression OAI.SubsphereRegression.Learner
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace
open scoped Topology
open InnerProductSpace
open scoped Pointwise


theorem solution.{u} : type_of% @_root_.OAI.SubsphereRegression.Learner.streaming_success_bound.{u} := @_root_.OAI.SubsphereRegression.Learner.streaming_success_bound.{u}
