-- Prove2me | solution 1 for OAI.SubsphereCurrent.KernelLearner.uniformSuccess_asTape
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T08:50:22.532512+00:00
-- url     : https://prove2.me/submissions/c045266e-4628-4614-8a69-84094a20a9c7

-- Generated from openai/math@1581d4c lean/OAI/Probability/Subsphere/Kernels/Precision.lean:L770-L800
-- (upload_full_project.md Phase 4): solution for node OAI.SubsphereCurrent.KernelLearner.uniformSuccess_asTape. The node keeps its source
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
private theorem dite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α} {e : ¬c → α} : (dite c t e) = t hc := @dif_pos c h hc α t e
private theorem dite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t : c → α} {e : ¬c → α} : (dite c t e) = e hc := @dif_neg c h hc α t e

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
lemma measurable_countable_select {X Y J : Type*} [MeasurableSpace X]
    [MeasurableSpace Y] [MeasurableSpace J] [MeasurableSingletonClass J] [Countable J]
    {h : J → X → Y} (hh : ∀ j, Measurable (h j)) {φ : X → J} (hφ : Measurable φ) :
    Measurable (fun x => h (φ x) x) :=
  (measurable_from_prod_countable_right (f := fun p : J × X => h p.1 p.2) hh).comp
    (hφ.prodMk measurable_id)
end SubsphereCurrent

namespace SubsphereRegression.Learner
open SubsphereCurrent (measurable_countable_select)

lemma measurable_run_of_rules {d M T : ℕ} {Ω X : Type*} [MeasurableSpace Ω]
    [MeasurableSpace X] (L : Learner d M T Ω)
    (hi : Measurable L.initialChoice)
    (ht : ∀ t q, Measurable (fun z : Ω × (Vector d × ℝ) => L.transition t z.1 q z.2))
    {s : X → UnitSphere d} {ω : X → Ω} {x : X → Samples d T}
    (hs : Measurable s) (hω : Measurable ω) (hx : Measurable x) (n : ℕ) :
    Measurable (fun z => L.run (s z) (ω z) (x z) n) := by
  induction n with
  | zero =>
    exact (measurable_of_countable (fun a : Bool × State M =>
      if a.1 then Sum.inr (0,a.2) else Sum.inl a.2)).comp (hi.comp hω)
  | succ n ih =>
    change Measurable (fun z => (match L.run (s z) (ω z) (x z) n with
      | Sum.inr done => Sum.inr done
      | Sum.inl q => if hn : n < T then
          let row := x z ⟨n,hn⟩
          let a := L.transition (n+1) (ω z) q (row, ⟪row,(s z).val⟫)
          if a.1 then Sum.inr (n+1,a.2) else Sum.inl a.2
        else Sum.inl q))
    let F : RunStatus M → X → RunStatus M := fun status z => match status with
      | Sum.inr done => Sum.inr done
      | Sum.inl q => if hn : n < T then
          let row := x z ⟨n,hn⟩
          let a := L.transition (n+1) (ω z) q (row, ⟪row,(s z).val⟫)
          if a.1 then Sum.inr (n+1,a.2) else Sum.inl a.2
        else Sum.inl q
    have hF : ∀ status, Measurable (F status) := by
      intro status
      cases status with
      | inr done => exact measurable_const
      | inl q =>
        by_cases hn : n < T
        · dsimp [F]
          simp only [dite_eq_left hn]
          have hr : Measurable (fun z => x z ⟨n,hn⟩) := (measurable_pi_apply _).comp hx
          exact (measurable_of_countable (fun a : Bool × State M =>
            (if a.1 then Sum.inr (n+1,a.2) else Sum.inl a.2 : RunStatus M))).comp
            ((ht (n+1) q).comp (hω.prodMk (hr.prodMk (hr.inner (measurable_subtype_coe.comp hs)))))
        · dsimp [F]
          simp only [dite_eq_right hn]
          exact measurable_const
    exact measurable_countable_select hF ih

lemma measurable_estimate_of_rules {d M T : ℕ} {Ω X : Type*} [MeasurableSpace Ω]
    [MeasurableSpace X] (L : Learner d M T Ω)
    (hi : Measurable L.initialChoice)
    (ht : ∀ t q, Measurable (fun z : Ω × (Vector d × ℝ) => L.transition t z.1 q z.2))
    (ho : ∀ t q, Measurable (fun ω => L.output t ω q))
    {s : X → UnitSphere d} {ω : X → Ω} {x : X → Samples d T}
    (hs : Measurable s) (hω : Measurable ω) (hx : Measurable x) :
    Measurable (fun z => L.estimate (s z) (ω z) (x z)) := by
  have hr := L.measurable_run_of_rules hi ht hs hω hx T
  have hterm : Measurable (fun z => L.terminal (s z) (ω z) (x z)) := by
    unfold terminal
    exact (measurable_of_countable (fun status : RunStatus M =>
      match status with | Sum.inl q => (T,q) | Sum.inr done => done) :
      Measurable (fun status : RunStatus M =>
        match status with | Sum.inl q => (T,q) | Sum.inr done => done)).comp hr
  exact measurable_countable_select (fun a : ℕ × State M => (ho a.1 a.2).comp hω) hterm
end SubsphereRegression.Learner

namespace SubsphereCurrent
namespace KernelLearner
lemma measurable_tapeCoin {d M T : ℕ} (t : ℕ) :
    Measurable (tapeCoin (d := d) (M := M) (T := T) t) := by
  unfold tapeCoin
  split_ifs <;> fun_prop

lemma asTape_measurable_transition {d M T : ℕ} (L : KernelLearner d M T)
    (hL : L.BorelRules) (t : ℕ) (q : State M) :
    Measurable (fun z : Tape d M T × (Vector d × ℝ) => L.asTape.transition t z.1 q z.2) :=
  measurable_samplePMF (fun a => (hL t q a).comp measurable_snd)
    ((measurable_tapeCoin t).comp measurable_fst)

lemma stepDet_measurable {d M T : ℕ} (L : KernelLearner d M T)
    (s : UnitSphere d) (x : Samples d T) (n : ℕ) (a : RunStatus M) :
    Measurable (L.stepDet s x n a) := by
  cases a with
  | inr done => exact measurable_const
  | inl q =>
    unfold stepDet
    split_ifs
    · exact (measurable_of_countable (tagged M (n+1))).comp
        (measurable_samplePMF (fun _ => measurable_const) measurable_id)
    · exact measurable_const

lemma stepDet_map {d M T : ℕ} (L : KernelLearner d M T)
    (s : UnitSphere d) (x : Samples d T) (n : ℕ) (a : RunStatus M) :
    coinLaw.map (L.stepDet s x n a) = (L.stepPMF s x n a).toMeasure := by
  cases a with
  | inr done =>
    change coinLaw.map (fun _ => Sum.inr done) = (PMF.pure (Sum.inr done) : PMF (RunStatus M)).toMeasure
    simp [PMF.toMeasure_pure]
  | inl q =>
    unfold stepDet stepPMF
    split_ifs
    · rw [← PMF.toMeasure_map _ _ (measurable_of_countable _), ← samplePMF_map]
      exact (Measure.map_map (measurable_of_countable (tagged M (n+1)))
        (measurable_samplePMF (fun _ => measurable_const) measurable_id)).symm
    · simp [PMF.toMeasure_pure]

lemma run_eq_bind_chain {d M T : ℕ} (L : KernelLearner d M T)
    (s : UnitSphere d) (x : Samples d T) (n : ℕ) :
    L.run s x n = (L.initial.map (tagged M 0)).bind
      (fun a => lawChain (L.stepPMF s x) a n) := by
  induction n with
  | zero => simp [run, lawChain]
  | succ n ih =>
    change (L.run s x n).bind (L.stepPMF s x n) = _
    rw [ih, PMF.bind_bind]
    rfl

lemma asTape_run_eq_detChain {d M T : ℕ} (L : KernelLearner d M T)
    (s : UnitSphere d) (x : Samples d T) (ω : Tape d M T) {n : ℕ} (hn : n ≤ T) :
    L.asTape.run s ω x n = detChain (L.stepDet s x) (tagged M 0 ω.1) n
      (fun i => ω.2.1 (Fin.castLE hn i)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [SubsphereRegression.fin_prefix_snoc hn, detChain_snoc]
    simp only [SubsphereRegression.Learner.run, ih (by omega)]
    cases he : detChain (L.stepDet s x) (tagged M 0 ω.1) n
      (fun i => ω.2.1 (Fin.castLE (by omega) i)) with
    | inr done => rfl
    | inl q => simp [stepDet, asTape, tapeCoin, tagged, show n < T by omega]

lemma asTape_estimate_eq {d M T : ℕ} (L : KernelLearner d M T)
    (s : UnitSphere d) (x : Samples d T) (ω : Tape d M T) :
    L.asTape.estimate s ω x =
      ω.2.2 (finish M T (detChain (L.stepDet s x) (tagged M 0 ω.1) T ω.2.1)) := by
  unfold SubsphereRegression.Learner.estimate SubsphereRegression.Learner.terminal
  rw [L.asTape_run_eq_detChain s x ω le_rfl]
  rfl

lemma lintegral_outputTape_eval {d M T : ℕ} (L : KernelLearner d M T)
    (a : ℕ × State M) (f : UnitSphere d → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ o, f (o a) ∂L.outputTapeLaw) = ∫⁻ u, f u ∂L.output a.1 a.2 := by
  let : ∀ a : ℕ × State M, IsProbabilityMeasure (L.output a.1 a.2) :=
    fun a => L.output_probability a.1 a.2
  exact (measurePreserving_eval_infinitePi (fun a : ℕ × State M => L.output a.1 a.2) a).lintegral_comp hf

lemma lintegral_asTape_estimate {d M T : ℕ} (L : KernelLearner d M T)
    (hL : L.BorelRules) (s : UnitSphere d) (x : Samples d T)
    (f : UnitSphere d → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ ω, f (L.asTape.estimate s ω x) ∂L.tapeLaw) = ∫⁻ u, f u ∂L.estimateLaw s x := by
  have hE : Measurable (fun ω => f (L.asTape.estimate s ω x)) :=
    hf.comp (L.asTape.measurable_estimate_of_rules measurable_fst
      (L.asTape_measurable_transition hL) (fun t q => by
        change Measurable (fun ω : Tape d M T => ω.2.2 (t,q)); fun_prop)
      measurable_const measurable_id measurable_const)
  rw [tapeLaw, lintegral_prod _ hE.aemeasurable]
  calc
    _ = ∫⁻ a, ∫⁻ r : Fin T → ℝ,
        ∫⁻ u, f u ∂L.output
          (finish M T (detChain (L.stepDet s x) (tagged M 0 a) T r)).1
          (finish M T (detChain (L.stepDet s x) (tagged M 0 a) T r)).2
        ∂Measure.pi (fun _ => coinLaw) ∂L.initial.toMeasure := by
      apply lintegral_congr
      intro a
      rw [lintegral_prod (fun y : (Fin T → ℝ) × OutputTape d M =>
        f (L.asTape.estimate s (a,y) x))
        (hE.comp (measurable_const.prodMk measurable_id)).aemeasurable]
      apply lintegral_congr
      intro r
      simp_rw [asTape_estimate_eq]
      exact L.lintegral_outputTape_eval _ f hf
    _ = ∫⁻ a, ∫⁻ b, ∫⁻ u, f u ∂L.output (finish M T b).1 (finish M T b).2
        ∂(lawChain (L.stepPMF s x) (tagged M 0 a) T).toMeasure ∂L.initial.toMeasure := by
      apply lintegral_congr
      intro a
      exact detChain_lintegral (L.stepDet_measurable s x) (L.stepDet_map s x) (tagged M 0 a) T
        (fun b => ∫⁻ u, f u ∂L.output (finish M T b).1 (finish M T b).2)
    _ = ∫⁻ b, ∫⁻ u, f u ∂L.output (finish M T b).1 (finish M T b).2
        ∂(L.run s x T).toMeasure := by
      rw [run_eq_bind_chain, pmf_lintegral_bind, ← PMF.toMeasure_map _ _ (measurable_of_countable _),
        lintegral_map (measurable_of_countable _) (measurable_of_countable _)]
    _ = ∫⁻ a, ∫⁻ u, f u ∂L.output a.1 a.2 ∂(L.terminal s x).toMeasure := by
      unfold terminal
      rw [← PMF.toMeasure_map _ _ (measurable_of_countable _),
        lintegral_map (measurable_of_countable _) (measurable_of_countable _)]
      rfl
    _ = _ := by
      rw [estimateLaw, Measure.lintegral_bind (measurable_of_countable _).aemeasurable hf.aemeasurable]

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
lemma measurable_successTest {d : ℕ} {X : Type*} [MeasurableSpace X]
    {s u : X → UnitSphere d} (hs : Measurable s) (hu : Measurable u) (ε : ℝ) :
    Measurable (fun x => successTest (s x) ε (u x)) := by
  have he : Measurable (fun x => angularError (s x) (u x)) :=
    Real.continuous_arccos.measurable.comp
      ((measurable_subtype_coe.comp hu).inner (measurable_subtype_coe.comp hs))
  simpa only [successTest, Set.indicator_apply, Set.mem_ofPred_eq] using
    (Measurable.ite (measurableSet_le he measurable_const) measurable_const measurable_const :
      Measurable (fun x => if angularError (s x) (u x) ≤ ε then (1 : ℝ≥0∞) else 0))

lemma conditionalSuccess_eq_integral_tape {d M T : ℕ} (L : KernelLearner d M T)
    (hL : L.BorelRules) (ε : ℝ) (s : UnitSphere d) (x : Samples d T) :
    L.conditionalSuccess ε s x = ∫⁻ ω, successTest s ε (L.asTape.estimate s ω x) ∂L.tapeLaw := by
  rw [L.lintegral_asTape_estimate hL s x (successTest s ε)
    (measurable_successTest measurable_const measurable_id ε)]
  have hS : MeasurableSet {u : UnitSphere d | angularError s u ≤ ε} :=
    measurableSet_le (by unfold angularError; fun_prop) measurable_const
  simp only [successTest, conditionalSuccess, lintegral_indicator_const hS, one_mul]

lemma measurable_tape_test {d M T : ℕ} (L : KernelLearner d M T)
    (hL : L.BorelRules) (ε : ℝ) {X : Type*} [MeasurableSpace X]
    {s : X → UnitSphere d} {ω : X → Tape d M T} {x : X → Samples d T}
    (hs : Measurable s) (hω : Measurable ω) (hx : Measurable x) :
    Measurable (fun z => successTest (s z) ε (L.asTape.estimate (s z) (ω z) (x z))) :=
  measurable_successTest hs (L.asTape.measurable_estimate_of_rules measurable_fst
    (L.asTape_measurable_transition hL) (fun t q => by
      change Measurable (fun ω : Tape d M T => ω.2.2 (t,q)); fun_prop) hs hω hx) ε

lemma measurable_conditionalSuccess {d M T : ℕ} (L : KernelLearner d M T)
    (hL : L.BorelRules) (ε : ℝ) :
    Measurable (fun z : UnitSphere d × Samples d T => L.conditionalSuccess ε z.1 z.2) := by
  simp_rw [L.conditionalSuccess_eq_integral_tape hL ε]
  exact (L.measurable_tape_test hL ε (measurable_fst.comp measurable_fst)
    measurable_snd (measurable_snd.comp measurable_fst)).lintegral_prod_right

lemma uniformSuccess_asTape {d M T : ℕ} (L : KernelLearner d M T)
    (hL : L.BorelRules) (ε : ℝ) [NeZero d] :
    L.asTape.uniformSuccess L.tapeLaw ε =
      ∫⁻ z : UnitSphere d × Samples d T, L.conditionalSuccess ε z.1 z.2
        ∂(uniformSphere d).prod (sampleLaw d T) := by
  have hm := L.measurable_tape_test hL ε measurable_fst
    (measurable_fst.comp measurable_snd) (measurable_snd.comp measurable_snd)
  have hset : MeasurableSet {z : UnitSphere d × (Tape d M T × Samples d T) |
      angularError z.1 (L.asTape.estimate z.1 z.2.1 z.2.2) ≤ ε} := by
    apply measurableSet_le _ measurable_const
    exact Real.continuous_arccos.measurable.comp
      ((measurable_subtype_coe.comp (L.asTape.measurable_estimate_of_rules measurable_fst
        (L.asTape_measurable_transition hL) (fun t q => by
          change Measurable (fun ω : Tape d M T => ω.2.2 (t,q)); fun_prop)
        measurable_fst (measurable_fst.comp measurable_snd) (measurable_snd.comp measurable_snd))).inner
        (measurable_subtype_coe.comp measurable_fst))
  change ((uniformSphere d).prod (L.tapeLaw.prod (sampleLaw d T)))
    {z | angularError z.1 (L.asTape.estimate z.1 z.2.1 z.2.2) ≤ ε} = _
  rw [← one_mul (((uniformSphere d).prod (L.tapeLaw.prod (sampleLaw d T))) _),
    ← lintegral_indicator_const hset 1]
  change (∫⁻ z : UnitSphere d × (Tape d M T × Samples d T),
    successTest z.1 ε (L.asTape.estimate z.1 z.2.1 z.2.2)
      ∂(uniformSphere d).prod (L.tapeLaw.prod (sampleLaw d T))) = _
  rw [lintegral_prod (μ := uniformSphere d) (ν := L.tapeLaw.prod (sampleLaw d T))
      (fun z => successTest z.1 ε (L.asTape.estimate z.1 z.2.1 z.2.2)) hm.aemeasurable,
    lintegral_prod _ (L.measurable_conditionalSuccess hL ε).aemeasurable]
  apply lintegral_congr
  intro s
  rw [lintegral_prod_symm _ (L.measurable_tape_test hL ε measurable_const
    measurable_fst measurable_snd).aemeasurable]
  exact lintegral_congr fun x => (L.conditionalSuccess_eq_integral_tape hL ε s x).symm

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

-- ---- platform node ----
open OAI OAI.SubsphereCurrent OAI.SubsphereCurrent.KernelLearner
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace


theorem solution : type_of% @_root_.OAI.SubsphereCurrent.KernelLearner.uniformSuccess_asTape := @_root_.OAI.SubsphereCurrent.KernelLearner.uniformSuccess_asTape
