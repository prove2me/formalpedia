-- Prove2me | solution 1 for OAI.SubsphereCurrent.KernelLearner.asTape_admissible
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T08:47:29.766566+00:00
-- url     : https://prove2.me/submissions/d2676813-9987-424e-8b4f-50340dad4319

-- Generated from openai/math@1581d4c lean/OAI/Probability/Subsphere/Kernels/Precision.lean:L545-L558
-- (upload_full_project.md Phase 4): solution for node OAI.SubsphereCurrent.KernelLearner.asTape_admissible. The node keeps its source
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
import Theorems.Thm_OAI_SubsphereCurrent_measurable_finiteSample

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

lemma asTape_admissible {d M T : ℕ} (L : KernelLearner d M T)
    (hL : L.BorelRules) : L.asTape.Admissible L.tapeLaw := by
  have hi : Measurable L.asTape.initialChoice := measurable_fst
  have ht := L.asTape_measurable_transition hL
  have ho (t : ℕ) (q : State M) : Measurable (fun ω => L.asTape.output t ω q) := by
    change Measurable (fun ω : Tape d M T => ω.2.2 (t,q))
    fun_prop
  refine ⟨hi.aemeasurable, fun t q => (ht t q).aemeasurable,
    fun t q => (ho t q).aemeasurable, ?_, ?_⟩
  · intro s
    exact (L.asTape.measurable_estimate_of_rules hi ht ho measurable_const
      measurable_fst measurable_snd).aemeasurable
  · exact (L.asTape.measurable_estimate_of_rules hi ht ho measurable_fst
      (measurable_fst.comp measurable_snd) (measurable_snd.comp measurable_snd)).aemeasurable

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

-- ---- platform node ----
open OAI OAI.SubsphereCurrent OAI.SubsphereCurrent.KernelLearner
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace


theorem solution : type_of% @_root_.OAI.SubsphereCurrent.KernelLearner.asTape_admissible := @_root_.OAI.SubsphereCurrent.KernelLearner.asTape_admissible
