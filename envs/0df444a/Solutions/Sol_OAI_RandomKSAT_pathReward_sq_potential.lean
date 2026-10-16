-- Prove2me | solution 1 for OAI.RandomKSAT.pathReward_sq_potential
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T19:14:30.798251+00:00
-- url     : https://prove2.me/submissions/9ed2ad31-57b4-4c5e-a0d5-14e9a0dd91ee

-- Generated from openai/math@1581d4c lean/OAI/Probability/SATVariance/FiberRefresh.lean:L255-L302
-- (upload_full_project.md Phase 4): solution for node OAI.RandomKSAT.pathReward_sq_potential. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_SATVariance
import Definitions.Def_OAI_Probability_SATVariance_ClauseCombinatorics__SATVariance
import Definitions.Def_OAI_Probability_SATVariance_FrozenReplacement__SATVariance
import Definitions.Def_OAI_Probability_SATVariance_BlockKilling
import Definitions.Def_OAI_Probability_SATVariance_MarkovReplacement__SATVariance
import Definitions.Def_OAI_Probability_SATVariance_FiniteVariance
import Definitions.Def_OAI_Probability_SATVariance_LifetimePotential
import Definitions.Def_OAI_Probability_SATVariance_RootDisintegration__SATVariance
import Definitions.Def_OAI_Probability_SATVariance_FiberRefresh
import Theorems.Thm_OAI_RandomKSAT_markovSum_potential

-- ---- from OAI.Probability.SATVariance.MarkovReplacement ----
namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace RandomKSAT

open scoped Classical ENNReal

lemma favg_mono.{u_1} {α : Type u_1} [Fintype α] {f g : α → ℝ} (h : ∀ a, f a ≤ g a) :
    favg f ≤ favg g := by
  exact div_le_div_of_nonneg_right (Finset.sum_le_sum fun a _ => h a) (by positivity)

lemma favg_const.{u_1} {α : Type u_1} [Fintype α] [Nonempty α] (c : ℝ) :
    favg (fun _ : α => c) = c := by
  simp [favg, Fintype.card_ne_zero]

lemma favg_add.{u_1} {α : Type u_1} [Fintype α] (f g : α → ℝ) :
    favg (fun a => f a + g a) = favg f + favg g := by
  simp only [favg, Finset.sum_add_distrib, add_div]

lemma favg_equiv.{u_1, u_2} {α : Type u_1} {β : Type u_2} [Fintype α] [Fintype β] (e : α ≃ β) (f : β → ℝ) :
    favg (fun a => f (e a)) = favg f := by
  rw [favg, favg, e.sum_comp f, Fintype.card_congr e]

lemma favg_comm.{u_1, u_2} {α : Type u_1} {β : Type u_2} [Fintype α] [Fintype β] (f : α → β → ℝ) :
    favg (fun a => favg (f a)) = favg (fun b => favg (fun a => f a b)) := by
  simp only [favg, ← Finset.sum_div]
  rw [Finset.sum_comm]
  ring

lemma favg_prod.{u_1, u_2} {α : Type u_1} {β : Type u_2} [Fintype α] [Fintype β] (f : α × β → ℝ) :
    favg f = favg (fun a => favg fun b => f (a,b)) := by
  simp only [favg, Fintype.sum_prod_type, Fintype.card_prod, Nat.cast_mul,
    ← Finset.sum_div]
  ring

lemma favg_mul.{u_1} {α : Type u_1} [Fintype α] (c : ℝ) (f : α → ℝ) :
    favg (fun a => c*f a) = c*favg f := by
  simp only [favg, ← Finset.mul_sum]
  ring

end RandomKSAT

end

end OAI

-- ---- from OAI.Probability.SATVariance.FiniteVariance ----
-- Lean 4.33 compatibility: Measurable.of_eval is the renamed measurable_pi_lambda
-- (Mathlib/MeasureTheory/MeasurableSpace/Constructions.lean at d13f23b records the alias).
section Lean433MeasurableOfEval
end Lean433MeasurableOfEval

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace RandomKSAT

open scoped Classical ENNReal

lemma favg_cons.{u_1} {α : Type u_1} [Fintype α] {m : ℕ} (f : (Fin (m+1) → α) → ℝ) :
    favg f = favg (fun t : Fin m → α => favg (fun a : α => f (Fin.cons a t))) := by
  rw [← favg_equiv (Fin.consEquiv (fun _ : Fin (m+1) => α)) f, favg_prod, favg_comm]
  rfl

end RandomKSAT

end

end OAI

-- ---- from OAI.Probability.SATVariance.FiberRefresh ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace RandomKSAT

open scoped Classical ENNReal

lemma uniformStep_mono.{u_1, u_2} {X : Type u_1} {α : Type u_2} [Fintype α] (step : ℕ → α → X → X) (i : ℕ) :
    Monotone (uniformStep step i) := by
  intro f g h x
  exact favg_mono fun _ => h _

lemma uniformStep_add.{u_1, u_2} {X : Type u_1} {α : Type u_2} [Fintype α] (step : ℕ → α → X → X)
    (i : ℕ) (f g : X → ℝ) :
    uniformStep step i (fun x => f x+g x) = fun x => uniformStep step i f x+uniformStep step i g x := by
  funext x
  exact favg_add _ _

lemma uniformStep_const.{u_1, u_2} {X : Type u_1} {α : Type u_2} [Fintype α] [Nonempty α]
    (step : ℕ → α → X → X) (i : ℕ) (c : ℝ) :
    uniformStep step i (fun _ => c) = fun _ => c := by
  funext x
  exact favg_const _

lemma uniformStep_add_const.{u_1, u_2} {X : Type u_1} {α : Type u_2} [Fintype α] [Nonempty α]
    (step : ℕ → α → X → X) (i : ℕ) (f : X → ℝ) (c : ℝ) :
    uniformStep step i (fun x => f x+c) = fun x => uniformStep step i f x+c := by
  rw [uniformStep_add, uniformStep_const]

lemma pathReward_avg.{u_1, u_2} {X : Type u_1} {α : Type u_2} [Fintype α] [Nonempty α]
    (step : ℕ → α → X → X) (f : X → ℝ) (m : ℕ) (x : X) :
    favg (fun z : Fin m → α => pathReward step f m z x) =
      markovSum (uniformStep step) f m x := by
  induction m generalizing step x with
  | zero => simp [pathReward, markovSum, favg_const]
  | succ m ih =>
    rw [favg_cons, favg_comm]
    simp only [pathReward, Fin.cons_zero, Fin.tail_cons, favg_add, favg_const]
    simp_rw [ih]
    rfl

lemma pathReward_sq_potential.{u_1, u_2} {X : Type u_1} {α : Type u_2} [Fintype α] [Nonempty α]
    (step : ℕ → α → X → X) (f τ : X → ℝ)
    (hf : ∀ x, 0 ≤ f x) (hτ : ∀ x, 0 ≤ τ x) (z : ℕ → ℝ)
    (hz : ∀ i, 0 ≤ z i)
    (hdrift : ∀ i x, f x + uniformStep step i τ x ≤ τ x+z i)
    {Z : ℝ} (m : ℕ) (hZ : (∑ i ∈ Finset.range m, z i) ≤ Z) (x : X) :
    favg (fun w : Fin m → α => (pathReward step f m w x)^2) ≤
      2 * markovSum (uniformStep step) (fun y => f y*(τ y+Z)) m x := by
  induction m generalizing step z x with
  | zero => simp [pathReward, markovSum, favg_const]
  | succ m ih =>
    have hzt : (∑ i ∈ Finset.range m, z (i+1)) ≤ Z := by
      rw [Finset.sum_range_succ'] at hZ
      linarith [hz 0]
    have hfuture : uniformStep step 0
        (markovSum (uniformStep (fun i => step (i+1))) f m) x ≤
        τ x+Z-f x := by
      have hh := uniformStep_mono step 0 (fun y =>
        markovSum_potential (uniformStep (fun i => step (i+1)))
          (uniformStep_mono _) (uniformStep_add_const _) f τ hτ (fun i => z (i+1))
          (fun i => hdrift (i+1)) m y) x
      rw [uniformStep_add_const] at hh
      rw [Finset.sum_range_succ'] at hZ
      linarith [hdrift 0 x]
    have hi := favg_mono (fun a : α =>
      ih (fun i => step (i+1)) (fun i => z (i+1)) (fun i => hz (i+1))
        (fun i => hdrift (i+1)) hzt (step 0 a x))
    rw [favg_mul] at hi
    rw [favg_cons, favg_comm]
    have hs (a : α) : favg (fun w : Fin m → α =>
        (pathReward step f (m+1) (Fin.cons a w) x)^2) =
        (f x)^2 + 2*f x * markovSum (uniformStep (fun i => step (i+1))) f m (step 0 a x) +
          favg (fun w : Fin m → α =>
            (pathReward (fun i => step (i+1)) f m w (step 0 a x))^2) := by
      simp only [pathReward, Fin.cons_zero, Fin.tail_cons, add_sq]
      rw [favg_add, favg_add, favg_const]
      rw [favg_mul, pathReward_avg]
    simp_rw [hs]
    rw [favg_add, favg_add, favg_const, favg_mul]
    change _ ≤ 2*(f x*(τ x+Z)+_)
    change favg _ ≤ 2*uniformStep step 0
      (markovSum (uniformStep (fun i => step (i+1))) (fun y => f y*(τ y+Z)) m) x at hi
    change f x^2 + 2*f x * uniformStep step 0
      (markovSum (uniformStep (fun i => step (i+1))) f m) x + _ ≤
      2*(f x*(τ x+Z)+uniformStep step 0
        (markovSum (uniformStep (fun i => step (i+1))) (fun y => f y*(τ y+Z)) m) x)
    nlinarith [mul_le_mul_of_nonneg_left hfuture (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (hf x)),
      sq_nonneg (f x)]

end RandomKSAT

end

end OAI

-- ---- platform node ----
open OAI OAI.RandomKSAT
open MeasureTheory ProbabilityTheory
open scoped Classical ENNReal


theorem solution : type_of% @_root_.OAI.RandomKSAT.pathReward_sq_potential := @_root_.OAI.RandomKSAT.pathReward_sq_potential
