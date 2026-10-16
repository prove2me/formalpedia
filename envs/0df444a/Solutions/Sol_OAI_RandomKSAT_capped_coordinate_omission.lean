-- Prove2me | solution 1 for OAI.RandomKSAT.capped_coordinate_omission
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T19:01:29.767341+00:00
-- url     : https://prove2.me/submissions/299efd04-3940-491b-b83b-1a3eebcd59aa

-- Generated from openai/math@1581d4c lean/OAI/Probability/SATVariance/FiniteVariance.lean:L196-L211
-- (upload_full_project.md Phase 4): solution for node OAI.RandomKSAT.capped_coordinate_omission. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_SATVariance
import Definitions.Def_OAI_Probability_SATVariance_ClauseCombinatorics__SATVariance
import Definitions.Def_OAI_Probability_SATVariance_FrozenReplacement__SATVariance
import Definitions.Def_OAI_Probability_SATVariance_BlockKilling
import Definitions.Def_OAI_Probability_SATVariance_MarkovReplacement__SATVariance
import Definitions.Def_OAI_Probability_SATVariance_FiniteVariance
import Theorems.Thm_OAI_RandomKSAT_finiteTime_stream

-- ---- from OAI.Probability.SATVariance.ClauseCombinatorics ----
namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace RandomKSAT

open scoped Classical ENNReal

lemma support_card (n k : ℕ) :
    Fintype.card {s : Finset (Fin n) // s.card = k} = n.choose k := by
  classical
  rw [Fintype.card_of_subtype ((Finset.univ : Finset (Fin n)).powersetCard k)
    (by intro s; simp)]
  simp

lemma clause_card (n k : ℕ) : Fintype.card (Clause n k) = n.choose k * 2 ^ k := by
  classical
  change Fintype.card ((s : {s : Finset (Fin n) // s.card = k}) × (s.1 → Bool)) = _
  rw [Fintype.card_sigma]
  simp only [Fintype.card_fun, Fintype.card_bool, Fintype.card_coe]
  trans ∑ _ : {s : Finset (Fin n) // s.card = k}, 2 ^ k
  · apply Finset.sum_congr rfl
    intro s _
    rw [s.property]
  · rw [Finset.sum_const, Finset.card_univ, support_card, smul_eq_mul]

lemma clause_nonempty (n k : ℕ) (hkn : k ≤ n) : Nonempty (Clause n k) := by
  rw [← Fintype.card_pos_iff, clause_card]
  exact Nat.mul_pos (Nat.choose_pos hkn) (pow_pos (by decide) _)

lemma clauseLaw_probability (n k : ℕ) (hkn : k ≤ n) :
    IsProbabilityMeasure (clauseLaw n k) := by
  let := clause_nonempty n k hkn
  unfold clauseLaw
  infer_instance

end RandomKSAT

end

end OAI

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

lemma favg_sub.{u_1} {α : Type u_1} [Fintype α] (f g : α → ℝ) :
    favg (fun a => f a - g a) = favg f - favg g := by
  simp only [favg, Finset.sum_sub_distrib, sub_div]

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

lemma prefixLaw {u s : ℕ} (hsu : s ≤ u) (m : ℕ) :
    (streamLaw u s).map (fun ω (i : Fin m) => ω i) =
      uniformOn (Set.univ : Set (Fin m → Clause u s)) := by
  let := clauseLaw_probability u s hsu
  rw [streamLaw, Measure.map_infinitePi_infinitePi_of_inj Fin.val_injective,
    Measure.infinitePi_eq_pi]
  simpa only [Set.pi_univ, clauseLaw] using
    (uniformOn_pi (f := fun _ : Fin m => (Set.univ : Set (Clause u s)))).symm

lemma favg_mul.{u_1} {α : Type u_1} [Fintype α] (c : ℝ) (f : α → ℝ) :
    favg (fun a => c*f a) = c*favg f := by
  simp only [favg, ← Finset.mul_sum]
  ring

lemma favg_nonneg.{u_1} {α : Type u_1} [Fintype α] {f : α → ℝ} (h : ∀ a, 0 ≤ f a) :
    0 ≤ favg f := by
  exact div_nonneg (Finset.sum_nonneg fun a _ => h a) (by positivity)

end RandomKSAT

end

end OAI

-- ---- from OAI.Probability.SATVariance.FiniteVariance ----
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

noncomputable section

open MeasureTheory ProbabilityTheory

namespace RandomKSAT

open scoped Classical ENNReal

lemma favg_sq_sub_const.{u_1} {α : Type u_1} [Fintype α] [Nonempty α] (f : α → ℝ) (c : ℝ) :
    favg (fun a => (f a-c)^2) = favg (fun a => (f a)^2) - 2*c*favg f + c^2 := by
  have he : (fun a => (f a-c)^2) = (fun a => (f a)^2 - (2*c)*f a + c^2) := by
    funext a; ring
  rw [he, favg_add, favg_sub, favg_mul, favg_const]

lemma fvariance_centered.{u_1} {α : Type u_1} [Fintype α] [Nonempty α] (f : α → ℝ) :
    fvariance f = favg (fun a => (f a-favg f)^2) := by
  rw [favg_sq_sub_const, fvariance]; ring

lemma fvariance_nonneg.{u_1} {α : Type u_1} [Fintype α] [Nonempty α] (f : α → ℝ) :
    0 ≤ fvariance f := by
  rw [fvariance_centered]
  exact favg_nonneg fun a => sq_nonneg _

lemma favg_sq_le.{u_1} {α : Type u_1} [Fintype α] [Nonempty α] (f : α → ℝ) :
    (favg f)^2 ≤ favg (fun a => (f a)^2) := sub_nonneg.mp (fvariance_nonneg f)

lemma fvariance_le_sq_sub.{u_1} {α : Type u_1} [Fintype α] [Nonempty α] (f : α → ℝ) (c : ℝ) :
    fvariance f ≤ favg (fun a => (f a-c)^2) := by
  rw [favg_sq_sub_const, fvariance]
  nlinarith [sq_nonneg (favg f-c)]

lemma fvariance_equiv.{u_1, u_2} {α : Type u_1} {β : Type u_2} [Fintype α] [Fintype β] (e : α ≃ β) (f : β → ℝ) :
    fvariance (fun a => f (e a)) = fvariance f := by
  unfold fvariance
  rw [favg_equiv e (fun b => (f b)^2), favg_equiv e f]

lemma fvariance_prod.{u_1, u_2} {α : Type u_1} {β : Type u_2} [Fintype α] [Fintype β] (f : α × β → ℝ) :
    fvariance f = favg (fun b => fvariance (fun a => f (a,b))) +
      fvariance (fun b => favg (fun a => f (a,b))) := by
  simp only [fvariance, favg_sub, favg_prod]
  rw [favg_comm (fun a b => (f (a,b))^2), favg_comm (fun a b => f (a,b))]
  ring

lemma favg_cons.{u_1} {α : Type u_1} [Fintype α] {m : ℕ} (f : (Fin (m+1) → α) → ℝ) :
    favg f = favg (fun t : Fin m → α => favg (fun a : α => f (Fin.cons a t))) := by
  rw [← favg_equiv (Fin.consEquiv (fun _ : Fin (m+1) => α)) f, favg_prod, favg_comm]
  rfl

lemma coordinate_omission.{u_1} {α : Type u_1} [Fintype α] [Nonempty α] (m : ℕ)
    (f : (Fin m → α) → ℝ) (g : Fin m → (Fin m → α) → ℝ)
    (hg : ∀ i x a, g i (Function.update x i a) = g i x) :
    fvariance f ≤ ∑ i, favg (fun x => (f x-g i x)^2) := by
  classical
  induction m with
  | zero => simp [fvariance, favg]
  | succ m ih =>
    let F (t : Fin m → α) := favg (fun a : α => f (Fin.cons a t))
    let G (i : Fin m) (t : Fin m → α) := favg (fun a : α => g i.succ (Fin.cons a t))
    have hG : ∀ i t a, G i (Function.update t i a) = G i t := by
      intro i t a
      dsimp [G]
      congr 1
      funext b
      rw [Fin.cons_update, hg]
    have hi := ih F G hG
    have hdec : fvariance f = favg (fun t : Fin m → α =>
        fvariance (fun a : α => f (Fin.cons a t))) + fvariance F := by
      rw [← fvariance_equiv (Fin.consEquiv (fun _ : Fin (m+1) => α)) f, fvariance_prod]
      rfl
    have h0 : favg (fun t : Fin m → α => fvariance (fun a : α => f (Fin.cons a t))) ≤
        favg (fun x => (f x-g 0 x)^2) := by
      rw [favg_cons]
      apply favg_mono
      intro t
      let a₀ : α := Classical.choice ‹Nonempty α›
      convert fvariance_le_sq_sub (fun a : α => f (Fin.cons a t)) (g 0 (Fin.cons a₀ t)) using 1
      congr 1
      funext a
      rw [show g 0 (Fin.cons a t) = g 0 (Fin.cons a₀ t) by
        simpa only [Fin.update_cons_zero] using hg 0 (Fin.cons a₀ t) a]
    have hh : ∑ i : Fin m, favg (fun t => (F t-G i t)^2) ≤
        ∑ i : Fin m, favg (fun x => (f x-g i.succ x)^2) := by
      apply Finset.sum_le_sum
      intro i _
      rw [favg_cons]
      apply favg_mono
      intro t
      simpa only [F, G, favg_sub] using
        favg_sq_le (fun a : α => f (Fin.cons a t)-g i.succ (Fin.cons a t))
    rw [hdec, Fin.sum_univ_succ]
    exact add_le_add h0 (hi.trans hh)

lemma integral_uniform.{u_1} {α : Type u_1} [Fintype α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (f : α → ℝ) :
    ∫ a, f a ∂uniformOn Set.univ = favg f := by
  rw [integral_fintype Integrable.of_finite]
  simp only [measureReal_def, uniformOn_univ, Measure.count_singleton,
    one_div, ENNReal.toReal_inv, ENNReal.toReal_natCast, smul_eq_mul,
    ← Finset.mul_sum, favg]
  ring

lemma variance_uniform.{u_1} {α : Type u_1} [Fintype α] [Nonempty α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (f : α → ℝ) :
    ProbabilityTheory.variance f (uniformOn Set.univ) = fvariance f := by
  have hm : MemLp f 2 (uniformOn Set.univ) :=
    (memLp_two_iff_integrable_sq (measurable_of_countable f).aestronglyMeasurable).mpr
      Integrable.of_finite
  rw [variance_eq_sub hm, integral_uniform, integral_uniform]
  rfl

lemma omittedTime_update {n k L : ℕ} (i : Fin L) (cs : Fin L → Clause n k) (c : Clause n k) :
    omittedTime i (Function.update cs i c) = omittedTime i cs := by
  apply Finset.sum_congr rfl
  intro m _
  congr 1
  apply propext
  constructor <;> rintro ⟨a, ha⟩ <;> refine ⟨a, fun j hj hji => ?_⟩
  · simpa only [Function.update_of_ne hji] using ha j hj hji
  · simpa only [Function.update_of_ne hji] using ha j hj hji

lemma capped_coordinate_omission {n k : ℕ} (hkn : k ≤ n) (B : ℝ) :
    ProbabilityTheory.variance (T B : Stream n k → ℝ) (streamLaw n k) ≤
      ∑ i : Fin (cap n B), favg (fun cs : Fin (cap n B) → Clause n k =>
        (omittedTime i cs - finiteTime cs)^2) := by
  let := clause_nonempty n k hkn
  have hm : Measurable (fun ω : Stream n k => fun j : Fin (cap n B) => ω j) := by
    exact Measurable.of_eval fun j => measurable_pi_apply (j.val)
  have he : (T B : Stream n k → ℝ) =
      finiteTime ∘ (fun ω : Stream n k => fun j : Fin (cap n B) => ω j) := by
    funext ω
    exact (finiteTime_stream ω).symm
  rw [he, ← variance_map (measurable_of_countable finiteTime).aemeasurable hm.aemeasurable,
    prefixLaw hkn, variance_uniform]
  have hh := coordinate_omission (cap n B) (finiteTime (n := n) (k := k)) omittedTime
    omittedTime_update
  simpa only [sub_sq_comm] using hh

end RandomKSAT

end

end OAI

-- ---- platform node ----
open OAI OAI.RandomKSAT
open MeasureTheory ProbabilityTheory
open scoped Classical ENNReal


theorem solution : type_of% @_root_.OAI.RandomKSAT.capped_coordinate_omission := @_root_.OAI.RandomKSAT.capped_coordinate_omission
