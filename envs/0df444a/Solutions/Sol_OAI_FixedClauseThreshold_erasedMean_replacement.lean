-- Prove2me | solution 1 for OAI.FixedClauseThreshold.erasedMean_replacement
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T05:30:05.218994+00:00
-- url     : https://prove2.me/submissions/bd9923f6-09dd-4c30-8621-59999e531056

-- Generated from openai/math@1581d4c lean/OAI/Probability/RandomSAT/Forcing.lean:L265-L316
-- (upload_full_project.md Phase 4): solution for node OAI.FixedClauseThreshold.erasedMean_replacement. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_FixedClauseThreshold
import Definitions.Def_OAI_Probability_RandomSAT_Clauses
import Definitions.Def_OAI_Probability_RandomSAT_Replacement
import Definitions.Def_OAI_Probability_RandomSAT_FiniteMean
import Definitions.Def_OAI_Probability_RandomSAT_ClauseProcess
import Definitions.Def_OAI_Probability_RandomSAT_Binomial
import Definitions.Def_OAI_Probability_RandomSAT_Forcing
import Theorems.Thm_OAI_FixedClauseThreshold_clauseHead_mean
import Theorems.Thm_OAI_FixedClauseThreshold_shorter_clause_replacement
import Theorems.Thm_OAI_FixedClauseThreshold_singleUNSAT_eq

-- ---- from OAI.Probability.RandomSAT.Clauses ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

/-!
Signed variable sets, clause cardinalities, and the exact probability of killing
a nonempty solution set.
-/

namespace FixedClauseThreshold

open Finset

noncomputable section

attribute [local instance] Classical.propDecidable

theorem nonempty_properClause {n k : ℕ} (hkn : k ≤ n) :
    Nonempty (ProperClause n k) := by
  apply Fintype.card_pos_iff.mp
  rw [card_properClause]
  exact Nat.mul_pos (Nat.choose_pos hkn) (by positivity)

end

end FixedClauseThreshold

end OAI

-- ---- from OAI.Probability.RandomSAT.Replacement ----
namespace OAI

/-!
Quantitative comparison of a shorter clause with a block of independent proper
clauses, uniformly over the background solution set.
-/

namespace FixedClauseThreshold

open Finset

noncomputable section

attribute [local instance] Classical.propDecidable

theorem uniformProbability_not {α : Type*} [Fintype α] [Nonempty α] (p : α → Prop) :
    uniformProbability (fun a => ¬ p a) = 1 - uniformProbability p := by
  unfold uniformProbability
  rw [Fintype.card_subtype_compl, Nat.cast_sub (Fintype.card_subtype_le p), sub_div,
    div_self (by exact_mod_cast Fintype.card_ne_zero)]

end

end FixedClauseThreshold

end OAI

-- ---- from OAI.Probability.RandomSAT.FiniteMean ----
namespace OAI

/-!
Uniform finite expectations and variances.
-/

namespace FixedClauseThreshold

open Finset

noncomputable section

attribute [local instance] Classical.propDecidable

theorem uniformMean_add {α : Type*} [Fintype α] (f g : α → ℝ) :
    uniformMean (fun a => f a + g a) = uniformMean f + uniformMean g := by
  simp [uniformMean, Finset.sum_add_distrib, add_div]

theorem uniformMean_sub {α : Type*} [Fintype α] (f g : α → ℝ) :
    uniformMean (fun a => f a - g a) = uniformMean f - uniformMean g := by
  simp [uniformMean, Finset.sum_sub_distrib, sub_div]

theorem uniformMean_const_mul {α : Type*} [Fintype α] (c : ℝ) (f : α → ℝ) :
    uniformMean (fun a => c * f a) = c * uniformMean f := by
  simp only [uniformMean, ← Finset.mul_sum]
  ring

theorem uniformMean_mono {α : Type*} [Fintype α] {f g : α → ℝ}
    (h : ∀ a, f a ≤ g a) : uniformMean f ≤ uniformMean g := by
  exact div_le_div_of_nonneg_right (Finset.sum_le_sum (fun a _ => h a)) (Nat.cast_nonneg _)

theorem uniformMean_comm {α β : Type*} [Fintype α] [Fintype β]
    (f : α → β → ℝ) :
    uniformMean (fun a => uniformMean (f a)) =
      uniformMean (fun b => uniformMean (fun a => f a b)) := by
  simp only [uniformMean, ← Finset.sum_div]
  rw [Finset.sum_comm]
  ring

theorem uniformProbability_eq_mean {α : Type*} [Fintype α] (p : α → Prop) :
    uniformProbability p = uniformMean (fun a => if p a then 1 else 0) := by
  classical
  unfold uniformProbability uniformMean
  congr 1
  simp [Fintype.card_subtype]

end

end FixedClauseThreshold

end OAI

-- ---- from OAI.Probability.RandomSAT.ClauseProcess ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

/-!
Coordinate erasure, independent clause averaging, survival probabilities, and
iterated replacement.
-/

namespace FixedClauseThreshold

open Finset

noncomputable section

attribute [local instance] Classical.propDecidable

theorem addClause_comm {n k r : ℕ} (S : Finset (Assignment n))
    (C : ProperClause n k) (D : ProperClause n r) :
    addClause (addClause S C) D = addClause (addClause S D) C := by
  ext σ
  simp only [mem_addClause]
  tauto

theorem clauseAverage_mono {n k : ℕ} {f g : Finset (Assignment n) → ℝ}
    (hfg : ∀ S, f S ≤ g S) : ∀ S, clauseAverage k f S ≤ clauseAverage k g S := by
  intro S
  exact uniformMean_mono (fun C => hfg (addClause S C))

theorem clauseAverage_sub_const {n k : ℕ} (hkn : k ≤ n)
    (f : Finset (Assignment n) → ℝ) (c : ℝ) (S : Finset (Assignment n)) :
    clauseAverage k (fun T => f T - c) S = clauseAverage k f S - c := by
  let : Nonempty (ProperClause n k) := nonempty_properClause hkn
  exact (uniformMean_sub _ _).trans (by rw [uniformMean_const]; rfl)

theorem clauseAverage_commute {n k r : ℕ} :
    Function.Commute (clauseAverage (n := n) k) (clauseAverage r) := by
  intro f
  funext S
  unfold clauseAverage
  rw [uniformMean_comm]
  apply uniformMean_congr
  intro C
  apply uniformMean_congr
  intro D
  rw [addClause_comm]

theorem clauseAverage_iterate_mono {n k m : ℕ} {f g : Finset (Assignment n) → ℝ}
    (hfg : ∀ S, f S ≤ g S) : ∀ S,
    ((clauseAverage k)^[m] f) S ≤ ((clauseAverage k)^[m] g) S := by
  induction m with
  | zero => exact hfg
  | succ m ih =>
    simp only [Function.iterate_succ_apply']
    exact clauseAverage_mono ih

theorem clauseAverage_iterate_sub_const {n k m : ℕ} (hkn : k ≤ n)
    (f : Finset (Assignment n) → ℝ) (c : ℝ) :
    (clauseAverage k)^[m] (fun T => f T - c) =
      (fun S => ((clauseAverage k)^[m] f) S - c) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [Function.iterate_succ_apply', ih, Function.iterate_succ_apply']
    funext S
    exact clauseAverage_sub_const hkn _ _ _

theorem survival_shift {n k r m d : ℕ} (S : Finset (Assignment n)) :
    ((clauseAverage k)^[m] (survival r d)) S =
      ((clauseAverage r)^[d] (survival k m)) S := by
  exact congrArg (fun f => f S) ((clauseAverage_commute (n := n) (k := k) (r := r)).iterate_iterate m d alive)

theorem survival_add {n k m d : ℕ} (S : Finset (Assignment n)) :
    ((clauseAverage k)^[m] (survival k d)) S = survival k (m + d) S := by
  exact congrArg (fun f => f S) (Function.iterate_add_apply (clauseAverage k) m d alive).symm

theorem survival_eq_probability {n k m : ℕ} (S : Finset (Assignment n)) :
    survival k m S = uniformProbability (fun F : Formula n k m =>
      ∃ σ ∈ S, Satisfies σ F) := by
  rw [survival_eq_mean, uniformProbability_eq_mean]
  apply uniformMean_congr
  intro F
  unfold alive
  congr 1
  apply propext
  simp [Finset.Nonempty, Satisfies]

theorem blockUNSAT_eq {n k g : ℕ} (hkn : k ≤ n) (S : Finset (Assignment n)) :
    blockUNSATProbability k g S = 1 - survival k g S := by
  let : Nonempty (ProperClause n k) := nonempty_properClause hkn
  rw [survival_eq_probability]
  exact uniformProbability_not _

theorem shorter_survival_replacement {n k : ℕ} (hk : 3 ≤ k) (hn : k + 1 ≤ n)
    (S : Finset (Assignment (n - 1))) :
    survival k (replacementBlock n k) S - replacementError n k ≤ survival (k - 1) 1 S := by
  have h := shorter_clause_replacement hk hn S
  rw [singleUNSAT_eq (by omega), blockUNSAT_eq (by omega)] at h
  linarith

end

end FixedClauseThreshold

end OAI

-- ---- from OAI.Probability.RandomSAT.Binomial ----
namespace OAI

/-!
Finite Bernoulli-count expectations and integrated telescoping estimates.
-/

namespace FixedClauseThreshold

open Finset

noncomputable section

attribute [local instance] Classical.propDecidable

theorem binomialMean_congr {p : ℝ} {m : ℕ} {f g : ℕ → ℝ}
    (h : ∀ d ≤ m, f d = g d) : binomialMean p m f = binomialMean p m g := by
  induction m generalizing f g with
  | zero => exact h 0 (by omega)
  | succ m ih =>
    simp only [binomialMean]
    rw [ih (fun d hd => h d (by omega)), ih (fun d hd => h (d + 1) (by omega))]

theorem binomialMean_mono {p : ℝ} {m : ℕ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {f g : ℕ → ℝ} (h : ∀ d ≤ m, f d ≤ g d) : binomialMean p m f ≤ binomialMean p m g := by
  induction m generalizing f g with
  | zero => exact h 0 (by omega)
  | succ m ih =>
    exact add_le_add
      (mul_le_mul_of_nonneg_left (ih (fun d hd => h d (by omega))) (sub_nonneg.mpr hp1))
      (mul_le_mul_of_nonneg_left (ih (fun d hd => h (d + 1) (by omega))) hp0)

theorem uniformMean_binomialMean {α : Type*} [Fintype α]
    (p : ℝ) (m : ℕ) (f : ℕ → α → ℝ) :
    uniformMean (fun a => binomialMean p m (fun d => f d a)) =
      binomialMean p m (fun d => uniformMean (f d)) := by
  induction m generalizing f with
  | zero => rfl
  | succ m ih =>
    simp only [binomialMean, uniformMean_add, uniformMean_const_mul, ih]

end

end FixedClauseThreshold

end OAI

-- ---- from OAI.Probability.RandomSAT.Forcing ----
namespace OAI

/-!
Deletion and erasure of a coordinate, permutation symmetry, and the integrated
forcing bound.
-/

namespace FixedClauseThreshold

open Finset

noncomputable section

attribute [local instance] Classical.propDecidable

theorem erasedSolutions_cons_inl {v k m : ℕ} (S : Finset (Assignment v))
    (C : ProperClause v k) (F : Fin m → SplitClause v k) :
    erasedSolutions S (Fin.cons (.inl C) F) = erasedSolutions (addClause S C) F := by
  ext σ
  simp only [mem_erasedSolutions, mem_addClause, Fin.forall_fin_succ,
    Fin.cons_zero, Fin.cons_succ, ErasedSatisfied]
  tauto

theorem erasedSolutions_cons_inr {v k m : ℕ} (S : Finset (Assignment v))
    (Q : ProperClause v (k - 1)) (b : Bool) (F : Fin m → SplitClause v k) :
    erasedSolutions S (Fin.cons (.inr (Q, b)) F) = erasedSolutions (addClause S Q) F := by
  ext σ
  simp only [mem_erasedSolutions, mem_addClause, Fin.forall_fin_succ,
    Fin.cons_zero, Fin.cons_succ, ErasedSatisfied]
  tauto

theorem erasedMean_succ {v k m : ℕ} (hk : 0 < k) (hkv : k ≤ v)
    (S : Finset (Assignment v)) :
    erasedMean hk (m + 1) S =
      (1 - (k : ℝ) / (v + 1)) * clauseAverage k (erasedMean hk m) S +
      ((k : ℝ) / (v + 1)) * clauseAverage (k - 1) (erasedMean hk m) S := by
  unfold erasedMean
  rw [uniformMean_fin_succ]
  have hcons (C : ProperClause (v + 1) k) (F : Formula (v + 1) k m) :
      (fun i : Fin (m + 1) => clauseHeadSplit hk ((Fin.cons C F : Formula (v + 1) k (m + 1)) i)) =
        Fin.cons (clauseHeadSplit hk C) (fun i => clauseHeadSplit hk (F i)) := by
    funext i
    refine Fin.cases ?_ (fun _ => ?_) i <;> rfl
  simp only [hcons]
  rw [clauseHead_mean hk hkv (fun X => uniformMean (fun F : Formula (v + 1) k m =>
    alive (erasedSolutions S (Fin.cons X (fun i => clauseHeadSplit hk (F i))))))]
  simp only [erasedSolutions_cons_inl, erasedSolutions_cons_inr,
    uniformMean_const]
  rfl

theorem clauseAverage_binomialMean {v k : ℕ} (p : ℝ) (m : ℕ)
    (f : ℕ → Finset (Assignment v) → ℝ) (S : Finset (Assignment v)) :
    clauseAverage k (fun T => binomialMean p m (fun d => f d T)) S =
      binomialMean p m (fun d => clauseAverage k (f d) S) :=
  uniformMean_binomialMean p m _

theorem clauseAverage_survival {v k t : ℕ} (S : Finset (Assignment v)) :
    clauseAverage k (survival k t) S = survival k (t + 1) S :=
  (survival_succ S).symm

theorem clauseAverage_short_survival {n k t : ℕ} (hk : 3 ≤ k) (hn : k + 1 ≤ n)
    (S : Finset (Assignment (n - 1))) :
    survival k (t + replacementBlock n k) S - replacementError n k ≤
      clauseAverage (k - 1) (survival k t) S := by
  have h := clauseAverage_iterate_mono (k := k) (m := t)
    (shorter_survival_replacement hk hn) S
  rw [clauseAverage_iterate_sub_const (by omega)] at h
  dsimp only at h
  rw [survival_add] at h
  have he : clauseAverage (k - 1) (survival k t) S =
      ((clauseAverage k)^[t] (survival (k - 1) 1)) S :=
    survival_shift (m := 1) (d := t) S
  rw [he]
  simpa using h

theorem erasedMean_replacement {n k m : ℕ} (hk : 3 ≤ k) (hn : k + 1 ≤ n)
    (S : Finset (Assignment (n - 1))) :
    binomialMean ((k : ℝ) / n) m (fun d =>
      survival k (m - d + replacementBlock n k * d) S -
        (d : ℝ) * replacementError n k) ≤ erasedMean (by omega : 0 < k) m S := by
  have hkn : k ≤ n - 1 := by omega
  have hshort : k - 1 ≤ n - 1 := by omega
  have hn1 : n - 1 + 1 = n := by omega
  have hp0 : 0 ≤ (k : ℝ) / n := by positivity
  have hp1 : (k : ℝ) / n ≤ 1 := by
    apply (div_le_one (by exact_mod_cast (by omega : 0 < n))).mpr
    exact_mod_cast (by omega : k ≤ n)
  induction m generalizing S with
  | zero => simp [binomialMean]
  | succ m ih =>
    rw [erasedMean_succ (by omega) hkn]
    have hden : ((n - 1 : ℕ) : ℝ) + 1 = n := by exact_mod_cast hn1
    rw [hden]
    have hlong := clauseAverage_mono (k := k) ih S
    have hshorter := clauseAverage_mono (k := k - 1) ih S
    rw [clauseAverage_binomialMean] at hlong hshorter
    have ha : binomialMean ((k : ℝ) / n) m (fun d =>
        survival k (m + 1 - d + replacementBlock n k * d) S -
          (d : ℝ) * replacementError n k) ≤ clauseAverage k (erasedMean (by omega : 0 < k) m) S := by
      calc
        _ = binomialMean ((k : ℝ) / n) m (fun d => clauseAverage k
            (fun T => survival k (m - d + replacementBlock n k * d) T -
              (d : ℝ) * replacementError n k) S) := by
          apply binomialMean_congr
          intro d hd
          rw [clauseAverage_sub_const hkn, clauseAverage_survival]
          congr 2
          omega
        _ ≤ _ := hlong
    have hb : binomialMean ((k : ℝ) / n) m (fun d =>
        survival k (m + 1 - (d + 1) + replacementBlock n k * (d + 1)) S -
          ((d + 1 : ℕ) : ℝ) * replacementError n k) ≤
        clauseAverage (k - 1) (erasedMean (by omega : 0 < k) m) S := by
      apply le_trans _ hshorter
      apply binomialMean_mono hp0 hp1
      intro d _
      rw [clauseAverage_sub_const hshort]
      have h := clauseAverage_short_survival (t := m - d + replacementBlock n k * d) hk hn S
      have he : m + 1 - (d + 1) + replacementBlock n k * (d + 1) =
          m - d + replacementBlock n k * d + replacementBlock n k := by
        rw [Nat.mul_add, Nat.mul_one]
        omega
      rw [he]
      push_cast
      linarith
    exact add_le_add (mul_le_mul_of_nonneg_left ha (sub_nonneg.mpr hp1))
      (mul_le_mul_of_nonneg_left hb hp0)

end

end FixedClauseThreshold

end OAI

-- ---- platform node ----
open OAI OAI.FixedClauseThreshold
open Finset
attribute [local instance] Classical.propDecidable


theorem solution : type_of% @_root_.OAI.FixedClauseThreshold.erasedMean_replacement := @_root_.OAI.FixedClauseThreshold.erasedMean_replacement
