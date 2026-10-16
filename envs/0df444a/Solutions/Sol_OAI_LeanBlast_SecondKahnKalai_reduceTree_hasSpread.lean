-- Prove2me | solution 1 for OAI.LeanBlast.SecondKahnKalai.reduceTree_hasSpread
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T02:49:02.452525+00:00
-- url     : https://prove2.me/submissions/6a7ebdd4-1c2b-4af7-941c-11a23c869f78

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/GraphThreshold/TreeReduction.lean:L253-L285
-- (upload_full_project.md Phase 4): solution for node OAI.LeanBlast.SecondKahnKalai.reduceTree_hasSpread. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Action.Pointwise.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Combinatorics.SimpleGraph.Copy
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.List.Pairwise
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Real.Basic
import Mathlib.Logic.Equiv.Fintype
import Mathlib.Order.Interval.Set.Monotone
import Mathlib.Tactic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Order.Monotone
import Definitions.Def_SecondKahnKalai
import Definitions.Def_OAI_Combinatorics_GraphThreshold_GraphEncoding
import Definitions.Def_OAI_Combinatorics_GraphThreshold_GraphProbability
import Definitions.Def_OAI_Combinatorics_GraphThreshold_EmbeddingExtension
import Definitions.Def_OAI_Combinatorics_GraphThreshold_GraphSupport
import Definitions.Def_OAI_Combinatorics_GraphThreshold_Basic
import Definitions.Def_OAI_Combinatorics_GraphThreshold_FiniteProbability
import Definitions.Def_OAI_Combinatorics_GraphThreshold_CopyOrbits
import Definitions.Def_OAI_Combinatorics_GraphThreshold_GraphExpectedCopies
import Definitions.Def_OAI_Combinatorics_GraphThreshold_GraphCopies
import Definitions.Def_OAI_Combinatorics_GraphThreshold_ProbabilityTree
import Definitions.Def_OAI_Combinatorics_GraphThreshold_LocalFailureNumerics
import Definitions.Def_OAI_Combinatorics_GraphThreshold_Predecessor
import Definitions.Def_OAI_Combinatorics_GraphThreshold_GraphHierarchy
import Definitions.Def_OAI_Combinatorics_GraphThreshold_BernoulliCoupling
import Definitions.Def_OAI_Combinatorics_GraphThreshold_AdaptiveTrials
import Definitions.Def_OAI_Combinatorics_GraphThreshold_ProbabilityTreeFacts
import Definitions.Def_OAI_Combinatorics_GraphThreshold_ProbabilityTreeTrim
import Definitions.Def_OAI_Combinatorics_GraphThreshold_CapacityIteration
import Definitions.Def_OAI_Combinatorics_GraphThreshold_Resampling
import Definitions.Def_OAI_Combinatorics_GraphThreshold_ResamplingEvents
import Definitions.Def_OAI_Combinatorics_GraphThreshold_TreeReductionData
import Definitions.Def_OAI_Combinatorics_GraphThreshold_TreeReduction

-- ---- from OAI.Combinatorics.GraphThreshold.Resampling ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section
open scoped BigOperators

namespace LeanBlast.SecondKahnKalai

variable {X B : Type*} [DecidableEq X] [Fintype B]

theorem resamplingWeight_eq_zero_of_not_subset (ν : FiniteLaw B) (A : B → Finset X)
    (ρ : ℝ) (W : Finset X) (c b : B) (hb : ¬A b ⊆ resamplingY A W c) :
    resamplingWeight ν A ρ W (c, b) = 0 := by
  simp [resamplingWeight, resamplingTargetWeight, resamplingNumerator, hb]

theorem resampling_target_subset_of_pos (ν : FiniteLaw B) (A : B → Finset X)
    (ρ : ℝ) (W : Finset X) (c b : B)
    (hcb : 0 < resamplingWeight ν A ρ W (c, b)) : A b ⊆ resamplingY A W c := by
  by_contra hb
  rw [resamplingWeight_eq_zero_of_not_subset ν A ρ W c b hb] at hcb
  exact (lt_irrefl 0) hcb

theorem resamplingFragment_subset_source (ν : FiniteLaw B) (A : B → Finset X)
    (ρ : ℝ) (W : Finset X) (c b : B)
    (hcb : 0 < resamplingWeight ν A ρ W (c, b)) :
    resamplingFragment A W b ⊆ A c := by
  intro x hx
  have hx' := Finset.mem_sdiff.mp hx
  rcases Finset.mem_union.mp (resampling_target_subset_of_pos ν A ρ W c b hcb hx'.1) with hW | hc
  · exact (hx'.2 hW).elim
  · exact hc

end LeanBlast.SecondKahnKalai

end

end OAI

-- ---- from OAI.Combinatorics.GraphThreshold.TreeReduction ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

open scoped BigOperators
open Classical

noncomputable section

namespace LeanBlast.SecondKahnKalai

section RetainedLaw

variable {B X : Type*} [Fintype B] [DecidableEq X]

theorem sum_retained_indicator (w : B → ℝ) (G Q : B → Prop) (hw : ∀ b, 0 ≤ w b) :
    (∑ b : RetainedIndex w G, if Q b then w b else 0) =
      ∑ b, if G b ∧ Q b then w b else 0 := by
  simpa only [mul_ite, mul_one, mul_zero, ite_and] using
    sum_retained w G hw (fun b => if Q b then 1 else 0)

theorem retainedLaw_prob (w : B → ℝ) (G Q : B → Prop) (hw : ∀ b, 0 ≤ w b)
    (hpos : 0 < retainedMass w G) :
    (retainedLaw w G hw hpos).prob (fun b => Q b) =
      (∑ b, if G b ∧ Q b then w b else 0) / retainedMass w G := by
  rw [← sum_retained_indicator w G Q hw, Finset.sum_div]
  unfold FiniteLaw.prob
  apply Finset.sum_congr rfl
  intro b _
  by_cases hq : Q b <;> simp [retainedLaw, hq]

theorem retainedLaw_isSpread (w : B → ℝ) (G : B → Prop) (hw : ∀ b, 0 ≤ w b)
    (hpos : 0 < retainedMass w G) (F : B → Finset X) {a q : ℝ}
    (ha : 0 ≤ a) (hq : 0 < q) (hq1 : q ≤ 1) (hretain : q ≤ retainedMass w G)
    (hnum : ∀ J : Finset X, J.Nonempty →
      (∑ b, if G b ∧ J ⊆ F b then w b else 0) ≤ a ^ J.card) :
    IsSpread (retainedLaw w G hw hpos) (fun b => F b) (a / q) := by
  classical
  intro J hJ
  change (retainedLaw w G hw hpos).prob (fun b => J ⊆ F b.val) ≤ (a / q) ^ J.card
  rw [retainedLaw_prob w G (fun b => J ⊆ F b) hw hpos]
  have hpower : q ^ J.card ≤ q :=
    pow_le_of_le_one hq.le hq1 (Nat.ne_of_gt hJ.card_pos)
  calc
    _ ≤ a ^ J.card / retainedMass w G := by
      apply div_le_div_of_nonneg_right _ hpos.le
      refine le_trans (le_of_eq ?_) (hnum J hJ)
      apply Finset.sum_congr rfl
      intro b _
      by_cases hb : G b ∧ J ⊆ F b <;> simp [hb]
    _ ≤ a ^ J.card / q := div_le_div_of_nonneg_left (pow_nonneg ha _) hq hretain
    _ ≤ a ^ J.card / q ^ J.card :=
      div_le_div_of_nonneg_left (pow_nonneg ha _) (pow_pos hq _) hpower
    _ = (a / q) ^ J.card := (div_pow a q J.card).symm

theorem target_fragment_mass_le_source
    (μ : FiniteLaw B) (A F : B → Finset X) (joint : B × B → ℝ)
    (event : B → B → Prop) (G : B → Prop)
    (hjoint : ∀ c b, 0 ≤ joint (c, b))
    (hsource : ∀ c, ∑ b, joint (c, b) = μ.weight c)
    (hfragment : ∀ c b, 0 < joint (c, b) → F b ⊆ A c) (J : Finset X) :
    (∑ b, if G b ∧ J ⊆ F b then ∑ c, if event c b then joint (c, b) else 0 else 0) ≤
      μ.prob (fun c => J ⊆ A c) := by
  calc
    _ = ∑ b, ∑ c,
        if G b ∧ J ⊆ F b then if event c b then joint (c, b) else 0 else 0 := by
      apply Finset.sum_congr rfl
      intro b _
      by_cases hb : G b ∧ J ⊆ F b <;> simp [hb]
    _ = ∑ c, ∑ b,
        if G b ∧ J ⊆ F b then if event c b then joint (c, b) else 0 else 0 :=
      Finset.sum_comm
    _ ≤ ∑ c, ∑ b, if J ⊆ A c then joint (c, b) else 0 := by
      apply Finset.sum_le_sum
      intro c _
      apply Finset.sum_le_sum
      intro b _
      by_cases hb : G b ∧ J ⊆ F b
      · by_cases he : event c b
        · by_cases hj : 0 < joint (c, b)
          · have hJA : J ⊆ A c := hb.2.trans (hfragment c b hj)
            simp [hb, he, hJA]
          · have hz : joint (c, b) = 0 :=
              le_antisymm (le_of_not_gt hj) (hjoint c b)
            simp [hb, he, hz]
        · simp only [ite_eq_left hb, ite_eq_right he]
          split_ifs <;> linarith [hjoint c b]
      · simp only [ite_eq_right hb]
        split_ifs <;> linarith [hjoint c b]
    _ = μ.prob (fun c => J ⊆ A c) := by
      unfold FiniteLaw.prob
      apply Finset.sum_congr rfl
      intro c _
      by_cases hc : J ⊆ A c <;> simp [hc, hsource]

end RetainedLaw

section Construction

variable {X : Type} [DecidableEq X]

theorem reduceTree_hasSpread (ρ : ℝ) (m : ℕ → ℕ) (W : Finset X) {d : ℕ}
    (T : ProbabilityTree X d) (hρ : 0 < ρ) (hm : ∀ j < d, 0 < m j)
    (hg : Good ρ m W T) (a : ℕ → ℝ) (ha : ∀ j < d, 0 ≤ a j)
    (hT : T.HasSpread a) :
    (reduceTree ρ m W T hρ hm hg).HasSpread
      (fun j => a j / (1 - Real.exp (-(m j : ℝ)))) := by
  induction T generalizing m a with
  | leaf => simp only [reduceTree, ProbabilityTree.HasSpread]
  | @node n B inst μ hμ A child ih =>
      simp only [reduceTree, ProbabilityTree.HasSpread]
      constructor
      · refine retainedLaw_isSpread (successfulTargetMass μ A ρ (m 0) W)
          (fun b => Good ρ (fun j => m (j + 1)) W (child b))
          (successfulTargetMass_nonneg μ A hρ.le (m 0) W)
          (good_retainedMass_pos μ hμ A child ρ m W (hm 0 (Nat.succ_pos _)) hg)
          (fun b => A b \ W)
          (ha 0 (Nat.succ_pos _))
          (one_sub_exp_neg_nat_pos (hm 0 (Nat.succ_pos _))) ?_ ?_ ?_
        · linarith [Real.exp_pos (-(m 0 : ℝ))]
        · simpa only [retainedMass, Good] using hg
        · intro J hJ
          exact (target_fragment_mass_le_source μ A (fun b => A b \ W)
            (resamplingWeight μ A ρ W) (LocalSuccess μ A ρ (m 0) W)
            (fun b => Good ρ (fun j => m (j + 1)) W (child b))
            (fun c b => resamplingWeight_nonneg μ A hρ.le W (c, b))
            (resampling_source_marginal μ A hμ hρ W)
            (fun c b hp => resamplingFragment_subset_source μ A ρ W c b hp) J).trans
            (hT.1 J hJ)
      · intro b
        exact ih b.val (fun j => m (j + 1))
          (fun j hj => hm (j + 1) (Nat.succ_lt_succ hj)) b.property.1
          (fun j => a (j + 1)) (fun j hj => ha (j + 1) (Nat.succ_lt_succ hj))
          (hT.2 b.val)

end Construction

end LeanBlast.SecondKahnKalai

end

end OAI

-- ---- platform node ----
open OAI OAI.LeanBlast OAI.LeanBlast.SecondKahnKalai
open scoped BigOperators
open Classical


theorem solution : type_of% @_root_.OAI.LeanBlast.SecondKahnKalai.reduceTree_hasSpread := @_root_.OAI.LeanBlast.SecondKahnKalai.reduceTree_hasSpread
