-- Prove2me | solution 1 for OAI.CriticalPercolation.SearchTree.normalized_centered_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T17:26:44.183336+00:00
-- url     : https://prove2.me/submissions/5837fb00-9c96-40b6-bd0e-754877c5dc88

import Mathlib
import Definitions.Def_OAIQ228B002

section
-- module Solutions.Q228_CP.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem dite_eq_right {α : Sort _} {c : Prop} {_ : Decidable c} {a : c → α} {b : ¬c → α} (h : ¬c) :
    dite c a b = b h := dif_neg h
end OAICompat434

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Criticality_DyadicBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open scoped BigOperators

namespace CriticalPercolation
lemma sum_two_pow (N : ℕ) : ∑ k ∈ Finset.range N, (2:ℝ)^k = 2^N-1 := by
  induction N with
  | zero => simp
  | succ N ih => rw [Finset.sum_range_succ,ih,pow_succ]; ring

lemma sum_two_inv_pow (N : ℕ) : ∑ k ∈ Finset.range N, 1/(2:ℝ)^k = 2-2/2^N := by
  induction N with
  | zero => norm_num
  | succ N ih =>
    rw [Finset.sum_range_succ,ih,pow_succ]
    field_simp
    ring

lemma dyadic_sum_bound (N K : ℕ) :
    (∑ k ∈ Finset.range N,
      min ((2:ℝ)^(k+1)/4^K) ((2:ℝ)^(k+1)/4^k)) ≤ 6/2^K := by
  have hfour (k : ℕ) : (4:ℝ)^k = (2^k)^2 := by
    rw [← pow_mul,mul_comm k 2,pow_mul]
    norm_num
  have hnonneg (k : ℕ) : 0 ≤ min ((2:ℝ)^(k+1)/4^K) ((2:ℝ)^(k+1)/4^k) := by positivity
  calc
    _ ≤ ∑ k ∈ Finset.range (K+N),
        min ((2:ℝ)^(k+1)/4^K) ((2:ℝ)^(k+1)/4^k) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega))
      intro k _ _
      exact hnonneg k
    _ = (∑ k ∈ Finset.range K,
        min ((2:ℝ)^(k+1)/4^K) ((2:ℝ)^(k+1)/4^k)) +
        ∑ k ∈ Finset.range N,
        min ((2:ℝ)^(K+k+1)/4^K) ((2:ℝ)^(K+k+1)/4^(K+k)) :=
      Finset.sum_range_add _ _ _
    _ ≤ (∑ k ∈ Finset.range K, (2:ℝ)^(k+1)/4^K) +
        ∑ k ∈ Finset.range N, (2:ℝ)^(K+k+1)/4^(K+k) := by
      apply add_le_add
      · exact Finset.sum_le_sum (fun k _ => min_le_left _ _)
      · exact Finset.sum_le_sum (fun k _ => min_le_right _ _)
    _ ≤ 6/2^K := by
      have h1 : (∑ k ∈ Finset.range K, (2:ℝ)^(k+1)/4^K) =
          2*(2^K-1)/4^K := by
        simp only [pow_succ,mul_div_assoc]
        rw [← Finset.sum_mul,sum_two_pow]
        ring
      have h2 : (∑ k ∈ Finset.range N, (2:ℝ)^(K+k+1)/4^(K+k)) =
          2/2^K * (2-2/2^N) := by
        have he (k : ℕ) : (2:ℝ)^(K+k+1)/4^(K+k) = (2/2^K)*(1/2^k) := by
          rw [hfour,pow_succ,pow_add]
          field_simp
        simp_rw [he]
        rw [← Finset.mul_sum,sum_two_inv_pow]
      rw [h1,h2,hfour]
      have hpowK : (0:ℝ)<2^K := by positivity
      have hpowN : (0:ℝ)<2^N := by positivity
      have h1' : 2*((2:ℝ)^K-1)/((2:ℝ)^K)^2 ≤ 2/2^K := by
        apply (div_le_iff₀ (sq_pos_of_pos hpowK)).mpr
        field_simp
        nlinarith
      have h2' : (2/(2:ℝ)^K) * (2-2/2^N) ≤ 4/2^K := by
        calc _ ≤ (2/(2:ℝ)^K)*2 := mul_le_mul_of_nonneg_left (by have := (div_nonneg (by norm_num : (0:ℝ)≤2) hpowN.le); linarith) (by positivity)
             _ = _ := by ring
      calc _ ≤ 2/(2:ℝ)^K+4/2^K := add_le_add h1' h2'
           _ = _ := by ring

end CriticalPercolation
end
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Exploration_SearchTree
attribute [-instance] _root_.OAI.CriticalPercolation.OrderedQuery.localNodeDecidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open Set
open scoped BigOperators
open scoped Classical

namespace CriticalPercolation

namespace SearchTree
variable {E R : Type*}

lemma reads_disjoint [DecidableEq E] (t : SearchTree E R) (used : Finset E) (h : t.Valid used)
    (ω : E → Bool) : ∀ e ∈ t.reads ω, e ∉ used := by
  induction t generalizing used with
  | done r => simp [reads]
  | ask e l r hl hr =>
    intro f hf
    rcases List.mem_cons.mp hf with rfl | hf
    · exact h.1
    · by_cases he : ω e = true
      · have hm : f ∈ r.reads ω := by simpa [reads,he] using hf
        exact fun hx => hr _ h.2.2 _ hm (Finset.mem_insert_of_mem hx)
      · have hm : f ∈ l.reads ω := by simpa [reads,he] using hf
        exact fun hx => hl _ h.2.1 _ hm (Finset.mem_insert_of_mem hx)

lemma reads_nodup [DecidableEq E] (t : SearchTree E R) (used : Finset E) (h : t.Valid used)
    (ω : E → Bool) : (t.reads ω).Nodup := by
  induction t generalizing used with
  | done r => simp [reads]
  | ask e l r hl hr =>
    rw [reads,List.nodup_cons]
    by_cases he : ω e = true
    · simp only [he,↓reduceIte]
      exact ⟨fun hm => reads_disjoint r _ h.2.2 ω e hm (Finset.mem_insert_self _ _), hr _ h.2.2⟩
    · simp only [he]
      exact ⟨fun hm => reads_disjoint l _ h.2.1 ω e hm (Finset.mem_insert_self _ _), hl _ h.2.1⟩
end SearchTree

end CriticalPercolation

end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_ProductMeasure_Density
attribute [-instance] _root_.OAI.CriticalPercolation.Priority.instFintypeOrder _root_.OAI.CriticalPercolation.QueryTree.leafFintype _root_.OAI.CriticalPercolation.QueryTree.nodeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators
open Set

namespace CriticalPercolation.FiniteProduct
variable {E A : Type*} [Fintype E] [Fintype A]

omit [Fintype A] in
lemma density_nonneg {w : E → A → ℝ} (h : ∀ e a, 0 ≤ w e a) (ω : E → A) :
    0 ≤ density w ω := Finset.prod_nonneg fun e _ => h e (ω e)

lemma sum_density [DecidableEq E] (w : E → A → ℝ) (h : ∀ e, ∑ a, w e a = 1) :
    ∑ ω, density w ω = 1 := by
  classical
  unfold density
  rw [← Fintype.prod_sum]
  simp [h]

lemma expect_const (w : E → A → ℝ) (h : ∀ e, ∑ a, w e a = 1) (c : ℝ) :
    expect w (fun _ => c) = c := by
  classical
  rw [expect, ← Finset.sum_mul, sum_density w h, one_mul]

lemma expect_add (w : E → A → ℝ) (f g : (E → A) → ℝ) :
    expect w (fun ω => f ω + g ω) = expect w f + expect w g := by
  classical
  simp [expect, mul_add, Finset.sum_add_distrib]

lemma expect_mono {w : E → A → ℝ} (hw : ∀ e a, 0 ≤ w e a)
    {f g : (E → A) → ℝ} (hfg : ∀ ω, f ω ≤ g ω) : expect w f ≤ expect w g := by
  classical
  exact Finset.sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left (hfg ω) (density_nonneg hw ω)

lemma expect_mul_const (w : E → A → ℝ) (f : (E → A) → ℝ) (c : ℝ) :
    expect w (fun ω => f ω * c) = expect w f * c := by
  classical
  unfold expect
  rw [Finset.sum_mul]
  apply Finset.sum_congr (by ext; simp)
  intro ω _
  ring

end CriticalPercolation.FiniteProduct

end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_ProductMeasure_Distribution
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open Set
open scoped BigOperators

namespace CriticalPercolation.FiniteProduct
variable {E A : Type*} [Fintype E] [Fintype A]
lemma expect_const_mul (w : E → A → ℝ) (c : ℝ) (f : (E → A) → ℝ) :
    expect w (fun ω => c * f ω) = c * expect w f := by
  simp only [mul_comm c]
  exact expect_mul_const w f c
end CriticalPercolation.FiniteProduct

end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_ProductMeasure_FiniteProductPin
attribute [-instance] _root_.OAI.CriticalPercolation.Priority.instFintypeOrder _root_.OAI.CriticalPercolation.QueryTree.leafFintype _root_.OAI.CriticalPercolation.QueryTree.nodeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open Set
open scoped BigOperators
open scoped Classical

namespace CriticalPercolation.FiniteProduct
open scoped Classical

variable {E A : Type*} [Fintype E] [Fintype A]

omit [Fintype E] in
lemma pin_normalized (w : E → A → ℝ) (hw : ∀ e, ∑ a, w e a = 1) (e : E) (b : A) :
    ∀ j, ∑ a, pin w e b j a = 1 := by
  intro j
  by_cases h : j = e
  · subst j; simp [pin]
  · simpa [pin,h] using hw j

omit [Fintype A] in
lemma density_pin (w : E → A → ℝ) (e : E) (b : A) (ω : E → A) :
    density (pin w e b) ω =
      (if ω e = b then 1 else 0)*∏ j ∈ (Finset.univ : Finset E).erase e, w j (ω j) := by
  rw [density,← Finset.prod_erase_mul _ _ (Finset.mem_univ e)]
  simp only [pin,Function.update_self]
  have he : (∏ j ∈ (Finset.univ : Finset E).erase e, Function.update w e
      (fun a => if a = b then 1 else 0) j (ω j)) =
      ∏ j ∈ (Finset.univ : Finset E).erase e, w j (ω j) := by
    apply Finset.prod_congr rfl
    intro j hj
    rw [Function.update_of_ne (Finset.mem_erase.mp hj).1]
  rw [he,mul_comm]

lemma expect_mask_pin (w : E → A → ℝ) (e : E) (b : A) (f : (E → A) → ℝ) :
    expect w (fun ω => if ω e = b then f ω else 0) = w e b*expect (pin w e b) f := by
  unfold expect
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ω _
  rw [density_pin]
  dsimp only
  by_cases h : ω e = b
  · rw [ite_eq_left h,ite_eq_left h,one_mul]
    rw [density,← Finset.prod_erase_mul _ _ (Finset.mem_univ e),h]
    ring
  · simp [h]

end CriticalPercolation.FiniteProduct

end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_ProductMeasure_Potential
attribute [-instance] _root_.OAI.CriticalPercolation.Priority.instFintypeOrder _root_.OAI.CriticalPercolation.QueryTree.leafFintype _root_.OAI.CriticalPercolation.QueryTree.nodeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open Set
open scoped BigOperators
open scoped Classical

namespace CriticalPercolation.FiniteProduct
open scoped Classical

variable {E : Type*} [Fintype E]

lemma expect_prop_mask_pin (w : E → Prop → ℝ) (e : E) (b : Prop) (f : (E → Prop) → ℝ) :
    expect w (fun ω => if ω e = b then f ω else 0) = w e b*expect (pin w e b) f := by
  convert expect_mask_pin w e b f using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  funext ω
  by_cases h : ω e = b <;> simp [h]

end CriticalPercolation.FiniteProduct

end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Exploration_Score
attribute [-instance] _root_.OAI.CriticalPercolation.Priority.instFintypeOrder _root_.OAI.CriticalPercolation.QueryTree.leafFintype _root_.OAI.CriticalPercolation.QueryTree.nodeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open Set
open scoped BigOperators
open scoped Classical

namespace CriticalPercolation.SearchTree
open scoped Classical
open FiniteProduct

variable {E R : Type*} [Fintype E]

lemma expect_prop_ite (w : E → Prop → ℝ) (e : E) (f g : Set E → ℝ) :
    expect w (fun ω => if ω e then f ω else g ω) =
      w e True*expect (pin w e True) f+w e False*expect (pin w e False) g := by
  calc
    _ = expect w (fun ω => (if ω e = True then f ω else 0) +
        (if ω e = False then g ω else 0)) := by
      congr 1
      funext ω
      by_cases h : ω e <;> simp [h]
    _ = _ := by
      rw [expect_add]
      apply congrArg₂ (· + ·)
      · convert expect_prop_mask_pin w e True f using 1
        all_goals try with_reducible_and_instances rfl
        congr 1
        funext ω
        by_cases h : ω e <;> simp [h]
      · convert expect_prop_mask_pin w e False g using 1
        all_goals try with_reducible_and_instances rfl
        congr 1
        funext ω
        by_cases h : ω e <;> simp [h]

end CriticalPercolation.SearchTree

namespace CriticalPercolation.LazyDFS
open scoped Classical
open FiniteProduct SearchTree

variable {V E : Type*} [Fintype E] [DecidableEq V] [DecidableEq E]

omit [Fintype E] [DecidableEq V] in
lemma fresh_pin (w : E → Prop → ℝ) (p : ℝ) (read : Finset E) (hf : Fresh w p read)
    (e : E) (b : Prop) : Fresh (pin w e b) p (insert e read) := by
  intro j hj
  have hj' : j ≠ e ∧ j ∉ read := by simpa only [Finset.mem_insert,not_or] using hj
  have hje : j ≠ e := hj'.1
  unfold pin
  simp only [Function.update,dite_eq_right hje]
  exact hf j hj'.2

end CriticalPercolation.LazyDFS

end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Exploration_ClosedFresh
attribute [-instance] _root_.OAI.CriticalPercolation.Priority.instFintypeOrder _root_.OAI.CriticalPercolation.QueryTree.leafFintype _root_.OAI.CriticalPercolation.QueryTree.nodeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open Set
open scoped BigOperators
open scoped Classical

namespace CriticalPercolation.SearchTree
open scoped Classical
open FiniteProduct LazyDFS

variable {E R : Type*} [Fintype E] [DecidableEq E]

omit [DecidableEq E] in
lemma expect_square_add_const (v : E → Prop → ℝ) (hv : ∀ e, ∑ b, v e b = 1)
    (a : ℝ) (f : (E → Prop) → ℝ) :
    expect v (fun ω => (a+f ω)^2) = a^2+2*a*expect v f+expect v (fun ω => (f ω)^2) := by
  have heq : (fun ω => (a+f ω)^2) = (fun ω => a^2+2*a*f ω+(f ω)^2) := by
    funext ω; ring
  rw [heq,expect_add,expect_add,expect_const v hv,expect_const_mul]

end CriticalPercolation.SearchTree

end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Modular_WeightedCauchy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open Real
open Set Real
open scoped Topology
open scoped BigOperators
open Set
open Set MeasureTheory
open Set MeasureTheory Real
open scoped Interval
open scoped Classical

namespace CriticalPercolation.FiniteEntropy
variable {X A : Type*} [Fintype X] [Fintype A]

lemma weighted_cauchy (w f g : X → ℝ) (hw : ∀ x, 0 ≤ w x) :
    (∑ x, w x * f x * g x)^2 ≤ (∑ x, w x * (f x)^2) * ∑ x, w x * (g x)^2 := by
  apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
  · intro x _; exact mul_nonneg (hw x) (sq_nonneg _)
  · intro x _; exact mul_nonneg (hw x) (sq_nonneg _)
  · intro x _; apply le_of_eq; ring

end CriticalPercolation.FiniteEntropy

end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_ProductMeasure_QueryMartingale
attribute [-instance] _root_.OAI.CriticalPercolation.Priority.instFintypeOrder _root_.OAI.CriticalPercolation.QueryTree.leafFintype _root_.OAI.CriticalPercolation.QueryTree.nodeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
namespace CriticalPercolation.SearchTree
open scoped Classical
open FiniteProduct

variable {E R : Type*}

lemma truncate_valid [DecidableEq E] (t : SearchTree E R) (n : ℕ) (used : Finset E)
    (h : t.Valid used) : (t.truncate n).Valid used := by
  induction n generalizing t used with
  | zero => simp [truncate,Valid]
  | succ n ih =>
    cases t with
    | done r => trivial
    | ask e l r => exact ⟨h.1, ih l _ h.2.1, ih r _ h.2.2⟩

lemma queryCount_truncate_le (t : SearchTree E R) (n : ℕ) (ω : E → Prop) :
    (t.truncate n).queryCount ω ≤ n := by
  induction n generalizing t with
  | zero => simp [truncate,queryCount]
  | succ n ih =>
    cases t with
    | done r => simp [truncate,queryCount]
    | ask e l r =>
      simp only [truncate,queryCount]
      split_ifs <;> have := ih r <;> have := ih l <;> omega

lemma centeredSum_truncate_eq (t : SearchTree E R) (n : ℕ) (ω : E → Prop)
    (h : t.queryCount ω ≤ n) (p : ℝ) :
    (t.truncate n).centeredSum p ω = t.centeredSum p ω := by
  induction n generalizing t with
  | zero =>
    cases t with
    | done r => rfl
    | ask e l r => simp [queryCount] at h
  | succ n ih =>
    cases t with
    | done r => rfl
    | ask e l r =>
      by_cases he : ω e
      · simp only [queryCount,ite_eq_left he] at h
        simp only [truncate,centeredSum,ite_eq_left he]
        rw [ih r (by omega)]
      · simp only [queryCount,ite_eq_right he] at h
        simp only [truncate,centeredSum,ite_eq_right he]
        rw [ih l (by omega)]

variable [Fintype E] [DecidableEq E]

lemma centeredSum_moments (t : SearchTree E R) (used : Finset E) (ht : t.Valid used)
    (p : ℝ) (w : E → Prop → ℝ) (hw : ∀ e, ∑ b, w e b = 1)
    (hf : LazyDFS.Fresh w p used) :
    expect w (t.centeredSum p) = 0 ∧
      expect w (fun ω => (t.centeredSum p ω)^2) =
        p*(1-p)*expect w (fun ω => (t.queryCount ω : ℝ)) := by
  induction t generalizing used w with
  | done r => simp [centeredSum,queryCount,expect_const w hw]
  | ask e l r hl hr =>
    have h0 := hl (insert e used) ht.2.1 (pin w e False)
      (pin_normalized w hw e False) (LazyDFS.fresh_pin w p used hf e False)
    have h1 := hr (insert e used) ht.2.2 (pin w e True)
      (pin_normalized w hw e True) (LazyDFS.fresh_pin w p used hf e True)
    have he := hf e ht.1
    constructor
    · simp only [centeredSum]
      erw [expect_prop_ite]
      simp only [expect_add, expect_const _ (pin_normalized w hw e False),
        expect_const _ (pin_normalized w hw e True),h0.1,h1.1,he.1,he.2]
      ring
    · have hx : (fun ω => ((.ask e l r : SearchTree E R).centeredSum p ω)^2) =
          (fun ω => if ω e then ((1-p)+r.centeredSum p ω)^2
            else (-p+l.centeredSum p ω)^2) := by funext ω; simp only [centeredSum]; split_ifs <;> rfl
      rw [hx]
      erw [expect_prop_ite,
        expect_square_add_const _ (pin_normalized w hw e False),
        expect_square_add_const _ (pin_normalized w hw e True),h0.1,h1.1,h0.2,h1.2,he.1,he.2]
      have hc : (fun ω => ((.ask e l r : SearchTree E R).queryCount ω : ℝ)) =
          (fun ω => 1+(if ω e then (r.queryCount ω : ℝ) else (l.queryCount ω : ℝ))) := by
        funext ω; simp only [queryCount]; split_ifs <;> simp
      rw [hc,expect_add]
      erw [expect_prop_ite,expect_const w hw,he.1,he.2]
      ring

lemma truncated_second_le (t : SearchTree E R) (used : Finset E) (ht : t.Valid used)
    (p : ℝ) (hp : p ∈ Set.Icc 0 1) (w : E → Prop → ℝ)
    (hw : ∀ e, ∑ b, w e b = 1) (hn : ∀ e b, 0 ≤ w e b)
    (hf : LazyDFS.Fresh w p used) (n : ℕ) :
    expect w (fun ω => ((t.truncate n).centeredSum p ω)^2) ≤ p*(1-p)*n := by
  rw [(t.truncate n).centeredSum_moments used (t.truncate_valid n used ht) p w hw hf |>.2]
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg hp.1 (sub_nonneg.mpr hp.2))
  calc expect w (fun ω => ((t.truncate n).queryCount ω : ℝ)) ≤ expect w (fun _ => (n:ℝ)) :=
        expect_mono hn (fun ω => Nat.cast_le.mpr (t.queryCount_truncate_le n ω))
       _ = n := expect_const w hw _

end CriticalPercolation.SearchTree
end
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Exploration_QueryBand
attribute [-instance] _root_.OAI.CriticalPercolation.Priority.instFintypeOrder _root_.OAI.CriticalPercolation.QueryTree.leafFintype _root_.OAI.CriticalPercolation.QueryTree.nodeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
namespace CriticalPercolation.FiniteProduct
open scoped Classical

variable {E : Type*} [Fintype E]

lemma expect_abs_sq_le (w : E → Prop → ℝ) (hw : ∀ e, ∑ b, w e b = 1)
    (hn : ∀ e b, 0≤w e b) (f : (E → Prop) → ℝ) :
    (expect w (fun ω => |f ω|))^2 ≤ expect w (fun ω => (f ω)^2) := by
  have h := FiniteEntropy.weighted_cauchy (density w) (fun ω => |f ω|) (fun _ => 1)
    (fun ω => density_nonneg hn ω)
  simp only [mul_one,one_pow,sq_abs] at h
  have hw1 : ∑ ω, density w ω = 1 := by
    simpa only [expect,mul_one] using expect_const w hw (1:ℝ)
  simpa only [hw1,mul_one,expect] using h

lemma expect_abs_le_of_second_le (w : E → Prop → ℝ) (hw : ∀ e, ∑ b, w e b = 1)
    (hn : ∀ e b, 0≤w e b) (f : (E → Prop) → ℝ) {a : ℝ} (ha : 0≤a)
    (hf : expect w (fun ω => (f ω)^2) ≤ a^2) : expect w (fun ω => |f ω|) ≤ a := by
  nlinarith [expect_abs_sq_le w hw hn f]

end CriticalPercolation.FiniteProduct
namespace CriticalPercolation.SearchTree
open scoped Classical
open FiniteProduct

variable {E R : Type*}

lemma queryCount_eq_reads_length (t : SearchTree E R) (ω : E → Prop) :
    t.queryCount ω = (t.reads (fun e => decide (ω e))).length := by
  induction t with
  | done r => rfl
  | ask e l r hl hr =>
    by_cases he : ω e <;> simp [queryCount,reads,he,hl,hr,Nat.add_comm]

lemma centeredSum_eq_zero_of_count (t : SearchTree E R) (ω : E → Prop)
    (h : t.queryCount ω = 0) (p : ℝ) : t.centeredSum p ω = 0 := by
  cases t with
  | done r => rfl
  | ask e l r => simp [queryCount] at h

variable [Fintype E] [DecidableEq E]

lemma queryCount_le_card (t : SearchTree E R) (used : Finset E) (ht : t.Valid used)
    (ω : E → Prop) : t.queryCount ω ≤ Fintype.card E := by
  rw [queryCount_eq_reads_length]
  exact List.Nodup.length_le_card (t.reads_nodup used ht _)

lemma band_centered_bound (t : SearchTree E R) (used : Finset E) (ht : t.Valid used)
    (p : ℝ) (hp : p ∈ Set.Icc 0 1) (w : E → Prop → ℝ)
    (hw : ∀ e, ∑ b, w e b = 1) (hn : ∀ e b, 0≤w e b)
    (hf : LazyDFS.Fresh w p used) (k : ℕ) :
    expect w (fun ω => if 4^k ≤ t.queryCount ω ∧ t.queryCount ω < 4^(k+1)
      then |t.centeredSum p ω| else 0) ≤ (2:ℝ)^(k+1) := by
  calc
    _ ≤ expect w (fun ω => |(t.truncate (4^(k+1))).centeredSum p ω|) := by
      apply expect_mono hn
      intro ω
      split_ifs with h
      · rw [t.centeredSum_truncate_eq _ ω h.2.le p]
      · exact abs_nonneg _
    _ ≤ (2:ℝ)^(k+1) := by
      apply expect_abs_le_of_second_le w hw hn _ (by positivity)
      have ht' := t.truncated_second_le used ht p hp w hw hn hf (4^(k+1))
      have hpp : p*(1-p) ≤ 1 := by nlinarith [hp.2,sq_nonneg p]
      have hN : (4^(k+1) : ℝ) = ((2:ℝ)^(k+1))^2 := by
        rw [← pow_mul, mul_comm (k+1) 2, pow_mul]
        norm_num
      calc _ ≤ p*(1-p)*(4^(k+1) : ℕ) := ht'
           _ ≤ (4^(k+1) : ℝ) := by
             simpa using mul_le_mul_of_nonneg_right hpp (by positivity : 0≤(4^(k+1):ℝ))
           _ = _ := hN

end CriticalPercolation.SearchTree
end
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Exploration_QueryNormalized
attribute [-instance] _root_.OAI.CriticalPercolation.Priority.instFintypeOrder _root_.OAI.CriticalPercolation.QueryTree.leafFintype _root_.OAI.CriticalPercolation.QueryTree.nodeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
namespace CriticalPercolation.SearchTree
open scoped Classical
open FiniteProduct

variable {E R : Type*} [Fintype E] [DecidableEq E]

lemma normalized_centered_bound_oai (t : SearchTree E R) (used : Finset E) (ht : t.Valid used)
    (p : ℝ) (hp : p ∈ Set.Icc 0 1) (w : E → Prop → ℝ)
    (hw : ∀ e, ∑ b, w e b = 1) (hn : ∀ e b, 0≤w e b)
    (hf : LazyDFS.Fresh w p used) (K : ℕ) :
    expect w (fun ω => |t.centeredSum p ω| *
      min (1/(4:ℝ)^K) (1/(t.queryCount ω : ℝ))) ≤ 6/(2:ℝ)^K := by
  let N := Fintype.card E + 1
  let a (k : ℕ) := min (1/(4:ℝ)^K) (1/(4:ℝ)^k)
  let b (k : ℕ) (ω : E → Prop) :=
    if 4^k ≤ t.queryCount ω ∧ t.queryCount ω < 4^(k+1)
      then |t.centeredSum p ω| else 0
  have ha (k : ℕ) : 0≤a k := by dsimp [a] <;> positivity
  have hb (k : ℕ) (ω : E → Prop) : 0≤b k ω := by
    dsimp [b]; split_ifs <;> positivity
  have hpoint (ω : E → Prop) : |t.centeredSum p ω| *
      min (1/(4:ℝ)^K) (1/(t.queryCount ω : ℝ)) ≤
        ∑ k ∈ Finset.range N, b k ω * a k := by
    by_cases hT : t.queryCount ω = 0
    · rw [t.centeredSum_eq_zero_of_count ω hT p,abs_zero,zero_mul]
      exact Finset.sum_nonneg (fun k _ => mul_nonneg (hb k ω) (ha k))
    · let k := Nat.log 4 (t.queryCount ω)
      have hklo : 4^k ≤ t.queryCount ω := Nat.pow_log_le_self 4 hT
      have hkhi : t.queryCount ω < 4^(k+1) := Nat.lt_pow_succ_log_self (by omega) _
      have hkN : k ∈ Finset.range N := by
        apply Finset.mem_range.mpr
        have h1 := Nat.log_le_self 4 (t.queryCount ω)
        have h2 := t.queryCount_le_card used ht ω
        dsimp [k,N]
        omega
      calc
        _ ≤ b k ω * a k := by
          have hband : 4^k ≤ t.queryCount ω ∧ t.queryCount ω < 4^(k+1) := ⟨hklo,hkhi⟩
          simp only [b,ite_eq_left hband]
          apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
          apply min_le_min le_rfl
          apply one_div_le_one_div_of_le (by positivity : (0:ℝ)<(4:ℝ)^k)
          exact_mod_cast hklo
        _ ≤ _ := Finset.single_le_sum (fun j _ => mul_nonneg (hb j ω) (ha j)) hkN
  calc
    _ ≤ expect w (fun ω => ∑ k ∈ Finset.range N, b k ω * a k) := expect_mono hn hpoint
    _ = ∑ k ∈ Finset.range N, expect w (b k) * a k := by
      simp only [expect,Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k _
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro ω _
      ring
    _ ≤ ∑ k ∈ Finset.range N, (2:ℝ)^(k+1)*a k := by
      apply Finset.sum_le_sum
      intro k _
      exact mul_le_mul_of_nonneg_right (t.band_centered_bound used ht p hp w hw hn hf k) (ha k)
    _ = ∑ k ∈ Finset.range N,
        min ((2:ℝ)^(k+1)/4^K) ((2:ℝ)^(k+1)/4^k) := by
      apply Finset.sum_congr rfl
      intro k _
      dsimp [a]
      rw [mul_min_of_nonneg _ _ (by positivity)]
      simp only [mul_one_div]
    _ ≤ _ := dyadic_sum_bound N K

end CriticalPercolation.SearchTree
end
end
end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.CriticalPercolation.SearchTree.normalized_centered_bound_oai.{u_1, u_2} := @OAI.CriticalPercolation.SearchTree.normalized_centered_bound_oai.{u_1, u_2}
