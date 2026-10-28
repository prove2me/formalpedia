-- Prove2me | solution 1 for OAI.DilutedSpinGlass.UniversalDictionary.regular_node_pointwise_sat
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T06:40:39.332529+00:00
-- url     : https://prove2.me/submissions/187b5198-e15f-44b8-b8f9-0f32ea0d5cd5

import Mathlib
import Definitions.Def_DilutedSpin
import Definitions.Def_OAIQ041D000
import Definitions.Def_OAIQ067A000
import Theorems.Thm_OAI_DilutedSpinGlass_UniversalDictionary_physical_grid_scheduled_step

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_FiniteLaw
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open _root_.MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology
attribute [local instance] DilutedSpinGlass.instMeasurableSpaceCarrier_challenge DilutedSpinGlass.instBorelSpaceCarrier_challenge
namespace DilutedSpinGlass

namespace FiniteLaw

variable {Ω : Type*} [Fintype Ω] (P : FiniteLaw Ω)

theorem covariance_centered (f g : Ω → ℝ) :
    P.covariance f g = P.expect (fun x => (f x - P.expect f) * (g x - P.expect g)) := by
  rw [covariance]
  calc
    _ = P.expect (fun x => f x * g x - f x * P.expect g -
        P.expect f * g x + P.expect f * P.expect g) := by simp
    _ = _ := P.expect_congr (fun x => by ring)

variable {n : ℕ}

/-- Finite-law Cauchy-Schwarz. -/
theorem expect_mul_sq_le (f g : Ω → ℝ) :
    P.expect (fun x => f x * g x)^2 ≤
      P.expect (fun x => f x^2) * P.expect (fun x => g x^2) := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun x => Real.sqrt (P.weight x) * f x)
    (fun x => Real.sqrt (P.weight x) * g x)
  have hm (x : Ω) : Real.sqrt (P.weight x) * f x *
      (Real.sqrt (P.weight x) * g x) = P.weight x * (f x * g x) := by
    calc
      _ = Real.sqrt (P.weight x)^2 * (f x * g x) := by ring
      _ = _ := by rw [Real.sq_sqrt (P.nonneg x)]
  simpa only [hm, mul_pow, Real.sq_sqrt (P.nonneg _), expect] using h

end FiniteLaw
end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_TreeDerivatives
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.edgeFintype _root_.OAI.DilutedSpinGlass.PrescribedTree.leafDecidableEq _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open _root_.MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology
attribute [local instance] DilutedSpinGlass.instMeasurableSpaceCarrier_challenge DilutedSpinGlass.instBorelSpaceCarrier_challenge

namespace DilutedSpinGlass.PrescribedTree

/-- The exact signed budget for internal extensions with finite exponent indices. -/
theorem sum_gamma {n : ℕ} (S : PrescribedTree n) (m : Fin (n+1) → ℝ) :
    (∑ v : Internal S, gamma S m v) = m 0 - (leaves S : ℝ) * m (Fin.last n) := by
  induction S with
  | leaf =>
    change (∑ v : Empty, gamma .leaf m v) = _
    have hs : (∑ v : Empty, gamma .leaf m v) = 0 :=
      Finset.sum_eq_zero (fun v _ => nomatch v)
    rw [hs]
    simp [leaves, Fin.last_zero]
  | @node n k C ih =>
    change (∑ v : Option ((i : Fin k) × Internal (C i)), _) = _
    erw [Fintype.sum_option, Fintype.sum_sigma]
    change m 0 - (k : ℝ) * m 1 +
      (∑ i, ∑ v : Internal (C i), gamma (C i) (fun j => m j.succ) v) = _
    simp_rw [ih]
    simp only [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul,
      Finset.card_univ, Fintype.card_fin, leaves, Nat.cast_sum, Fin.succ_last, Fin.succ_zero_eq_one]
    rw [← Finset.sum_mul]
    ring

theorem gamma_nonpos {n : ℕ} (S : PrescribedTree n) (m : Fin (n+1) → ℝ)
    (hm : Monotone m) (hpos : ∀ j, 0 ≤ m j) (v : Internal S) : gamma S m v ≤ 0 := by
  induction S with
  | leaf => nomatch v
  | @node n k C ih =>
    change Option ((i : Fin k) × Internal (C i)) at v
    cases v with
    | none =>
      change m 0 - (k : ℝ) * m 1 ≤ 0
      have hh : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast k.property
      have h01 := hm (show (0 : Fin (n+2)) ≤ 1 by exact Fin.zero_le _)
      nlinarith [mul_nonneg (sub_nonneg.mpr hh) (hpos 1)]
    | some v =>
      obtain ⟨i,v⟩ := v
      exact ih i (fun j => m j.succ) (fun a b h => hm (Fin.succ_le_succ_iff.mpr h))
        (fun j => hpos j.succ) v

/-- Absolute coefficients sum to the number of old leaves. -/
theorem sum_abs_gamma {n : ℕ} (S : PrescribedTree n) (m : Fin (n+1) → ℝ)
    (hm : Monotone m) (hpos : ∀ j, 0 ≤ m j)
    (hroot : m 0 = 0) (hend : m (Fin.last n) = 1) :
    (∑ v : Internal S, |gamma S m v|) = (leaves S : ℝ) := by
  simp_rw [abs_of_nonpos (gamma_nonpos S m hm hpos _)]
  rw [Finset.sum_neg_distrib, sum_gamma, hroot, hend]
  ring

end DilutedSpinGlass.PrescribedTree

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_HistoryGeometry
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.edgeFintype _root_.OAI.DilutedSpinGlass.PrescribedTree.leafDecidableEq _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped BigOperators

namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators

attribute [local instance] OAI.DilutedSpinGlass.PrescribedTree.instDecidable
/-- Full cancellation inside a reference-free subtree, indexed by actual
leaf positions and actual internal vertices. -/
theorem all_choices_total {n : ℕ} (S : PrescribedTree n) (m : Fin (n+1) → ℝ)
    (hend : m (Fin.last n) = 1) :
    (∑ _a : Leaf S, (1 : ℝ)) + (∑ v : Internal S, gamma S m v) = m 0 := by
  have hcard : Fintype.card (Leaf S) = leaves S := by
    clear hend m
    induction S with
    | leaf => exact Fintype.card_unit
    | @node height arity children inductionHypotheses =>
      change Fintype.card ((index : Fin arity) × Leaf (children index)) = _
      simp [Fintype.card_sigma, leaves, inductionHypotheses]
  rw [sum_gamma]
  simp only [Finset.sum_const, Finset.card_univ, hcard, nsmul_eq_mul, mul_one, hend]
  ring

/-- The signed normalizing sum of ALL eligible old-or-fresh choices with a
specified deepest reference prefix is independent of all unused old branches.
Unlike reference_total, this is stated on the actual global choice indices. -/
theorem divergence_choice_total {n : ℕ} {S : PrescribedTree n}
    (D : Divergence S) (m : Fin (n+1) → ℝ) (hend : m (Fin.last n) = 1) :
    (∑ a : Leaf S, if D.oldAllowed a then (1 : ℝ) else 0) +
      (∑ v : Internal S, if D.freshAllowed v then gamma S m v else 0) = D.coefficient m := by
  induction D with
  | @here n k C J =>
    change (∑ a : (i : Fin k) × Leaf (C i), _) +
      (∑ v : Option ((i : Fin k) × Internal (C i)), _) = _
    rw [Fintype.sum_sigma, Fintype.sum_option, Fintype.sum_sigma]
    have ho_def (i : Fin k) (a : Leaf (C i)) :
        (Divergence.here J : Divergence (.node k C)).oldAllowed (⟨i,a⟩ : Leaf (.node k C)) ↔ i ∉ J := by
      erw [Divergence.oldAllowed.eq_1]
    simp_rw [ho_def]
    simp! only [Divergence.freshAllowed, Divergence.coefficient, gamma, ite_true]
    change (∑ i, ∑ _a : Leaf (C i), if i ∉ J then (1:ℝ) else 0) +
      (m 0 - (k:ℝ)*m 1 + ∑ i, ∑ v : Internal (C i),
        if i ∉ J then gamma (C i) (fun j => m j.succ) v else 0) =
      m 0 - (J.card:ℝ)*m 1
    have hm' : (fun j : Fin (n+1) => m j.succ) (Fin.last n) = 1 := hend
    have ht (i : Fin k) :
        (∑ a : Leaf (C i), if i ∉ J then (1:ℝ) else 0) +
          (∑ v : Internal (C i), if i ∉ J then gamma (C i) (fun j => m j.succ) v else 0) =
          if i ∉ J then m 1 else 0 := by
      by_cases hi : i ∉ J
      · simp only [hi]
        exact all_choices_total (C i) _ hm'
      · simp only [hi, ite_false, Finset.sum_const_zero, zero_add]
    calc
      _ = m 0 - (k:ℝ)*m 1 + ∑ i, (
          (∑ a : Leaf (C i), if i ∉ J then (1:ℝ) else 0) +
          (∑ v : Internal (C i), if i ∉ J then gamma (C i) (fun j => m j.succ) v else 0)) := by
        rw [Finset.sum_add_distrib]; ring
      _ = m 0 - (k:ℝ)*m 1 + ∑ i : Fin k, if i ∉ J then m 1 else 0 := by simp_rw [ht]
      _ = _ := by
        rw [← Finset.sum_filter]
        have hset : Finset.univ.filter (fun i : Fin k => i ∉ J) = Finset.univ \ J := by ext i; simp
        rw [hset, Finset.sum_const, nsmul_eq_mul, Finset.card_sdiff, Finset.inter_univ,
          Nat.cast_sub (Finset.card_le_card (Finset.subset_univ J))]
        simp only [Finset.card_univ, Fintype.card_fin]
        ring
  | @descend n k C i D ih =>
    change (∑ a : (j : Fin k) × Leaf (C j), _) +
      (∑ v : Option ((j : Fin k) × Internal (C j)), _) = _
    rw [Fintype.sum_sigma, Fintype.sum_option, Fintype.sum_sigma]
    have ho_def (j : Fin k) (a : Leaf (C j)) :
        (Divergence.descend i D).oldAllowed (⟨j,a⟩ : Leaf (.node k C)) ↔
          ∃ h : j = i, D.oldAllowed (h ▸ a) := by
      erw [Divergence.oldAllowed.eq_2]
    simp_rw [ho_def]
    simp! only [Divergence.freshAllowed, Divergence.coefficient, gamma, ite_false]
    change (∑ j, ∑ a : Leaf (C j), if ∃ h : j = i, D.oldAllowed (h ▸ a) then (1:ℝ) else 0) +
      (0 + ∑ j, ∑ v : Internal (C j), if ∃ h : j = i, D.freshAllowed (h ▸ v) then
        gamma (C j) (fun q => m q.succ) v else 0) = D.coefficient (fun q => m q.succ)
    rw [zero_add]
    have ho (j : Fin k) :
        (∑ a : Leaf (C j), if ∃ h : j = i, D.oldAllowed (h ▸ a) then (1:ℝ) else 0) =
          if j = i then (∑ a : Leaf (C i), if D.oldAllowed a then (1:ℝ) else 0) else 0 := by
      by_cases h : j = i
      · subst j; simp
      · simp [h]
    have hf (j : Fin k) :
        (∑ v : Internal (C j), if ∃ h : j = i, D.freshAllowed (h ▸ v) then
          gamma (C j) (fun q => m q.succ) v else 0) =
          if j = i then (∑ v : Internal (C i), if D.freshAllowed v then
            gamma (C i) (fun q => m q.succ) v else 0) else 0 := by
      by_cases h : j = i
      · subst j; simp
      · simp [h]
    simp_rw [ho, hf]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    exact ih _ hend

end DilutedSpinGlass.PrescribedTree

namespace DilutedSpinGlass.PrescribedTree

theorem splitDepth_cast {n : ℕ} (A B : PrescribedTree n) (h : B = A) (a b : Leaf A) :
    splitDepth B (cast (congrArg Leaf h.symm) a) (cast (congrArg Leaf h.symm) b) =
      splitDepth A a b := by
  subst B
  rfl

attribute [local instance] OAI.DilutedSpinGlass.PrescribedTree.instDecidable_1
/-- Fresh splitting refers to the enlarged tree's actual labeled positions. -/
theorem splitDepth_new_old {n : ℕ} (S : PrescribedTree n) (v : Internal S) (a : Leaf S) :
    splitDepth (grow S v) (newLeaf S v) (oldLeaf S v a) = freshSplitDepth S v a := by
  induction S with
  | leaf => exact v.elim
  | @node n k C ih =>
    change Option ((i : Fin k) × Internal (C i)) at v
    cases v with
    | none =>
      change (if h : (0 : Fin (k+1)) = a.1.succ then _ else 0) = 0
      rw [dite_eq_right (Ne.symm (Fin.succ_ne_zero a.1))]
    | some v =>
      obtain ⟨i,v⟩ := v
      obtain ⟨j,a⟩ := a
      by_cases h : j = i
      · subst j
        let C' := Function.update C i (grow (C i) v)
        have heq : C' i = grow (C i) v := Function.update_self ..
        have hc := splitDepth_cast (grow (C i) v) (C' i) heq
          (newLeaf (C i) v) (oldLeaf (C i) v a)
        erw [newLeaf.eq_1, oldLeaf.eq_1]
        dsimp only [id]
        simp only [dite_eq_left]
        change (if h : i = i then 1 + splitDepth (C' i)
          (cast (congrArg Leaf heq.symm) (newLeaf (C i) v))
          (cast (congrArg Leaf heq.symm) (oldLeaf (C i) v a)) else 0) =
          (if h : i = i then 1 + freshSplitDepth (C i) v a else 0)
        simp only
        rw [hc, ih]
      · erw [newLeaf.eq_1, oldLeaf.eq_1]
        dsimp only [id]
        simp only [dite_eq_right h]
        change (if h' : i = j then _ else 0) = (if h' : j = i then _ else 0)
        rw [dite_eq_right (Ne.symm h), dite_eq_right h]

end DilutedSpinGlass.PrescribedTree

namespace DilutedSpinGlass.PrescribedTree

attribute [local instance] OAI.DilutedSpinGlass.PrescribedTree.instDecidable_2
/-- Ancestry constraints with ALL existing references, not merely a local
subtree, are exactly the global eligible-old-leaf selector. -/
theorem referenceDivergence_oldAllowed {n : ℕ} (S : PrescribedTree n)
    (a : Leaf S) (d : ℕ) (hd : d < n) (R : Finset (Leaf S)) (ha : a ∈ R) (b : Leaf S) :
    (referenceDivergence S a d hd R).oldAllowed b ↔ matchesOldProfile S R a d b := by
  induction S generalizing d with
  | leaf => omega
  | @node n k C ih =>
    cases d with
    | zero =>
      change b.1 ∉ R.image (fun a => a.1) ↔
        ∀ r ∈ R, splitDepth (.node k C) b r = 0
      constructor
      · intro h r hr
        apply (splitDepth_node_zero C b r).mpr
        intro heq
        exact h (Finset.mem_image.mpr ⟨r,hr,heq.symm⟩)
      · intro h hb
        obtain ⟨r,hr,heq⟩ := Finset.mem_image.mp hb
        exact ((splitDepth_node_zero C b r).mp (h r hr)) heq.symm
    | succ d =>
      obtain ⟨i,a⟩ := a
      obtain ⟨j,b⟩ := b
      have hd' : d < n := by omega
      by_cases hji : j = i
      · subst j
        have hchild : a ∈ childRefs R i := (mem_childRefs R i a).mpr ha
        have hreduce : (referenceDivergence (.node k C) ⟨i,a⟩ (d+1) hd R).oldAllowed ⟨i,b⟩ ↔
            (referenceDivergence (C i) a d hd' (childRefs R i)).oldAllowed b := by
          change (∃ h : i = i,
            (referenceDivergence (C i) a d hd' (childRefs R i)).oldAllowed (h ▸ b)) ↔ _
          simp
        rw [hreduce, ih i a d hd' (childRefs R i) hchild b]
        constructor
        · intro h r hr
          obtain ⟨j,r⟩ := r
          by_cases hji : j = i
          · subst j
            have hh := h r ((mem_childRefs R i r).mpr hr)
            rw [splitDepth_same_child, splitDepth_same_child]
            omega
          · rw [splitDepth_diff_child C i j (Ne.symm hji),
              splitDepth_diff_child C i j (Ne.symm hji)]
            exact (Nat.min_zero _).symm
        · intro h r hr
          have hh := h ⟨i,r⟩ ((mem_childRefs R i r).mp hr)
          rw [splitDepth_same_child, splitDepth_same_child] at hh
          omega
      · have hnone : ¬(referenceDivergence (.node k C) ⟨i,a⟩ (d+1) hd R).oldAllowed ⟨j,b⟩ := by
          change ¬∃ h : j = i, _
          exact fun ⟨h,_⟩ => hji h
        rw [iff_false_left hnone]
        intro h
        have hh := h ⟨i,a⟩ ha
        rw [splitDepth_diff_child C j i hji] at hh
        have hhself : splitDepth (.node k C) (⟨i,a⟩ : Leaf (.node k C)) ⟨i,a⟩ = n+1 :=
          splitDepth_self _ _
        rw [hhself] at hh
        omega

end DilutedSpinGlass.PrescribedTree

namespace DilutedSpinGlass.PrescribedTree

attribute [local instance] OAI.DilutedSpinGlass.PrescribedTree.instDecidable_3
theorem freshSplitDepth_same_child {n : ℕ} {k : ℕ+} (C : Fin k → PrescribedTree n)
    (i : Fin k) (v : Internal (C i)) (a : Leaf (C i)) :
    freshSplitDepth (.node k C) (some ⟨i,v⟩) ⟨i,a⟩ = 1 + freshSplitDepth (C i) v a := by
  change (if h : i = i then 1 + freshSplitDepth (C i) v (h ▸ a) else 0) = _
  simp

theorem freshSplitDepth_diff_child {n : ℕ} {k : ℕ+} (C : Fin k → PrescribedTree n)
    (i j : Fin k) (hij : j ≠ i) (v : Internal (C i)) (a : Leaf (C j)) :
    freshSplitDepth (.node k C) (some ⟨i,v⟩) ⟨j,a⟩ = 0 := by
  change (if h : j = i then 1 + freshSplitDepth (C i) v (h ▸ a) else 0) = 0
  rw [dite_eq_right hij]

theorem freshSplitDepth_node_zero {n : ℕ} {k : ℕ+} (C : Fin k → PrescribedTree n)
    (i : Fin k) (v : Internal (C i)) (a : Leaf (.node k C)) :
    freshSplitDepth (.node k C) (some ⟨i,v⟩) a = 0 ↔ a.1 ≠ i := by
  obtain ⟨j,a⟩ := a
  by_cases h : j = i
  · subst j
    rw [freshSplitDepth_same_child]
    simp
  · rw [freshSplitDepth_diff_child C i j h]
    simp [h]

/-- Fresh divergences satisfy exactly the same all-reference positional profile
as the old-choice selector; the profile is also the actual new leaf's profile
in the enlarged tree, by splitDepth_new_old. -/
theorem referenceDivergence_freshAllowed {n : ℕ} (S : PrescribedTree n)
    (a : Leaf S) (d : ℕ) (hd : d < n) (R : Finset (Leaf S)) (ha : a ∈ R) (v : Internal S) :
    (referenceDivergence S a d hd R).freshAllowed v ↔ matchesFreshProfile S R a d v := by
  induction S generalizing d with
  | leaf => omega
  | @node n k C ih =>
    change Option ((i : Fin k) × Internal (C i)) at v
    cases d with
    | zero =>
      cases v with
      | none =>
        change True ↔ ∀ r ∈ R, (0 : ℕ) = 0
        simp
      | some v =>
        obtain ⟨i,v⟩ := v
        change i ∉ R.image (fun a => a.1) ↔
          ∀ r ∈ R, freshSplitDepth (.node k C) (some ⟨i,v⟩) r = 0
        constructor
        · intro h r hr
          apply (freshSplitDepth_node_zero C i v r).mpr
          intro heq
          exact h (Finset.mem_image.mpr ⟨r,hr,heq⟩)
        · intro h hb
          obtain ⟨r,hr,heq⟩ := Finset.mem_image.mp hb
          exact ((freshSplitDepth_node_zero C i v r).mp (h r hr)) heq
    | succ d =>
      obtain ⟨i,a⟩ := a
      have hd' : d < n := by omega
      cases v with
      | none =>
        change False ↔ _
        rw [false_iff]
        intro h
        have hh := h ⟨i,a⟩ ha
        change 0 = min (d+1) (splitDepth (.node k C) (⟨i,a⟩ : Leaf (.node k C)) ⟨i,a⟩) at hh
        have hhself : splitDepth (.node k C) (⟨i,a⟩ : Leaf (.node k C)) ⟨i,a⟩ = n+1 :=
          splitDepth_self _ _
        rw [hhself] at hh
        omega
      | some v =>
        obtain ⟨j,v⟩ := v
        by_cases hji : j = i
        · subst j
          have hchild : a ∈ childRefs R i := (mem_childRefs R i a).mpr ha
          have hreduce : (referenceDivergence (.node k C) ⟨i,a⟩ (d+1) hd R).freshAllowed (some ⟨i,v⟩) ↔
              (referenceDivergence (C i) a d hd' (childRefs R i)).freshAllowed v := by
            change (∃ h : i = i,
              (referenceDivergence (C i) a d hd' (childRefs R i)).freshAllowed (h ▸ v)) ↔ _
            simp
          rw [hreduce, ih i a d hd' (childRefs R i) hchild v]
          constructor
          · intro h r hr
            obtain ⟨j,r⟩ := r
            by_cases hji : j = i
            · subst j
              have hh := h r ((mem_childRefs R i r).mpr hr)
              rw [freshSplitDepth_same_child, splitDepth_same_child]
              omega
            · rw [freshSplitDepth_diff_child C i j hji,
                splitDepth_diff_child C i j (Ne.symm hji)]
              exact (Nat.min_zero _).symm
          · intro h r hr
            have hh := h ⟨i,r⟩ ((mem_childRefs R i r).mp hr)
            rw [freshSplitDepth_same_child, splitDepth_same_child] at hh
            omega
        · have hnone : ¬(referenceDivergence (.node k C) ⟨i,a⟩ (d+1) hd R).freshAllowed (some ⟨j,v⟩) := by
            change ¬∃ h : j = i, _
            exact fun ⟨h,_⟩ => hji h
          rw [iff_false_left hnone]
          intro h
          have hh := h ⟨i,a⟩ ha
          rw [freshSplitDepth_diff_child C j i (Ne.symm hji)] at hh
          have hhself : splitDepth (.node k C) (⟨i,a⟩ : Leaf (.node k C)) ⟨i,a⟩ = n+1 :=
            splitDepth_self _ _
          rw [hhself] at hh
          omega

/-- The reference-path normalizing identity over globally admissible old or
fresh labels. No conditioning on sampled spin values occurs in the selector. -/
theorem reference_profile_total {n : ℕ} (S : PrescribedTree n)
    (a : Leaf S) (d : ℕ) (hd : d < n) (R : Finset (Leaf S)) (ha : a ∈ R)
    (m : Fin (n+1) → ℝ) (hend : m (Fin.last n) = 1) :
    (∑ b : Leaf S, if matchesOldProfile S R a d b then (1 : ℝ) else 0) +
      (∑ v : Internal S, if matchesFreshProfile S R a d v then gamma S m v else 0) =
      (referenceDivergence S a d hd R).coefficient m := by
  simp_rw [← referenceDivergence_oldAllowed S a d hd R ha,
    ← referenceDivergence_freshAllowed S a d hd R ha]
  exact divergence_choice_total _ m hend

end DilutedSpinGlass.PrescribedTree

namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators

attribute [local instance] OAI.DilutedSpinGlass.PrescribedTree.instDecidable_5
/-- A finite number of represented equivalence classes depends only on the
kernel relation, not on their ambient set of representatives. -/
theorem card_image_of_same_kernel {ι α β : Type*} [DecidableEq ι]
    [DecidableEq α] [DecidableEq β] (R : Finset ι) (f : ι → α) (g : ι → β)
    (h : ∀ i ∈ R, ∀ j ∈ R, f i = f j ↔ g i = g j) :
    (R.image f).card = (R.image g).card := by
  induction R using Finset.induction_on with
  | empty => simp
  | @insert a R ha ih =>
    have hR : ∀ i ∈ R, ∀ j ∈ R, f i = f j ↔ g i = g j := by
      intro i hi j hj
      exact h i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj)
    have he : f a ∈ R.image f ↔ g a ∈ R.image g := by
      constructor
      · intro hh
        obtain ⟨i,hi,heq⟩ := Finset.mem_image.mp hh
        exact Finset.mem_image.mpr ⟨i,hi,(h i (Finset.mem_insert_of_mem hi) a
          (Finset.mem_insert_self ..)).mp heq⟩
      · intro hg
        obtain ⟨i,hi,heq⟩ := Finset.mem_image.mp hg
        exact Finset.mem_image.mpr ⟨i,hi,(h i (Finset.mem_insert_of_mem hi) a
          (Finset.mem_insert_self ..)).mpr heq⟩
    rw [Finset.image_insert, Finset.image_insert]
    by_cases hf : f a ∈ R.image f
    · rw [Finset.card_insert_of_mem hf, Finset.card_insert_of_mem (he.mp hf), ih hR]
    · rw [Finset.card_insert_of_notMem hf,
        Finset.card_insert_of_notMem (fun hg => hf (he.mpr hg)), ih hR]

theorem sigma_cast_snd {α : Type*} {β : α → Type*} (x : Sigma β) (i : α)
    (h : x.1 = i) : (⟨i,h ▸ x.2⟩ : Sigma β) = x := by
  obtain ⟨j,x⟩ := x
  dsimp at h
  subst i
  rfl

/-- Returning a restricted reference label to its original tree. -/
theorem childLabelLeaf_embed {n : ℕ} {k : ℕ+} {C : Fin k → PrescribedTree n}
    {ι : Type} (r : ι → Leaf (.node k C)) (i : Fin k) (l : ChildLabels r i) :
    (⟨i,childLabelLeaf r i l⟩ : Leaf (.node k C)) = r l.val := by
  exact sigma_cast_snd (r l.val) i l.property

/-- The child reference set really is the image of the child-restricted labels. -/
theorem childRefs_image {n : ℕ} {k : ℕ+} {C : Fin k → PrescribedTree n}
    {ι : Type} [Fintype ι] (r : ι → Leaf (.node k C)) (i : Fin k) :
    childRefs (Finset.univ.image r) i =
      Finset.univ.image (childLabelLeaf r i) := by
  classical
  ext b
  constructor
  · intro hb
    obtain ⟨l,_,hl⟩ := (Finset.mem_image (f := r)).mp ((mem_childRefs _ i b).mp hb)
    have hi : (r l).1 = i := congrArg Sigma.fst hl
    apply Finset.mem_image.mpr
    refine ⟨⟨l,hi⟩,Finset.mem_univ _, ?_⟩
    have he := (childLabelLeaf_embed r i ⟨l,hi⟩).trans hl
    exact eq_of_heq ((Sigma.mk.inj_iff.mp he).2)
  · intro hb
    obtain ⟨l,_,hl⟩ := Finset.mem_image.mp hb
    apply (mem_childRefs _ i b).mpr
    exact (Finset.mem_image (f := r)).mpr ⟨l.val,Finset.mem_univ _, by
      rw [← childLabelLeaf_embed r i l, hl]⟩


/-- One-step signed reference normalization is determined by the entire
labeled splitting matrix, not by the unused old leaves of its realization. -/
theorem reference_coefficient_invariant {n : ℕ} (S T : PrescribedTree n)
    {ι : Type} [Fintype ι] (r : ι → Leaf S) (s : ι → Leaf T) (a : ι)
    (hsplit : ∀ i j, splitDepth S (r i) (r j) = splitDepth T (s i) (s j))
    (d : ℕ) (hd : d < n) (m : Fin (n+1) → ℝ) :
    (referenceDivergence S (r a) d hd (Finset.univ.image r)).coefficient m =
      (referenceDivergence T (s a) d hd (Finset.univ.image s)).coefficient m := by
  classical
  induction n generalizing ι d with
  | zero => omega
  | succ n ih =>
    cases S with | node k C =>
    cases T with | node k' C' =>
    have hf (i j : ι) : (r i).1 = (r j).1 ↔ (s i).1 = (s j).1 := by
      have he := hsplit i j
      have hr := splitDepth_node_zero C (r i) (r j)
      have hs := splitDepth_node_zero C' (s i) (s j)
      rw [he] at hr
      tauto
    cases d with
    | zero =>
      change m 0 - (((Finset.univ.image r).image (fun b => b.1)).card : ℝ)*m 1 =
        m 0 - (((Finset.univ.image s).image (fun b => b.1)).card : ℝ)*m 1
      rw [Finset.image_image, Finset.image_image]
      have he := card_image_of_same_kernel Finset.univ (fun i => (r i).1)
        (fun i => (s i).1) (fun i _ j _ => hf i j)
      dsimp only [Function.comp_def]
      erw [he]
    | succ d =>
      let I := ChildLabels r (r a).1
      let rr : I → Leaf (C (r a).1) := childLabelLeaf r (r a).1
      let ss : I → Leaf (C' (s a).1) := fun l =>
        childLabelLeaf s (s a).1 ⟨l.val,(hf l.val a).mp l.property⟩
      let aa : I := ⟨a,rfl⟩
      have hr (i : I) : (⟨(r a).1,rr i⟩ : Leaf (.node k C)) = r i.val :=
        childLabelLeaf_embed r _ i
      have hs (i : I) : (⟨(s a).1,ss i⟩ : Leaf (.node k' C')) = s i.val :=
        childLabelLeaf_embed s _ _
      have hsplit' (i j : I) : splitDepth (C (r a).1) (rr i) (rr j) =
          splitDepth (C' (s a).1) (ss i) (ss j) := by
        have he := hsplit i.val j.val
        rw [← hr i, ← hr j, ← hs i, ← hs j,
          splitDepth_same_child, splitDepth_same_child] at he
        omega
      have hR := childRefs_image r (r a).1
      have hS : childRefs (Finset.univ.image s) (s a).1 = Finset.univ.image ss := by
        ext b
        constructor
        · intro hb
          obtain ⟨l,_,hl⟩ := (Finset.mem_image (f := s)).mp ((mem_childRefs _ _ b).mp hb)
          have hls : (s l).1 = (s a).1 := by
            have hh := congrArg (fun x : Leaf (.node k' C') => x.1) hl
            exact hh
          let l' : I := ⟨l,(hf l a).mpr hls⟩
          refine Finset.mem_image.mpr ⟨l',Finset.mem_univ _, ?_⟩
          have hh := (hs l').trans hl
          exact eq_of_heq ((Sigma.mk.inj_iff.mp hh).2)
        · intro hb
          obtain ⟨l,_,hl⟩ := Finset.mem_image.mp hb
          apply (mem_childRefs _ _ b).mpr
          exact (Finset.mem_image (f := s)).mpr ⟨l.val,Finset.mem_univ _, by rw [← hs l, hl]⟩
      have hd' : d < n := by omega
      change (referenceDivergence (C (r a).1) (r a).2 d hd'
        (childRefs (Finset.univ.image r) (r a).1)).coefficient (fun j => m j.succ) =
        (referenceDivergence (C' (s a).1) (s a).2 d hd'
        (childRefs (Finset.univ.image s) (s a).1)).coefficient (fun j => m j.succ)
      rw [hR,hS]
      exact ih _ _ rr ss aa hsplit' d hd' _

end DilutedSpinGlass.PrescribedTree

namespace DilutedSpinGlass.PrescribedTree

theorem splitDepth_symm {n : ℕ} (S : PrescribedTree n) (a b : Leaf S) :
    splitDepth S a b = splitDepth S b a := by
  induction S with
  | leaf => rfl
  | @node n k C ih =>
    obtain ⟨i,a⟩ := a
    obtain ⟨j,b⟩ := b
    by_cases h : i = j
    · subst j
      rw [splitDepth_same_child, splitDepth_same_child, ih]
    · rw [splitDepth_diff_child C i j h, splitDepth_diff_child C j i (Ne.symm h)]

noncomputable local instance instDecidable_6_rb0cef7_1 (p : Prop) : Decidable p := Classical.propDecidable p
/-- Positional ancestry is an ultrametric similarity, independently of spins. -/
theorem splitDepth_ultrametric {n : ℕ} (S : PrescribedTree n) (a b c : Leaf S) :
    min (splitDepth S a b) (splitDepth S b c) ≤ splitDepth S a c := by
  induction S with
  | leaf => exact le_refl _
  | @node n k C ih =>
    obtain ⟨i,a⟩ := a
    obtain ⟨j,b⟩ := b
    obtain ⟨l,c⟩ := c
    by_cases hij : i = j
    · subst j
      by_cases hil : i = l
      · subst l
        rw [splitDepth_same_child, splitDepth_same_child, splitDepth_same_child]
        have h := ih i a b c
        omega
      · rw [splitDepth_diff_child C i l hil, Nat.min_zero]
        exact Nat.zero_le _
    · rw [splitDepth_diff_child C i j hij, Nat.zero_min]
      exact Nat.zero_le _

 
theorem deepest_reference_profile {n : ℕ} (S : PrescribedTree n) (b a r : Leaf S)
    (hmax : splitDepth S b r ≤ splitDepth S b a) :
    splitDepth S b r = min (splitDepth S b a) (splitDepth S a r) := by
  have h1 := splitDepth_ultrametric S b a r
  have h2 := splitDepth_ultrametric S a b r
  rw [splitDepth_symm S a b, min_eq_right hmax] at h2
  exact le_antisymm (le_min hmax h2) h1

end DilutedSpinGlass.PrescribedTree

namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators

attribute [local instance] OAI.DilutedSpinGlass.PrescribedTree.instDecidable_7
theorem labeledOldMatch_profile {n : ℕ} (S T : PrescribedTree n)
    {ι : Type} [Fintype ι] (r : ι → Leaf S) (s : ι → Leaf T) (b : Leaf T) (a : ι)
    (hsplit : ∀ i j, splitDepth S (r i) (r j) = splitDepth T (s i) (s j))
    (hmax : ∀ i, splitDepth T b (s i) ≤ splitDepth T b (s a)) (x : Leaf S) :
    labeledOldMatch S T r s b x ↔
      matchesOldProfile S (Finset.univ.image r) (r a) (splitDepth T b (s a)) x := by
  constructor
  · intro h y hy
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hy
    rw [h i, hsplit, deepest_reference_profile T b (s a) (s i) (hmax i)]
  · intro h i
    have hh := h (r i) (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩)
    rw [hsplit] at hh
    rw [hh, deepest_reference_profile T b (s a) (s i) (hmax i)]

theorem labeledFreshMatch_profile {n : ℕ} (S T : PrescribedTree n)
    {ι : Type} [Fintype ι] (r : ι → Leaf S) (s : ι → Leaf T) (b : Leaf T) (a : ι)
    (hsplit : ∀ i j, splitDepth S (r i) (r j) = splitDepth T (s i) (s j))
    (hmax : ∀ i, splitDepth T b (s i) ≤ splitDepth T b (s a)) (v : Internal S) :
    labeledFreshMatch S T r s b v ↔
      matchesFreshProfile S (Finset.univ.image r) (r a) (splitDepth T b (s a)) v := by
  constructor
  · intro h y hy
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hy
    rw [h i, hsplit, deepest_reference_profile T b (s a) (s i) (hmax i)]
  · intro h i
    have hh := h (r i) (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩)
    rw [hsplit] at hh
    rw [hh, deepest_reference_profile T b (s a) (s i) (hmax i)]

/-- Every eligible old or fresh choice is counted once. Its signed total
depends only on the prescribed reference splitting matrix. -/
theorem labeled_choice_total {n : ℕ} (S T : PrescribedTree n)
    {ι : Type} [Fintype ι] (r : ι → Leaf S) (s : ι → Leaf T) (b : Leaf T) (a : ι)
    (hsplit : ∀ i j, splitDepth S (r i) (r j) = splitDepth T (s i) (s j))
    (hne : b ≠ s a) (hmax : ∀ i, splitDepth T b (s i) ≤ splitDepth T b (s a))
    (m : Fin (n+1) → ℝ) (hend : m (Fin.last n) = 1) :
    (∑ x : Leaf S, if labeledOldMatch S T r s b x then (1:ℝ) else 0) +
      (∑ v : Internal S, if labeledFreshMatch S T r s b v then gamma S m v else 0) =
      (referenceDivergence T (s a) (splitDepth T b (s a))
        (splitDepth_lt_of_ne T b (s a) hne) (Finset.univ.image s)).coefficient m := by
  simp_rw [labeledOldMatch_profile S T r s b a hsplit hmax,
    labeledFreshMatch_profile S T r s b a hsplit hmax]
  rw [reference_profile_total S (r a) (splitDepth T b (s a))
    (splitDepth_lt_of_ne T b (s a) hne) (Finset.univ.image r)
    (Finset.mem_image.mpr ⟨a,Finset.mem_univ _,rfl⟩) m hend]
  exact reference_coefficient_invariant S T r s a hsplit _ _ m

end DilutedSpinGlass.PrescribedTree

end

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_ActualCharging
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.edgeFintype _root_.OAI.DilutedSpinGlass.PrescribedTree.leafDecidableEq _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators

attribute [local instance 2000] OAI.DilutedSpinGlass.PrescribedTree.instDecidableEqLeaf_1
noncomputable local instance (priority := 2000) instDecidableEqSigma_rb0cef7_1 {α : Type*} (β : α → Type*) : DecidableEq (Sigma β) := Classical.decEq _
theorem branchProduct_succ (x y : ℝ) {k : ℕ} (hk : 0 < k) :
    branchProduct x y (k+1) = branchProduct x y k * (x-(k:ℝ)*y) := by
  classical
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (ne_of_gt hk)
  simp [branchProduct, Finset.prod_range_succ, Nat.cast_add, Nat.cast_one]


theorem childRefs_insert_other {n : ℕ} {k : ℕ+} {C : Fin k → PrescribedTree n}
    (R : Finset (Leaf (.node k C))) (i j : Fin k) (hij : j ≠ i) (a : Leaf (C i)) :
    childRefs (insert (⟨i,a⟩ : Leaf (.node k C)) R) j = childRefs R j := by
  classical
  ext b
  constructor
  · intro h
    have hh := (mem_childRefs _ j b).mp h
    rcases Finset.mem_insert.mp hh with hab | hb
    · exact (hij (congrArg Sigma.fst hab)).elim
    · exact (mem_childRefs R j b).mpr hb
  · intro h
    apply (mem_childRefs _ j b).mpr
    exact Finset.mem_insert_of_mem ((mem_childRefs R j b).mp h)

theorem childRefs_singleton_other {n : ℕ} {k : ℕ+} {C : Fin k → PrescribedTree n}
    (i j : Fin k) (hij : j ≠ i) (a : Leaf (C i)) :
    childRefs (C := C) ({⟨i,a⟩} : Finset (Leaf (.node k C))) j = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro b hb
  have hh := Finset.mem_singleton.mp ((mem_childRefs _ j b).mp hb)
  exact hij (congrArg Sigma.fst hh)

@[simp] theorem partialKappa_singleton {n : ℕ} (S : PrescribedTree n)
    (m : Fin (n+1) → ℝ) (a : Leaf S) : partialKappa S m {a} = 1 := by
  classical
  induction S with
  | leaf => rfl
  | @node n k C ih =>
    obtain ⟨i,a⟩ := a
    change branchProduct (m 0) (m 1) (Finset.image (fun a : Sigma (fun j => Leaf (C j)) => a.1) {⟨i,a⟩}).card * _ = 1
    rw [Finset.image_singleton,Finset.card_singleton,branchProduct_one,one_mul]
    apply Finset.prod_eq_one
    intro j _
    by_cases hji : j = i
    · subst j
      rw [childRefs_singleton_same]
      exact ih i (fun j => m j.succ) a
    · rw [childRefs_singleton_other i j hji,partialKappa_empty]

end DilutedSpinGlass.PrescribedTree

namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators

attribute [local instance 2000] OAI.DilutedSpinGlass.PrescribedTree.instDecidableEqLeaf_2
noncomputable local instance (priority := 2000) instDecidableEqSigma_1_rb0cef7_1 {α : Type*} (β : α → Type*) : DecidableEq (Sigma β) := Classical.decEq _
private theorem prod_local_factor {α : Type*} [Fintype α] (f g : α → ℝ) (i : α) (c : ℝ)
    (hi : f i = c*g i) (ho : ∀ j, j ≠ i → f j = g j) :
    (∏ j, f j) = c*∏ j, g j := by
  classical
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i),
    ← Finset.mul_prod_erase _ _ (Finset.mem_univ i),hi]
  have he : (∏ j ∈ Finset.univ.erase i, f j) = ∏ j ∈ Finset.univ.erase i, g j :=
    Finset.prod_congr rfl (fun j hj => ho j (Finset.mem_erase.mp hj).1)
  rw [he,mul_assoc]

private theorem childRefs_eq_empty_of_unoccupied {n : ℕ} {k : ℕ+} {C : Fin k → PrescribedTree n}
    (R : Finset (Leaf (.node k C))) (i : Fin k) (hi : i ∉ R.image (fun a => a.1)) :
    childRefs R i = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro a ha
  exact hi (Finset.mem_image.mpr ⟨⟨i,a⟩,(mem_childRefs R i a).mp ha,rfl⟩)

 
theorem partialKappa_insert {n : ℕ} (S : PrescribedTree n)
    (m : Fin (n+1) → ℝ) (R : Finset (Leaf S)) (a b : Leaf S)
    (ha : a ∈ R) (hb : b ∉ R)
    (hmax : ∀ r ∈ R, splitDepth S b r ≤ splitDepth S b a) :
    partialKappa S m (insert b R) =
      (referenceDivergence S a (splitDepth S b a)
        (splitDepth_lt_of_ne S b a (fun h => hb (h ▸ ha))) R).coefficient m *
        partialKappa S m R := by
  classical
  induction S with
  | leaf =>
    have he : a = b := @Subsingleton.elim Unit (inferInstanceAs (Subsingleton Unit)) a b
    exact (hb (he ▸ ha)).elim
  | @node n k C ih =>
    obtain ⟨i,a⟩ := a
    obtain ⟨j,b⟩ := b
    by_cases hji : j = i
    · subst j
      have hai : a ∈ childRefs R i := (mem_childRefs R i a).mpr ha
      have hbi : b ∉ childRefs R i := fun h => hb ((mem_childRefs R i b).mp h)
      have hmi : ∀ r ∈ childRefs R i, splitDepth (C i) b r ≤ splitDepth (C i) b a := by
        intro r hr
        have hh := hmax ⟨i,r⟩ ((mem_childRefs R i r).mp hr)
        rw [splitDepth_same_child,splitDepth_same_child] at hh
        omega
      have hei : i ∈ R.image (fun r => r.1) := Finset.mem_image.mpr ⟨⟨i,a⟩,ha,rfl⟩
      have hroot : (insert (⟨i,b⟩ : Leaf (.node k C)) R).image (fun r => r.1) =
          R.image (fun r => r.1) := by
        erw [Finset.image_insert]
        exact Finset.insert_eq_of_mem hei
      let c := (referenceDivergence (C i) a (splitDepth (C i) b a)
        (splitDepth_lt_of_ne _ b a (fun h => hbi (h ▸ hai))) (childRefs R i)).coefficient
          (fun z => m z.succ)
      have hprod : (∏ t, partialKappa (C t) (fun z => m z.succ)
          (childRefs (insert (⟨i,b⟩ : Leaf (.node k C)) R) t)) =
          c*∏ t, partialKappa (C t) (fun z => m z.succ) (childRefs R t) := by
        apply prod_local_factor _ _ i c
        · rw [childRefs_insert_same]
          exact ih i (fun z => m z.succ) (childRefs R i) a b hai hbi hmi
        · intro t hti
          rw [childRefs_insert_other R i t hti]
      change branchProduct (m 0) (m 1) ((insert (⟨i,b⟩ : Leaf (.node k C)) R).image
        (fun r => r.1)).card * _ = _
      erw [hroot,hprod]
      simp only [splitDepth_same_child,Nat.add_comm 1]
      change branchProduct (m 0) (m 1) (R.image (fun r => r.1)).card * (c*_) =
        c*(branchProduct (m 0) (m 1) (R.image (fun r => r.1)).card * _)
      ring
    · have hz : splitDepth (.node k C) (⟨j,b⟩ : Leaf (.node k C)) ⟨i,a⟩ = 0 :=
        splitDepth_diff_child C j i hji b a
      have hj : j ∉ R.image (fun r => r.1) := by
        intro h
        obtain ⟨⟨t,r⟩,hr,ht⟩ := Finset.mem_image.mp h
        change t = j at ht
        subst t
        have hh := hmax ⟨j,r⟩ hr
        rw [hz,splitDepth_same_child] at hh
        omega
      have hchild := childRefs_eq_empty_of_unoccupied R j hj
      have hcard : 0 < (R.image (fun r => r.1)).card :=
        Finset.card_pos.mpr ⟨i,Finset.mem_image.mpr ⟨⟨i,a⟩,ha,rfl⟩⟩
      have hroot : ((insert (⟨j,b⟩ : Leaf (.node k C)) R).image (fun r => r.1)).card =
          (R.image (fun r => r.1)).card+1 := by
        erw [Finset.image_insert,Finset.card_insert_of_notMem hj]
      have hprod : (∏ t, partialKappa (C t) (fun z => m z.succ)
          (childRefs (insert (⟨j,b⟩ : Leaf (.node k C)) R) t)) =
          ∏ t, partialKappa (C t) (fun z => m z.succ) (childRefs R t) := by
        apply Finset.prod_congr rfl
        intro t _
        by_cases ht : t = j
        · subst t
          rw [childRefs_insert_same,hchild,Finset.insert_empty,partialKappa_singleton,
            partialKappa_empty]
        · rw [childRefs_insert_other R j t ht]
      change branchProduct (m 0) (m 1) ((insert (⟨j,b⟩ : Leaf (.node k C)) R).image
        (fun r => r.1)).card * _ = _
      erw [hroot,hprod,branchProduct_succ _ _ hcard]
      simp only [hz]
      change (_ * (m 0-((R.image (fun r => r.1)).card : ℝ)*m 1))*_ =
        (m 0-((R.image (fun r => r.1)).card : ℝ)*m 1)*(_*_)
      ring

end DilutedSpinGlass.PrescribedTree

end

end

section
section
namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators

attribute [local instance] OAI.DilutedSpinGlass.PrescribedTree.instDecidable_10
theorem leaves_pos {n : ℕ} (S : PrescribedTree n) : 0 < leaves S := by
  induction S with
  | leaf => decide
  | @node n k C ih =>
    exact Finset.sum_pos (fun i _ => ih i) Finset.univ_nonempty

end DilutedSpinGlass.PrescribedTree

namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators

attribute [local instance] OAI.DilutedSpinGlass.PrescribedTree.instDecidable_11
theorem sum_abs_gamma_grid {L : ℕ} (hL : 0 < L) (S : PrescribedTree L) :
    (∑ v : Internal S, |gamma S (grid L 0 L) v|) = (leaves S:ℝ) := by
  apply sum_abs_gamma
  · intro i j hij
    simp only [grid, Nat.zero_add]
    exact div_le_div_of_nonneg_right (Nat.cast_le.mpr hij) (Nat.cast_nonneg _)
  · intro i
    exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  · simp [grid]
  · simp [grid, ne_of_gt hL]

theorem chargeBound_nonneg {C D : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D) (k b : ℕ) :
    0 ≤ chargeBound C D k b := by
  induction k generalizing b with
  | zero => simp only [chargeBound]; split <;> norm_num
  | succ k ih =>
    cases b with
    | zero => exact mul_nonneg hC (ih 0)
    | succ b => exact add_nonneg (mul_nonneg hC (ih _)) (mul_nonneg hD (ih _))

end DilutedSpinGlass.PrescribedTree
end

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_ShapeMean
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.edgeFintype _root_.OAI.DilutedSpinGlass.PrescribedTree.leafDecidableEq _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section

namespace DilutedSpinGlass.PrescribedTree
variable {Ω : Type} [Fintype Ω]

omit [Fintype Ω] in
theorem leafProduct_eq_prod {n : ℕ} (S : PrescribedTree n)
    (f : FinitePath Ω n → ℝ) (z : Sample Ω S) :
    leafProduct S f z = ∏ a : Leaf S, f (pathAt S a z) := by
  induction S with
  | leaf =>
    change f () = ∏ _ : Unit, f ()
    simp
  | @node n k C ih =>
    simp only [leafProduct]
    change _ = ∏ a : (i : Fin k) × Leaf (C i), f (pathAt (.node k C) a z)
    rw [Fintype.prod_sigma]
    exact Finset.prod_congr rfl (fun i _ => ih i (fun y => f ((z i).1,y)) (z i).2)

omit [Fintype Ω] in
theorem leafProduct_bound {n : ℕ} (S : PrescribedTree n)
    {f : FinitePath Ω n → ℝ} (hf : ∀ x, |f x| ≤ 1) (z : Sample Ω S) :
    |leafProduct S f z| ≤ 1 := by
  rw [leafProduct_eq_prod,Finset.abs_prod]
  exact Finset.prod_le_one (fun _ _ => abs_nonneg _) (fun a _ => hf (pathAt S a z))

end DilutedSpinGlass.PrescribedTree

end

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_SplitDepthContinuity
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.edgeFintype _root_.OAI.DilutedSpinGlass.PrescribedTree.leafDecidableEq _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators

attribute [local instance] OAI.DilutedSpinGlass.PrescribedTree.instDecidableSplitDepthContinuity
lemma pairDivergence_coefficient {n : ℕ} (S : PrescribedTree n) (a : S.Leaf)
    (d : ℕ) (hd : d < n) (m : Fin (n+1) → ℝ) :
    (pairDivergence S a d hd).coefficient m =
      m ⟨d,by omega⟩ - m ⟨d+1,by omega⟩ := by
  induction S generalizing d with
  | leaf => omega
  | @node n k C ih =>
    cases d with
    | zero => simp [pairDivergence,Divergence.coefficient]
    | succ d => exact ih a.1 a.2 d (by omega) (fun j => m j.succ)

lemma pairDivergence_old {n : ℕ} (S : PrescribedTree n) (a b : S.Leaf)
    (d : ℕ) (hd : d < n) :
    (pairDivergence S a d hd).oldAllowed b ↔ splitDepth S a b = d := by
  induction S generalizing d with
  | leaf => omega
  | @node n k C ih =>
    rcases a with ⟨i,a⟩
    rcases b with ⟨j,b⟩
    cases d with
    | zero =>
      change j ∉ ({i} : Finset (Fin k)) ↔ _
      simp only [Finset.mem_singleton]
      by_cases h : i = j
      · subst j; rw [splitDepth_same_child]; simp
      · rw [splitDepth_diff_child C i j h]; simp [Ne.symm h]
    | succ d =>
      change (∃ h : j = i, (pairDivergence (C i) a d (by omega)).oldAllowed (h ▸ b)) ↔ _
      by_cases h : j = i
      · subst j
        simp only [exists_const,splitDepth_same_child]
        rw [ih i a b d (by omega)]
        omega
      · rw [splitDepth_diff_child C i j (Ne.symm h)]
        constructor
        · rintro ⟨he,_⟩; exact (h he).elim
        · intro he; omega

lemma pairDivergence_fresh {n : ℕ} (S : PrescribedTree n) (a : S.Leaf)
    (v : S.Internal) (d : ℕ) (hd : d < n) :
    (pairDivergence S a d hd).freshAllowed v ↔ freshSplitDepth S v a = d := by
  induction S generalizing d with
  | leaf => exact v.elim
  | @node n k C ih =>
    rcases a with ⟨i,a⟩
    change Option ((j : Fin k) × (C j).Internal) at v
    cases d with
    | zero =>
      cases v with
      | none => change True ↔ 0 = 0; simp
      | some v =>
        rcases v with ⟨j,v⟩
        change j ∉ ({i} : Finset (Fin k)) ↔ _
        simp only [Finset.mem_singleton]
        exact ne_comm.trans (freshSplitDepth_node_zero C j v ⟨i,a⟩).symm
    | succ d =>
      cases v with
      | none => change False ↔ 0 = d+1; simp
      | some v =>
        rcases v with ⟨j,v⟩
        change (∃ h : j = i, (pairDivergence (C i) a d (by omega)).freshAllowed (h ▸ v)) ↔ _
        by_cases h : j = i
        · subst j
          simp only [exists_const,freshSplitDepth_same_child]
          rw [ih i a v d (by omega)]
          omega
        · rw [freshSplitDepth_diff_child C j i (Ne.symm h)]
          constructor
          · rintro ⟨he,_⟩; exact (h he).elim
          · intro he; omega

/-- Exact signed total of every path splitting from the anchor at d. -/
theorem pair_choice_total {n : ℕ} (S : PrescribedTree n) (a : S.Leaf)
    (d : ℕ) (hd : d < n) (m : Fin (n+1) → ℝ) (hend : m (Fin.last n) = 1) :
    (∑ b : S.Leaf, if splitDepth S a b = d then (1:ℝ) else 0) +
      (∑ v : S.Internal, if splitDepth (grow S v) (oldLeaf S v a) (newLeaf S v) = d
        then gamma S m v else 0) = m ⟨d,by omega⟩ - m ⟨d+1,by omega⟩ := by
  simp_rw [splitDepth_symm (grow S _) (oldLeaf S _ a),splitDepth_new_old,
    ← pairDivergence_old S a _ d hd,← pairDivergence_fresh S a _ d hd]
  rw [divergence_choice_total _ m hend,pairDivergence_coefficient]

end DilutedSpinGlass.PrescribedTree
end

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_RegularDepth
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.DepthAverage
open scoped BigOperators
noncomputable local instance regularDepthPropDecidable_rb0cef7_1 (proposition : Prop) : Decidable proposition :=
  Classical.propDecidable proposition
variable {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
  {L : ℕ} [NeZero L]

lemma rotate_val_of_room (q : Fin L) (hq : q.val+1 < L) :
    (finRotate L q).val=q.val+1 := by
  cases L with
  | zero => exact q.elim0
  | succ n =>
    rcases q with ⟨v,hv⟩
    change v+1<n+1 at hq
    have hn : v<n := by omega
    exact congrArg Fin.val (finRotate_of_lt hn)

omit [Fintype α] [DecidableEq α] in
lemma regular_room {η : ℝ} (hlarge : 1 < η*(L:ℝ)) {q : α → Fin L}
    (hq : Regular η q) (i : α) : (q i).val+1 < L := by
  have hL : (0:ℝ)<L := Nat.cast_pos.mpr (NeZero.pos L)
  have hi := (div_lt_iff₀ hL).mp (hq.1 i).2
  have hh : ((q i).val:ℝ)+1 < (L:ℝ) := by nlinarith
  exact_mod_cast hh

end DilutedSpinGlass.DepthAverage
end

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_ProfileHistory
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators
variable {n : ℕ} {C ι : Type} [DecidableEq C] [DecidableEq ι]

omit [DecidableEq C] [DecidableEq ι] in
/-- Available-old sums equal unrestricted old-leaf sums for any observable
that vanishes on the protected references. No probability calculation occurs. -/
lemma HistoryCover.sum_available {S : PrescribedTree n} {U : Finset ι}
    {loc : ι → S.Leaf} {P : Finset C} {pos : C → S.Leaf}
    (h : HistoryCover S U loc P pos) (F : S.Leaf → ℝ)
    (hF : ∀ c ∈ P, F (pos c) = 0) :
    (∑ i ∈ U, F (loc i)) = ∑ b : S.Leaf, F b := by
  classical
  rw [← Finset.sum_image (fun i _ j _ hij => h.loc_inj hij)]
  apply Finset.sum_subset (Finset.subset_univ _)
  intro b _ hb
  rcases h.cover b with ⟨i,hi,rfl⟩ | ⟨c,hc,rfl⟩
  · exact False.elim (hb (Finset.mem_image.mpr ⟨i,hi,rfl⟩))
  · exact hF c hc

end DilutedSpinGlass.PrescribedTree
end

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_MatrixHistory
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators

noncomputable local instance kappaRegularDecidable_rb0cef7_1 (p : Prop) : Decidable p :=
  Classical.propDecidable p
attribute [local instance] OAI.DilutedSpinGlass.PrescribedTree.kappaRegularLeafDecidableEq
lemma branchProduct_ne_zero {x y : ℝ} (hxy : x < y) (hy : 0 ≤ y) (k : ℕ) :
    branchProduct x y k ≠ 0 := by
  unfold branchProduct
  apply Finset.prod_ne_zero_iff.mpr
  intro j _
  apply ne_of_lt
  have hj : (0:ℝ) ≤ j := Nat.cast_nonneg j
  have hmul := mul_nonneg hj hy
  nlinarith

theorem partialKappa_ne_zero {n : ℕ} (S : PrescribedTree n)
    (m : Fin (n+1) → ℝ) (hm : StrictMono m) (hp : ∀ j, 0 ≤ m j) (P : Finset S.Leaf) :
    partialKappa S m P ≠ 0 := by
  induction S with
  | leaf => exact one_ne_zero
  | @node n k C ih =>
    apply mul_ne_zero
    · exact branchProduct_ne_zero (hm (by simp : (0 : Fin (n+1+1)) < 1)) (hp 1) _
    · exact Finset.prod_ne_zero_iff.mpr (fun i _ => ih i _
        (fun a b h => hm (Fin.succ_lt_succ_iff.mpr h)) (fun j => hp j.succ) _)

variable {n : ℕ} {C ι : Type} [Fintype C] [DecidableEq C] [DecidableEq ι]

omit [DecidableEq ι] in
/-- The actual one-step protected extension total is the ratio of the two
unordered branching products. Complete split constraints, not a surrogate
probability mechanism, determine this coefficient. -/
theorem matrix_choice_kappa (T S : PrescribedTree n) (q : C → T.Leaf)
    (hq : Function.Injective q) (P : Finset C) (hP : P.Nonempty)
    (c : C) (hc : c ∉ P) (pos : C → S.Leaf) (U : Finset ι) (loc : ι → S.Leaf)
    (hcover : HistoryCover S U loc P pos)
    (hsplit : ∀ a ∈ P, ∀ b ∈ P,
      splitDepth S (pos a) (pos b) = splitDepth T (q a) (q b))
    (m : Fin (n+1) → ℝ) (hm : StrictMono m) (hp : ∀ j, 0 ≤ m j)
    (hend : m (Fin.last n) = 1) :
    (∑ i ∈ U, if ∀ d ∈ P, splitDepth S (loc i) (pos d) = splitDepth T (q c) (q d)
      then (1:ℝ) else 0) +
    (∑ v : S.Internal, if ∀ d ∈ P, freshSplitDepth S v (pos d) = splitDepth T (q c) (q d)
      then gamma S m v else 0) =
    partialKappa T m ((insert c P).image q) / partialKappa T m (P.image q) := by
  classical
  obtain ⟨a,ha,hmax⟩ := Finset.exists_max_image P (fun a => splitDepth T (q c) (q a)) hP
  let r : P → S.Leaf := fun a => pos a
  let s : P → T.Leaf := fun a => q a
  have himage : Finset.univ.image s = P.image q := by
    ext x
    simp only [Finset.mem_image,Finset.mem_univ,true_and]
    constructor
    · rintro ⟨b,hb⟩
      exact ⟨b,b.property,hb⟩
    · rintro ⟨b,hb,he⟩
      exact ⟨⟨b,hb⟩,he⟩
  have hqa : q c ≠ q a := fun h => hc (hq h ▸ ha)
  have hn : q c ∉ P.image q := by
    rintro h
    obtain ⟨d,hd,he⟩ := Finset.mem_image.mp h
    exact hc (hq he ▸ hd)
  have he := labeled_choice_total S T r s (q c) ⟨a,ha⟩
    (fun a b => hsplit a a.property b b.property) hqa (fun b => hmax b b.property) m hend
  have ho (b : S.Leaf) : labeledOldMatch S T r s (q c) b ↔
      ∀ d ∈ P, splitDepth S b (pos d) = splitDepth T (q c) (q d) := by
    simp only [labeledOldMatch,r,s,Subtype.forall]
  have hf (v : S.Internal) : labeledFreshMatch S T r s (q c) v ↔
      ∀ d ∈ P, freshSplitDepth S v (pos d) = splitDepth T (q c) (q d) := by
    simp only [labeledFreshMatch,r,s,Subtype.forall]
  simp_rw [ho,hf] at he
  have hav := hcover.sum_available
    (fun b => if ∀ d ∈ P, splitDepth S b (pos d) = splitDepth T (q c) (q d) then (1:ℝ) else 0)
    (by
      intro d hd
      apply ite_eq_right
      intro h
      have hh := h d hd
      rw [splitDepth_self] at hh
      exact hc (hq ((splitDepth_eq_height T (q c) (q d)).mp hh.symm) ▸ hd))
  rw [hav,he]
  have hk := partialKappa_insert T m (P.image q) (q a) (q c)
    (Finset.mem_image.mpr ⟨a,ha,rfl⟩) hn
    (by rintro t ht; obtain ⟨d,hd,rfl⟩ := Finset.mem_image.mp ht; exact hmax d hd)
  rw [Finset.image_insert,hk]
  rw [mul_div_cancel_right₀ _ (partialKappa_ne_zero T m hm hp _)]
  simp only [himage,s]

end DilutedSpinGlass.PrescribedTree
end

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_GlobalSelectedAverage
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators
variable {Ω : Type} [Fintype Ω] {n : ℕ}

noncomputable local instance pairObservableHistoryDecidable_rb0cef7_1 (proposition : Prop) :
    Decidable proposition := Classical.propDecidable proposition
lemma pair_univ_erase (S : PrescribedTree n) (a : S.Leaf) (d : ℕ) (hd : d < n) :
    (∑ b ∈ Finset.univ.erase a, if splitDepth S a b = d then (1:ℝ) else 0) =
      ∑ b : S.Leaf, if splitDepth S a b = d then (1:ℝ) else 0 := by
  classical
  have he := Finset.sum_erase_add (Finset.univ : Finset S.Leaf)
    (fun b => if splitDepth S a b = d then (1:ℝ) else 0) (Finset.mem_univ a)
  simpa only [splitDepth_self,ite_eq_right (Ne.symm (Nat.ne_of_lt hd)),add_zero] using he

end DilutedSpinGlass.PrescribedTree
end

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_MatrixPair
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators
variable {Ω C : Type} [Fintype Ω] [Fintype C] [DecidableEq C] {n : ℕ}

noncomputable local instance matrixPairPropDecidable_rb0cef7_1 (proposition : Prop) : Decidable proposition :=
  Classical.propDecidable proposition
omit [Fintype C] [DecidableEq C] in
lemma singleton_history_cover (S : PrescribedTree n) (x : S.Leaf) (a : C) :
    HistoryCover S (Finset.univ.erase x) id ({a} : Finset C) (fun _ => x) := by
  classical
  refine ⟨⟨Function.injective_id,?_,?_⟩,?_⟩
  · intro c hc d hd _
    simp only [Finset.mem_coe,Finset.mem_singleton] at hc hd
    exact hc.trans hd.symm
  · intro y hy c _
    exact (Finset.mem_erase.mp hy).1
  · intro y
    by_cases h : y = x
    · exact Or.inr ⟨a,by simp,h⟩
    · exact Or.inl ⟨y,by simp [h],rfl⟩

end DilutedSpinGlass.PrescribedTree
end

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_MatrixConstant
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators
variable {n : ℕ}

noncomputable local instance partialKappaPairDecidable_rb0cef7_1 (proposition : Prop) : Decidable proposition :=
  Classical.propDecidable proposition
lemma partialKappa_pair (T : PrescribedTree n) (m : Fin (n+1) → ℝ)
    (hm : StrictMono m) (hp : ∀ j, 0 ≤ m j) (hend : m (Fin.last n) = 1)
    (a b : T.Leaf) (hab : a ≠ b) :
    partialKappa T m {b,a} =
      m ⟨splitDepth T a b,by have := splitDepth_lt_of_ne T a b hab; omega⟩-
      m ⟨splitDepth T a b+1,by have := splitDepth_lt_of_ne T a b hab; omega⟩ := by
  classical
  have h := matrix_choice_kappa T T id Function.injective_id {a} (Finset.singleton_nonempty _)
    b (by simpa using hab.symm) (fun _ => a) (Finset.univ.erase a) id
    (singleton_history_cover T a a)
    (by intro c hc d hd; have hc' := Finset.mem_singleton.mp hc; have hd' := Finset.mem_singleton.mp hd
        subst c; subst d; rfl) m hm hp hend
  simp only [Finset.mem_singleton,forall_eq,id_eq,Finset.image_id,partialKappa_singleton,div_one] at h
  simp_rw [splitDepth_symm T _ a] at h
  have he (v : T.Internal) : freshSplitDepth T v a = splitDepth (grow T v) (oldLeaf T v a) (newLeaf T v) := by
    rw [splitDepth_symm,splitDepth_new_old]
  simp_rw [he] at h
  rw [pair_univ_erase T a (splitDepth T a b) (splitDepth_lt_of_ne T a b hab),
    pair_choice_total T a (splitDepth T a b) (splitDepth_lt_of_ne T a b hab) m hend] at h
  exact h.symm

end DilutedSpinGlass.PrescribedTree
end

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_MatrixEnergy
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators
variable {Ω C : Type} [Fintype Ω] [Fintype C] [DecidableEq C] {L N : ℕ}

noncomputable local instance matrixEnergyPropDecidable_rb0cef7_1 (proposition : Prop) :
    Decidable proposition := Classical.propDecidable proposition
lemma grid_strictMono (hL : 0 < L) : StrictMono (grid L 0 L) := by
  intro i j hij
  dsimp only [grid]
  simp only [Nat.zero_add]
  exact div_lt_div_of_pos_right (Nat.cast_lt.mpr hij) (Nat.cast_pos.mpr hL)

lemma grid_nonneg : ∀ j, 0 ≤ grid L 0 L j := by
  intro j
  exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

lemma grid_last (hL : 0 < L) : grid L 0 L (Fin.last L) = 1 := by
  simp [grid,ne_of_gt hL]

end DilutedSpinGlass.PrescribedTree
end

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_MatrixTriple
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators

noncomputable local instance kappaLowerDecidable_rb0cef7_1 (proposition : Prop) : Decidable proposition :=
  Classical.propDecidable proposition
noncomputable local instance kappaLowerLeafDecidableEq_rb0cef7_1 {depth : ℕ} (tree : PrescribedTree depth) :
    DecidableEq tree.Leaf := Classical.decEq _
lemma branchProduct_lower {x y η : ℝ} (hxy : x ≤ y) (hη : 0 ≤ η) (hy : η ≤ y) (k : ℕ) :
    (y-x)*η^k ≤ |branchProduct x y (k+2)| := by
  classical
  induction k with
  | zero =>
    simp only [pow_zero,mul_one,branchProduct,show (2:ℕ)-1 = 1 from rfl,Finset.prod_range_one,Nat.cast_zero,zero_add,one_mul]
    rw [abs_of_nonpos (sub_nonpos.mpr hxy)]
    linarith
  | succ k ih =>
    rw [show k+1+2 = (k+2)+1 by omega,branchProduct_succ x y (by omega),abs_mul,pow_succ]
    have hh : η ≤ |x-((k+2:ℕ):ℝ)*y| := by
      have hY : 0 ≤ y := hη.trans hy
      have hk : (0:ℝ) ≤ k := Nat.cast_nonneg k
      have hmul := mul_nonneg hk hY
      have hn : x-((k+2:ℕ):ℝ)*y ≤ 0 := by push_cast; nlinarith
      rw [abs_of_nonpos hn]
      push_cast
      nlinarith
    simpa only [mul_assoc] using mul_le_mul ih hh hη (abs_nonneg _)

lemma branchProduct_lower_pos {x y η : ℝ} (hxy : x ≤ y) (hη : 0 ≤ η) (hy : η ≤ y)
    (k : ℕ+) :
    (y-x)^(if 1 < (k:ℕ) then 1 else 0)*η^((k:ℕ)-2) ≤ |branchProduct x y k| := by
  classical
  have hk := k.property
  by_cases h : 1 < (k:ℕ)
  · obtain ⟨j,hj⟩ := Nat.exists_eq_add_of_le (show 2 ≤ (k:ℕ) by omega)
    have hkj : (k:ℕ) = j+2 := by omega
    simp only [ite_eq_left h,pow_one]
    rw [hkj]
    simp only [Nat.add_sub_cancel]
    exact branchProduct_lower hxy hη hy j
  · have hle : (k:ℕ) ≤ 1 := le_of_not_gt h
    have he : (k:ℕ) = 1 := Nat.le_antisymm hle (Nat.succ_le_of_lt hk)
    simp [he]

lemma leaf_nonempty {n : ℕ} (S : PrescribedTree n) : Nonempty S.Leaf := by
  induction S with
  | leaf => exact ⟨()⟩
  | @node n k C ih =>
    obtain ⟨a⟩ := ih ⟨0,k.property⟩
    exact ⟨⟨⟨0,k.property⟩,a⟩⟩

lemma childRefs_univ {n : ℕ} {k : ℕ+} (C : Fin k → PrescribedTree n) (i : Fin k) :
    childRefs (C := C) Finset.univ i = Finset.univ := by
  classical
  ext a
  rw [mem_childRefs]
  exact iff_of_true (Finset.mem_univ _) (Finset.mem_univ _)

lemma partialKappa_univ_node {n : ℕ} (k : ℕ+) (C : Fin k → PrescribedTree n)
    (m : Fin (n+2) → ℝ) :
    partialKappa (.node k C) m Finset.univ = branchProduct (m 0) (m 1) k *
      ∏ i, partialKappa (C i) (fun j => m j.succ) Finset.univ := by
  classical
  rw [partialKappa]
  have he : Finset.image (fun a : Leaf (.node k C) => a.1) Finset.univ = Finset.univ := by
    ext i
    simp only [Finset.mem_image,Finset.mem_univ,true_and,iff_true]
    obtain ⟨a⟩ := leaf_nonempty (C i)
    exact ⟨⟨i,a⟩,rfl⟩
  rw [he]
  simp only [Finset.card_univ,Fintype.card_fin,childRefs_univ]

lemma branchProduct_lower_regular {x y η : ℝ} (hxy : x ≤ y) (hη : 0 ≤ η) (k : ℕ+)
    (hy : 2 < (k:ℕ) → η ≤ y) :
    (y-x)^(if 1 < (k:ℕ) then 1 else 0)*η^((k:ℕ)-2) ≤ |branchProduct x y k| := by
  classical
  by_cases hk : 2 < (k:ℕ)
  · exact branchProduct_lower_pos hxy hη (hy hk) k
  · have hp := k.property
    have hle : (k:ℕ) ≤ 2 := le_of_not_gt hk
    have he : (k:ℕ) = 1 ∨ (k:ℕ) = 2 := by
      rcases Nat.lt_or_eq_of_le hle with hs | hs
      · exact Or.inl (Nat.le_antisymm (Nat.le_of_lt_succ hs) (Nat.succ_le_of_lt hp))
      · exact Or.inr hs
    rcases he with he|he
    · simp [he]
    · simp only [he,show 1 < (2:ℕ) from by omega,ite_true,pow_one,Nat.sub_self,pow_zero,mul_one]
      simp only [branchProduct,show (2:ℕ)-1 = 1 from rfl,Finset.prod_range_one,Nat.cast_zero,zero_add,one_mul]
      rw [abs_of_nonpos (sub_nonpos.mpr hxy)]
      linarith

 
theorem partialKappa_grid_lower {n : ℕ} (S : PrescribedTree n) (d L : ℕ)
    (η : ℝ) (hη : 0 ≤ η) (hr : BranchRegular S (grid n d L) η) :
    (L:ℝ)⁻¹^(branchingCount S (fun _ => True))*η^(branchExcess S) ≤
      |partialKappa S (grid n d L) Finset.univ| := by
  classical
  induction S generalizing d with
  | leaf => simp [partialKappa,branchingCount,branchExcess]
  | @node n k C ih =>
    have he : (fun j : Fin (n+1) => grid (n+1) d L j.succ) = grid n (d+1) L := by
      funext j
      simp [grid,Fin.val_succ,Nat.add_comm,Nat.add_left_comm]
    have hr' : (2 < (k:ℕ) → η ≤ grid (n+1) d L 1) ∧
        ∀ i, BranchRegular (C i) (grid n (d+1) L) η := by
      simpa only [BranchRegular,he] using hr
    have hδ : grid (n+1) d L 1-grid (n+1) d L 0 = (L:ℝ)⁻¹ := by
      simp [grid,Nat.cast_add,add_div]
    have hle : grid (n+1) d L 0 ≤ grid (n+1) d L 1 := by
      have hnonneg : (0:ℝ) ≤ (L:ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg L)
      linarith
    have hroot := branchProduct_lower_regular hle hη k hr'.1
    rw [hδ] at hroot
    have hchild := Finset.prod_le_prod (fun i (_ : i ∈ (Finset.univ : Finset (Fin k))) =>
      mul_nonneg (pow_nonneg (inv_nonneg.mpr (Nat.cast_nonneg L)) _) (pow_nonneg hη _))
      (fun i _ => ih i (d+1) (hr'.2 i))
    have h := mul_le_mul hroot hchild
      (Finset.prod_nonneg (fun i _ => mul_nonneg
        (pow_nonneg (inv_nonneg.mpr (Nat.cast_nonneg L)) _) (pow_nonneg hη _))) (abs_nonneg _)
    rw [partialKappa_univ_node,abs_mul,Finset.abs_prod,he]
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    simp only [branchingCount,branchExcess,true_and,pow_add,Finset.prod_mul_distrib,← Finset.prod_pow_eq_pow_sum]
    ring

end DilutedSpinGlass.PrescribedTree
end

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_RootMatrixTriple
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators Classical
variable {L : ℕ}

lemma partialKappa_grid_pair (hL : 0 < L) (T : PrescribedTree L)
    (a b : T.Leaf) (hab : a ≠ b) :
    partialKappa T (grid L 0 L) {b,a} = -(L:ℝ)⁻¹ := by
  rw [partialKappa_pair T _ (grid_strictMono hL) grid_nonneg (grid_last hL) a b hab]
  simp [grid,Nat.cast_add,add_div]

/-- The separation vertex is the protected pair factor, leaving exactly the
powers charged at the shifted internal branching vertices. -/
theorem protectedKappa_grid_lower (hL : 0 < L) (T : PrescribedTree L)
    (a b : T.Leaf) (hab : a ≠ b) (η : ℝ) (hη : 0 ≤ η)
    (hr : BranchRegular T (grid L 0 L) η) (k : ℕ)
    (hk : branchingCount T (fun _ => True) = k+1) :
    (L:ℝ)⁻¹^k*η^(branchExcess T) ≤
      |partialKappa T (grid L 0 L) Finset.univ / partialKappa T (grid L 0 L) {b,a}| := by
  have hδ : 0 < (L:ℝ)⁻¹ := inv_pos.mpr (Nat.cast_pos.mpr hL)
  rw [abs_div,partialKappa_grid_pair hL T a b hab,abs_neg,abs_of_pos hδ]
  apply (le_div_iff₀ (inv_pos.mpr (Nat.cast_pos.mpr hL))).mpr
  have h := partialKappa_grid_lower T 0 L η hη hr
  rw [hk,pow_succ] at h
  nlinarith [h]

/-- The manuscript's relative absolute-cost bound. Its dimensional power of
L cancels EXACTLY, including distinct target vertices sharing a depth. -/
theorem shiftedCharge_relative_bound (hL : 0 < L) (Q : Finset ℕ)
    (T S : PrescribedTree L) (k : ℕ) (a b : T.Leaf) (hab : a ≠ b)
    (η : ℝ) (hη : 0 < η) (hr : BranchRegular T (grid L 0 L) η)
    (hb : branchingCount T (fun _ => True) = branchingCount T (· ∈ Q)+1) :
    shiftedCharge Q T S k /
        |partialKappa T (grid L 0 L) Finset.univ / partialKappa T (grid L 0 L) {b,a}| ≤
      chargeBound (2*(leaves S+k:ℕ)) ((Q.card:ℝ)*(leaves S+k:ℕ)) k
        (branchingCount T (· ∈ Q)) / η^(branchExcess T) := by
  let J := |partialKappa T (grid L 0 L) Finset.univ / partialKappa T (grid L 0 L) {b,a}|
  let A := chargeBound (2*(leaves S+k:ℕ)) ((Q.card:ℝ)*(leaves S+k:ℕ)) k
    (branchingCount T (· ∈ Q))
  let D := (L:ℝ)⁻¹^(branchingCount T (· ∈ Q))
  let E := η^(branchExcess T)
  have hD : 0 < D := pow_pos (inv_pos.mpr (Nat.cast_pos.mpr hL)) _
  have hE : 0 < E := pow_pos hη _
  have hA : 0 ≤ A := chargeBound_nonneg (by positivity) (by positivity) _ _
  have hlo : D*E ≤ J := protectedKappa_grid_lower hL T a b hab η hη.le hr _ hb
  have hJ : 0 < J := (mul_pos hD hE).trans_le hlo
  change A*D/J ≤ A/E
  apply (div_le_div_iff₀ hJ hE).mpr
  have hh := mul_le_mul_of_nonneg_left hlo hA
  nlinarith [hh]

end DilutedSpinGlass.PrescribedTree
end

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_ShapeProjectionEnergy
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.PrescribedTree
variable {Ω : Type} [Fintype Ω] {N n : ℕ}

lemma shapeEnergyAt_nonneg (C : PrescribedTree n) (d : ℕ) (T : KernelTower Ω (n+1+d))
    (f : FinitePath Ω (n+1+d) → Fin N → ℝ) : 0 ≤ shapeEnergyAt C d T f := by
  induction d with
  | zero => unfold shapeEnergyAt childEnergy FiniteLaw.covarianceEnergy; positivity
  | succ d ih => exact T.1.expect_nonneg (fun z => ih (T.2 z) (fun y => f (z,y)))

end DilutedSpinGlass.PrescribedTree
end

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_ShiftedTree
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators

attribute [local instance] OAI.DilutedSpinGlass.PrescribedTree.shiftedTreeDecidable
lemma branchingCount_unary {n : ℕ} (S : PrescribedTree n) (P : ℕ → Prop) :
    branchingCount (unary S) P = branchingCount S (fun d => P (d+1)) := by
  classical
  change (if P 0 ∧ 1 < (1:ℕ) then 1 else 0)+
    (∑ _ : Fin 1, branchingCount S (fun d => P (d+1))) = _
  simp

lemma leaves_bottom {n : ℕ} (S : PrescribedTree n) : leaves (bottomUnary S) = leaves S := by
  induction S with
  | leaf =>
    change (∑ _ : Fin 1, (1:ℕ)) = 1
    simp
  | @node n k C ih => simp only [bottomUnary,leaves,ih]

lemma leaves_unary {n : ℕ} (S : PrescribedTree n) : leaves (unary S) = leaves S := by
  change (∑ _ : Fin 1, leaves S) = _
  simp

/-- Literal branching-vertex count as a sum. Distinct vertices at equal
depths occur separately; no count by distinct depth values is substituted. -/
lemma branchingCount_eq_vertexSum {n : ℕ} (S : PrescribedTree n) (P : ℕ → Prop) :
    branchingCount S P = ∑ v : S.Internal,
      if 1 < vertexArity S v ∧ P (vertexDepth S v) then 1 else 0 := by
  classical
  induction S generalizing P with
  | leaf =>
    change 0 = ∑ v : Empty, _
    simp
  | @node n k C ih =>
    change _ = ∑ v : Option ((i : Fin k) × Internal (C i)), _
    rw [Fintype.sum_option]
    simp only [vertexArity,vertexDepth,Fintype.sum_sigma,branchingCount,ih,and_comm]

lemma mem_branchingDepths {n : ℕ} (S : PrescribedTree n) (d : ℕ) :
    d ∈ branchingDepths S ↔ ∃ v : S.Internal, 1 < vertexArity S v ∧ vertexDepth S v=d := by
  classical
  simp only [branchingDepths,Finset.mem_image,Finset.mem_filter,Finset.mem_univ,true_and]

lemma branchingCount_congr_on {n : ℕ} (S : PrescribedTree n) (P Q : ℕ → Prop)
    (h : ∀ d ∈ branchingDepths S, P d ↔ Q d) : branchingCount S P = branchingCount S Q := by
  classical
  rw [branchingCount_eq_vertexSum,branchingCount_eq_vertexSum]
  apply Finset.sum_congr rfl
  intro v _
  by_cases hv : 1 < vertexArity S v
  · have hd := h (vertexDepth S v) ((mem_branchingDepths S _).mpr ⟨v,hv,rfl⟩)
    simp only [hv,true_and,hd]
  · simp only [hv,false_and,ite_false]


lemma zero_not_mem_shiftedTwinDepths {n : ℕ} (S : PrescribedTree n) :
    0 ∉ shiftedTwinDepths S := by
  classical
  simp [shiftedTwinDepths]

lemma shifted_twin_target_count {n : ℕ} (S : PrescribedTree n) :
    branchingCount (doubled (unary S)) (· ∈ shiftedTwinDepths S) =
      2*branchingCount S (fun _ => True) := by
  classical
  have hC : branchingCount S (fun d => d+1+1 ∈ shiftedTwinDepths S) =
      branchingCount S (fun _ => True) := by
    apply branchingCount_congr_on
    intro d hd
    exact iff_of_true (Finset.mem_image.mpr ⟨d,hd,by omega⟩) trivial
  simp only [doubled,branchingCount]

  simp only [zero_not_mem_shiftedTwinDepths,false_and,ite_false,branchingCount_unary,hC,
    Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,zero_add]
  norm_num

lemma shifted_twin_total_count {n : ℕ} (S : PrescribedTree n) :
    branchingCount (doubled (unary S)) (fun _ => True) =
      branchingCount (doubled (unary S)) (· ∈ shiftedTwinDepths S)+1 := by
  classical
  rw [shifted_twin_target_count]
  simp only [doubled,branchingCount]

  simp only [branchingCount_unary,
    Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  norm_num at *
  omega

end DilutedSpinGlass.PrescribedTree
end

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_ScheduledTopology
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass
open scoped BigOperators

namespace ReducedTopology

attribute [local instance] OAI.DilutedSpinGlass.instDecidable_solutions
lemma realize_leaves (r d : ℕ) (S : ReducedTopology) (q : S.Vertex → ℕ)
    (h : Admissible S q d (d+r)) :
    PrescribedTree.leaves (realize r d S q) = Fintype.card S.Leaf := by
  induction r generalizing d S with
  | zero =>
    cases S with
    | leaf => rfl
    | node k hk C => have := h.2.1; have := h.1; omega
  | succ r ih =>
    cases S with
    | leaf =>
      rw [realize,PrescribedTree.leaves_unary]
      exact ih (d+1) .leaf q trivial
    | node k hk C =>
      rw [realize]
      split_ifs with hd
      · rw [PrescribedTree.leaves_unary]
        apply ih
        exact ⟨hd,by simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h.2⟩
      · have he : q none=d := by have := h.1; omega
        simp only [PrescribedTree.leaves]
        change _ = Fintype.card ((i : Fin k) × (C i).Leaf)
        rw [Fintype.card_sigma]
        apply Finset.sum_congr rfl
        intro i _
        apply ih
        simpa [he,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h.2.2 i

end ReducedTopology
end DilutedSpinGlass
end

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_StemCoupling
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.ReducedTopology
open scoped BigOperators

lemma leaf_card_pos (S : ReducedTopology) : 0<Fintype.card S.Leaf := by
  induction S with
  | leaf => exact Nat.zero_lt_one
  | node k hk C ih =>
    change 0<Fintype.card ((j : Fin k) × (C j).Leaf)
    rw [Fintype.card_sigma]
    exact Finset.sum_pos' (fun _ _ => Nat.zero_le _)
      ⟨⟨0,k.property⟩,Finset.mem_univ _,ih _⟩

end DilutedSpinGlass.ReducedTopology
end

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_DoubledStemProjection
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators
variable {Ω : Type} [Fintype Ω] {n N : ℕ}

lemma splitDepth_stem (S : PrescribedTree n) (r : ℕ) (a b : S.Leaf) :
    splitDepth (stem S r) (stemLeaf S r a) (stemLeaf S r b)=splitDepth S a b+r := by
  induction r with
  | zero => rfl
  | succ r ih =>
    change splitDepth (.node 1 (fun _ => stem S r)) ⟨0,stemLeaf S r a⟩ ⟨0,stemLeaf S r b⟩=_
    rw [splitDepth_same_child,ih]
    omega

end DilutedSpinGlass.PrescribedTree
end

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_UniformRootDecorrelation
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators
variable {L : ℕ}

/-- Unlike a bound by all grid vertices, the exact full history mass is
uniform in the number of unary levels. -/
lemma pairHistoryMass_grid (hL : 0<L) (S : PrescribedTree L) (a : S.Leaf) :
    pairHistoryMass S (grid L 0 L) a=2*(leaves S:ℝ)-1 := by
  unfold pairHistoryMass
  rw [sum_abs_gamma_grid hL S,Finset.card_erase_of_mem (Finset.mem_univ a),Finset.card_univ,card_leaf]
  have hp : 1≤leaves S := by
    rw [← card_leaf]
    exact Fintype.card_pos_iff.mpr ⟨a⟩
  rw [Nat.cast_sub hp]
  simp only [Nat.cast_one]
  ring

end DilutedSpinGlass.PrescribedTree
end

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_VertexContinuity
attribute [-instance] _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.ReducedTopology
open scoped BigOperators

attribute [local instance] OAI.DilutedSpinGlass.ReducedTopology.realizeTranslationDecidable
lemma realize_translate (H d a : ℕ) (S : ReducedTopology) (q : S.Vertex → ℕ) :
    realize H (d+a) S (fun v => q v+a)=realize H d S q := by
  induction H generalizing d S with
  | zero => rfl
  | succ H ih =>
    cases S with
    | leaf =>
      simp only [realize]
      rw [show d+a+1=(d+1)+a by omega, ih]
    | node k hk C =>
      simp only [realize, Nat.add_lt_add_iff_right]
      split_ifs with hd
      · rw [show d+a+1=(d+1)+a by omega,ih]
      · congr 1
        funext i
        rw [show d+a+1=(d+1)+a by omega,ih]

/-- Bottom extension preserves all assigned internal depths, and supplies
precisely the old tree used opposite a delayed target in the matrix identity. -/
theorem realize_bottom (H d : ℕ) (S : ReducedTopology) (q : S.Vertex → ℕ)
    (hq : Admissible S q d (d+H)) :
    realize (H+1) d S q=PrescribedTree.bottomUnary (realize H d S q) := by
  induction H generalizing d S with
  | zero =>
    cases S with
    | leaf => rfl
    | node k hk C => have := hq.1; have := hq.2.1; omega
  | succ H ih =>
    cases S with
    | leaf =>
      simp only [realize,PrescribedTree.unary,PrescribedTree.bottomUnary]
      congr 1
      funext i
      exact ih (d+1) .leaf q trivial
    | node k hk C =>
      conv_lhs => rw [realize]
      conv_rhs => arg 1; rw [realize]
      split_ifs with hd
      · change PrescribedTree.node 1 _=PrescribedTree.node 1 _
        congr 1
        funext i
        apply ih
        exact ⟨hd,by simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hq.2⟩
      · simp only [PrescribedTree.bottomUnary]
        congr 1
        funext i
        apply ih
        have he : q none=d := by have := hq.1; omega
        simpa [he,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hq.2.2 i

end DilutedSpinGlass.ReducedTopology
end

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_MultileafMatrixPointwise
attribute [-instance] _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators
variable {Ω I : Type} [Fintype Ω] [Fintype I] [DecidableEq I] {n N : ℕ}

lemma splitFrame_split (S : PrescribedTree n) (r d : ℕ) (a : S.Leaf) :
    splitDepth (splitFrame S r d) (splitFrameLeaf S r d 0 a) (splitFrameLeaf S r d 1 a)=d := by
  exact (splitDepth_stem (doubled (stem S r)) d
    ⟨0,stemLeaf S r a⟩ ⟨1,stemLeaf S r a⟩).trans
    (by
      exact (congrArg (fun x => x+d)
        (splitDepth_diff_child (fun _ : Fin (2:ℕ+) => stem S r) 0 1 (by decide)
          (a := stemLeaf S r a) (b := stemLeaf S r a))).trans (Nat.zero_add d))

end DilutedSpinGlass.PrescribedTree
end

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_PhysicalPairConnection
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.DilutedSpinGlass.UniversalDictionary.reservoirLaw_prob _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section

namespace DilutedSpinGlass.UniversalDictionary
open _root_.MeasureTheory ProbabilityTheory HeterogeneousMarks PrescribedTree ConcreteReservoir
open scoped NNReal BigOperators
variable {Ω X Y : Type} [Fintype Ω] [MeasurableSpace X] [MeasurableSpace Y] {L M N : ℕ}

omit [Fintype Ω] in
lemma readVector_bound (read : Site N → FinitePath Ω (L+1) → Spin) (x) (i) :
    |readVector read x i| ≤ 1 := by simp only [readVector,abs_spin,le_refl]

end DilutedSpinGlass.UniversalDictionary
end

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_FullCubeConditionalContinuity
attribute [-instance] _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.UniversalDictionary
open _root_.MeasureTheory ProbabilityTheory HeterogeneousMarks PhysicalRoot PrescribedTree ConcreteReservoir Filter Set
open scoped NNReal BigOperators Topology
variable {L p : ℕ}

lemma gridExponents_cons (L : ℕ) :
    Fin.cons 0 (gridExponents L) = grid (L+1) 0 (L+1) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [grid]
  · simp [grid,gridExponents,Fin.val_succ]

end DilutedSpinGlass.UniversalDictionary
end

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_ProjectionShiftError
attribute [-instance] _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.ReducedTopology
open scoped BigOperators
noncomputable local instance projectionShiftErrorPropDecidable_rb0cef7_1 (proposition : Prop) :
    Decidable proposition := Classical.propDecidable proposition
variable {Ω α ι : Type} [Fintype Ω] [Fintype α] [DecidableEq α] [Fintype ι]
  {L N : ℕ} [NeZero L]


omit [Fintype α] [DecidableEq α] [NeZero L] in
lemma projectionShiftError_nonneg (a : α) (C : ι → ReducedTopology)
    (e : (j : ι) → (C j).Vertex → {j : α // j≠a})
    (T : KernelTower Ω L) (f : FinitePath Ω L → Fin N → ℝ) (Q : α → Fin L) :
    0≤projectionShiftError a C e T f Q := mul_nonneg (by norm_num) (Real.sqrt_nonneg _)

end DilutedSpinGlass.ReducedTopology
end

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_HeightTransport
attribute [-instance] _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass

namespace PrescribedTree
variable {Ω I : Type} [Fintype Ω] [Fintype I] [DecidableEq I] {n m N : ℕ}

lemma leafHeightCast_bijective (h : n=m) (S : PrescribedTree n) :
    Function.Bijective (leafHeightCast h S) := by cases h; exact Function.bijective_id

end PrescribedTree
end DilutedSpinGlass
end

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_ScheduledCovariance
attribute [-instance] _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.ReducedTopology
open PrescribedTree
variable {Ω : Type} [Fintype Ω] {N L : ℕ}

lemma scheduledShapeEnergy_nonneg (d : ℕ) (S : ReducedTopology) (q : S.Vertex → ℕ)
    (T : KernelTower Ω L) (f : FinitePath Ω L → Fin N → ℝ) :
    0 ≤ scheduledShapeEnergy L d S q T f := by
  unfold scheduledShapeEnergy
  split_ifs
  · exact shapeEnergyAt_nonneg _ _ _ _
  · exact le_rfl

end DilutedSpinGlass.ReducedTopology
end

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_ShiftedFrameGeometry
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators
variable {n : ℕ}

noncomputable local instance shiftedFrameGeometryPropDecidable_rb0cef7_1 (proposition : Prop) :
    Decidable proposition := Classical.propDecidable proposition
lemma branchingCount_stem (S : PrescribedTree n) (r : ℕ) (P : ℕ → Prop) :
    branchingCount (stem S r) P=branchingCount S (fun u => P (u+r)) := by
  induction r generalizing P with
  | zero => rfl
  | succ r ih =>
    change branchingCount (unary (stem S r)) P=_
    rw [branchingCount_unary,ih]
    simp only [Nat.add_assoc]

lemma mem_shiftedPrefixDepths (S : PrescribedTree n) (d u : ℕ) :
    u+d ∈ shiftedPrefixDepths S d ↔ u ∈ shiftedTwinDepths S := by
  classical
  simp [shiftedPrefixDepths]

theorem shifted_prefix_total_count (S : PrescribedTree n) (d : ℕ) :
    branchingCount (stem (doubled (unary S)) d) (fun _ => True)=
      branchingCount (stem (doubled (unary S)) d) (· ∈ shiftedPrefixDepths S d)+1 := by
  rw [branchingCount_stem,branchingCount_stem]
  simpa only [mem_shiftedPrefixDepths] using shifted_twin_total_count S

lemma branchRegular_unary {n : ℕ} (S : PrescribedTree n) (m : Fin (n+2) → ℝ) (η : ℝ) :
    BranchRegular (unary S) m η ↔ BranchRegular S (fun j => m j.succ) η := by
  simp only [unary,BranchRegular]
  simp

lemma branchRegular_grid_stem (S : PrescribedTree n) (r d L : ℕ) (η : ℝ) :
    BranchRegular (stem S r) (grid (n+r) d L) η ↔
      BranchRegular S (grid n (d+r) L) η := by
  induction r generalizing d with
  | zero => simp only [Nat.add_zero]; rfl
  | succ r ih =>
    change BranchRegular (unary (stem S r)) (grid (n+r+1) d L) η ↔ _
    rw [branchRegular_unary]
    have he : (fun j : Fin (n+r+1) => grid (n+r+1) d L j.succ)=grid (n+r) (d+1) L := by
      funext j
      simp [grid,Fin.val_succ,Nat.add_comm,Nat.add_left_comm]
    rw [he,ih]
    rw [show d+1+r=d+(r+1) by omega]

/-- All higher-degree factors below a regularly interior evaluation depth
are uniformly positive; no regularity of a union of shapes is needed. -/
lemma branchRegular_grid_of_lower (S : PrescribedTree n) (d L : ℕ) (η : ℝ)
    (h : η≤(d:ℝ)/(L:ℝ)) : BranchRegular S (grid n d L) η := by
  induction S generalizing d with
  | leaf => trivial
  | @node n k C ih =>
    have h' : η≤((d+1:ℕ):ℝ)/(L:ℝ) := h.trans (by
      apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg L)
      exact_mod_cast Nat.le_succ d)
    constructor
    · intro _
      simpa [grid] using h'
    · intro i
      have he : (fun j : Fin (n+1) => grid (n+1) d L j.succ)=grid n (d+1) L := by
        funext j
        simp [grid,Fin.val_succ,Nat.add_comm,Nat.add_left_comm]
      rw [he]
      exact ih i (d+1) h'

lemma branchRegular_shifted_frame (S : PrescribedTree n) (r d L : ℕ) (η : ℝ)
    (he : η≤((d+r+2:ℕ):ℝ)/(L:ℝ)) :
    BranchRegular (stem (doubled (unary (stem S r))) d)
      (grid (n+r+1+1+d) 0 L) η := by
  rw [branchRegular_grid_stem]
  simp only [Nat.zero_add,doubled,BranchRegular]
  refine ⟨by norm_num,?_⟩
  intro i
  have hgrid : (fun j : Fin (n+r+1+1) => grid (n+r+1+1) d L j.succ)=grid (n+r+1) (d+1) L := by
    funext j
    simp [grid,Fin.val_succ,Nat.add_comm,Nat.add_left_comm]
  rw [hgrid,branchRegular_unary]
  have hgrid' : (fun j : Fin (n+r+1) => grid (n+r+1) (d+1) L j.succ)=grid (n+r) (d+2) L := by
    funext j
    simp [grid,Fin.val_succ,Nat.add_comm,Nat.add_left_comm]
  rw [hgrid',branchRegular_grid_stem]
  apply branchRegular_grid_of_lower
  simpa only [show d+2+r=d+r+2 by omega] using he

end DilutedSpinGlass.PrescribedTree
end

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_ScheduledFrameGeometry
attribute [-instance] _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators
variable {n m : ℕ}

lemma branchRegular_heightCast (h : n=m) (S : PrescribedTree n) (d L : ℕ) (η : ℝ) :
    BranchRegular (heightCast h S) (grid m d L) η ↔ BranchRegular S (grid n d L) η := by
  cases h; rfl

end DilutedSpinGlass.PrescribedTree

namespace DilutedSpinGlass.ReducedTopology
open PrescribedTree
open scoped BigOperators
variable {α : Type} [Fintype α] [DecidableEq α]

omit [Fintype α] [DecidableEq α] in
/-- All target branches except the protected separation vertex are charged. -/
theorem scheduled_frame_target_total (H r d : ℕ) (k : ℕ+) (a : α)
    (C : Fin k → ReducedTopology) (e : (j : Fin k) → (C j).Vertex → {j : α // j≠a})
    (Q : α → Fin (H+1+1+r+1+d)) :
    let Base := PrescribedTree.node k (fun j => realize H (r+1+d+1) (C j) (fun v => (Q (e j v)).val))
    let New := PrescribedTree.node k (fun j => realize H (r+1+1+d+1) (C j) (fun v => (Q (e j v)).val+1))
    let Target := heightCast (shiftedFrameHeight H r d) (splitFrame New (r+1) d)
    branchingCount Target (fun _ => True)=
      branchingCount Target (· ∈ shiftedPrefixDepths (stem Base r) d)+1 := by
  dsimp only
  simp only [branchingCount_heightCast]
  have he : (PrescribedTree.node k (fun j => realize H (r+1+1+d+1) (C j)
      (fun v => (Q (e j v)).val+1))) =
      PrescribedTree.node k (fun j => realize H (r+1+d+1) (C j) (fun v => (Q (e j v)).val)) := by
    congr 1
    funext j
    rw [show r+1+1+d+1=(r+1+d+1)+1 by omega,realize_translate]
  rw [he]
  change branchingCount (stem (doubled (unary (stem _ r))) d) _=_
  exact shifted_prefix_total_count _ d

omit [Fintype α] [DecidableEq α] in
/-- Higher-degree target factors are uniformly interior at every regular
first split. No premise is imposed on an overlay of the two shapes. -/
theorem scheduled_frame_target_regular (H r d : ℕ) (k : ℕ+) (a : α)
    (C : Fin k → ReducedTopology) (e : (j : Fin k) → (C j).Vertex → {j : α // j≠a})
    (Q : α → Fin (H+1+1+r+1+d)) (η : ℝ)
    (heval : η≤((d+r+2:ℕ):ℝ)/((H+1+1+r+1+d:ℕ):ℝ)) :
    let New := PrescribedTree.node k (fun j => realize H (r+1+1+d+1) (C j) (fun v => (Q (e j v)).val+1))
    let Target := heightCast (shiftedFrameHeight H r d) (splitFrame New (r+1) d)
    BranchRegular Target (grid (H+1+1+r+1+d) 0 (H+1+1+r+1+d)) η := by
  dsimp only
  rw [branchRegular_heightCast]
  change BranchRegular (stem (doubled (unary (stem _ r))) d) _ _
  exact branchRegular_shifted_frame _ r d _ η heval

end DilutedSpinGlass.ReducedTopology
end

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_TwoPointLabeling
attribute [-instance] _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass

/-- Finite labeling can pin both protected leaves without changing the full
leaf set; this is not an assumed identification of the two tree experiments. -/
lemma exists_equiv_two_points {α β : Type} [Fintype α] [Fintype β]
    (hcard : Fintype.card α=Fintype.card β) (a b : α) (c d : β)
    (hab : a≠b) (hcd : c≠d) : ∃ e : α ≃ β, e a=c ∧ e b=d := by
  classical
  let e₀ := Fintype.equivOfCardEq hcard
  let e₁ := e₀.trans (Equiv.swap (e₀ a) c)
  have ha : e₁ a=c := by simp [e₁]
  have hb : e₁ b≠c := by rw [← ha]; exact fun h => hab (e₁.injective h).symm
  refine ⟨e₁.trans (Equiv.swap (e₁ b) d),?_,?_⟩
  · simp only [Equiv.trans_apply,ha]
    exact Equiv.swap_apply_of_ne_of_ne hb.symm hcd
  · simp

namespace PrescribedTree

/-- Every split frame has a canonical Option/Fin dictionary labeling with
`none` and the FIRST inserted label at the protected corresponding twin leaves. -/
lemma splitFrame_canonical_labeling {n : ℕ} (S : PrescribedTree n) (r d t : ℕ)
    (b : S.Leaf) (hcard : Fintype.card (splitFrame S r d).Leaf=t+2) :
    ∃ q : Option (Fin (t+1)) ≃ (splitFrame S r d).Leaf,
      q none=splitFrameLeaf S r d 0 b ∧
      q (some (Fin.last t))=splitFrameLeaf S r d 1 b := by
  apply exists_equiv_two_points
  · simpa only [Fintype.card_option,Fintype.card_fin] using hcard.symm
  · simp
  · intro h
    have he := splitFrame_split S r d b
    rw [h,splitDepth_self] at he
    omega

end PrescribedTree
end DilutedSpinGlass
end

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_PhysicalScheduledStep
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.DilutedSpinGlass.UniversalDictionary.reservoirLaw_prob _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.UniversalDictionary
open _root_.MeasureTheory ProbabilityTheory HeterogeneousMarks PhysicalRoot PrescribedTree ConcreteReservoir
open ReducedTopology
open scoped NNReal BigOperators
variable {p : ℕ}


attribute [local instance] OAI.DilutedSpinGlass.UniversalDictionary.physicalScheduledStepDecidableEq
lemma physicalScheduledEnergy_nonneg (M : Model p) (θB hB : ℝ) (N L : ℕ)
    (u : Spec L × ℕ → ℝ) (S : ReducedTopology) (Q : Option S.Vertex → Fin (L+1)) :
    0 ≤ physicalScheduledEnergy M θB hB N L u S Q :=
  integral_nonneg (fun _ => scheduledShapeEnergy_nonneg _ _ _ _ _)

end DilutedSpinGlass.UniversalDictionary
end

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_RegularFrameExtraction
attribute [-instance] _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.ReducedTopology
open DepthAverage

noncomputable local instance regularFrameExtractionDecidableEq_rb0cef7_1 (β : Type) :
    DecidableEq β := Classical.decEq β
lemma admissible_replace_upper (S : ReducedTopology) (q : S.Vertex → ℕ)
    {lo hi hi' : ℕ} (ha : Admissible S q lo hi) (hr : ∀ v, q v<hi') :
    Admissible S q lo hi' := by
  induction S generalizing lo with
  | leaf => trivial
  | node k hk C ih =>
    exact ⟨ha.1,hr none,fun j => ih j _ (ha.2.2 j) (fun v => hr (some ⟨j,v⟩))⟩

/-- Every assignment in the actual regular/admissible parent domain is one
of the literal frames of physical_grid_scheduled_step. The extraction keeps
the complete terminal horizon, evaluation level and first branching level;
it loses neither endpoint cases nor further child branching coordinates. -/
theorem regular_node_frame {L : ℕ} [NeZero L] {η : ℝ} (hη : 0<η)
    (hlarge : 1<η*(L:ℝ)) (k : ℕ+) (hk : 2≤(k:ℕ)) (C : Fin k → ReducedTopology)
    (Q : Option (ReducedTopology.node k hk C).Vertex → Fin L)
    (hQ : regularShapeDomain (.node k hk C) L η Q) :
    ∃ H r d : ℕ, L=H+1+1+r+1+(d+1) ∧ (Q none).val=d+1 ∧
      (Q (some none)).val=r+1+(d+1) ∧
      ∀ j, Admissible (C j) (fun v => (Q (some (some ⟨j,v⟩))).val)
        (r+1+(d+1)+1) (r+1+(d+1)+1+H) := by
  have hL : (0:ℝ)<L := Nat.cast_pos.mpr (NeZero.pos L)
  have hdpos : 0<(Q none).val := by
    have hh := (lt_div_iff₀ hL).mp (hQ.1.1 none).1
    have hh' : (0:ℝ)<((Q none).val:ℝ) := (mul_pos hη hL).trans hh
    exact_mod_cast hh'
  have heval : (Q none).val+1≤(Q (some none)).val := hQ.2.1
  have hroom := regular_room hlarge hQ.1
  let d := (Q none).val-1
  let r := (Q (some none)).val-(Q none).val-1
  let H := L-(Q (some none)).val-2
  have hd : (Q none).val=d+1 := by dsimp [d]; omega
  have hr : (Q (some none)).val=r+1+(d+1) := by dsimp [r,d]; omega
  have hH : L=H+1+1+r+1+(d+1) := by
    have hh := hroom (some none)
    dsimp [H,r,d]
    omega
  refine ⟨H,r,d,hH,hd,hr,?_⟩
  intro j
  have ha := admissible_replace_upper (C j) _ (hQ.2.2.2 j)
    (hi' := r+1+(d+1)+1+H) (by
      intro v
      have hh := hroom (some (some ⟨j,v⟩))
      change (Q (some (some ⟨j,v⟩))).val < r+1+(d+1)+1+H
      omega)
  simpa only [hr] using ha

end DilutedSpinGlass.ReducedTopology
end

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_ScheduledEnergyBound
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.DilutedSpinGlass.UniversalDictionary.reservoirLaw_prob _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.FiniteLaw
open scoped BigOperators
variable {Ω : Type} [Fintype Ω]

lemma centered_square_le_one (P : FiniteLaw Ω) (f : Ω → ℝ) (hf : ∀ x, |f x|≤1) :
    P.expect (fun x => (f x-P.expect f)^2)≤1 := by
  have hs : P.expect (fun x => f x^2)≤1 := by
    calc
      _ ≤ P.expect (fun _ => 1) := P.expect_mono (fun x => by
        simpa using sq_le_sq.mpr (show |f x|≤|(1:ℝ)| by simpa using hf x))
      _ = _ := P.expect_const 1
  have he : P.expect (fun x => (f x-P.expect f)^2)=P.expect (fun x => f x^2)-(P.expect f)^2 := by
    calc
      _ = P.expect (fun x => f x^2-2*P.expect f*f x+(P.expect f)^2) := P.expect_congr (fun x => by ring)
      _ = _ := by simp; ring
  rw [he]
  nlinarith [sq_nonneg (P.expect f)]

lemma covariance_sq_le_one (P : FiniteLaw Ω) (f g : Ω → ℝ)
    (hf : ∀ x, |f x|≤1) (hg : ∀ x, |g x|≤1) : (P.covariance f g)^2≤1 := by
  rw [P.covariance_centered]
  exact (P.expect_mul_sq_le _ _).trans (by
    have hh := mul_le_mul (P.centered_square_le_one f hf) (P.centered_square_le_one g hg)
      (P.expect_nonneg (fun x => sq_nonneg (g x-P.expect g))) zero_le_one
    simpa only [one_mul] using hh)

lemma covarianceEnergy_le_one {N : ℕ} (P : FiniteLaw Ω) (X : Ω → Fin N → ℝ)
    (hX : ∀ x i, |X x i|≤1) : P.covarianceEnergy X≤1 := by
  by_cases hN : N=0
  · simp [covarianceEnergy,hN]
  · have hpos : 0<(N:ℝ)^2 := sq_pos_of_pos (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hN))
    unfold covarianceEnergy
    apply (div_le_iff₀ hpos).mpr
    calc
      _ ≤ ∑ i : Fin N, ∑ j : Fin N, (1:ℝ) := by
        apply Finset.sum_le_sum; intro i _
        apply Finset.sum_le_sum; intro j _
        exact P.covariance_sq_le_one _ _ (fun x => hX x i) (fun x => hX x j)
      _ = _ := by simp; ring

end DilutedSpinGlass.FiniteLaw
namespace DilutedSpinGlass.PrescribedTree
variable {Ω : Type} [Fintype Ω] {n N : ℕ}

lemma shapeEnergyAt_le_one (C : PrescribedTree n) (d : ℕ)
    (T : KernelTower Ω (n+1+d)) (X : FinitePath Ω (n+1+d) → Fin N → ℝ)
    (hX : ∀ y i, |X y i|≤1) : shapeEnergyAt C d T X≤1 := by
  induction d with
  | zero =>
      unfold shapeEnergyAt childEnergy
      apply FiniteLaw.covarianceEnergy_le_one
      intro a i
      exact leafProduct_bound C (fun y => hX (a.1,y) i) a.2
  | succ d ih =>
      exact (T.1.expect_mono (fun a => ih (T.2 a) (fun y => X (a,y))
        (fun y i => hX (a,y) i))).trans_eq (T.1.expect_const 1)

end DilutedSpinGlass.PrescribedTree
namespace DilutedSpinGlass.ReducedTopology
open PrescribedTree
variable {Ω : Type} [Fintype Ω] {N L : ℕ}

lemma scheduledShapeEnergy_le_one (d : ℕ) (S : ReducedTopology) (q : S.Vertex → ℕ)
    (T : KernelTower Ω L) (X : FinitePath Ω L → Fin N → ℝ)
    (hX : ∀ y i, |X y i|≤1) : scheduledShapeEnergy L d S q T X≤1 := by
  unfold scheduledShapeEnergy
  split_ifs
  · exact shapeEnergyAt_le_one _ _ _ _ (fun _ index => hX _ index)
  · exact zero_le_one

end DilutedSpinGlass.ReducedTopology
namespace DilutedSpinGlass.UniversalDictionary
open _root_.MeasureTheory ProbabilityTheory HeterogeneousMarks PhysicalRoot PrescribedTree ConcreteReservoir
open ReducedTopology
open scoped NNReal BigOperators
variable {p : ℕ}

noncomputable local instance scheduledEnergyBoundDecidableEq_rb0cef7_1 (type : Type) :
    DecidableEq type := Classical.decEq type
/-- Unit bound for the actual physical covariance, including N=0, leaves,
inadmissible schedules and the countable variable-alphabet root. -/
lemma physicalScheduledEnergy_le_one (M : Model p) (θB hB : ℝ) (N L : ℕ)
    (u : Spec L × ℕ → ℝ) (S : ReducedTopology) (Q : Option S.Vertex → Fin (L+1)) :
    physicalScheduledEnergy M θB hB N L u S Q≤1 := by
  unfold physicalScheduledEnergy
  calc
    _ ≤ ∫ _, (1:ℝ) ∂fullRootLaw (fun _ : Fin N => M.field.toMeasure) (bondLaw M N)
        (markLaw (weights L) N) (M.alpha*N) (scoreRate N) := by
      apply integral_mono_of_nonneg
      · exact Filter.Eventually.of_forall (fun _ => scheduledShapeEnergy_nonneg _ _ _ _ _)
      · exact integrable_const _
      · exact Filter.Eventually.of_forall (fun _ => scheduledShapeEnergy_le_one _ _ _ _ _
          (fun _ _ => readVector_bound _ _ _))
    _ = 1 := by simp

end DilutedSpinGlass.UniversalDictionary
end

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_ScheduledProtectedLabels
attribute [-instance] _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators

lemma leaves_stem {n : ℕ} (S : PrescribedTree n) (r : ℕ) :
    leaves (stem S r)=leaves S := by
  induction r with
  | zero => rfl
  | succ r ih => rw [stem,leaves_unary,ih]

lemma leaves_doubled {n : ℕ} (S : PrescribedTree n) :
    leaves (doubled S)=2*leaves S := by
  change (∑ _ : Fin 2, leaves S)=2*leaves S
  simp [Nat.two_mul]

lemma leaves_splitFrame {n : ℕ} (S : PrescribedTree n) (r d : ℕ) :
    leaves (splitFrame S r d)=2*leaves S := by
  rw [splitFrame,leaves_stem,leaves_doubled,leaves_stem]

end DilutedSpinGlass.PrescribedTree

namespace DilutedSpinGlass.ReducedTopology
open PrescribedTree
open scoped BigOperators

/-- The shifted children retain exactly their topology leaves. In particular
one fixed dictionary arity works for every admissible depth assignment. -/
lemma delayed_node_leaves (H lo : ℕ) (k : ℕ+) (hk : 2≤(k:ℕ))
    (C : Fin k → ReducedTopology) (q : (j : Fin k) → (C j).Vertex → ℕ)
    (had : ∀ j, Admissible (C j) (q j) lo (lo+H)) :
    leaves (PrescribedTree.node k (fun j => realize H (lo+1) (C j)
      (fun v => q j v+1))) = Fintype.card (ReducedTopology.node k hk C).Leaf := by
  change (∑ j, leaves (realize H (lo+1) (C j) (fun v => q j v+1))) =
    Fintype.card ((j : Fin k) × (C j).Leaf)
  rw [Fintype.card_sigma]
  exact Finset.sum_congr rfl (fun j _ => by
    rw [realize_translate H lo 1,realize_leaves H lo (C j) (q j) (had j)])

/-- Actual assignment-dependent protected labeling for the genuinely delayed
multileaf target. The dictionary size depends only on the reduced topology,
not the grid horizon or any of its branching-coordinate assignments. -/
theorem delayed_node_protected_labeling (H lo r d : ℕ) (k : ℕ+)
    (hk : 2≤(k:ℕ)) (C : Fin k → ReducedTopology)
    (q : (j : Fin k) → (C j).Vertex → ℕ)
    (had : ∀ j, Admissible (C j) (q j) lo (lo+H)) :
    let S := PrescribedTree.node k (fun j => realize H (lo+1) (C j)
      (fun v => q j v+1))
    let t := 2*Fintype.card (ReducedTopology.node k hk C).Leaf-2
    ∃ (b : S.Leaf) (e : Option (Fin (t+1)) ≃ (splitFrame S r d).Leaf),
      e none=splitFrameLeaf S r d 0 b ∧
      e (some (Fin.last t))=splitFrameLeaf S r d 1 b := by
  dsimp only
  let S := PrescribedTree.node k (fun j => realize H (lo+1) (C j)
    (fun v => q j v+1))
  have hcard := delayed_node_leaves H lo k hk C q had
  have hpos := leaves_pos S
  have hc : Fintype.card (splitFrame S r d).Leaf =
      2*Fintype.card (ReducedTopology.node k hk C).Leaf-2+2 := by
    rw [card_leaf,leaves_splitFrame]
    change leaves S = _ at hcard
    rw [hcard]
    omega
  obtain ⟨b⟩ := leaf_nonempty S
  obtain ⟨e,he₀,he₁⟩ := splitFrame_canonical_labeling S r d
    (2*Fintype.card (ReducedTopology.node k hk C).Leaf-2) b hc
  exact ⟨b,e,he₀,he₁⟩

end DilutedSpinGlass.ReducedTopology
end

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_ScheduledRelativeCharge
attribute [-instance] _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators
variable {I : Type} [Fintype I] [DecidableEq I] {n : ℕ}

lemma partialKappa_ratio_bijective (T : PrescribedTree n) (q : I → T.Leaf)
    (hq : Function.Bijective q) (m : Fin (n+1) → ℝ) (u v : I) :
    partialKappa T m (Finset.univ.image q)/partialKappa T m ((insert v ({u}:Finset I)).image q)=
      partialKappa T m Finset.univ/partialKappa T m {q v,q u} := by
  classical
  rw [Finset.image_univ_of_surjective hq.2]
  simp only [Finset.image_insert,Finset.image_singleton]

end DilutedSpinGlass.PrescribedTree
end

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_TopologyChargeBound
attribute [-instance] _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators

/-- Exact leaf budget, counting vertices with multiplicity and not merely
branching depth values. Unary grid levels consume no budget. -/
lemma branch_budget {n : ℕ} (S : PrescribedTree n) :
    branchingCount S (fun _ => True)+branchExcess S+1=leaves S := by
  classical
  induction S with
  | leaf => rfl
  | @node n k C ih =>
    have hs : (∑ i, branchingCount (C i) (fun _ => True))+
        (∑ i, branchExcess (C i))+(k:ℕ)=∑ i, leaves (C i) := by
      calc
        _ = ∑ i, (branchingCount (C i) (fun _ => True)+branchExcess (C i)+1) := by
          simp [Finset.sum_add_distrib]
        _ = _ := Finset.sum_congr rfl (fun i _ => ih i)
    simp only [branchingCount,branchExcess,leaves,true_and]
    have hp : 0 < (k:ℕ) := k.property
    split <;> omega

lemma branchingDepths_card_le {n : ℕ} (S : PrescribedTree n) :
    (branchingDepths S).card≤branchingCount S (fun _ => True) := by
  classical
  rw [branchingCount_eq_vertexSum]
  simp only [and_true]
  calc
    _ ≤ (Finset.univ.filter (fun v : S.Internal => 1<vertexArity S v)).card := Finset.card_image_le
    _ = _ := by rw [Finset.card_eq_sum_ones,Finset.sum_filter]

lemma shiftedPrefixDepths_card_le {n : ℕ} (S : PrescribedTree n) (d : ℕ) :
    (shiftedPrefixDepths S d).card≤leaves S := by
  calc
    _ ≤ (shiftedTwinDepths S).card := Finset.card_image_le
    _ ≤ (branchingDepths S).card := Finset.card_image_le
    _ ≤ branchingCount S (fun _ => True) := branchingDepths_card_le S
    _ ≤ leaves S := by have h := branch_budget S; omega

lemma chargeBound_le_pow {C D : ℝ} (hC : 0≤C) (hD : 0≤D) (k b : ℕ) :
    chargeBound C D k b≤(C+D)^k := by
  induction k generalizing b with
  | zero => simp only [chargeBound,pow_zero]; split <;> norm_num
  | succ k ih =>
    cases b with
    | zero =>
      simp only [chargeBound,pow_succ]
      calc
        _ ≤ C*(C+D)^k := mul_le_mul_of_nonneg_left (ih 0) hC
        _ ≤ _ := by nlinarith [pow_nonneg (add_nonneg hC hD) k]
    | succ b =>
      simp only [chargeBound,pow_succ]
      calc
        _ ≤ C*(C+D)^k+D*(C+D)^k := add_le_add
          (mul_le_mul_of_nonneg_left (ih _) hC) (mul_le_mul_of_nonneg_left (ih _) hD)
        _ = _ := by ring

/-- A topology-only constant for the genuine relative signed-history cost.
The grid size is absent. Its hypotheses are just leaf/depth counts, not a
covariance estimate or any desired limiting conclusion. -/
theorem shiftedCharge_relative_uniform {L : ℕ} (hL : 0<L) (Q : Finset ℕ)
    (T S : PrescribedTree L) (k R : ℕ) (hQ : Q.card≤R)
    (hS : leaves S+k≤R) (hT : leaves T≤R)
    (a b : T.Leaf) (hab : a≠b) (η : ℝ) (hη : 0<η)
    (hr : BranchRegular T (grid L 0 L) η)
    (hb : branchingCount T (fun _ => True)=branchingCount T (· ∈ Q)+1) :
    shiftedCharge Q T S k /
      |partialKappa T (grid L 0 L) Finset.univ/partialKappa T (grid L 0 L) {b,a}| ≤
      (((2+(R:ℝ))*(R:ℝ))^k)/(min η 1)^R := by
  classical
  have hA := chargeBound_nonneg (C := 2*(leaves S+k:ℕ))
    (D := (Q.card:ℝ)*(leaves S+k:ℕ)) (by positivity) (by positivity) k
    (branchingCount T (· ∈ Q))
  have hp := chargeBound_le_pow (C := 2*(leaves S+k:ℕ))
    (D := (Q.card:ℝ)*(leaves S+k:ℕ)) (by positivity) (by positivity) k
    (branchingCount T (· ∈ Q))
  have hv : (2*(leaves S+k:ℕ)+(Q.card:ℝ)*(leaves S+k:ℕ))≤(2+(R:ℝ))*(R:ℝ) := by
    have hSr : ((leaves S+k:ℕ):ℝ)≤R := by exact_mod_cast hS
    have hQr : (Q.card:ℝ)≤R := by exact_mod_cast hQ
    nlinarith [mul_nonneg (sub_nonneg.mpr hSr) (by positivity : 0≤(R:ℝ)),
      mul_nonneg (sub_nonneg.mpr hQr) (show 0≤((leaves S+k:ℕ):ℝ) by positivity)]
  have hex : branchExcess T≤R := by have hh := branch_budget T; omega
  have hm : 0 < min η 1 := lt_min hη zero_lt_one
  have he : (min η 1)^R≤η^(branchExcess T) :=
    (pow_le_pow_of_le_one hm.le (min_le_right _ _) hex).trans
      (pow_le_pow_left₀ hm.le (min_le_left _ _) _)
  exact (shiftedCharge_relative_bound hL Q T S k a b hab η hη hr hb).trans
    (div_le_div₀ (by positivity) (hp.trans (pow_le_pow_left₀ (by positivity) hv _))
      (pow_pos hm _) he)

end DilutedSpinGlass.PrescribedTree
end

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_RegularNodeGeometry
attribute [-instance] _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace DilutedSpinGlass.ReducedTopology
open PrescribedTree
open scoped BigOperators

lemma node_realize_leaves (H lo : ℕ) (k : ℕ+) (hk : 2≤(k:ℕ))
    (C : Fin k → ReducedTopology) (q : (j : Fin k) → (C j).Vertex → ℕ)
    (had : ∀ j, Admissible (C j) (q j) lo (lo+H)) :
    leaves (PrescribedTree.node k (fun j => realize H lo (C j) (q j))) =
      Fintype.card (ReducedTopology.node k hk C).Leaf := by
  change (∑ j, leaves (realize H lo (C j) (q j))) = Fintype.card ((j : Fin k) × (C j).Leaf)
  rw [Fintype.card_sigma]
  exact Finset.sum_congr rfl (fun j _ => realize_leaves H lo (C j) (q j) (had j))

lemma node_old_realize_leaves (H lo : ℕ) (k : ℕ+) (hk : 2≤(k:ℕ))
    (C : Fin k → ReducedTopology) (q : (j : Fin k) → (C j).Vertex → ℕ)
    (had : ∀ j, Admissible (C j) (q j) lo (lo+H)) :
    leaves (PrescribedTree.node k (fun j => realize (H+1) lo (C j) (q j))) =
      Fintype.card (ReducedTopology.node k hk C).Leaf := by
  change (∑ j, leaves (realize (H+1) lo (C j) (q j))) = Fintype.card ((j : Fin k) × (C j).Leaf)
  rw [Fintype.card_sigma]
  apply Finset.sum_congr rfl
  intro j _
  rw [realize_bottom H lo (C j) (q j) (had j),leaves_bottom,
    realize_leaves H lo (C j) (q j) (had j)]

variable {α I : Type} [Fintype α] [DecidableEq α] [Fintype I] [DecidableEq I]

omit [Fintype α] [DecidableEq α] in
/-- The actual frame charging cost is bounded only by the reduced topology
and the separation parameter. The canonical ratio and vertex multiplicities
are retained; no maximization over a grid-dependent majorant is used. -/
theorem node_frame_charge_uniform (H r d : ℕ) (k : ℕ+) (hk : 2≤(k:ℕ)) (a : α)
    (C : Fin k → ReducedTopology) (e : (j : Fin k) → (C j).Vertex → {j : α // j≠a})
    (Q : α → Fin (H+1+1+r+1+d))
    (had : ∀ j, Admissible (C j) (fun v => (Q (e j v)).val) (r+1+d+1) (r+1+d+1+H))
    {η : ℝ} (hη : 0<η)
    (heval : η≤((d+r+2:ℕ):ℝ)/((H+1+1+r+1+d:ℕ):ℝ)) :
    let Base := PrescribedTree.node k (fun j => realize H (r+1+d+1) (C j) (fun v => (Q (e j v)).val))
    let Old := PrescribedTree.node k (fun j => realize (H+1) (r+1+d+1) (C j) (fun v => (Q (e j v)).val))
    let New := PrescribedTree.node k (fun j => realize H (r+1+1+d+1) (C j) (fun v => (Q (e j v)).val+1))
    let Target := heightCast (shiftedFrameHeight H r d) (splitFrame New (r+1) d)
    let S := splitFrame Old r d
    let B := shiftedPrefixDepths (stem Base r) d
    let t := 2*Fintype.card (ReducedTopology.node k hk C).Leaf-2
    ∀ (q : I → Target.Leaf), Function.Bijective q → ∀ (u v : I), u≠v →
    shiftedCharge B Target S (t+1) /
      |partialKappa Target (grid (H+1+1+r+1+d) 0 (H+1+1+r+1+d)) (Finset.univ.image q)/
        partialKappa Target (grid (H+1+1+r+1+d) 0 (H+1+1+r+1+d)) ((insert v ({u}:Finset I)).image q)| ≤
      nodeChargeConstant k hk C η := by
  dsimp only
  intro q hq u v huv
  rw [partialKappa_ratio_bijective _ q hq]
  have hbase := node_realize_leaves H (r+1+d+1) k hk C (fun j v => (Q (e j v)).val) had
  have hold := node_old_realize_leaves H (r+1+d+1) k hk C (fun j v => (Q (e j v)).val) had
  have hnew := delayed_node_leaves H (r+1+d+1) k hk C (fun j v => (Q (e j v)).val) had
  rw [show r+1+d+1+1=r+1+1+d+1 by omega] at hnew
  have hpos := leaf_card_pos (ReducedTopology.node k hk C)
  apply shiftedCharge_relative_uniform (by omega) _ _ _ _ (nodeHistoryBudget k hk C)
  · apply (shiftedPrefixDepths_card_le _ _).trans
    rw [leaves_stem,hbase]
    unfold nodeHistoryBudget
    omega
  · rw [leaves_splitFrame,hold]
    unfold nodeHistoryBudget
    omega
  · rw [leaves_heightCast,leaves_splitFrame,hnew]
    unfold nodeHistoryBudget
    omega
  · exact fun h => huv (hq.1 h)
  · exact hη
  · exact scheduled_frame_target_regular H r d k a C e Q η heval
  · exact scheduled_frame_target_total H r d k a C e Q

end DilutedSpinGlass.ReducedTopology

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_RegularNodeEstimates
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.DilutedSpinGlass.UniversalDictionary.reservoirLaw_prob _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass.UniversalDictionary
open _root_.MeasureTheory ProbabilityTheory HeterogeneousMarks PhysicalRoot PrescribedTree ConcreteReservoir
open ReducedTopology
open scoped NNReal BigOperators
variable {p : ℕ}

attribute [local instance] OAI.DilutedSpinGlass.UniversalDictionary.regularNodeEstimatesDecidableEq
lemma physicalChildMass_nonneg (M : Model p) (θB hB : ℝ) (N L : ℕ)
    (u : Spec L × ℕ → ℝ) (k : ℕ+) (hk : 2≤(k:ℕ)) (C : Fin k → ReducedTopology)
    (s : Bool) (Q : Option (ReducedTopology.node k hk C).Vertex → Fin (L+1)) :
    0≤physicalChildMass M θB hB N L u k hk C s Q := by
  unfold physicalChildMass
  positivity

lemma physicalChildMass_le_square (M : Model p) (θB hB : ℝ) (N L : ℕ)
    (u : Spec L × ℕ → ℝ) (k : ℕ+) (hk : 2≤(k:ℕ)) (C : Fin k → ReducedTopology)
    (s : Bool) (Q : Option (ReducedTopology.node k hk C).Vertex → Fin (L+1)) :
    physicalChildMass M θB hB N L u k hk C s Q≤(k:ℝ)^2 := by
  unfold physicalChildMass
  calc
    _ ≤ (k:ℝ)*∑ j : Fin k, (1:ℝ) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Finset.sum_le_sum
      intro j _
      exact (Real.sqrt_le_sqrt (physicalScheduledEnergy_le_one M θB hB N L u (C j) _)).trans_eq
        Real.sqrt_one
    _ = _ := by simp; ring

lemma physicalChildMass_le_sqrt (M : Model p) (θB hB : ℝ) (N L : ℕ)
    (u : Spec L × ℕ → ℝ) (k : ℕ+) (hk : 2≤(k:ℕ)) (C : Fin k → ReducedTopology)
    (s : Bool) (Q : Option (ReducedTopology.node k hk C).Vertex → Fin (L+1)) :
    physicalChildMass M θB hB N L u k hk C s Q ≤
      (k:ℝ)*Real.sqrt (physicalChildMass M θB hB N L u k hk C s Q) := by
  have h := Real.sqrt_le_sqrt (physicalChildMass_le_square M θB hB N L u k hk C s Q)
  rw [Real.sqrt_sq (by positivity : (0:ℝ)≤k)] at h
  have hm := mul_le_mul_of_nonneg_right h
    (Real.sqrt_nonneg (physicalChildMass M θB hB N L u k hk C s Q))
  simpa only [← sq,Real.sq_sqrt (physicalChildMass_nonneg M θB hB N L u k hk C s Q)] using hm


lemma physicalNodeShift_nonneg (M : Model p) (θB hB : ℝ) (N L : ℕ)
    (u : Spec L × ℕ → ℝ) (k : ℕ+) (hk : 2≤(k:ℕ)) (C : Fin k → ReducedTopology)
    (Q : Option (ReducedTopology.node k hk C).Vertex → Fin (L+1)) :
    0≤physicalNodeShift M θB hB N L u k hk C Q :=
  integral_nonneg (fun _ => projectionShiftError_nonneg _ _ _ _ _ _)

lemma multileaf_scalar_bound {η c v δ err w w' h ch pa K P k : ℝ}
    (hc : η ≤ c) (hc1 : c≤1) (hv : 0≤v) (hw : 0≤w) (hh : 0≤h)
    (hch : ch≤K) (hpa : pa≤P) (hwk : w≤k*Real.sqrt w)
    (hstep : c*v≤2*(2*δ+err+(2*Real.sqrt w'+h)*ch+pa*(2*Real.sqrt w))+c*(16*w)) :
    η*v ≤ 4*δ+2*err+4*K*Real.sqrt w'+2*K*h+(4*P+16*k)*Real.sqrt w := by
  have h₁ := mul_le_mul_of_nonneg_left hch (by positivity : 0≤2*Real.sqrt w'+h)
  have h₂ := mul_le_mul_of_nonneg_right hpa (by positivity : 0≤2*Real.sqrt w)
  have h₃ := mul_le_mul_of_nonneg_right hc1 (by positivity : 0≤16*w)
  have h₄ := mul_le_mul_of_nonneg_left hwk (by norm_num : (0:ℝ)≤16)
  have h₅ := mul_le_mul_of_nonneg_right hc hv
  nlinarith only [hstep,h₁,h₂,h₃,h₄,h₅]

end DilutedSpinGlass.UniversalDictionary

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_RegularNodeProducer
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.DilutedSpinGlass.UniversalDictionary.reservoirLaw_prob _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass.UniversalDictionary
open _root_.MeasureTheory ProbabilityTheory HeterogeneousMarks PhysicalRoot PrescribedTree ConcreteReservoir
open ReducedTopology
open scoped NNReal BigOperators
variable {p : ℕ}
attribute [local irreducible] projectionShiftError matrixProjectionError oldProjectionError
    matrixObservableHistory KernelTower.halfTripleDifferenceAt splitProjector

attribute [local instance] OAI.DilutedSpinGlass.UniversalDictionary.instDecidableEq_solutions_1
/-- On every regular admissible parent assignment there is one literal signed
matrix experiment. Its geometry is fixed before the physical size and probe
parameters are chosen, and its charging constants are independent of the grid.
This is the pointwise producer for the averaged decorrelation induction. -/
theorem regular_node_pointwise_sat_oai (M : Model p) (θB hB : ℝ) (L : ℕ)
    (k : ℕ+) (hk : 2≤(k:ℕ)) (C : Fin k → ReducedTopology)
    {η : ℝ} (hη : 0<η) (hlarge : 1<η*(L+1:ℕ))
    (Q : Option (ReducedTopology.node k hk C).Vertex → Fin (L+1))
    (hQ : regularShapeDomain (.node k hk C) (L+1) η Q) :
    ∃ (S T : PrescribedTree (L+1)) (a : S.Leaf)
      (q : Option (Fin (2*Fintype.card (ReducedTopology.node k hk C).Leaf-2+1)) → T.Leaf)
      (J : ℝ), ∀ (N : ℕ) (u : Spec L × ℕ → ℝ),
    η*physicalScheduledEnergy M θB hB N L u (.node k hk C) Q ≤
      4*((L+1:ℕ):ℝ)⁻¹ +
      2*(|physicalTreeMatrixCovariance (gridExponents L) S a M θB hB N u T q|/|J|) +
      4*nodeChargeConstant k hk C η*Real.sqrt (physicalChildMass M θB hB N L u k hk C true Q) +
      2*nodeChargeConstant k hk C η*physicalNodeShift M θB hB N L u k hk C Q +
      (4*(nodeHistoryBudget k hk C:ℝ)+16*(k:ℝ))*
        Real.sqrt (physicalChildMass M θB hB N L u k hk C false Q) := by
  obtain ⟨H,r,d,hL,hd,he,had⟩ := regular_node_frame hη hlarge k hk C Q hQ
  have hL' : L=H+1+1+r+1+d := by omega
  subst L
  let L₀ := H+1+1+r+1+d
  let t := 2*Fintype.card (ReducedTopology.node k hk C).Leaf-2
  let OldNode := PrescribedTree.node k (fun j => realize (H+1) (r+1+(d+1)+1) (C j)
    (fun v => (Q (some (some ⟨j,v⟩))).val))
  let NewNode := PrescribedTree.node k (fun j => realize H (r+1+1+(d+1)+1) (C j)
    (fun v => (Q (some (some ⟨j,v⟩))).val+1))
  let BaseNode := PrescribedTree.node k (fun j => realize H (r+1+(d+1)+1) (C j)
    (fun v => (Q (some (some ⟨j,v⟩))).val))
  let S := splitFrame OldNode r (d+1)
  let RawTarget := splitFrame NewNode (r+1) (d+1)
  let ht := shiftedFrameHeight H r (d+1)
  let T := heightCast ht RawTarget
  obtain ⟨b⟩ := leaf_nonempty OldNode
  have hlabel := delayed_node_protected_labeling H (r+1+(d+1)+1) (r+1) (d+1) k hk C
    (fun j v => (Q (some (some ⟨j,v⟩))).val) had
  dsimp only at hlabel
  rw [show r+1+(d+1)+1+1=r+1+1+(d+1)+1 by omega] at hlabel
  obtain ⟨b',q₀,hq₀,hq₁⟩ := hlabel
  let q : Option (Fin (t+1)) → T.Leaf := fun i => leafHeightCast ht RawTarget (q₀ i)
  let a : S.Leaf := splitFrameLeaf OldNode r (d+1) 0 b
  let v : Option (Fin (t+1)) := some (Fin.last t)
  let m : Fin (L₀+2) → ℝ := Fin.cons 0 (gridExponents L₀)
  let J := partialKappa T m (Finset.univ.image q)/partialKappa T m ((insert v ({none}:Finset _)).image q)
  refine ⟨S,T,a,q,J,?_⟩
  intro N u
  have hstep := physical_grid_scheduled_step M θB hB N H r d u k hk (some none) C
    (fun j => childBranchCoordinates (hk := hk) j) Q he had hlarge hQ.1
    b b' q₀ q₀.bijective hq₀ hq₁
  dsimp only at hstep
  have hroom := DepthAverage.regular_room hlarge hQ.1
  have hrot (i : Option (ReducedTopology.node k hk C).Vertex) :
      ((finRotate (L₀+1)) (Q i)).val=(Q i).val+1 :=
    DepthAverage.rotate_val_of_room _ (hroom i)
  have hparent : (fun v => (Q (some v)).val) =
      rootSchedule (hk := hk) (r+1+(d+1)) (fun j v => (Q (some (some ⟨j,v⟩))).val) := by
    funext v
    cases v with
    | none => exact he
    | some v => rfl
  have henergy : physicalScheduledEnergy M θB hB N L₀ u (.node k hk C) Q =
      ∫ z, scheduledShapeEnergy (L₀+1) (d+1) (.node k hk C)
        (rootSchedule (r+1+(d+1)) (fun j v => (Q (some (some ⟨j,v⟩))).val))
        (rootTower (KernelTower.terminalTower (fun _ : Fin N => false) FiniteLaw.uniform L₀)
          (fun i : Labels L₀ (Site N) => prior i.1.1) (gridExponents L₀) (physicalBase M θB hB N)
          (dictionaryFactor (observableAt direction N) (observableAt anchor N) u) z)
        (rootVector (readVector (fun v x => readSpin (KernelTower.terminalState L₀ x) v))
          (I := Labels L₀ (Site N)) (A := fun i => Alphabet i.1.1) (X := Bond p N) (Y := ℝ) (M := N) z)
        ∂fullRootLaw (fun _ : Fin N => M.field.toMeasure) (bondLaw M N)
          (markLaw (weights L₀) N) (M.alpha*N) (scoreRate N) := by
    unfold physicalScheduledEnergy
    rw [hd,hparent]
  have hchild (s : Bool) : physicalChildMass M θB hB N L₀ u k hk C s Q =
      (k:ℝ)*∑ j, Real.sqrt (∫ z, scheduledShapeEnergy (L₀+1)
        (r+1+(d+1)+(if s then 1 else 0)) (C j)
        (fun v => (Q (some (some ⟨j,v⟩))).val+(if s then 1 else 0))
        (rootTower (KernelTower.terminalTower (fun _ : Fin N => false) FiniteLaw.uniform L₀)
          (fun i : Labels L₀ (Site N) => prior i.1.1) (gridExponents L₀) (physicalBase M θB hB N)
          (dictionaryFactor (observableAt direction N) (observableAt anchor N) u) z)
        (rootVector (readVector (fun v x => readSpin (KernelTower.terminalState L₀ x) v))
          (I := Labels L₀ (Site N)) (A := fun i => Alphabet i.1.1) (X := Bond p N) (Y := ℝ) (M := N) z)
        ∂fullRootLaw (fun _ : Fin N => M.field.toMeasure) (bondLaw M N)
          (markLaw (weights L₀) N) (M.alpha*N) (scoreRate N)) := by
    cases s <;> simp only [physicalChildMass,physicalScheduledEnergy,
      DepthAverage.coordinateProjection,childCoordinates,DepthAverage.shiftPerm,
      Bool.false_eq_true,ite_false,ite_true,Equiv.refl_apply,hrot,
      he,Nat.add_zero]
  have hold := hchild false
  have hnew := hchild true
  simp only [Bool.false_eq_true,ite_false,Nat.add_zero] at hold
  simp only [ite_true,show r+1+(d+1)+1=r+1+1+(d+1) by omega] at hnew
  have hg : m = grid (L₀+1) 0 (L₀+1) := gridExponents_cons L₀
  have hbij : Function.Bijective q := (leafHeightCast_bijective ht RawTarget).comp q₀.bijective
  have hfirst : η≤((d+1+r+2:ℕ):ℝ)/((H+1+1+r+1+(d+1):ℕ):ℝ) := by
    have hx := (hQ.1.1 (some none)).1.le
    dsimp only [DepthAverage.normalized] at hx
    rw [he] at hx
    exact hx.trans (div_le_div_of_nonneg_right (by exact_mod_cast (show r+1+(d+1)≤d+1+r+2 by omega)) (by positivity))
  have hcharge := node_frame_charge_uniform H r (d+1) k hk (some none) C
    (fun j => childBranchCoordinates (hk := hk) j) Q had hη hfirst q hbij none v (by simp [v])
  have hpair : pairHistoryMass S m a ≤ (nodeHistoryBudget k hk C:ℝ) := by
    rw [hg,pairHistoryMass_grid (L := L₀+1) (by omega) S a]
    dsimp only [S]
    rw [leaves_splitFrame,node_old_realize_leaves H (r+1+(d+1)+1) k hk C _ had]
    unfold nodeHistoryBudget
    push_cast
    linarith
  have hc : η≤(((d+1:ℕ):ℝ)+2)/((L₀+1:ℕ):ℝ) := by
    have hx := (hQ.1.1 none).1.le
    dsimp only [DepthAverage.normalized] at hx
    rw [hd] at hx
    exact hx.trans (div_le_div_of_nonneg_right (by linarith) (by positivity))
  have hc1 : (((d+1:ℕ):ℝ)+2)/((L₀+1:ℕ):ℝ)≤1 := by
    apply (div_le_one (by positivity)).mpr
    dsimp only [L₀]
    push_cast
    linarith
  change _ ≤ 2*(2*((L₀+1:ℕ):ℝ)⁻¹+
      |physicalTreeMatrixCovariance (gridExponents L₀) S a M θB hB N u T q|/|J|+
      (2*Real.sqrt _ + physicalNodeShift M θB hB N L₀ u k hk C Q)*
        shiftedCharge (shiftedPrefixDepths (stem BaseNode r) (d+1)) T S
          (v::canonicalMatrixTail t).length/|J|+
      pairHistoryMass S m a*(2*Real.sqrt _)) + _ at hstep
  dsimp only [childBranchCoordinates] at hstep
  rw [← henergy,← hold,← hnew] at hstep
  rw [List.length_cons,canonicalMatrixTail_length] at hstep
  have hcharge' : shiftedCharge (shiftedPrefixDepths (stem BaseNode r) (d+1)) T S (t+1)/|J| ≤
      nodeChargeConstant k hk C η := by
    simp only [J,hg]
    convert hcharge using 1
    all_goals try with_reducible_and_instances rfl
    dsimp only [childBranchCoordinates,BaseNode,T,S,t,RawTarget,NewNode,OldNode,L₀]
    congr 4
  have hs := multileaf_scalar_bound
    (δ := ((L₀+1:ℕ):ℝ)⁻¹)
    (err := |physicalTreeMatrixCovariance (gridExponents L₀) S a M θB hB N u T q|/|J|)
    (w' := physicalChildMass M θB hB N L₀ u k hk C true Q) hc hc1
    (physicalScheduledEnergy_nonneg M θB hB N L₀ u _ Q)
    (physicalChildMass_nonneg M θB hB N L₀ u k hk C false Q)
    (physicalNodeShift_nonneg M θB hB N L₀ u k hk C Q) hcharge' hpair
    (physicalChildMass_le_sqrt M θB hB N L₀ u k hk C false Q) (by
      convert hstep using 1
      all_goals try with_reducible_and_instances rfl
      ring)
  exact hs

end DilutedSpinGlass.UniversalDictionary

end

end OAI
end

theorem solution : type_of% @OAI.DilutedSpinGlass.UniversalDictionary.regular_node_pointwise_sat_oai := @OAI.DilutedSpinGlass.UniversalDictionary.regular_node_pointwise_sat_oai
