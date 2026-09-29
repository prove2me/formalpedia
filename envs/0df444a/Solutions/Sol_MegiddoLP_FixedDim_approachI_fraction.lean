-- Prove2me | solution 1 for MegiddoLP.FixedDim.approachI_fraction
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T04:02:46.258829+00:00
-- url     : https://prove2.me/submissions/c6f903e6-c900-453a-ad2c-808585e561df

import Mathlib
import Definitions.Def_MegiddoLP_FixedDim_QueryTree

namespace MegiddoLP.FixedDim

open QTree

/-! Generic tree operations -/

def aux_mgA_map {d : ℕ} {α β : Type} (f : α → β) : QTree d α → QTree d β
  | .leaf o => .leaf (f o)
  | .query a b l e g => .query a b (aux_mgA_map f l) (aux_mgA_map f e) (aux_mgA_map f g)

theorem aux_mgA_map_eval {d : ℕ} {α β : Type} (f : α → β) (T : QTree d α) (x : Fin d → ℝ) :
    (aux_mgA_map f T).eval x = f (T.eval x) := by
  induction T with
  | leaf o => rfl
  | query a b l e g ihl ihe ihg =>
    simp only [aux_mgA_map, QTree.eval]
    cases compare (a ⬝ᵥ x) b <;> simp [ihl, ihe, ihg]

theorem aux_mgA_map_num {d : ℕ} {α β : Type} (f : α → β) (T : QTree d α) (x : Fin d → ℝ) :
    (aux_mgA_map f T).numQueries x = T.numQueries x := by
  induction T with
  | leaf o => rfl
  | query a b l e g ihl ihe ihg =>
    simp only [aux_mgA_map, QTree.numQueries]
    cases compare (a ⬝ᵥ x) b <;> simp [ihl, ihe, ihg]

def aux_mgA_bind {d : ℕ} {α β : Type} (F : α → QTree d β) : QTree d α → QTree d β
  | .leaf o => F o
  | .query a b l e g => .query a b (aux_mgA_bind F l) (aux_mgA_bind F e) (aux_mgA_bind F g)

theorem aux_mgA_bind_eval {d : ℕ} {α β : Type} (F : α → QTree d β) (T : QTree d α)
    (x : Fin d → ℝ) : (aux_mgA_bind F T).eval x = (F (T.eval x)).eval x := by
  induction T with
  | leaf o => rfl
  | query a b l e g ihl ihe ihg =>
    simp only [aux_mgA_bind, QTree.eval]
    cases compare (a ⬝ᵥ x) b <;> simp [ihl, ihe, ihg]

theorem aux_mgA_bind_num {d : ℕ} {α β : Type} (F : α → QTree d β) (T : QTree d α)
    (x : Fin d → ℝ) :
    (aux_mgA_bind F T).numQueries x = T.numQueries x + (F (T.eval x)).numQueries x := by
  induction T with
  | leaf o => simp [aux_mgA_bind, QTree.numQueries, QTree.eval]
  | query a b l e g ihl ihe ihg =>
    simp only [aux_mgA_bind, QTree.numQueries, QTree.eval]
    cases compare (a ⬝ᵥ x) b <;> simp [ihl, ihe, ihg] <;> omega

def aux_mgA_pull {d e : ℕ} {α : Type} (adj : (Fin e → ℝ) → (Fin d → ℝ)) :
    QTree e α → QTree d α
  | .leaf o => .leaf o
  | .query a b l m g => .query (adj a) b (aux_mgA_pull adj l) (aux_mgA_pull adj m)
      (aux_mgA_pull adj g)

theorem aux_mgA_pull_eval {d e : ℕ} {α : Type} (adj : (Fin e → ℝ) → (Fin d → ℝ))
    (P : (Fin d → ℝ) → (Fin e → ℝ)) (hadj : ∀ v y, adj v ⬝ᵥ y = v ⬝ᵥ P y)
    (T : QTree e α) (x : Fin d → ℝ) : (aux_mgA_pull adj T).eval x = T.eval (P x) := by
  induction T with
  | leaf o => rfl
  | query a b l m g ihl ihm ihg =>
    simp only [aux_mgA_pull, QTree.eval, hadj]
    cases compare (a ⬝ᵥ P x) b <;> simp [ihl, ihm, ihg]

theorem aux_mgA_pull_num {d e : ℕ} {α : Type} (adj : (Fin e → ℝ) → (Fin d → ℝ))
    (P : (Fin d → ℝ) → (Fin e → ℝ)) (hadj : ∀ v y, adj v ⬝ᵥ y = v ⬝ᵥ P y)
    (T : QTree e α) (x : Fin d → ℝ) :
    (aux_mgA_pull adj T).numQueries x = T.numQueries (P x) := by
  induction T with
  | leaf o => rfl
  | query a b l m g ihl ihm ihg =>
    simp only [aux_mgA_pull, QTree.numQueries, hadj]
    cases compare (a ⬝ᵥ P x) b <;> simp [ihl, ihm, ihg]

/-- best output given the region (preimage of the leaf value) -/
noncomputable def aux_mgA_best {d : ℕ} {ι β : Type} (T : QTree d β) (a : ι → Fin d → ℝ)
    (b : ι → ℝ) (v : β) (i : ι) : Option Ordering := by
  classical
  exact if h : ∃ o, ∀ y, T.eval y = v → compare (a i ⬝ᵥ y) (b i) = o then some h.choose
    else none

theorem aux_mgA_best_correct {d : ℕ} {ι β : Type} (T : QTree d β) (a : ι → Fin d → ℝ)
    (b : ι → ℝ) (x : Fin d → ℝ) (i : ι) (o : Ordering)
    (h : aux_mgA_best T a b (T.eval x) i = some o) : compare (a i ⬝ᵥ x) (b i) = o := by
  classical
  unfold aux_mgA_best at h
  split_ifs at h with h'
  · cases h
    exact h'.choose_spec x rfl

theorem aux_mgA_best_some {d : ℕ} {ι β : Type} (T : QTree d β) (a : ι → Fin d → ℝ)
    (b : ι → ℝ) (x : Fin d → ℝ) (i : ι)
    (h : ∀ y, T.eval y = T.eval x → compare (a i ⬝ᵥ y) (b i) = compare (a i ⬝ᵥ x) (b i)) :
    (aux_mgA_best T a b (T.eval x) i).isSome := by
  classical
  unfold aux_mgA_best
  rw [dif_pos ⟨_, h⟩]
  rfl

/-! compare helpers -/

theorem aux_mgA_cmp_sub (A B : ℝ) : compare A B = compare (A - B) 0 := by
  rcases lt_trichotomy A B with h | h | h
  · rw [compare_lt_iff_lt.mpr h, compare_lt_iff_lt.mpr (by linarith)]
  · subst h; simp
  · rw [compare_gt_iff_gt.mpr h, compare_gt_iff_gt.mpr (by linarith)]

theorem aux_mgA_cmp_mul_pos {t : ℝ} (ht : 0 < t) (A : ℝ) : compare (t * A) 0 = compare A 0 := by
  rcases lt_trichotomy A 0 with h | h | h
  · rw [compare_lt_iff_lt.mpr h, compare_lt_iff_lt.mpr (mul_neg_of_pos_of_neg ht h)]
  · subst h; simp
  · rw [compare_gt_iff_gt.mpr h, compare_gt_iff_gt.mpr (mul_pos ht h)]

theorem aux_mgA_cmp_neg (A : ℝ) : compare (-A) 0 = (compare A 0).swap := by
  rcases lt_trichotomy A 0 with h | h | h
  · rw [compare_lt_iff_lt.mpr h, compare_gt_iff_gt.mpr (by linarith)]; rfl
  · subst h; simp
  · rw [compare_gt_iff_gt.mpr h, compare_lt_iff_lt.mpr (by linarith)]; rfl

theorem aux_mgA_cmp_mul {t : ℝ} (ht : t ≠ 0) {A B : ℝ}
    (h : compare (t * A) 0 = compare (t * B) 0) : compare A 0 = compare B 0 := by
  rcases ht.lt_or_gt with h' | h'
  · have e : ∀ X : ℝ, t * X = -((-t) * X) := fun X => by ring
    rw [e A, e B, aux_mgA_cmp_neg, aux_mgA_cmp_neg, aux_mgA_cmp_mul_pos (neg_pos.mpr h'),
      aux_mgA_cmp_mul_pos (neg_pos.mpr h')] at h
    exact Ordering.swap_inj.mp h
  · rwa [aux_mgA_cmp_mul_pos h', aux_mgA_cmp_mul_pos h'] at h

/-! median -/

theorem aux_mgA_median {ι : Type} (s : Finset ι) (t : ι → ℝ) :
    ∃ c : ℝ, 2 * (s.filter (fun i => t i < c)).card ≤ s.card ∧
      2 * (s.filter (fun i => c < t i)).card ≤ s.card := by
  classical
  by_cases hs : s.Nonempty
  swap
  · refine ⟨0, ?_⟩; simp [Finset.not_nonempty_iff_eq_empty.mp hs]
  set A := s.filter (fun i => s.card ≤ 2 * (s.filter (fun j => t j ≤ t i)).card) with hA
  have hAne : A.Nonempty := by
    obtain ⟨i0, hi0, hmax⟩ := s.exists_max_image t hs
    refine ⟨i0, Finset.mem_filter.mpr ⟨hi0, ?_⟩⟩
    have : s.filter (fun j => t j ≤ t i0) = s := Finset.filter_true_of_mem (fun j hj => hmax j hj)
    rw [this]; omega
  obtain ⟨i1, hi1, hmin⟩ := A.exists_min_image t hAne
  refine ⟨t i1, ?_, ?_⟩
  · by_cases hB : (s.filter (fun i => t i < t i1)).Nonempty
    · obtain ⟨j1, hj1, hjmax⟩ := (s.filter (fun i => t i < t i1)).exists_max_image t hB
      have hj1' := Finset.mem_filter.mp hj1
      have heq : s.filter (fun i => t i < t i1) = s.filter (fun i => t i ≤ t j1) := by
        ext i; simp only [Finset.mem_filter]; constructor
        · rintro ⟨hi, hlt⟩; exact ⟨hi, hjmax i (Finset.mem_filter.mpr ⟨hi, hlt⟩)⟩
        · rintro ⟨hi, hle⟩; exact ⟨hi, lt_of_le_of_lt hle hj1'.2⟩
      have hj1A : j1 ∉ A := by
        intro h; have := hmin j1 h; linarith [hj1'.2]
      rw [heq]
      simp only [hA, Finset.mem_filter, not_and, not_le] at hj1A
      have := hj1A hj1'.1; omega
    · rw [Finset.not_nonempty_iff_eq_empty.mp hB]; simp
  · have h1 := (Finset.mem_filter.mp hi1).2
    have := Finset.card_filter_add_card_filter_not (s := s) (fun j => t j ≤ t i1)
    have heq : s.filter (fun j => ¬ t j ≤ t i1) = s.filter (fun j => t i1 < t j) := by
      ext; simp [not_le]
    rw [heq] at this; omega

/-! the planar lemma -/

theorem aux_mgA_tri (z : ℝ) : (z < 0 ∧ compare z 0 = .lt) ∨ (z = 0 ∧ compare z 0 = .eq) ∨
    (0 < z ∧ compare z 0 = .gt) := by
  rcases lt_trichotomy z 0 with h | h | h
  · exact Or.inl ⟨h, compare_lt_iff_lt.mpr h⟩
  · exact Or.inr (Or.inl ⟨h, compare_eq_iff_eq.mpr h⟩)
  · exact Or.inr (Or.inr ⟨h, compare_gt_iff_gt.mpr h⟩)

theorem aux_mgA_two {α β u v : ℝ} (hα : 0 < α) (hβ : 0 < β) :
    (∀ u' v' : ℝ, compare (u' - v') 0 = compare (u - v) 0 →
        compare (β * u' + α * v') 0 = compare (β * u + α * v) 0 → compare u' 0 = compare u 0) ∨
    (∀ u' v' : ℝ, compare (u' - v') 0 = compare (u - v) 0 →
        compare (β * u' + α * v') 0 = compare (β * u + α * v) 0 → compare v' 0 = compare v 0) := by
  have key1 : ∀ u v : ℝ, compare (u - v) 0 = compare (β * u + α * v) 0 →
      compare u 0 = compare (u - v) 0 := by
    intro u v h
    rcases lt_trichotomy (u - v) 0 with h1 | h1 | h1
    · rw [compare_lt_iff_lt.mpr h1] at h ⊢
      have h2 := compare_lt_iff_lt.mp h.symm
      exact compare_lt_iff_lt.mpr (by nlinarith)
    · rw [compare_eq_iff_eq.mpr h1] at h ⊢
      have h2 := compare_eq_iff_eq.mp h.symm
      exact compare_eq_iff_eq.mpr (by nlinarith)
    · rw [compare_gt_iff_gt.mpr h1] at h ⊢
      have h2 := compare_gt_iff_gt.mp h.symm
      exact compare_gt_iff_gt.mpr (by nlinarith)
  let f : Ordering → Ordering → Ordering := fun s1 s2 => if s2 = .eq then s1.swap else s2
  have key2 : ∀ u v : ℝ, compare (u - v) 0 ≠ compare (β * u + α * v) 0 →
      compare v 0 = f (compare (u - v) 0) (compare (β * u + α * v) 0) := by
    intro u v h
    rcases aux_mgA_tri (u - v) with ⟨h1, e1⟩ | ⟨h1, e1⟩ | ⟨h1, e1⟩ <;>
    rcases aux_mgA_tri (β * u + α * v) with ⟨h2, e2⟩ | ⟨h2, e2⟩ | ⟨h2, e2⟩ <;>
    simp only [e1, e2, f, ne_eq, not_true_eq_false, reduceCtorEq, if_true, if_false,
      Ordering.swap] at h ⊢
    · exact compare_gt_iff_gt.mpr (by nlinarith)
    · exact compare_gt_iff_gt.mpr (by nlinarith)
    · exact compare_lt_iff_lt.mpr (by nlinarith)
    · exact compare_gt_iff_gt.mpr (by nlinarith)
    · exact compare_lt_iff_lt.mpr (by nlinarith)
    · exact compare_lt_iff_lt.mpr (by nlinarith)
  by_cases h : compare (u - v) 0 = compare (β * u + α * v) 0
  · left
    intro u' v' h1 h2
    have : compare (u' - v') 0 = compare (β * u' + α * v') 0 := by rw [h1, h2, h]
    rw [key1 u' v' this, key1 u v h, h1]
  · right
    intro u' v' h1 h2
    have hne : compare (u' - v') 0 ≠ compare (β * u' + α * v') 0 := by rw [h1, h2]; exact h
    rw [key2 u' v' hne, key2 u v h, h1, h2]


/-- The main statement at dimension `d+1`, for an arbitrary finite index type. -/
def aux_mgA_P (d : ℕ) : Prop :=
  ∀ (ι : Type) [Fintype ι] (a : ι → Fin (d+1) → ℝ) (b : ι → ℝ), (∀ i, a i ≠ 0) →
    ∃ T : QTree (d+1) (ι → Option Ordering), ∀ x : Fin (d+1) → ℝ,
      T.numQueries x ≤ 2 ^ d ∧
      (∀ i o, T.eval x i = some o → compare (a i ⬝ᵥ x) (b i) = o) ∧
      Fintype.card ι / 2 ^ (2 ^ (d+1) - 1) ≤
        (Finset.univ.filter fun i => (T.eval x i).isSome).card

theorem aux_mgA_combine (d : ℕ) (IH : aux_mgA_P d) {ι υ : Type} [Fintype ι] [Fintype υ]
    (a : ι → Fin (d+2) → ℝ) (b : ι → ℝ)
    (P1 P2 : (Fin (d+2) → ℝ) → (Fin (d+1) → ℝ))
    (adj1 adj2 : (Fin (d+1) → ℝ) → (Fin (d+2) → ℝ))
    (hadj1 : ∀ v y, adj1 v ⬝ᵥ y = v ⬝ᵥ P1 y) (hadj2 : ∀ v y, adj2 v ⬝ᵥ y = v ⬝ᵥ P2 y)
    (h1 h2 : υ → Fin (d+1) → ℝ) (c1 c2 : υ → ℝ) (hh1 : ∀ u, h1 u ≠ 0) (hh2 : ∀ u, h2 u ≠ 0)
    (R : υ → ι → Prop) (hR : ∀ u v i, R u i → R v i → u = v)
    (hdec : ∀ u (x : Fin (d+2) → ℝ), ∃ i, R u i ∧ ∀ y,
      compare (adj1 (h1 u) ⬝ᵥ y) (c1 u) = compare (adj1 (h1 u) ⬝ᵥ x) (c1 u) →
      compare (adj2 (h2 u) ⬝ᵥ y) (c2 u) = compare (adj2 (h2 u) ⬝ᵥ x) (c2 u) →
      compare (a i ⬝ᵥ y) (b i) = compare (a i ⬝ᵥ x) (b i))
    (hcard : Fintype.card ι / 2 ≤ Fintype.card υ) :
    ∃ T : QTree (d+2) (ι → Option Ordering), ∀ x : Fin (d+2) → ℝ,
      T.numQueries x ≤ 2 ^ (d+1) ∧
      (∀ i o, T.eval x i = some o → compare (a i ⬝ᵥ x) (b i) = o) ∧
      Fintype.card ι / 2 ^ (2 ^ (d+2) - 1) ≤
        (Finset.univ.filter fun i => (T.eval x i).isSome).card := by
  classical
  obtain ⟨T1', hT1'⟩ := IH υ h1 c1 hh1
  set K := 2 ^ (2 ^ (d+1) - 1) with hK
  let T1 := aux_mgA_pull adj1 T1'
  have hT1e : ∀ x, T1.eval x = T1'.eval (P1 x) := aux_mgA_pull_eval adj1 P1 hadj1 T1'
  have hT1n : ∀ x, T1.numQueries x = T1'.numQueries (P1 x) :=
    aux_mgA_pull_num adj1 P1 hadj1 T1'
  let S : (υ → Option Ordering) → Finset υ :=
    fun o1 => Finset.univ.filter fun u => (o1 u).isSome
  have hT2ex : ∀ o1 : υ → Option Ordering, ∃ T2 : QTree (d+2) (υ → Option Ordering), ∀ x,
      T2.numQueries x ≤ 2 ^ d ∧
      (∀ u σ, T2.eval x u = some σ → compare (h2 u ⬝ᵥ P2 x) (c2 u) = σ) ∧
      (S o1).card / K ≤
        (Finset.univ.filter fun u => (o1 u).isSome ∧ (T2.eval x u).isSome).card := by
    intro o1
    obtain ⟨T2', hT2'⟩ := IH (S o1) (fun u => h2 u) (fun u => c2 u) (fun u => hh2 u)
    let ext : ((S o1) → Option Ordering) → υ → Option Ordering :=
      fun o u => if h : u ∈ S o1 then o ⟨u, h⟩ else none
    refine ⟨aux_mgA_map ext (aux_mgA_pull adj2 T2'), fun x => ?_⟩
    rw [aux_mgA_map_num, aux_mgA_pull_num adj2 P2 hadj2, aux_mgA_map_eval,
      aux_mgA_pull_eval adj2 P2 hadj2]
    obtain ⟨hn, hc, hk⟩ := hT2' (P2 x)
    refine ⟨hn, ?_, ?_⟩
    · intro u σ h
      simp only [ext] at h
      split_ifs at h with hu
      exact hc _ _ h
    · rw [Fintype.card_coe] at hk
      refine hk.trans (Finset.card_le_card_of_injOn Subtype.val ?_ ?_)
      · intro u hu
        simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hu ⊢
        have hu2 := u.2
        refine ⟨(Finset.mem_filter.mp hu2).2, ?_⟩
        simp only [ext, dif_pos hu2]
        exact hu
      · intro u _ v _ h; exact Subtype.ext h
  choose T2 hT2 using hT2ex
  let T0 : QTree (d+2) ((υ → Option Ordering) × (υ → Option Ordering)) :=
    aux_mgA_bind (fun o1 => aux_mgA_map (fun o2 => (o1, o2)) (T2 o1)) T1
  have hT0e : ∀ x, T0.eval x = (T1.eval x, (T2 (T1.eval x)).eval x) := by
    intro x; simp only [T0, aux_mgA_bind_eval, aux_mgA_map_eval]
  have hT0n : ∀ x, T0.numQueries x = T1.numQueries x + (T2 (T1.eval x)).numQueries x := by
    intro x; simp only [T0, aux_mgA_bind_num, aux_mgA_map_num]
  refine ⟨aux_mgA_map (aux_mgA_best T0 a b) T0, fun x => ?_⟩
  simp only [aux_mgA_map_num, aux_mgA_map_eval]
  refine ⟨?_, fun i o h => aux_mgA_best_correct T0 a b x i o h, ?_⟩
  · rw [hT0n, hT1n]
    have := (hT1' (P1 x)).1
    have := (hT2 (T1.eval x) x).1
    rw [pow_succ]; omega
  · have hF : Fintype.card ι / 2 ^ (2 ^ (d+2) - 1) ≤ (Finset.univ.filter fun u =>
        ((T1.eval x) u).isSome ∧ (((T2 (T1.eval x)).eval x) u).isSome).card := by
      have h3 := (hT2 (T1.eval x) x).2.2
      have h4 : Fintype.card υ / K ≤ (S (T1.eval x)).card := by
        have := (hT1' (P1 x)).2.2
        simp only [S, hT1e]
        exact this
      have e : 2 ^ (2 ^ (d+2) - 1) = 2 * K * K := by
        rw [hK, ← pow_succ', ← pow_add]; congr 1
        have : 2 ^ (d+2) = 2 * 2 ^ (d+1) := by rw [pow_succ]; ring
        have : 1 ≤ 2 ^ (d+1) := Nat.one_le_two_pow
        omega
      rw [e, ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul]
      refine le_trans ?_ h3
      exact Nat.div_le_div_right (le_trans (Nat.div_le_div_right hcard) h4)
    refine hF.trans ?_
    have hdec' : ∀ u, ∃ i, R u i ∧ ∀ y,
        compare (adj1 (h1 u) ⬝ᵥ y) (c1 u) = compare (adj1 (h1 u) ⬝ᵥ x) (c1 u) →
        compare (adj2 (h2 u) ⬝ᵥ y) (c2 u) = compare (adj2 (h2 u) ⬝ᵥ x) (c2 u) →
        compare (a i ⬝ᵥ y) (b i) = compare (a i ⬝ᵥ x) (b i) := fun u => hdec u x
    choose g hgR hg using hdec'
    refine Finset.card_le_card_of_injOn g ?_ ?_
    · intro u hu
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hu ⊢
      apply aux_mgA_best_some
      intro y hy
      rw [hT0e, hT0e] at hy
      have hy1 : T1.eval y = T1.eval x := congrArg Prod.fst hy
      have hy2 : (T2 (T1.eval x)).eval y = (T2 (T1.eval x)).eval x := by
        have := congrArg Prod.snd hy; simp only at this; rw [hy1] at this; exact this
      apply hg u y
      · obtain ⟨σ1, hσ1⟩ := Option.isSome_iff_exists.mp hu.1
        rw [hadj1, hadj1]
        have hA := (hT1' (P1 y)).2.1 u σ1 (by rw [← hT1e, hy1]; exact hσ1)
        have hB := (hT1' (P1 x)).2.1 u σ1 (by rw [← hT1e]; exact hσ1)
        rw [hA, hB]
      · obtain ⟨σ2, hσ2⟩ := Option.isSome_iff_exists.mp hu.2
        rw [hadj2, hadj2]
        have hA := (hT2 (T1.eval x) y).2.1 u σ2 (by rw [hy2]; exact hσ2)
        have hB := (hT2 (T1.eval x) x).2.1 u σ2 hσ2
        rw [hA, hB]
    · intro u _ v _ h
      exact hR u v (g u) (hgR u) (h ▸ hgR v)


theorem aux_mgA_cmp_mul_iff {t : ℝ} (ht : t ≠ 0) (A B : ℝ) :
    compare (t * A) 0 = compare (t * B) 0 ↔ compare A 0 = compare B 0 := by
  refine ⟨aux_mgA_cmp_mul ht, fun h => ?_⟩
  rcases ht.lt_or_gt with h' | h'
  · have e : ∀ X : ℝ, t * X = -((-t) * X) := fun X => by ring
    rw [e A, e B, aux_mgA_cmp_neg, aux_mgA_cmp_neg, aux_mgA_cmp_mul_pos (neg_pos.mpr h'),
      aux_mgA_cmp_mul_pos (neg_pos.mpr h'), h]
  · rw [aux_mgA_cmp_mul_pos h', aux_mgA_cmp_mul_pos h', h]

theorem aux_mgA_base : aux_mgA_P 0 := by
  intro ι _ a b ha
  classical
  have hp : ∀ i, a i 0 ≠ 0 := by
    intro i h; apply ha i; ext j; fin_cases j; simpa using h
  let t : ι → ℝ := fun i => b i / a i 0
  obtain ⟨c, hcL, hcG⟩ := aux_mgA_median Finset.univ t
  let e1 : Fin 1 → ℝ := fun _ => 1
  have he1 : ∀ y : Fin 1 → ℝ, e1 ⬝ᵥ y = y 0 := by intro y; simp [e1, dotProduct]
  let T0 : QTree 1 Ordering := .query e1 c (.leaf .lt) (.leaf .eq) (.leaf .gt)
  have hT0 : ∀ y, T0.eval y = compare (y 0) c := by
    intro y; simp only [T0, QTree.eval, he1]; cases compare (y 0) c <;> rfl
  refine ⟨aux_mgA_map (aux_mgA_best T0 a b) T0, fun x => ?_⟩
  simp only [aux_mgA_map_num, aux_mgA_map_eval]
  refine ⟨?_, fun i o h => aux_mgA_best_correct T0 a b x i o h, ?_⟩
  · simp only [T0, QTree.numQueries]
    cases compare (e1 ⬝ᵥ x) c <;> simp
  · have hdot : ∀ i y, a i ⬝ᵥ y = a i 0 * y 0 := by intro i y; simp [dotProduct]
    have hknown : ∀ i, (∀ y : Fin 1 → ℝ, compare (y 0) c = compare (x 0) c →
        compare (y 0) (t i) = compare (x 0) (t i)) →
        (aux_mgA_best T0 a b (T0.eval x) i).isSome := by
      intro i hi
      apply aux_mgA_best_some
      intro y hy
      rw [hT0, hT0] at hy
      have h1 := hi y hy
      rw [aux_mgA_cmp_sub, aux_mgA_cmp_sub (a i ⬝ᵥ x), hdot, hdot]
      have e : ∀ z, a i 0 * z - b i = a i 0 * (z - t i) := by
        intro z; simp only [t]; field_simp [hp i]
      rw [e, e, aux_mgA_cmp_mul_iff (hp i), ← aux_mgA_cmp_sub, ← aux_mgA_cmp_sub]
      exact h1
    have hcard : (2 : ℕ) ^ (2 ^ (0 + 1) - 1) = 2 := by norm_num
    rw [hcard]
    rcases lt_trichotomy (x 0) c with hx | hx | hx
    · have hc := Finset.card_filter_add_card_filter_not (s := Finset.univ) (fun i => t i < c)
      rw [Finset.card_univ] at hc hcL
      calc Fintype.card ι / 2 ≤ (Finset.univ.filter fun i => ¬ t i < c).card := by omega
        _ ≤ _ := by
          apply Finset.card_le_card
          intro i hi
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at hi ⊢
          apply hknown
          intro y hy
          rw [compare_lt_iff_lt.mpr hx, compare_lt_iff_lt] at hy
          rw [compare_lt_iff_lt.mpr (by linarith), compare_lt_iff_lt.mpr (by linarith)]
    · calc Fintype.card ι / 2 ≤ Fintype.card ι := Nat.div_le_self _ _
        _ = (Finset.univ.filter fun i => (aux_mgA_best T0 a b (T0.eval x) i).isSome).card := by
          rw [← Finset.card_univ]; congr 1
          symm; apply Finset.filter_true_of_mem
          intro i _
          apply hknown
          intro y hy
          rw [compare_eq_iff_eq.mpr hx, compare_eq_iff_eq] at hy
          rw [hy, hx]
    · have hc := Finset.card_filter_add_card_filter_not (s := Finset.univ) (fun i => c < t i)
      rw [Finset.card_univ] at hc hcG
      calc Fintype.card ι / 2 ≤ (Finset.univ.filter fun i => ¬ c < t i).card := by omega
        _ ≤ _ := by
          apply Finset.card_le_card
          intro i hi
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at hi ⊢
          apply hknown
          intro y hy
          rw [compare_gt_iff_gt.mpr hx, compare_gt_iff_gt] at hy
          rw [compare_gt_iff_gt.mpr (by linarith), compare_gt_iff_gt.mpr (by linarith)]


theorem aux_mgA_step (d : ℕ) (IH : aux_mgA_P d) : aux_mgA_P (d+1) := by
  intro ι _ a b ha
  classical
  let p : ι → ℝ := fun i => a i 0
  let ρ : ι → ℝ := fun i => a i 1 / a i 0
  obtain ⟨c, hcL, hcG⟩ := aux_mgA_median (Finset.univ.filter fun i => p i ≠ 0) ρ
  set N := Finset.univ.filter fun i => p i ≠ 0 with hN
  set Lset := N.filter fun i => ρ i < c with hL
  set Gset := N.filter fun i => c < ρ i with hG
  have memL : ∀ i, i ∈ Lset ↔ p i ≠ 0 ∧ ρ i < c := by intro i; simp [hL, hN]
  have memG : ∀ i, i ∈ Gset ↔ p i ≠ 0 ∧ c < ρ i := by intro i; simp [hG, hN]
  set k := min Lset.card Gset.card with hk
  let eL : ↥Lset ≃ Fin Lset.card := Fintype.equivFinOfCardEq (Fintype.card_coe Lset)
  let eG : ↥Gset ≃ Fin Gset.card := Fintype.equivFinOfCardEq (Fintype.card_coe Gset)
  let ℓ : Fin k → ι := fun m => (eL.symm (Fin.castLE (min_le_left _ _) m)).1
  let γ : Fin k → ι := fun m => (eG.symm (Fin.castLE (min_le_right _ _) m)).1
  have hℓ : ∀ m, ℓ m ∈ Lset := fun m => (eL.symm _).2
  have hγ : ∀ m, γ m ∈ Gset := fun m => (eG.symm _).2
  have hℓinj : ∀ m m', ℓ m = ℓ m' → m = m' := by
    intro m m' h
    have h' := eL.symm.injective (Subtype.ext h)
    exact Fin.ext (by simpa using congrArg Fin.val h')
  have hγinj : ∀ m m', γ m = γ m' → m = m' := by
    intro m m' h
    have h' := eG.symm.injective (Subtype.ext h)
    exact Fin.ext (by simpa using congrArg Fin.val h')
  have hLG : ∀ m m', ℓ m ≠ γ m' := by
    intro m m' h
    have h1 := ((memL _).mp (hℓ m)).2
    have h2 := ((memG _).mp (hγ m')).2
    rw [h] at h1; linarith
  let ah : ι → Fin (d+2) → ℝ := fun i => (p i)⁻¹ • a i
  let bh : ι → ℝ := fun i => (p i)⁻¹ * b i
  have hah0 : ∀ i, p i ≠ 0 → ah i 0 = 1 := by
    intro i hi; simp only [ah, Pi.smul_apply, smul_eq_mul]; exact inv_mul_cancel₀ hi
  have hah1 : ∀ i, ah i 1 = ρ i := by
    intro i; simp only [ah, ρ, p, Pi.smul_apply, smul_eq_mul]; rw [div_eq_inv_mul]
  have hahdot : ∀ i y, ah i ⬝ᵥ y - bh i = (p i)⁻¹ * (a i ⬝ᵥ y - b i) := by
    intro i y; simp only [ah, bh, smul_dotProduct, smul_eq_mul]; ring
  let α : Fin k → ℝ := fun m => c - ρ (ℓ m)
  let β : Fin k → ℝ := fun m => ρ (γ m) - c
  have hα : ∀ m, 0 < α m := fun m => by
    have := ((memL _).mp (hℓ m)).2; simp only [α]; linarith
  have hβ : ∀ m, 0 < β m := fun m => by
    have := ((memG _).mp (hγ m)).2; simp only [β]; linarith
  let W1 : Fin k → Fin (d+2) → ℝ := fun m => ah (ℓ m) - ah (γ m)
  let C1 : Fin k → ℝ := fun m => bh (ℓ m) - bh (γ m)
  let W2 : Fin k → Fin (d+2) → ℝ := fun m => β m • ah (ℓ m) + α m • ah (γ m)
  let C2 : Fin k → ℝ := fun m => β m * bh (ℓ m) + α m * bh (γ m)
  let P1 : (Fin (d+2) → ℝ) → (Fin (d+1) → ℝ) := Fin.tail
  let adj1 : (Fin (d+1) → ℝ) → (Fin (d+2) → ℝ) := fun v => Fin.cons 0 v
  let P2 : (Fin (d+2) → ℝ) → (Fin (d+1) → ℝ) :=
    fun y => Fin.cons (y 0 + c * y 1) (Fin.tail (Fin.tail y))
  let adj2 : (Fin (d+1) → ℝ) → (Fin (d+2) → ℝ) :=
    fun v => Fin.cons (v 0) (Fin.cons (c * v 0) (Fin.tail v))
  have hadj1 : ∀ v y, adj1 v ⬝ᵥ y = v ⬝ᵥ P1 y := by
    intro v y; simp [adj1, P1, dotProduct, Fin.sum_univ_succ, Fin.tail]
  have hadj2 : ∀ v y, adj2 v ⬝ᵥ y = v ⬝ᵥ P2 y := by
    intro v y; simp [adj2, P2, dotProduct, Fin.sum_univ_succ, Fin.tail]; ring
  let red1 : (Fin (d+2) → ℝ) → (Fin (d+1) → ℝ) := Fin.tail
  let red2 : (Fin (d+2) → ℝ) → (Fin (d+1) → ℝ) :=
    fun w => Fin.cons (w 0) (Fin.tail (Fin.tail w))
  have hred1 : ∀ w : Fin (d+2) → ℝ, w 0 = 0 → adj1 (red1 w) = w := by
    intro w hw; simp only [adj1, red1]; rw [← hw]; exact Fin.cons_self_tail w
  have hred2 : ∀ w : Fin (d+2) → ℝ, w 1 = c * w 0 → adj2 (red2 w) = w := by
    intro w hw
    simp only [adj2, red2, Fin.cons_zero, Fin.tail_cons]
    have : c * w 0 = Fin.tail w 0 := by rw [← hw]; rfl
    rw [this, Fin.cons_self_tail, Fin.cons_self_tail]
  let one : Fin (d+1) → ℝ := fun _ => 1
  have hone : one ≠ 0 := fun h => by have := congrFun h 0; simp [one] at this
  let h1 : {i : ι // i ∉ Lset ∧ i ∉ Gset} ⊕ Fin k → Fin (d+1) → ℝ :=
    Sum.elim (fun i => if p i.1 = 0 then red1 (a i.1) else one) (fun m => red1 (W1 m))
  let c1 : {i : ι // i ∉ Lset ∧ i ∉ Gset} ⊕ Fin k → ℝ := Sum.elim (fun i => b i.1) C1
  let h2 : {i : ι // i ∉ Lset ∧ i ∉ Gset} ⊕ Fin k → Fin (d+1) → ℝ :=
    Sum.elim (fun i => if p i.1 = 0 then one else red2 (a i.1)) (fun m => red2 (W2 m))
  let c2 : {i : ι // i ∉ Lset ∧ i ∉ Gset} ⊕ Fin k → ℝ := Sum.elim (fun i => b i.1) C2
  let R : {i : ι // i ∉ Lset ∧ i ∉ Gset} ⊕ Fin k → ι → Prop :=
    Sum.elim (fun i j => j = i.1) (fun m j => j = ℓ m ∨ j = γ m)
  refine aux_mgA_combine d IH a b P1 P2 adj1 adj2 hadj1 hadj2 h1 h2 c1 c2 ?_ ?_ R ?_ ?_ ?_
  · rintro (⟨i, hi⟩ | m)
    · simp only [h1, Sum.elim_inl]
      split_ifs with hp0
      · intro h
        apply ha i
        rw [← hred1 (a i) hp0, h]
        ext j; refine Fin.cases ?_ (fun j => ?_) j <;> simp [adj1]
      · exact hone
    · simp only [h1, Sum.elim_inr]
      intro h
      have := congrFun h 0
      simp only [red1, Fin.tail, W1, Pi.sub_apply, Pi.zero_apply] at this
      have e1 : (Fin.succ (0 : Fin (d+1))) = (1 : Fin (d+2)) := rfl
      rw [e1, hah1, hah1] at this
      have := ((memL _).mp (hℓ m)).2
      have := ((memG _).mp (hγ m)).2
      linarith
  · rintro (⟨i, hi⟩ | m)
    · simp only [h2, Sum.elim_inl]
      split_ifs with hp0
      · exact hone
      · intro h
        have := congrFun h 0
        simp only [red2, Fin.cons_zero, Pi.zero_apply] at this
        exact hp0 this
    · simp only [h2, Sum.elim_inr]
      intro h
      have := congrFun h 0
      simp only [red2, Fin.cons_zero, W2, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
        Pi.zero_apply] at this
      rw [hah0 _ ((memL _).mp (hℓ m)).1, hah0 _ ((memG _).mp (hγ m)).1] at this
      have := hα m; have := hβ m; linarith
  · rintro (⟨i, hi⟩ | m) (⟨i', hi'⟩ | m') j hu hv
    · simp only [R, Sum.elim_inl] at hu hv
      subst hu; subst hv; rfl
    · simp only [R, Sum.elim_inl, Sum.elim_inr] at hu hv
      exfalso; subst hu; rcases hv with hv | hv
      · exact hi.1 (hv ▸ hℓ m')
      · exact hi.2 (hv ▸ hγ m')
    · simp only [R, Sum.elim_inl, Sum.elim_inr] at hu hv
      exfalso; subst hv; rcases hu with hu | hu
      · exact hi'.1 (hu ▸ hℓ m)
      · exact hi'.2 (hu ▸ hγ m)
    · simp only [R, Sum.elim_inr] at hu hv
      congr 1
      rcases hu with hu | hu <;> rcases hv with hv | hv
      · exact hℓinj m m' (hu ▸ hv)
      · exact absurd (hu ▸ hv) (hLG m m')
      · exact absurd (hv ▸ hu) (hLG m' m)
      · exact hγinj m m' (hu ▸ hv)
  · rintro (⟨i, hi⟩ | m) x
    · by_cases hp0 : p i = 0
      · refine ⟨i, rfl, fun y hy _ => ?_⟩
        simp only [h1, c1, Sum.elim_inl, if_pos hp0, hred1 (a i) hp0] at hy
        exact hy
      · have hq : a i 1 = c * a i 0 := by
          have h1' : ¬ ρ i < c := fun h => hi.1 ((memL i).mpr ⟨hp0, h⟩)
          have h2' : ¬ c < ρ i := fun h => hi.2 ((memG i).mpr ⟨hp0, h⟩)
          have : ρ i = c := le_antisymm (not_lt.mp h2') (not_lt.mp h1')
          simp only [ρ] at this
          rw [div_eq_iff hp0] at this
          exact this
        refine ⟨i, rfl, fun y _ hy => ?_⟩
        simp only [h2, c2, Sum.elim_inl, if_neg hp0, hred2 (a i) hq] at hy
        exact hy
    · have hpi : p (ℓ m) ≠ 0 := ((memL _).mp (hℓ m)).1
      have hpj : p (γ m) ≠ 0 := ((memG _).mp (hγ m)).1
      have hW10 : W1 m 0 = 0 := by
        simp only [W1, Pi.sub_apply, hah0 _ hpi, hah0 _ hpj, sub_self]
      have hW21 : W2 m 1 = c * W2 m 0 := by
        simp only [W2, Pi.add_apply, Pi.smul_apply, smul_eq_mul, hah0 _ hpi, hah0 _ hpj,
          hah1, α, β]
        ring
      have eW1 : ∀ y, compare (adj1 (h1 (.inr m)) ⬝ᵥ y) (c1 (.inr m)) =
          compare ((ah (ℓ m) ⬝ᵥ y - bh (ℓ m)) - (ah (γ m) ⬝ᵥ y - bh (γ m))) 0 := by
        intro y
        simp only [h1, c1, Sum.elim_inr]
        rw [hred1 _ hW10, aux_mgA_cmp_sub]
        congr 1
        simp only [W1, C1, sub_dotProduct]; ring
      have eW2 : ∀ y, compare (adj2 (h2 (.inr m)) ⬝ᵥ y) (c2 (.inr m)) =
          compare (β m * (ah (ℓ m) ⬝ᵥ y - bh (ℓ m)) + α m * (ah (γ m) ⬝ᵥ y - bh (γ m))) 0 := by
        intro y
        simp only [h2, c2, Sum.elim_inr]
        rw [hred2 _ hW21, aux_mgA_cmp_sub]
        congr 1
        simp only [W2, C2, add_dotProduct, smul_dotProduct, smul_eq_mul]; ring
      rcases aux_mgA_two (u := ah (ℓ m) ⬝ᵥ x - bh (ℓ m)) (v := ah (γ m) ⬝ᵥ x - bh (γ m))
        (hα m) (hβ m) with H | H
      · refine ⟨ℓ m, Or.inl rfl, fun y hy1 hy2 => ?_⟩
        rw [eW1, eW1] at hy1
        rw [eW2, eW2] at hy2
        have := H _ _ hy1 hy2
        rw [hahdot, hahdot, aux_mgA_cmp_mul_iff (inv_ne_zero hpi)] at this
        rw [aux_mgA_cmp_sub, aux_mgA_cmp_sub (a (ℓ m) ⬝ᵥ x)]
        exact this
      · refine ⟨γ m, Or.inr rfl, fun y hy1 hy2 => ?_⟩
        rw [eW1, eW1] at hy1
        rw [eW2, eW2] at hy2
        have := H _ _ hy1 hy2
        rw [hahdot, hahdot, aux_mgA_cmp_mul_iff (inv_ne_zero hpj)] at this
        rw [aux_mgA_cmp_sub, aux_mgA_cmp_sub (a (γ m) ⬝ᵥ x)]
        exact this
  · rw [Fintype.card_sum, Fintype.card_fin, Fintype.card_subtype]
    have hsub : (Finset.univ : Finset ι) ⊆
        (Finset.univ.filter fun i => i ∉ Lset ∧ i ∉ Gset) ∪ Lset ∪ Gset := by
      intro i _
      by_cases h1 : i ∈ Lset
      · simp [h1]
      · by_cases h2 : i ∈ Gset
        · simp [h2]
        · simp [h1, h2]
    have e1 := Finset.card_le_card hsub
    have e2 := Finset.card_union_le ((Finset.univ.filter fun i => i ∉ Lset ∧ i ∉ Gset) ∪ Lset) Gset
    have e3 := Finset.card_union_le (Finset.univ.filter fun i => i ∉ Lset ∧ i ∉ Gset) Lset
    have hNle : N.card ≤ Fintype.card ι := Finset.card_le_univ N
    rw [Finset.card_univ] at e1
    omega

theorem aux_mgA_all (d : ℕ) : aux_mgA_P d := by
  induction d with
  | zero => exact aux_mgA_base
  | succ d ih => exact aux_mgA_step d ih

end MegiddoLP.FixedDim

open MegiddoLP.FixedDim

theorem solution (d n : ℕ) (hd : 1 ≤ d) (a : Fin n → Fin d → ℝ) (b : Fin n → ℝ)
    (ha : ∀ i, a i ≠ 0) :
    ∃ T : QTree d (Fin n → Option Ordering), ∀ x : Fin d → ℝ,
      T.numQueries x ≤ 2 ^ (d - 1) ∧
      (∀ i o, T.eval x i = some o → compare (a i ⬝ᵥ x) (b i) = o) ∧
      n / 2 ^ (2 ^ d - 1) ≤ (Finset.univ.filter fun i => (T.eval x i).isSome).card := by
  obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
  obtain ⟨T, hT⟩ := aux_mgA_all d' (Fin n) a b ha
  refine ⟨T, fun x => ?_⟩
  obtain ⟨h1, h2, h3⟩ := hT x
  refine ⟨by simpa using h1, h2, by simpa using h3⟩
