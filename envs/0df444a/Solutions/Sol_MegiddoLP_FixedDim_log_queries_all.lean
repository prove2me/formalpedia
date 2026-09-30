-- Prove2me | solution 1 for MegiddoLP.FixedDim.log_queries_all
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T22:34:59.277331+00:00
-- url     : https://prove2.me/submissions/da6e71dc-79a5-480f-bd48-42cd4b22a886

import Mathlib
import Definitions.Def_MegiddoLP_FixedDim_QueryTree



namespace MegiddoLP.FixedDim

open Classical

namespace QTree
variable {d : ℕ} {α β : Type}

noncomputable def bindT : QTree d α → (α → QTree d β) → QTree d β
  | leaf o, f => f o
  | query a b l e g, f => query a b (bindT l f) (bindT e f) (bindT g f)

theorem eval_bindT (T : QTree d α) (f : α → QTree d β) (x : Fin d → ℝ) :
    (T.bindT f).eval x = (f (T.eval x)).eval x := by
  induction T with
  | leaf o => rfl
  | query a b l e g ihl ihe ihg =>
    simp only [bindT, eval]
    rcases compare (a ⬝ᵥ x) b <;> simp [ihl, ihe, ihg]

theorem numQueries_bindT (T : QTree d α) (f : α → QTree d β) (x : Fin d → ℝ) :
    (T.bindT f).numQueries x = T.numQueries x + (f (T.eval x)).numQueries x := by
  induction T with
  | leaf o => simp [bindT, numQueries, eval]
  | query a b l e g ihl ihe ihg =>
    simp only [bindT, eval, numQueries]
    rcases compare (a ⬝ᵥ x) b <;> simp [ihl, ihe, ihg] <;> omega

noncomputable def pullT {k D : ℕ} (g : (Fin k → ℝ) → (Fin D → ℝ)) : QTree k α → QTree D α
  | leaf o => leaf o
  | query a b l e h => query (g a) b (pullT g l) (pullT g e) (pullT g h)

theorem eval_pullT {k D : ℕ} (g : (Fin k → ℝ) → (Fin D → ℝ)) (f : (Fin D → ℝ) → (Fin k → ℝ))
    (hfg : ∀ a y, g a ⬝ᵥ y = a ⬝ᵥ f y) (T : QTree k α) (y : Fin D → ℝ) :
    (T.pullT g).eval y = T.eval (f y) ∧ (T.pullT g).numQueries y = T.numQueries (f y) := by
  induction T with
  | leaf o => simp [pullT, eval, numQueries]
  | query a b l e h ihl ihe ihh =>
    simp only [pullT, eval, numQueries, hfg]
    rcases compare (a ⬝ᵥ f y) b <;> simp [ihl, ihe, ihh]

end QTree

open QTree

/-- constant-fraction resolution property -/
def Frac (k : ℕ) (ε : ℝ) (K : ℕ) : Prop :=
  ∀ (ι : Type) (S : Finset ι) (c : ι → Fin k → ℝ) (b : ι → ℝ),
    ∃ T : QTree k (ι → Option Ordering), ∀ y : Fin k → ℝ,
      (∀ i ∈ S, ∀ o, T.eval y i = some o → compare (c i ⬝ᵥ y) (b i) = o) ∧
      ε * S.card ≤ ((S.filter fun i => (T.eval y i).isSome).card : ℝ) ∧
      T.numQueries y ≤ K

theorem frac_pull {k D : ℕ} {ε : ℝ} {K : ℕ} (h : Frac k ε K) {ι : Type} (S : Finset ι)
    (c : ι → Fin k → ℝ) (b : ι → ℝ) (f : (Fin D → ℝ) → (Fin k → ℝ))
    (g : (Fin k → ℝ) → (Fin D → ℝ)) (hfg : ∀ a y, g a ⬝ᵥ y = a ⬝ᵥ f y) :
    ∃ T : QTree D (ι → Option Ordering), ∀ y : Fin D → ℝ,
      (∀ i ∈ S, ∀ o, T.eval y i = some o → compare (c i ⬝ᵥ f y) (b i) = o) ∧
      ε * S.card ≤ ((S.filter fun i => (T.eval y i).isSome).card : ℝ) ∧
      T.numQueries y ≤ K := by
  obtain ⟨T, hT⟩ := h ι S c b
  refine ⟨T.pullT g, fun y => ?_⟩
  obtain ⟨h1, h2⟩ := eval_pullT g f hfg T y
  rw [h1, h2]
  exact hT (f y)

/-- iteration: full resolution -/
theorem frac_iter {d : ℕ} {ε : ℝ} {K : ℕ} (hε : 0 < ε) (hε1 : ε < 1) (h : Frac d ε K)
    {ι : Type} (c : ι → Fin d → ℝ) (b : ι → ℝ) :
    ∀ j : ℕ, ∀ S : Finset ι, (S.card : ℝ) * (1 - ε) ^ j < 1 →
    ∃ T : QTree d (ι → Option Ordering), ∀ y : Fin d → ℝ,
      (∀ i ∈ S, ∀ o, T.eval y i = some o → compare (c i ⬝ᵥ y) (b i) = o) ∧
      (∀ i ∈ S, (T.eval y i).isSome) ∧ T.numQueries y ≤ K * j := by
  intro j
  induction j with
  | zero =>
    intro S hS
    simp at hS
    subst hS
    exact ⟨QTree.leaf (fun _ => none), fun y => by simp [QTree.numQueries]⟩
  | succ j ih =>
    intro S hS
    obtain ⟨T1, hT1⟩ := h ι S c b
    let S' : (ι → Option Ordering) → Finset ι := fun o => S.filter fun i => (o i).isNone
    let F : (ι → Option Ordering) → QTree d (ι → Option Ordering) := fun o =>
      if hh : ((S' o).card : ℝ) * (1 - ε) ^ j < 1 then
        (QTree.bindT (Classical.choose (ih (S' o) hh))
          (fun o2 => QTree.leaf (fun i => if (o i).isSome then o i else o2 i)))
      else QTree.leaf o
    refine ⟨T1.bindT F, fun y => ?_⟩
    obtain ⟨g1, g2, g3⟩ := hT1 y
    set o := T1.eval y with ho
    have hcard : ((S' o).card : ℝ) * (1 - ε) ^ j < 1 := by
      have hsplit := Finset.card_filter_add_card_filter_not (s := S) (fun i => (o i).isSome)
      have : (S' o) = S.filter (fun i => ¬ (o i).isSome = true) := by
        simp [S', Option.isNone_iff_eq_none]
      rw [this]
      have hS'le : (((S.filter (fun i => ¬ (o i).isSome = true)).card : ℕ) : ℝ) ≤
          (1 - ε) * S.card := by
        have : ((S.filter (fun i => (o i).isSome = true)).card : ℝ) +
            ((S.filter (fun i => ¬ (o i).isSome = true)).card : ℝ) = S.card := by
          exact_mod_cast hsplit
        nlinarith
      have hp : 0 ≤ (1 - ε) ^ j := pow_nonneg (by linarith) _
      calc (((S.filter (fun i => ¬ (o i).isSome = true)).card : ℕ) : ℝ) * (1 - ε) ^ j
          ≤ (1 - ε) * S.card * (1 - ε) ^ j := mul_le_mul_of_nonneg_right hS'le hp
        _ = S.card * (1 - ε) ^ (j + 1) := by ring
        _ < 1 := hS
    have hF : F o = (QTree.bindT (Classical.choose (ih (S' o) hcard))
          (fun o2 => QTree.leaf (fun i => if (o i).isSome then o i else o2 i))) := by
      simp only [F, dif_pos hcard]
    have hspec := Classical.choose_spec (ih (S' o) hcard) y
    set T2 := Classical.choose (ih (S' o) hcard)
    obtain ⟨k1, k2, k3⟩ := hspec
    rw [QTree.eval_bindT, QTree.numQueries_bindT, ← ho, hF, QTree.eval_bindT,
      QTree.numQueries_bindT]
    simp only [QTree.eval, QTree.numQueries]
    refine ⟨?_, ?_, ?_⟩
    · intro i hi o' hio
      by_cases hs : (o i).isSome
      · simp only [hs, if_true] at hio
        exact g1 i hi o' hio
      · simp only [hs] at hio
        simp at hio
        exact k1 i (by simp [S', hi, Option.isNone_iff_eq_none]; simpa using hs) o' hio
    · intro i hi
      by_cases hs : (o i).isSome
      · simp [hs]
      · simp only [hs]
        simp
        have := k2 i (by simp [S', hi]; simpa using hs)
        simpa using this
    · have : K * (j + 1) = K + K * j := by ring
      rw [this]; omega



theorem lower_part {ι : Type} (N : Finset ι) (s : ι → ℝ) :
    ∀ m : ℕ, m ≤ N.card → ∃ A ⊆ N, A.card = m ∧ ∀ a ∈ A, ∀ x ∈ N, x ∉ A → s a ≤ s x := by
  intro m
  induction m with
  | zero => intro _; exact ⟨∅, by simp, by simp, by simp⟩
  | succ m ih =>
    intro hm
    obtain ⟨A, hAN, hAc, hA⟩ := ih (by omega)
    have hne : (N \ A).Nonempty := by
      rw [← Finset.card_pos, Finset.card_sdiff_of_subset hAN]; omega
    obtain ⟨x0, hx0, hmin⟩ := Finset.exists_min_image (N \ A) s hne
    rw [Finset.mem_sdiff] at hx0
    refine ⟨insert x0 A, Finset.insert_subset hx0.1 hAN, ?_, ?_⟩
    · rw [Finset.card_insert_of_notMem hx0.2, hAc]
    · intro a ha x hx hxA
      rw [Finset.mem_insert, not_or] at hxA
      rcases Finset.mem_insert.mp ha with rfl | ha
      · exact hmin x (Finset.mem_sdiff.mpr ⟨hx, hxA.2⟩)
      · exact hA a ha x hx hxA.2

noncomputable def adj (lam : ℝ) (o : Ordering) : Ordering := if 0 < lam then o else o.swap

theorem cmp_mul (A B lam F : ℝ) (hl : lam ≠ 0) (h : A - B = lam * F) :
    compare A B = adj lam (compare F 0) := by
  unfold adj
  rcases lt_or_gt_of_ne hl with hl | hl
  · rw [if_neg (by linarith)]
    rcases lt_trichotomy F 0 with hF | hF | hF
    · have : B < A := by nlinarith
      rw [compare_gt_iff_gt.mpr this, compare_lt_iff_lt.mpr hF]; rfl
    · have : A = B := by rw [hF] at h; linarith
      rw [compare_eq_iff_eq.mpr this, compare_eq_iff_eq.mpr hF]; rfl
    · have : A < B := by nlinarith
      rw [compare_lt_iff_lt.mpr this, compare_gt_iff_gt.mpr hF]; rfl
  · rw [if_pos hl]
    rcases lt_trichotomy F 0 with hF | hF | hF
    · have : A < B := by nlinarith
      rw [compare_lt_iff_lt.mpr this, compare_lt_iff_lt.mpr hF]
    · have : A = B := by rw [hF] at h; linarith
      rw [compare_eq_iff_eq.mpr this, compare_eq_iff_eq.mpr hF]
    · have : B < A := by nlinarith
      rw [compare_gt_iff_gt.mpr this, compare_gt_iff_gt.mpr hF]

/-- F_I = K + (1-w) H -/
noncomputable def resI (w : ℝ) (oK oH : Ordering) : Option Ordering :=
  if w = 1 ∨ oH = .eq ∨ oK = oH then some oK else if oK = .eq then some oH else none

/-- F_J = K - w H -/
noncomputable def resJ (w : ℝ) (oK oH : Ordering) : Option Ordering :=
  if w = 0 ∨ oH = .eq ∨ oK = oH.swap then some oK else if oK = .eq then some oH.swap else none

theorem cmp_cases (r : ℝ) : (compare r 0 = .lt ∧ r < 0) ∨ (compare r 0 = .eq ∧ r = 0) ∨
    (compare r 0 = .gt ∧ 0 < r) := by
  rcases lt_trichotomy r 0 with h | h | h
  · exact Or.inl ⟨compare_lt_iff_lt.mpr h, h⟩
  · exact Or.inr (Or.inl ⟨compare_eq_iff_eq.mpr h, h⟩)
  · exact Or.inr (Or.inr ⟨compare_gt_iff_gt.mpr h, h⟩)

theorem resI_ok (w H K FI : ℝ) (hw0 : 0 ≤ w) (hw1 : w ≤ 1) (hF : FI = K + (1 - w) * H)
    (o : Ordering) (h : resI w (compare K 0) (compare H 0) = some o) : compare FI 0 = o := by
  unfold resI at h
  rcases cmp_cases H with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
  rcases cmp_cases K with ⟨k1, k2⟩ | ⟨k1, k2⟩ | ⟨k1, k2⟩ <;>
  rw [h1, k1] at h <;>
  by_cases hw : w = 1 <;> simp [hw] at h <;> subst h <;>
  first
  | (apply compare_lt_iff_lt.mpr; subst hF; nlinarith)
  | (apply compare_gt_iff_gt.mpr; subst hF; nlinarith)
  | (apply compare_eq_iff_eq.mpr; rw [hF]; subst_vars; ring)
  | (apply compare_lt_iff_lt.mpr; subst hF; subst_vars; have : 0 < 1 - w := by
        rcases lt_or_eq_of_le hw1 with h | h
        · linarith
        · exact absurd h hw
     nlinarith)
  | (apply compare_gt_iff_gt.mpr; subst hF; subst_vars; have : 0 < 1 - w := by
        rcases lt_or_eq_of_le hw1 with h | h
        · linarith
        · exact absurd h hw
     nlinarith)

theorem resJ_ok (w H K FJ : ℝ) (hw0 : 0 ≤ w) (hw1 : w ≤ 1) (hF : FJ = K - w * H)
    (o : Ordering) (h : resJ w (compare K 0) (compare H 0) = some o) : compare FJ 0 = o := by
  unfold resJ at h
  rcases cmp_cases H with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
  rcases cmp_cases K with ⟨k1, k2⟩ | ⟨k1, k2⟩ | ⟨k1, k2⟩ <;>
  rw [h1, k1] at h <;>
  by_cases hw : w = 0 <;> simp [hw] at h <;> subst h <;>
  first
  | (apply compare_lt_iff_lt.mpr; subst hF; nlinarith)
  | (apply compare_gt_iff_gt.mpr; subst hF; nlinarith)
  | (apply compare_eq_iff_eq.mpr; rw [hF]; subst_vars; ring)
  | (apply compare_lt_iff_lt.mpr; subst hF; subst_vars; have : 0 < w := by
        rcases lt_or_eq_of_le hw0 with h | h
        · linarith
        · exact absurd h.symm hw
     nlinarith)
  | (apply compare_gt_iff_gt.mpr; subst hF; subst_vars; have : 0 < w := by
        rcases lt_or_eq_of_le hw0 with h | h
        · linarith
        · exact absurd h.symm hw
     nlinarith)

theorem res_some (w : ℝ) (oK oH : Ordering) : (resI w oK oH).isSome ∨ (resJ w oK oH).isSome := by
  unfold resI resJ
  cases oK <;> cases oH <;> simp [Ordering.swap] <;> split_ifs <;> simp



theorem dot_drop {n : ℕ} (v y : Fin (n+1) → ℝ) (hv : v (Fin.last n) = 0) :
    (fun j : Fin n => v j.castSucc) ⬝ᵥ (fun j => y j.castSucc) = v ⬝ᵥ y := by
  simp [dotProduct, Fin.sum_univ_castSucc, hv]

theorem dot_snoc {n : ℕ} (a : Fin n → ℝ) (y : Fin (n+1) → ℝ) :
    (Fin.snoc a 0 : Fin (n+1) → ℝ) ⬝ᵥ y = a ⬝ᵥ (fun j => y j.castSucc) := by
  simp [dotProduct, Fin.sum_univ_castSucc]

noncomputable def Lmap {k : ℕ} (σ : ℝ) (y : Fin (k+2) → ℝ) : Fin (k+1) → ℝ :=
  Fin.cons (σ * y 0 + y (Fin.last (k+1))) (fun j : Fin k => y j.succ.castSucc)

noncomputable def gL {k : ℕ} (σ : ℝ) (a : Fin (k+1) → ℝ) : Fin (k+2) → ℝ :=
  Fin.cons (σ * a 0) (Fin.snoc (fun j : Fin k => a j.succ) (a 0) : Fin (k+1) → ℝ)

theorem dot_L {k : ℕ} (σ : ℝ) (a : Fin (k+1) → ℝ) (y : Fin (k+2) → ℝ) :
    gL σ a ⬝ᵥ y = a ⬝ᵥ Lmap σ y := by
  unfold gL Lmap dotProduct
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ (f := fun i => a i * _), Fin.sum_univ_castSucc]
  simp only [Fin.cons_zero, Fin.cons_succ]
  simp only [Fin.snoc_castSucc, Fin.snoc_last]
  simp only [Fin.succ_last, Fin.succ_castSucc]
  ring

theorem dot_K {k : ℕ} (σ : ℝ) (v y : Fin (k+2) → ℝ) (h0 : v 0 = σ) (h1 : v (Fin.last (k+1)) = 1) :
    (Fin.cons 1 (fun j : Fin k => v j.succ.castSucc) : Fin (k+1) → ℝ) ⬝ᵥ Lmap σ y = v ⬝ᵥ y := by
  unfold Lmap dotProduct
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ (f := fun i => v i * y i), Fin.sum_univ_castSucc]
  simp only [Fin.cons_zero, Fin.cons_succ, Fin.succ_last, Fin.succ_castSucc, h0, h1]
  ring


theorem frac_count {ι : Type} (S U : Finset ι) (out : ι → Option Ordering) (ε : ℝ)
    (hU : ∀ i ∈ U, i ∈ S ∧ (out i).isSome) (h : ε * S.card ≤ U.card) :
    ε * S.card ≤ ((S.filter fun i => (out i).isSome).card : ℝ) := by
  have hsub : U ⊆ S.filter (fun i => (out i).isSome) := fun i hi => by
    simp [(hU i hi).1, (hU i hi).2]
  have := Finset.card_le_card hsub
  calc _ ≤ (U.card : ℝ) := h
    _ ≤ _ := by exact_mod_cast this

theorem dot1 (a y : Fin 1 → ℝ) : a ⬝ᵥ y = a 0 * y 0 := by simp [dotProduct]

theorem frac_one : Frac 1 (1/2) 1 := by
  intro ι S c b
  set Z := S.filter (fun i => c i 0 = 0) with hZ
  set N := S.filter (fun i => ¬ c i 0 = 0) with hN
  have hZN : Z.card + N.card = S.card := Finset.card_filter_add_card_filter_not _
  have hdisj : ∀ U ⊆ N, Disjoint Z U := fun U hU =>
    Finset.disjoint_of_subset_right hU (Finset.disjoint_filter_filter_not _ _ _)
  set θ : ι → ℝ := fun i => b i / c i 0 with hθ
  have key : ∀ i, c i 0 ≠ 0 → ∀ y : Fin 1 → ℝ,
      compare (c i ⬝ᵥ y) (b i) = adj (c i 0) (compare (y 0 - θ i) 0) := by
    intro i hi y; rw [dot1]; apply cmp_mul _ _ _ _ hi; simp only [θ]; field_simp
  have keyZ : ∀ i, c i 0 = 0 → ∀ y : Fin 1 → ℝ, compare (c i ⬝ᵥ y) (b i) = compare 0 (b i) := by
    intro i hi y; rw [dot1, hi, zero_mul]
  rcases N.eq_empty_or_nonempty with hNe | hNe
  · refine ⟨QTree.leaf (fun i => if c i 0 = 0 then some (compare 0 (b i)) else none),
      fun y => ⟨?_, ?_, ?_⟩⟩
    · intro i hi o ho
      simp only [QTree.eval] at ho
      split_ifs at ho with h1
      · cases ho; exact keyZ i h1 y
    · apply frac_count S S
      · intro i hi
        refine ⟨hi, ?_⟩
        have : c i 0 = 0 := by
          by_contra hc
          have : i ∈ N := by simp [hN, hi, hc]
          rw [hNe] at this; simp at this
        simp [QTree.eval, this]
      · have : (0:ℝ) ≤ S.card := by positivity
        linarith
    · simp [QTree.numQueries]
  · set m := (N.card + 1) / 2 with hm
    obtain ⟨A, hAN, hAc, hlow⟩ := lower_part N θ m (by omega)
    have hA : A.Nonempty := by
      rw [← Finset.card_pos, hAc]; have := hNe.card_pos; omega
    set σ := A.sup' hA θ with hσ
    obtain ⟨a0, ha0A, ha0⟩ := Finset.exists_mem_eq_sup' hA θ
    rw [← hσ] at ha0
    let outL : ι → Option Ordering := fun i =>
      if c i 0 = 0 then some (compare 0 (b i)) else
        if σ ≤ θ i then some (adj (c i 0) .lt) else none
    let outE : ι → Option Ordering := fun i =>
      if c i 0 = 0 then some (compare 0 (b i)) else some (adj (c i 0) (compare (σ - θ i) 0))
    let outG : ι → Option Ordering := fun i =>
      if c i 0 = 0 then some (compare 0 (b i)) else
        if θ i ≤ σ then some (adj (c i 0) .gt) else none
    refine ⟨QTree.query (fun _ => 1) σ (QTree.leaf outL) (QTree.leaf outE) (QTree.leaf outG),
      fun y => ?_⟩
    have hdot : (fun _ => (1:ℝ)) ⬝ᵥ y = y 0 := by rw [dot1, one_mul]
    simp only [QTree.eval, QTree.numQueries, hdot]
    rcases lt_trichotomy (y 0) σ with hy | hy | hy
    · rw [compare_lt_iff_lt.mpr hy]
      simp only
      refine ⟨?_, ?_, le_refl _⟩
      · intro i hi o ho
        simp only [outL] at ho
        split_ifs at ho with h1 h2
        · cases ho; exact keyZ i h1 y
        · cases ho; rw [key i h1 y, compare_lt_iff_lt.mpr (by linarith)]
      · apply frac_count S (Z ∪ insert a0 (N \ A))
        · intro i hi
          rcases Finset.mem_union.mp hi with hi | hi
          · have := Finset.mem_filter.mp hi
            exact ⟨this.1, by simp [outL, this.2]⟩
          · rcases Finset.mem_insert.mp hi with rfl | hi
            · have := Finset.mem_filter.mp (hAN ha0A)
              exact ⟨this.1, by simp [outL, this.2, ha0]⟩
            · have hi' := Finset.mem_sdiff.mp hi
              have := Finset.mem_filter.mp hi'.1
              have hle : σ ≤ θ i := by rw [ha0]; exact hlow a0 ha0A i hi'.1 hi'.2
              exact ⟨this.1, by simp [outL, this.2, hle]⟩
        · have hsub : insert a0 (N \ A) ⊆ N :=
            Finset.insert_subset (hAN ha0A) Finset.sdiff_subset
          rw [Finset.card_union_of_disjoint (hdisj _ hsub),
            Finset.card_insert_of_notMem (by simp [ha0A]), Finset.card_sdiff_of_subset hAN]
          have : 2 * (Z.card + (N.card - A.card + 1)) ≥ S.card := by omega
          have h2 : (2:ℝ) * ((Z.card + (N.card - A.card + 1) : ℕ) : ℝ) ≥ S.card := by
            exact_mod_cast this
          push_cast at h2 ⊢
          linarith
    · rw [compare_eq_iff_eq.mpr hy]
      simp only
      refine ⟨?_, ?_, le_refl _⟩
      · intro i hi o ho
        simp only [outE] at ho
        split_ifs at ho with h1
        · cases ho; exact keyZ i h1 y
        · cases ho; rw [key i h1 y, hy]
      · apply frac_count S S
        · intro i hi
          refine ⟨hi, ?_⟩
          simp only [outE]; split_ifs <;> simp
        · have : (0:ℝ) ≤ S.card := by positivity
          linarith
    · rw [compare_gt_iff_gt.mpr hy]
      simp only
      refine ⟨?_, ?_, le_refl _⟩
      · intro i hi o ho
        simp only [outG] at ho
        split_ifs at ho with h1 h2
        · cases ho; exact keyZ i h1 y
        · cases ho; rw [key i h1 y, compare_gt_iff_gt.mpr (by linarith)]
      · apply frac_count S (Z ∪ A)
        · intro i hi
          rcases Finset.mem_union.mp hi with hi | hi
          · have := Finset.mem_filter.mp hi
            exact ⟨this.1, by simp [outG, this.2]⟩
          · have := Finset.mem_filter.mp (hAN hi)
            have hle : θ i ≤ σ := Finset.le_sup' θ hi
            exact ⟨this.1, by simp [outG, this.2, hle]⟩
        · rw [Finset.card_union_of_disjoint (hdisj _ hAN)]
          have : 2 * (Z.card + A.card) ≥ S.card := by omega
          have h2 : (2:ℝ) * ((Z.card + A.card : ℕ) : ℝ) ≥ S.card := by exact_mod_cast this
          push_cast at h2 ⊢
          linarith

theorem cmp_sub (a b : ℝ) : compare a b = compare (a - b) 0 := by
  rcases lt_trichotomy a b with h | h | h
  · rw [compare_lt_iff_lt.mpr h, compare_lt_iff_lt.mpr (by linarith)]
  · rw [compare_eq_iff_eq.mpr h, compare_eq_iff_eq.mpr (by linarith)]
  · rw [compare_gt_iff_gt.mpr h, compare_gt_iff_gt.mpr (by linarith)]

theorem frac_step (k : ℕ) (ε : ℝ) (K : ℕ) (hε : 0 < ε) (hε1 : ε ≤ 1) (h : Frac (k+1) ε K) :
    Frac (k+2) (ε * ε / 6) (2 * K + 1) := by
  intro ι S c b
  set lst : Fin (k+2) := Fin.last (k+1) with hlst
  set Z := S.filter (fun i => c i lst = 0) with hZ
  set N := S.filter (fun i => ¬ c i lst = 0) with hN
  have hZN : Z.card + N.card = S.card := Finset.card_filter_add_card_filter_not _
  have hε2 : ε * ε / 6 ≤ ε / 2 := by nlinarith
  have hS0 : (0:ℝ) ≤ S.card := by positivity
  by_cases hZbig : S.card ≤ 2 * Z.card
  · obtain ⟨T, hT⟩ := frac_pull h Z (fun i j => c i j.castSucc) b (fun y j => y j.castSucc)
      (fun a => (Fin.snoc a 0 : Fin (k+2) → ℝ)) (fun a y => dot_snoc a y)
    refine ⟨T.bindT (fun o => QTree.leaf (fun i => if c i lst = 0 then o i else none)),
      fun y => ?_⟩
    obtain ⟨g1, g2, g3⟩ := hT y
    rw [QTree.eval_bindT, QTree.numQueries_bindT]
    simp only [QTree.eval, QTree.numQueries, add_zero]
    refine ⟨?_, ?_, by omega⟩
    · intro i hi o ho
      split_ifs at ho with h1
      have hiZ : i ∈ Z := Finset.mem_filter.mpr ⟨hi, h1⟩
      have := g1 i hiZ o ho
      rwa [dot_drop (c i) y h1] at this
    · apply frac_count S (Z.filter (fun i => (T.eval y i).isSome))
      · intro i hi
        obtain ⟨hi1, hi2⟩ := Finset.mem_filter.mp hi
        obtain ⟨hi3, hi4⟩ := Finset.mem_filter.mp hi1
        exact ⟨hi3, by simp [hi4, hi2]⟩
      · have hZr : (S.card : ℝ) ≤ 2 * Z.card := by exact_mod_cast hZbig
        nlinarith
  · have hNbig : S.card < 2 * N.card := by omega
    by_cases hN1 : N.card ≤ 1
    · obtain ⟨i0, hi0⟩ : N.Nonempty := Finset.card_pos.mp (by omega)
      have hS1 : S.card ≤ 1 := by omega
      let out : Ordering → ι → Option Ordering := fun r i => if i = i0 then some r else none
      refine ⟨QTree.query (c i0) (b i0) (QTree.leaf (out .lt)) (QTree.leaf (out .eq))
        (QTree.leaf (out .gt)), fun y => ?_⟩
      have hev : (QTree.query (c i0) (b i0) (QTree.leaf (out .lt)) (QTree.leaf (out .eq))
          (QTree.leaf (out .gt))).eval y = out (compare (c i0 ⬝ᵥ y) (b i0)) := by
        simp only [QTree.eval]
        cases compare (c i0 ⬝ᵥ y) (b i0) <;> rfl
      have hnq : (QTree.query (c i0) (b i0) (QTree.leaf (out .lt)) (QTree.leaf (out .eq))
          (QTree.leaf (out .gt))).numQueries y = 1 := by
        simp only [QTree.numQueries]
        cases compare (c i0 ⬝ᵥ y) (b i0) <;> rfl
      rw [hev, hnq]
      refine ⟨?_, ?_, by omega⟩
      · intro i hi o ho
        simp only [out] at ho
        split_ifs at ho with h1
        cases ho; rw [h1]
      · apply frac_count S {i0}
        · intro i hi
          rw [Finset.mem_singleton] at hi
          subst hi
          exact ⟨(Finset.mem_filter.mp hi0).1, by simp [out]⟩
        · have : (S.card : ℝ) ≤ 1 := by exact_mod_cast hS1
          simp only [Finset.card_singleton, Nat.cast_one]
          nlinarith
    · have hN2 : 2 ≤ N.card := by omega
      set u : ι → Fin (k+2) → ℝ := fun i => (c i lst)⁻¹ • c i with hu
      set β : ι → ℝ := fun i => (c i lst)⁻¹ * b i with hβ
      set s : ι → ℝ := fun i => u i 0 with hs
      have hu_lst : ∀ i ∈ N, u i lst = 1 := by
        intro i hi
        have := (Finset.mem_filter.mp hi).2
        simp only [hu, Pi.smul_apply, smul_eq_mul]
        exact inv_mul_cancel₀ this
      have hF : ∀ i ∈ N, ∀ y, c i ⬝ᵥ y - b i = c i lst * (u i ⬝ᵥ y - β i) := by
        intro i hi y
        have h0 := (Finset.mem_filter.mp hi).2
        simp only [hu, hβ, smul_dotProduct, smul_eq_mul]
        field_simp
      obtain ⟨A, hAN, hAc, hlow⟩ := lower_part N s (N.card / 2) (by omega)
      have hA : A.Nonempty := by rw [← Finset.card_pos, hAc]; omega
      set σ := A.sup' hA s with hσ
      have hσA : ∀ a ∈ A, s a ≤ σ := fun a ha => Finset.le_sup' s ha
      have hσB : ∀ x ∈ N, x ∉ A → σ ≤ s x := fun x hx hxA =>
        Finset.sup'_le hA s (fun a ha => hlow a ha x hx hxA)
      have hcardle : Fintype.card A ≤ Fintype.card (N \ A : Finset ι) := by
        simp only [Fintype.card_coe]; rw [Finset.card_sdiff_of_subset hAN, hAc]; omega
      obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le hcardle
      set E : ι → ι := fun p => if hp : p ∈ A then ((e ⟨p, hp⟩ : (N \ A : Finset ι)) : ι)
        else p with hE
      have hE1 : ∀ p ∈ A, E p ∈ N ∧ E p ∉ A := by
        intro p hp
        have := (e ⟨p, hp⟩).2
        simp only [hE, dif_pos hp]
        exact Finset.mem_sdiff.mp this
      have hEinj : ∀ p ∈ A, ∀ q ∈ A, E p = E q → p = q := by
        intro p hp q hq hpq
        simp only [hE, dif_pos hp, dif_pos hq] at hpq
        have := e.injective (Subtype.ext hpq)
        exact congrArg Subtype.val this
      set w : ι → ℝ := fun p => (σ - s p) / (s (E p) - s p) with hw
      have hw01 : ∀ p ∈ A, 0 ≤ w p ∧ w p ≤ 1 ∧ w p * s (E p) + (1 - w p) * s p = σ := by
        intro p hp
        have h1 := hσA p hp
        have h2 := hσB (E p) (hE1 p hp).1 (hE1 p hp).2
        rcases eq_or_lt_of_le (le_trans h1 h2) with heq | hlt
        · have : s (E p) - s p = 0 := by linarith
          simp only [hw, this, div_zero]
          refine ⟨le_refl _, zero_le_one, ?_⟩
          linarith
        · have hpos : 0 < s (E p) - s p := by linarith
          refine ⟨div_nonneg (by linarith) hpos.le, (div_le_one hpos).mpr (by linarith), ?_⟩
          simp only [hw]
          field_simp
          ring
      obtain ⟨T1, hT1⟩ := frac_pull h A (fun p j => (u (E p) - u p) j.castSucc)
        (fun p => β (E p) - β p) (fun y j => y j.castSucc)
        (fun a => (Fin.snoc a 0 : Fin (k+2) → ℝ)) (fun a y => dot_snoc a y)
      set A2 : (ι → Option Ordering) → Finset ι := fun o1 => A.filter (fun p => (o1 p).isSome)
        with hA2
      set kc : ι → Fin (k+1) → ℝ := fun p =>
        (Fin.cons 1 (fun j : Fin k => (w p • u (E p) + (1 - w p) • u p) j.succ.castSucc) :
          Fin (k+1) → ℝ) with hkc
      set kb : ι → ℝ := fun p => w p * β (E p) + (1 - w p) * β p with hkb
      have st2 := fun o1 => frac_pull h (A2 o1) kc kb (Lmap σ) (gL σ) (dot_L σ)
      let pr : (ι → Option Ordering) → (ι → Option Ordering) → ι →
          Option Ordering × Option Ordering := fun o1 o2 p =>
        match o1 p, o2 p with
        | some oH, some oK => ((resI (w p) oK oH).map (adj (c (E p) lst)),
            (resJ (w p) oK oH).map (adj (c p lst)))
        | _, _ => (none, none)
      let out : (ι → Option Ordering) → (ι → Option Ordering) → ι → Option Ordering :=
        fun o1 o2 i => if i ∈ A then (pr o1 o2 i).2 else
          if h' : ∃ p ∈ A, E p = i then (pr o1 o2 (Classical.choose h')).1 else none
      refine ⟨T1.bindT (fun o1 => (Classical.choose (st2 o1)).bindT
        (fun o2 => QTree.leaf (out o1 o2))), fun y => ?_⟩
      rw [QTree.eval_bindT, QTree.numQueries_bindT]
      obtain ⟨g1, g2, g3⟩ := hT1 y
      obtain ⟨k1, k2, k3⟩ := Classical.choose_spec (st2 (T1.eval y)) y
      rw [QTree.eval_bindT, QTree.numQueries_bindT]
      simp only [QTree.eval, QTree.numQueries, add_zero]
      generalize hT2 : Classical.choose (st2 (T1.eval y)) = T2 at k1 k2 k3 ⊢
      generalize ho1 : T1.eval y = o1 at g1 g2 k1 k2 ⊢
      generalize ho2 : T2.eval y = o2 at k1 k2 ⊢
      -- per-pair correctness
      have pairOK : ∀ p ∈ A, ∀ oH oK, o1 p = some oH → o2 p = some oK →
          (∀ o, (resI (w p) oK oH).map (adj (c (E p) lst)) = some o →
            compare (c (E p) ⬝ᵥ y) (b (E p)) = o) ∧
          (∀ o, (resJ (w p) oK oH).map (adj (c p lst)) = some o →
            compare (c p ⬝ᵥ y) (b p) = o) := by
        intro p hp oH oK h1 h2
        obtain ⟨w0, w1, wσ⟩ := hw01 p hp
        have hpN := hAN hp
        have hEN := (hE1 p hp).1
        have hH := g1 p hp oH h1
        have hlst0 : (u (E p) - u p) lst = 0 := by
          simp only [Pi.sub_apply, hu_lst _ hEN, hu_lst _ hpN, sub_self]
        rw [dot_drop (u (E p) - u p) y hlst0, sub_dotProduct, cmp_sub] at hH
        have hp2 : p ∈ A2 o1 := Finset.mem_filter.mpr ⟨hp, by simp [h1]⟩
        have hK := k1 p hp2 oK h2
        have hv0 : (w p • u (E p) + (1 - w p) • u p) 0 = σ := by
          simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; rw [← wσ]
        have hv1 : (w p • u (E p) + (1 - w p) • u p) lst = 1 := by
          simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hu_lst _ hEN, hu_lst _ hpN]; ring
        simp only [hkc, hkb] at hK
        have hdot : (w p • u (E p) + (1 - w p) • u p) ⬝ᵥ y =
            w p * (u (E p) ⬝ᵥ y) + (1 - w p) * (u p ⬝ᵥ y) := by
          simp only [add_dotProduct, smul_dotProduct, smul_eq_mul]
        rw [dot_K σ _ y hv0 hv1, hdot, cmp_sub] at hK
        set FE := u (E p) ⬝ᵥ y - β (E p)
        set Fp := u p ⬝ᵥ y - β p
        have eH : u (E p) ⬝ᵥ y - u p ⬝ᵥ y - (β (E p) - β p) = FE - Fp := by ring
        have eK : w p * (u (E p) ⬝ᵥ y) + (1 - w p) * (u p ⬝ᵥ y) -
            (w p * β (E p) + (1 - w p) * β p) = w p * FE + (1 - w p) * Fp := by ring
        rw [eH] at hH
        rw [eK] at hK
        constructor
        · intro o ho
          obtain ⟨o', ho', rfl⟩ := Option.map_eq_some_iff.mp ho
          rw [← hH, ← hK] at ho'
          have := resI_ok (w p) (FE - Fp) (w p * FE + (1 - w p) * Fp) FE w0 w1 (by ring) o' ho'
          rw [← this]
          exact cmp_mul _ _ _ _ (Finset.mem_filter.mp hEN).2 (hF _ hEN y)
        · intro o ho
          obtain ⟨o', ho', rfl⟩ := Option.map_eq_some_iff.mp ho
          rw [← hH, ← hK] at ho'
          have := resJ_ok (w p) (FE - Fp) (w p * FE + (1 - w p) * Fp) Fp w0 w1 (by ring) o' ho'
          rw [← this]
          exact cmp_mul _ _ _ _ (Finset.mem_filter.mp hpN).2 (hF _ hpN y)
      have prOK : ∀ p ∈ A,
          (∀ o, (pr o1 o2 p).1 = some o → compare (c (E p) ⬝ᵥ y) (b (E p)) = o) ∧
          (∀ o, (pr o1 o2 p).2 = some o → compare (c p ⬝ᵥ y) (b p) = o) := by
        intro p hp
        simp only [pr]
        rcases h1 : o1 p with _ | oH <;> rcases h2 : o2 p with _ | oK
        · simp
        · simp
        · simp
        · exact pairOK p hp oH oK h1 h2
      have prSome : ∀ p ∈ A, (o1 p).isSome → (o2 p).isSome →
          (pr o1 o2 p).1.isSome ∨ (pr o1 o2 p).2.isSome := by
        intro p hp h1 h2
        simp only [pr]
        obtain ⟨oH, h1'⟩ := Option.isSome_iff_exists.mp h1
        obtain ⟨oK, h2'⟩ := Option.isSome_iff_exists.mp h2
        rw [h1', h2']
        simpa using res_some (w p) oK oH
      have outE : ∀ p ∈ A, out o1 o2 (E p) = (pr o1 o2 p).1 := by
        intro p hp
        have hex : ∃ q ∈ A, E q = E p := ⟨p, hp, rfl⟩
        simp only [out, if_neg (hE1 p hp).2, dif_pos hex]
        have := Classical.choose_spec hex
        rw [hEinj _ this.1 p hp this.2]
      refine ⟨?_, ?_, by omega⟩
      · intro i hi o ho
        simp only [out] at ho
        split_ifs at ho with hiA hex
        · exact (prOK i hiA).2 o ho
        · have := Classical.choose_spec hex
          rw [← this.2]
          exact (prOK _ this.1).1 o ho
      · set A' := A.filter (fun p => (o1 p).isSome ∧ (o2 p).isSome) with hA'
        let φ : ι → ι := fun p => if (pr o1 o2 p).1.isSome then E p else p
        apply frac_count S (A'.image φ)
        · intro i hi
          obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hi
          obtain ⟨hpA, hp1, hp2⟩ : p ∈ A ∧ (o1 p).isSome ∧ (o2 p).isSome := by
            simpa [hA'] using hp
          simp only [φ]
          split_ifs with hs1
          · refine ⟨(Finset.mem_filter.mp (hE1 p hpA).1).1, ?_⟩
            rw [outE p hpA]; exact hs1
          · refine ⟨(Finset.mem_filter.mp (hAN hpA)).1, ?_⟩
            simp only [out, if_pos hpA]
            rcases prSome p hpA hp1 hp2 with h | h
            · exact absurd h hs1
            · exact h
        · have hinj : Set.InjOn φ A' := by
            intro p hp q hq hpq
            have hpA := (Finset.mem_filter.mp hp).1
            have hqA := (Finset.mem_filter.mp hq).1
            simp only [φ] at hpq
            split_ifs at hpq with hs1 hs2 hs2
            · exact hEinj p hpA q hqA hpq
            · exact absurd (hpq ▸ hqA) (hE1 p hpA).2
            · exact absurd (hpq.symm ▸ hpA) (hE1 q hqA).2
            · exact hpq
          rw [Finset.card_image_of_injOn hinj]
          have hA'eq : A' = (A2 o1).filter (fun p => (o2 p).isSome) := by
            ext p; simp only [hA', hA2, Finset.mem_filter, and_assoc]
          have e1 : ε * A.card ≤ ((A2 o1).card : ℝ) := g2
          have e2 : ε * (A2 o1).card ≤ (A'.card : ℝ) := by rw [hA'eq]; exact k2
          have e3 : (S.card : ℝ) ≤ 6 * A.card := by
            have : S.card ≤ 6 * A.card := by rw [hAc]; omega
            exact_mod_cast this
          have h4 : ε * (ε * A.card) ≤ A'.card :=
            le_trans (mul_le_mul_of_nonneg_left e1 hε.le) e2
          have h5 : ε * ε / 6 * (S.card : ℝ) ≤ ε * ε / 6 * (6 * A.card) :=
            mul_le_mul_of_nonneg_left e3 (by positivity)
          calc ε * ε / 6 * (S.card : ℝ) ≤ ε * ε / 6 * (6 * A.card) := h5
            _ = ε * (ε * A.card) := by ring
            _ ≤ A'.card := h4

theorem frac_exists (k : ℕ) : ∃ ε : ℝ, ∃ K : ℕ, 0 < ε ∧ ε < 1 ∧ Frac (k+1) ε K := by
  induction k with
  | zero => exact ⟨1/2, 1, by norm_num, by norm_num, frac_one⟩
  | succ k ih =>
    obtain ⟨ε, K, h0, h1, hF⟩ := ih
    exact ⟨ε * ε / 6, 2 * K + 1, by positivity, by nlinarith, frac_step k ε K h0 h1.le hF⟩

theorem log_queries_all_core (d : ℕ) (hd : 1 ≤ d) :
    ∃ C : ℝ, ∀ n : ℕ, 2 ≤ n → ∀ (a : Fin n → Fin d → ℝ) (b : Fin n → ℝ), (∀ i, a i ≠ 0) →
      ∃ T : QTree d (Fin n → Ordering), ∀ x : Fin d → ℝ,
        T.eval x = (fun i => compare (a i ⬝ᵥ x) (b i)) ∧
        (T.numQueries x : ℝ) ≤ C * Real.log n := by
  obtain ⟨k, rfl⟩ : ∃ k, d = k + 1 := ⟨d - 1, by omega⟩
  obtain ⟨ε, K, hε, hε1, hF⟩ := frac_exists k
  have hr0 : 0 < 1 - ε := by linarith
  have hr1 : 1 - ε < 1 := by linarith
  set L := -Real.log (1 - ε) with hL
  have hLpos : 0 < L := by
    have := Real.log_neg hr0 hr1
    linarith
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨K * (1 / L + 1 / Real.log 2), fun n hn a b _ => ?_⟩
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hlogn : Real.log 2 ≤ Real.log n :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hn)
  set j := ⌊Real.log n / L⌋₊ + 1 with hj
  have hjgt : Real.log n / L < j := by
    rw [hj]; push_cast; exact Nat.lt_floor_add_one _
  have hlt : ((Finset.univ : Finset (Fin n)).card : ℝ) * (1 - ε) ^ j < 1 := by
    rw [Finset.card_univ, Fintype.card_fin]
    have hpos : 0 < (n : ℝ) * (1 - ε) ^ j := mul_pos hn0 (pow_pos hr0 _)
    rw [← Real.log_neg_iff hpos, Real.log_mul hn0.ne' (pow_pos hr0 _).ne', Real.log_pow]
    have : Real.log n < j * L := by
      rw [div_lt_iff₀ hLpos] at hjgt; linarith
    linarith
  obtain ⟨T, hT⟩ := frac_iter hε hε1 hF a b j Finset.univ hlt
  refine ⟨T.bindT (fun o => QTree.leaf (fun i => (o i).getD .eq)), fun x => ?_⟩
  obtain ⟨h1, h2, h3⟩ := hT x
  rw [QTree.eval_bindT, QTree.numQueries_bindT]
  simp only [QTree.eval, QTree.numQueries, add_zero]
  refine ⟨?_, ?_⟩
  · funext i
    have hs := h2 i (Finset.mem_univ i)
    obtain ⟨o, ho⟩ := Option.isSome_iff_exists.mp hs
    rw [ho, Option.getD_some]
    exact (h1 i (Finset.mem_univ i) o ho).symm
  · have h3' : (T.numQueries x : ℝ) ≤ K * j := by exact_mod_cast h3
    have hjle : (j : ℝ) ≤ Real.log n / L + Real.log n / Real.log 2 := by
      have : (j : ℝ) ≤ Real.log n / L + 1 := by
        rw [hj]; push_cast
        have := Nat.floor_le (show 0 ≤ Real.log n / L from
          div_nonneg (by linarith) hLpos.le)
        linarith
      have : 1 ≤ Real.log n / Real.log 2 := by rw [le_div_iff₀ hl2]; linarith
      linarith
    have hK : (0 : ℝ) ≤ K := by positivity
    calc (T.numQueries x : ℝ) ≤ K * j := h3'
      _ ≤ K * (Real.log n / L + Real.log n / Real.log 2) := mul_le_mul_of_nonneg_left hjle hK
      _ = K * (1 / L + 1 / Real.log 2) * Real.log n := by ring

end MegiddoLP.FixedDim

open MegiddoLP.FixedDim


theorem solution (d : ℕ) (hd : 1 ≤ d) :
    ∃ C : ℝ, ∀ n : ℕ, 2 ≤ n → ∀ (a : Fin n → Fin d → ℝ) (b : Fin n → ℝ), (∀ i, a i ≠ 0) →
      ∃ T : QTree d (Fin n → Ordering), ∀ x : Fin d → ℝ,
        T.eval x = (fun i => compare (a i ⬝ᵥ x) (b i)) ∧
        (T.numQueries x : ℝ) ≤ C * Real.log n := by
  exact log_queries_all_core d hd
