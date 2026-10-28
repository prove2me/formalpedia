-- Prove2me | solution 1 for MatrixAnalytic.Stability.R_structure
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T09:49:14.696663+00:00
-- url     : https://prove2.me/submissions/1668eaef-473c-42d3-b3f7-018bf8444d05

import Mathlib
import Definitions.Def_MatrixAnalytic_Stability_Chain
import Definitions.Def_MatrixAnalytic_Stability_QBD
import Definitions.Def_MatrixAnalytic_Stability_Passage

open scoped ENNReal
open MatrixAnalytic.Stability

namespace GSX

/-! ### Irreducibility of `ℝ≥0∞` matrices via `TransGen` -/
section Irr
variable {κ : Type*} [DecidableEq κ]

lemma matPowE_one' (M : κ → κ → ℝ≥0∞) (i j : κ) : matPowE M 1 i j = M i j := by
  simp only [matPowE, matMulE, matOneE]
  rw [tsum_eq_single i]
  · simp
  · intro b hb; simp [Ne.symm hb]

lemma matPowE_succ' (M : κ → κ → ℝ≥0∞) (t : ℕ) (i j : κ) :
    matPowE M (t + 1) i j = ∑' k, matPowE M t i k * M k j := rfl

lemma irr_of_transGen (M : κ → κ → ℝ≥0∞)
    (h : ∀ i j, Relation.TransGen (fun a b => M a b ≠ 0) i j) : IrreducibleE M := by
  intro i j
  have hij := h i j
  induction hij with
  | single hab => exact ⟨1, one_pos, by rw [matPowE_one']; exact hab⟩
  | @tail b c _ hbc ih =>
    obtain ⟨t, _, hne⟩ := ih
    refine ⟨t + 1, by omega, ?_⟩
    rw [matPowE_succ']
    exact ne_of_gt (lt_of_lt_of_le (pos_iff_ne_zero.mpr (mul_ne_zero hne hbc)) (ENNReal.le_tsum b))

end Irr

/-! ### Generic combinatorial block structure -/
section Comb
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem comb [Nonempty ι] (E : ι → ι → Prop) (hrow : ∀ i, ∃ j, E i j)
    (hreach : ∀ i, Relation.TransGen E i i → ∀ j, Relation.TransGen E j i) :
    ∃ (σ : ι ≃ Fin (Fintype.card ι)) (k : ℕ), 0 < k ∧ k ≤ Fintype.card ι ∧
      (∀ i j : ι, (σ i : ℕ) < k → k ≤ (σ j : ℕ) → ¬ E i j) ∧
      (∀ a b : {i : ι // (σ i : ℕ) < k},
        Relation.TransGen (fun a b : {i : ι // (σ i : ℕ) < k} => E a.1 b.1) a b) ∧
      (∀ i j : ι, k ≤ (σ i : ℕ) → k ≤ (σ j : ℕ) → σ i ≤ σ j → ¬ E i j) := by
  classical
  set C : ι → Prop := fun i => Relation.TransGen E i i with hCd
  have hclosed : ∀ i j, C i → E i j → C j := fun i j hi hij => (hreach i hi j).tail hij
  have hCpath : ∀ x y, Relation.TransGen E x y → C x → C y := by
    intro x y h hx
    induction h with
    | single h => exact hclosed _ _ hx h
    | tail _ h ih => exact hclosed _ _ ih h
  -- a cycle exists
  have hne : ∃ i, C i := by
    choose g hg using hrow
    let f : ℕ → ι := fun n => g^[n] (Classical.arbitrary ι)
    have hf : ∀ n, E (f n) (f (n + 1)) := by
      intro n
      simp only [f, Function.iterate_succ_apply']
      exact hg _
    have hpath : ∀ a d, Relation.TransGen E (f a) (f (a + d + 1)) := by
      intro a d
      induction d with
      | zero => exact .single (hf a)
      | succ d ih => exact ih.tail (by rw [show a + (d + 1) + 1 = (a + d + 1) + 1 by omega]; exact hf _)
    obtain ⟨x, y, hxy, hfxy⟩ := Finite.exists_ne_map_eq_of_infinite f
    rcases Nat.lt_or_gt_of_ne hxy with h | h
    · refine ⟨f x, ?_⟩
      have := hpath x (y - x - 1)
      rw [show x + (y - x - 1) + 1 = y by omega, ← hfxy] at this
      exact this
    · refine ⟨f y, ?_⟩
      have := hpath y (x - y - 1)
      rw [show y + (x - y - 1) + 1 = x by omega, hfxy] at this
      exact this
  obtain ⟨i0, hi0⟩ := hne
  set n := Fintype.card ι with hn
  set e := Fintype.equivFin ι with he
  set anc : ι → Finset ι := fun i =>
    Finset.univ.filter (fun x => ¬ C x ∧ Relation.TransGen E i x) with hanc
  set c : ι → ℕ := fun i => if C i then 0 else (anc i).card + 1 with hcd
  have hc_lt : ∀ i j, ¬ C i → ¬ C j → E i j → c j < c i := by
    intro i j hi hj hij
    simp only [hcd, if_neg hi, if_neg hj]
    have : anc j ⊂ anc i := by
      rw [Finset.ssubset_iff_of_subset]
      · refine ⟨j, ?_, ?_⟩
        · simp only [hanc, Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨hj, .single hij⟩
        · simp only [hanc, Finset.mem_filter, Finset.mem_univ, true_and, not_and]
          intro _; exact hj
      · intro x hx
        simp only [hanc, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
        exact ⟨hx.1, .head hij hx.2⟩
    have := Finset.card_lt_card this
    omega
  set key : ι → ℕ := fun i => c i * n + (e i : ℕ) with hkey
  have hen : ∀ i, (e i : ℕ) < n := fun i => (e i).isLt
  have hkey_lt : ∀ i j, c i < c j → key i < key j := by
    intro i j h
    have h1 : (c i + 1) * n ≤ c j * n := Nat.mul_le_mul_right _ h
    have h2 := hen i
    simp only [hkey]
    nlinarith
  have hkey_inj : ∀ i j, key i = key j → i = j := by
    intro i j h
    rcases lt_trichotomy (c i) (c j) with h1 | h1 | h1
    · exact absurd h (ne_of_lt (hkey_lt i j h1))
    · simp only [hkey, h1] at h
      exact e.injective (Fin.ext (by omega))
    · exact absurd h (ne_of_gt (hkey_lt j i h1))
  set rk : ι → ℕ := fun i => (Finset.univ.filter (fun x => key x < key i)).card with hrk
  have hrk_lt_n : ∀ i, rk i < n := by
    intro i
    simp only [hrk, hn]
    rw [← Finset.card_univ]
    apply Finset.card_lt_card
    rw [Finset.ssubset_iff_of_subset (Finset.subset_univ _)]
    exact ⟨i, Finset.mem_univ _, by simp⟩
  have hrk_mono : ∀ i j, key i < key j → rk i < rk j := by
    intro i j h
    apply Finset.card_lt_card
    rw [Finset.ssubset_iff_of_subset]
    · exact ⟨i, by simp [h], by simp⟩
    · intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
      exact lt_trans hx h
  have hrk_inj : Function.Injective rk := by
    intro i j h
    by_contra hij
    rcases lt_trichotomy (key i) (key j) with h1 | h1 | h1
    · exact absurd h (ne_of_lt (hrk_mono i j h1))
    · exact hij (hkey_inj i j h1)
    · exact absurd h (ne_of_gt (hrk_mono j i h1))
  let σ : ι ≃ Fin n := Equiv.ofBijective (fun i => ⟨rk i, hrk_lt_n i⟩) (by
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨fun a b h => hrk_inj (by simpa using congrArg Fin.val h), by simp [hn]⟩)
  have hσ : ∀ i, (σ i : ℕ) = rk i := fun i => rfl
  set K := (Finset.univ.filter C).card with hK
  have hkeyC : ∀ i, C i → key i < n := by
    intro i hi; simp only [hkey, hcd, if_pos hi, zero_mul, zero_add]; exact hen i
  have hkeyN : ∀ i, ¬ C i → n ≤ key i := by
    intro i hi; simp only [hkey, hcd, if_neg hi]
    nlinarith
  have hσC : ∀ i, (σ i : ℕ) < K ↔ C i := by
    intro i
    rw [hσ]
    constructor
    · intro h
      by_contra hc
      have : Finset.univ.filter C ⊆ Finset.univ.filter (fun x => key x < key i) := by
        intro x hx
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
        exact lt_of_lt_of_le (hkeyC x hx) (hkeyN i hc)
      have := Finset.card_le_card this
      simp only [hrk] at h
      omega
    · intro hc
      apply Finset.card_lt_card
      rw [Finset.ssubset_iff_of_subset]
      · exact ⟨i, by simp [hc], by simp⟩
      · intro x hx
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
        by_contra hxc
        exact absurd (lt_trans hx (hkeyC i hc)) (not_lt.mpr (hkeyN x hxc))
  refine ⟨σ, K, ?_, ?_, ?_, ?_, ?_⟩
  · exact Finset.card_pos.mpr ⟨i0, by simp [hi0]⟩
  · exact Finset.card_filter_le _ _
  · intro i j hi hj hij
    have hCi := (hσC i).mp hi
    have hCj := hclosed i j hCi hij
    have := (hσC j).mpr hCj
    omega
  · intro a b
    have hab : Relation.TransGen E a.1 b.1 := hreach b.1 ((hσC b.1).mp b.2) a.1
    have hgen : ∀ y, Relation.TransGen E a.1 y → ∀ hy : (σ y : ℕ) < K,
        Relation.TransGen (fun a b : {i : ι // (σ i : ℕ) < K} => E a.1 b.1) a ⟨y, hy⟩ := by
      intro y h
      induction h with
      | single h => intro hy; exact .single h
      | @tail b' y' hb' hby ih =>
        intro hy
        have hCb : C b' := hCpath _ _ hb' ((hσC a.1).mp a.2)
        exact (ih ((hσC b').mpr hCb)).tail hby
    exact hgen b.1 hab b.2
  · intro i j hi hj hle hij
    have hCi : ¬ C i := fun h => by have := (hσC i).mpr h; omega
    have hCj : ¬ C j := fun h => by have := (hσC j).mpr h; omega
    have h1 := hrk_mono j i (hkey_lt j i (hc_lt i j hCi hCj hij))
    rw [← hσ, ← hσ] at h1
    exact absurd hle (not_le.mpr h1)

end Comb

/-! ### Generic chain lemmas -/
section Chain
variable {V : Type*} [Countable V] [DecidableEq V]

lemma stepPow_nonneg (P : V → V → ℝ) (hnn : ∀ x y, 0 ≤ P x y) :
    ∀ t x y, 0 ≤ stepPow P t x y := by
  intro t
  induction t with
  | zero => intro x y; simp only [stepPow]; split_ifs <;> norm_num
  | succ t ih => intro x y; exact tsum_nonneg fun z => mul_nonneg (ih _ _) (hnn _ _)

lemma rtg_of_stepPow (P : V → V → ℝ) (hnn : ∀ x y, 0 ≤ P x y) :
    ∀ t x y, 0 < stepPow P t x y → Relation.ReflTransGen (fun a b => 0 < P a b) x y := by
  intro t
  induction t with
  | zero =>
    intro x y h
    simp only [stepPow] at h
    split_ifs at h with hyx
    · subst hyx; exact .refl
    · exact absurd h (lt_irrefl 0)
  | succ t ih =>
    intro x y h
    simp only [stepPow] at h
    obtain ⟨z, hz⟩ : ∃ z, 0 < stepPow P t x z * P z y := by
      by_contra hc
      push Not at hc
      exact absurd h (not_lt.mpr (tsum_nonpos hc))
    have h1 : stepPow P t x z ≠ 0 := fun h0 => by rw [h0, zero_mul] at hz; exact lt_irrefl 0 hz
    have h2 : P z y ≠ 0 := fun h0 => by rw [h0, mul_zero] at hz; exact lt_irrefl 0 hz
    exact (ih x z (lt_of_le_of_ne (stepPow_nonneg P hnn t x z) (Ne.symm h1))).tail
      (lt_of_le_of_ne (hnn z y) (Ne.symm h2))

lemma npath_of_rtg {R : V → V → Prop} {x y : V} (h : Relation.ReflTransGen R x y) :
    ∃ (k : ℕ) (f : ℕ → V), f 0 = x ∧ f k = y ∧ ∀ s < k, R (f s) (f (s + 1)) := by
  induction h with
  | refl => exact ⟨0, fun _ => x, rfl, rfl, fun s hs => absurd hs (Nat.not_lt_zero _)⟩
  | @tail b c _ hbc ih =>
    obtain ⟨k, f, h0, hk, hs⟩ := ih
    refine ⟨k + 1, fun s => if s ≤ k then f s else c, by simp [h0], by simp, fun s hs' => ?_⟩
    by_cases h1 : s + 1 ≤ k
    · simp only [h1, show s ≤ k by omega, if_true]
      exact hs s h1
    · have : s = k := by omega
      subst this
      simp only [le_refl, if_true, h1, if_false]
      rw [hk]; exact hbc

end Chain

/-! ### QBD specifics -/
section QBD
variable {ι : Type*} [Fintype ι] [DecidableEq ι] (B A₀ A₁ A₂ : ι → ι → ℝ)

lemma q_up (L : ℕ) (a b : ι) (hL : 1 ≤ L) : qbdP B A₀ A₁ A₂ (L, a) (L + 1, b) = A₀ a b := by
  simp [qbdP, show L ≠ 0 by omega]

lemma q_same (L : ℕ) (a b : ι) (hL : 1 ≤ L) : qbdP B A₀ A₁ A₂ (L, a) (L, b) = A₁ a b := by
  simp [qbdP, show L ≠ 0 by omega]

lemma q_down (L : ℕ) (a b : ι) : qbdP B A₀ A₁ A₂ (L + 1, a) (L, b) = A₂ a b := by
  simp only [qbdP]
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  simp

lemma q_0up (a b : ι) : qbdP B A₀ A₁ A₂ (0, a) (1, b) = A₀ a b := by
  simp [qbdP]

lemma q_shift (x y : ℕ × ι) (hx : 1 ≤ x.1) (hy : 1 ≤ y.1) (n : ℕ) :
    qbdP B A₀ A₁ A₂ (x.1 + n, x.2) (y.1 + n, y.2) = qbdP B A₀ A₁ A₂ x y := by
  obtain ⟨L, a⟩ := x
  obtain ⟨M, b⟩ := y
  simp only at hx hy ⊢
  simp only [qbdP, show L + n ≠ 0 by omega, show L ≠ 0 by omega, if_false]
  simp only [show (M + n = L + n + 1 ↔ M = L + 1) by omega, show (M + n = L + n ↔ M = L) by omega,
    show (M + n + 1 = L + n ↔ M + 1 = L) by omega]

lemma q_cases (L M : ℕ) (a b : ι) (hL : 1 ≤ L) (h : 0 < qbdP B A₀ A₁ A₂ (L, a) (M, b)) :
    (M = L + 1 ∧ 0 < A₀ a b) ∨ (M = L ∧ 0 < A₁ a b) ∨ (M + 1 = L ∧ 0 < A₂ a b) := by
  simp only [qbdP] at h
  rw [if_neg (by omega)] at h
  split_ifs at h with h1 h2 h3
  · exact Or.inl ⟨h1, h⟩
  · exact Or.inr (Or.inl ⟨h2, h⟩)
  · exact Or.inr (Or.inr ⟨h3, h⟩)
  · exact absurd h (lt_irrefl 0)

lemma q_cases0 (M : ℕ) (a b : ι) (h : 0 < qbdP B A₀ A₁ A₂ (0, a) (M, b)) :
    M = 0 ∨ (M = 1 ∧ 0 < A₀ a b) := by
  simp only [qbdP, if_true] at h
  split_ifs at h with h1 h2
  · exact Or.inl h1
  · exact Or.inr ⟨h2, h⟩
  · exact absurd h (lt_irrefl 0)

/-- a step inside the levels `≥ 1` -/
def R0 (x y : ℕ × ι) : Prop := 0 < qbdP B A₀ A₁ A₂ x y ∧ 1 ≤ x.1 ∧ 1 ≤ y.1

lemma rtg_lev {x y : ℕ × ι} (h : Relation.ReflTransGen (R0 B A₀ A₁ A₂) x y) (hx : 1 ≤ x.1) :
    1 ≤ y.1 := by
  induction h with
  | refl => exact hx
  | tail _ h _ => exact h.2.2

lemma rtg_shift (n : ℕ) {x y : ℕ × ι} (h : Relation.ReflTransGen (R0 B A₀ A₁ A₂) x y) :
    Relation.ReflTransGen (R0 B A₀ A₁ A₂) (x.1 + n, x.2) (y.1 + n, y.2) :=
  Relation.ReflTransGen.lift (fun z : ℕ × ι => (z.1 + n, z.2))
    (fun a b (hab : R0 B A₀ A₁ A₂ a b) => show R0 B A₀ A₁ A₂ (a.1 + n, a.2) (b.1 + n, b.2) from ⟨by rw [q_shift B A₀ A₁ A₂ a b hab.2.1 hab.2.2]; exact hab.1,
      by simp only; have := hab.2.1; omega, by simp only; have := hab.2.2; omega⟩) _ _ h

lemma nonneg_A (hP : IsStochasticC (qbdP B A₀ A₁ A₂)) :
    (∀ a b, 0 ≤ A₀ a b) ∧ (∀ a b, 0 ≤ A₁ a b) ∧ (∀ a b, 0 ≤ A₂ a b) := by
  refine ⟨fun a b => ?_, fun a b => ?_, fun a b => ?_⟩
  · have := hP.1 (1, a) (1 + 1, b); rwa [q_up B A₀ A₁ A₂ 1 a b le_rfl] at this
  · have := hP.1 (1, a) (1, b); rwa [q_same B A₀ A₁ A₂ 1 a b le_rfl] at this
  · have := hP.1 (0 + 1, a) (0, b); rwa [q_down] at this

lemma lift_A (hP : IsStochasticC (qbdP B A₀ A₁ A₂)) {a b : ι}
    (h : Relation.ReflTransGen (fun a b => 0 < matA A₀ A₁ A₂ a b) a b) :
    ∃ u v : ℕ, ∀ L, 1 ≤ L →
      Relation.ReflTransGen (R0 B A₀ A₁ A₂) (L + u, a) (L + v, b) := by
  obtain ⟨n0, n1, n2⟩ := nonneg_A B A₀ A₁ A₂ hP
  induction h with
  | refl => exact ⟨0, 0, fun L _ => .refl⟩
  | @tail z b' _ hzb ih =>
    obtain ⟨u, v, huv⟩ := ih
    simp only [matA] at hzb
    by_cases h0 : 0 < A₀ z b'
    · refine ⟨u, v + 1, fun L hL => (huv L hL).tail ⟨?_, by simp only; omega, by simp only; omega⟩⟩
      rw [show L + (v + 1) = (L + v) + 1 by omega, q_up B A₀ A₁ A₂ _ _ _ (by omega)]; exact h0
    by_cases h1 : 0 < A₁ z b'
    · refine ⟨u, v, fun L hL => (huv L hL).tail ⟨?_, by simp only; omega, by simp only; omega⟩⟩
      rw [q_same B A₀ A₁ A₂ _ _ _ (by omega)]; exact h1
    have h2 : 0 < A₂ z b' := by
      have := n0 z b'; have := n1 z b'; push Not at h0 h1; linarith
    refine ⟨u + 1, v, fun L hL => ?_⟩
    have := huv (L + 1) (by omega)
    rw [show L + 1 + u = L + (u + 1) by omega, show L + 1 + v = (L + v) + 1 by omega] at this
    refine this.tail ⟨?_, by simp only; omega, by simp only; omega⟩
    rw [q_down]; exact h2

end QBD

/-! ### `R`-specific paths -/
section RPart
variable {ι : Type*} [Fintype ι] [DecidableEq ι] (B A₀ A₁ A₂ : ι → ι → ℝ)

def Up0 (a : ι) (x : ℕ × ι) : Prop :=
  ∃ y, 0 < qbdP B A₀ A₁ A₂ (0, a) y ∧ 1 ≤ y.1 ∧ Relation.ReflTransGen (R0 B A₀ A₁ A₂) y x

def Rr (a b : ι) : Prop := Up0 B A₀ A₁ A₂ a (1, b)

def RrPow : ℕ → ι → ι → Prop
  | 0, a, b => a = b
  | L + 1, a, b => ∃ c, RrPow L a c ∧ Rr B A₀ A₁ A₂ c b

lemma up_append {a : ι} {x x' : ℕ × ι} (h : Up0 B A₀ A₁ A₂ a x)
    (h' : Relation.ReflTransGen (R0 B A₀ A₁ A₂) x x') : Up0 B A₀ A₁ A₂ a x' :=
  let ⟨y, hp, hy, hr⟩ := h
  ⟨y, hp, hy, hr.trans h'⟩

lemma first_lev1 {a : ι} {y : ℕ × ι} (hy : 1 ≤ y.1) (h : 0 < qbdP B A₀ A₁ A₂ (0, a) y) :
    y = (1, y.2) ∧ 0 < A₀ a y.2 := by
  obtain ⟨M, b⟩ := y
  simp only at hy ⊢
  rcases q_cases0 B A₀ A₁ A₂ M a b h with h | h
  · omega
  · exact ⟨by rw [h.1], h.2⟩

lemma up_comp {m : ℕ} (hm : 1 ≤ m) {a c b : ι} (hu : Up0 B A₀ A₁ A₂ a (m, c))
    (hr : Rr B A₀ A₁ A₂ c b) : Up0 B A₀ A₁ A₂ a (m + 1, b) := by
  obtain ⟨y, hp, hyl, hrt⟩ := hr
  obtain ⟨hy1, hA0⟩ := first_lev1 B A₀ A₁ A₂ hyl hp
  have hs : Relation.ReflTransGen (R0 B A₀ A₁ A₂) (m + 1, y.2) (m + 1, b) := by
    have := rtg_shift B A₀ A₁ A₂ m hrt
    rw [hy1] at this
    simpa [add_comm] using this
  refine up_append B A₀ A₁ A₂ hu (Relation.ReflTransGen.head ⟨?_, hm, by simp⟩ hs)
  rw [q_up B A₀ A₁ A₂ m c y.2 hm]; exact hA0

lemma compR : ∀ L a b, RrPow B A₀ A₁ A₂ (L + 1) a b → Up0 B A₀ A₁ A₂ a (L + 1, b) := by
  intro L
  induction L with
  | zero =>
    rintro a b ⟨c, hac, hr⟩
    have hac' : a = c := hac
    subst hac'
    exact hr
  | succ L ih =>
    rintro a b ⟨c, hp, hr⟩
    exact up_comp B A₀ A₁ A₂ (m := L + 1) (by omega) (ih a c hp) hr

lemma decR {a : ι} {y x : ℕ × ι} (hp : 0 < qbdP B A₀ A₁ A₂ (0, a) y) (hyl : 1 ≤ y.1)
    (h : Relation.ReflTransGen (R0 B A₀ A₁ A₂) y x) : RrPow B A₀ A₁ A₂ x.1 a x.2 := by
  induction h with
  | refl =>
    obtain ⟨hy1, _⟩ := first_lev1 B A₀ A₁ A₂ hyl hp
    have e : y.1 = 1 := by rw [hy1]
    rw [e]
    exact ⟨a, rfl, y, hp, hyl, by rw [← hy1]⟩
  | @tail x x' hyx hxx' ih =>
    obtain ⟨L, d⟩ := x
    obtain ⟨M, d'⟩ := x'
    show RrPow B A₀ A₁ A₂ M a d'
    simp only at ih
    have hL : 1 ≤ L := hxx'.2.1
    have hM : 1 ≤ M := hxx'.2.2
    rcases q_cases B A₀ A₁ A₂ L M d d' hL hxx'.1 with ⟨h1, hA⟩ | ⟨h1, hA⟩ | ⟨h1, hA⟩
    · subst h1
      exact ⟨d, ih, (1, d'), by rw [q_0up]; exact hA, le_rfl, .refl⟩
    · rw [← h1] at ih
      obtain ⟨M', rfl⟩ : ∃ M', M = M' + 1 := ⟨M - 1, by omega⟩
      obtain ⟨c, hpow, hr⟩ := ih
      have hq : 0 < qbdP B A₀ A₁ A₂ (1, d) (1, d') := by
        rw [q_same B A₀ A₁ A₂ 1 d d' le_rfl]; exact hA
      exact ⟨c, hpow, up_append B A₀ A₁ A₂ hr (.single ⟨hq, le_rfl, le_rfl⟩)⟩
    · subst h1
      obtain ⟨M', rfl⟩ : ∃ M', M = M' + 1 := ⟨M - 1, by omega⟩
      obtain ⟨c', hpow', hr'⟩ := ih
      obtain ⟨c, hpow, hr⟩ := hpow'
      refine ⟨c, hpow, ?_⟩
      have h2 : Up0 B A₀ A₁ A₂ c (1 + 1, d) := up_comp B A₀ A₁ A₂ le_rfl hr hr'
      exact up_append B A₀ A₁ A₂ h2 (.single ⟨by rw [q_down]; exact hA, by simp, le_rfl⟩)

lemma up_of_rtg {x z : ℕ × ι}
    (h : Relation.ReflTransGen (fun a b => 0 < qbdP B A₀ A₁ A₂ a b) x z) (hx : x.1 = 0) :
    1 ≤ z.1 → ∃ a, Up0 B A₀ A₁ A₂ a z := by
  induction h with
  | refl => intro hz; omega
  | @tail w z _ hwz ih =>
    intro hz
    by_cases h0 : w.1 = 0
    · refine ⟨w.2, z, ?_, hz, .refl⟩
      have : w = (0, w.2) := Prod.ext h0 rfl
      rw [← this]; exact hwz
    · obtain ⟨a, ha⟩ := ih (by omega)
      exact ⟨a, up_append B A₀ A₁ A₂ ha (.single ⟨hwz, by omega, hz⟩)⟩

lemma tg_of_rrpow : ∀ n a b, RrPow B A₀ A₁ A₂ (n + 1) a b →
    Relation.TransGen (Rr B A₀ A₁ A₂) a b := by
  intro n
  induction n with
  | zero =>
    rintro a b ⟨c, hac, h⟩
    have hac' : a = c := hac
    subst hac'; exact .single h
  | succ n ih =>
    rintro a b ⟨c, hp, h⟩
    exact (ih a c hp).tail h

lemma rrpow_of_tg {a b : ι} (h : Relation.TransGen (Rr B A₀ A₁ A₂) a b) :
    ∃ n, RrPow B A₀ A₁ A₂ (n + 1) a b := by
  induction h with
  | single h => exact ⟨0, _, rfl, h⟩
  | tail _ h ih =>
    obtain ⟨n, hn⟩ := ih
    exact ⟨n + 1, _, hn, h⟩

lemma rrpow_add (m : ℕ) {a b : ι} (hab : RrPow B A₀ A₁ A₂ m a b) : ∀ l c,
    RrPow B A₀ A₁ A₂ l b c → RrPow B A₀ A₁ A₂ (m + l) a c := by
  intro l
  induction l with
  | zero =>
    intro c hbc
    have hbc' : b = c := hbc
    subst hbc'; exact hab
  | succ l ih =>
    rintro c ⟨d, hp, hr⟩
    exact ⟨d, ih d hp, hr⟩

lemma reachR (hP : IsStochasticC (qbdP B A₀ A₁ A₂)) (hA : IrreducibleC (matA A₀ A₁ A₂))
    (i : ι) (hi : Relation.TransGen (Rr B A₀ A₁ A₂) i i) (j : ι) :
    Relation.TransGen (Rr B A₀ A₁ A₂) i j := by
  obtain ⟨n, hn⟩ := rrpow_of_tg B A₀ A₁ A₂ hi
  have hpow : ∀ q, RrPow B A₀ A₁ A₂ ((n + 1) * (q + 1)) i i := by
    intro q
    induction q with
    | zero => simpa using hn
    | succ q ih =>
      have := rrpow_add B A₀ A₁ A₂ _ ih _ _ hn
      rw [show (n + 1) * (q + 1 + 1) = (n + 1) * (q + 1) + (n + 1) by ring]
      exact this
  obtain ⟨n0, n1, n2⟩ := nonneg_A B A₀ A₁ A₂ hP
  obtain ⟨t, ht⟩ := hA i j
  have hrt := rtg_of_stepPow (matA A₀ A₁ A₂)
    (fun a b => by simp only [matA]; linarith [n0 a b, n1 a b, n2 a b]) t i j ht
  obtain ⟨u, v, huv⟩ := lift_A B A₀ A₁ A₂ hP hrt
  set N := (n + 1) * (u + 1) with hN
  have huN : u + 1 ≤ N := Nat.le_mul_of_pos_left (u + 1) (by omega)
  have hd : Up0 B A₀ A₁ A₂ i (N, i) := by
    have := compR B A₀ A₁ A₂ (N - 1) i i (by rw [Nat.sub_add_cancel (by omega)]; exact hpow u)
    rwa [Nat.sub_add_cancel (by omega)] at this
  have hpath := huv (N - u) (by omega)
  rw [show N - u + u = N by omega] at hpath
  obtain ⟨y, hp, hyl, hrt'⟩ := up_append B A₀ A₁ A₂ hd hpath
  have hg := decR B A₀ A₁ A₂ hp hyl hrt'
  simp only at hg
  exact tg_of_rrpow B A₀ A₁ A₂ (N - u + v - 1) i j
    (by rw [show N - u + v - 1 + 1 = N - u + v by omega]; exact hg)

lemma R_ne_of_up (a b : ι) (h : Up0 B A₀ A₁ A₂ a (1, b)) :
    matR (qbdP B A₀ A₁ A₂) a b ≠ 0 := by
  classical
  obtain ⟨y, hp, hyl, hrt⟩ := h
  obtain ⟨k, f, h0, hk, hs⟩ := npath_of_rtg hrt
  have hlev : ∀ s ≤ k, 1 ≤ (f s).1 := by
    intro s hs'
    cases s with
    | zero => rw [h0]; exact hyl
    | succ s => exact (hs s (by omega)).2.2
  set g : ℕ → ℕ × ι := fun s => if s = 0 then (0, a) else f (s - 1) with hg
  set ω : Fin (k + 2) → ℕ × ι := fun s => g s.val with hω
  have hW : pathWeightE (qbdP B A₀ A₁ A₂) ω ≠ 0 := by
    unfold pathWeightE
    rw [Finset.prod_ne_zero_iff]
    intro s _
    apply ne_of_gt
    apply ENNReal.ofReal_pos.mpr
    simp only [hω, Fin.coe_castSucc, Fin.val_succ, hg]
    rw [if_neg (show (s : ℕ) + 1 ≠ 0 by omega)]
    by_cases h2 : (s : ℕ) = 0
    · rw [if_pos h2, h2, Nat.zero_add, Nat.sub_self, h0]; exact hp
    · rw [if_neg h2, show (s : ℕ) + 1 - 1 = (s - 1) + 1 by omega]
      exact (hs _ (by omega)).1
  have hcond : ω 0 = (0, a) ∧ ω (Fin.last (k + 1)) = (1, b) ∧
      ∀ s : Fin (k + 2), s ≠ 0 → ω s ∉ level 0 := by
    refine ⟨by simp [hω, hg], by simp [hω, hg, hk], fun s hs' => ?_⟩
    have hs0 : (s : ℕ) ≠ 0 := fun h => hs' (Fin.ext h)
    simp only [hω, hg, if_neg hs0, level, Set.mem_setOf_eq]
    have := hlev (s - 1) (by omega); omega
  intro h0'
  unfold matR expVisitsAvoid at h0'
  have := ENNReal.tsum_eq_zero.mp (ENNReal.tsum_eq_zero.mp h0' (k + 1)) ω
  rw [if_pos hcond] at this
  exact hW this

lemma up_of_R_ne (a b : ι) (h : matR (qbdP B A₀ A₁ A₂) a b ≠ 0) :
    Up0 B A₀ A₁ A₂ a (1, b) := by
  classical
  unfold matR expVisitsAvoid at h
  obtain ⟨t, ht⟩ : ∃ t, (∑' ω : Fin (t + 1) → ℕ × ι,
      if ω 0 = (0, a) ∧ ω (Fin.last t) = (1, b) ∧ ∀ s : Fin (t + 1), s ≠ 0 → ω s ∉ level 0
      then pathWeightE (qbdP B A₀ A₁ A₂) ω else 0) ≠ 0 := by
    by_contra hc; push Not at hc; exact h (ENNReal.tsum_eq_zero.mpr hc)
  obtain ⟨ω, hω⟩ : ∃ ω : Fin (t + 1) → ℕ × ι, (if ω 0 = (0, a) ∧ ω (Fin.last t) = (1, b) ∧
        ∀ s : Fin (t + 1), s ≠ 0 → ω s ∉ level 0
      then pathWeightE (qbdP B A₀ A₁ A₂) ω else 0) ≠ 0 := by
    by_contra hc; push Not at hc; exact ht (ENNReal.tsum_eq_zero.mpr hc)
  by_cases hc : ω 0 = (0, a) ∧ ω (Fin.last t) = (1, b) ∧
      ∀ s : Fin (t + 1), s ≠ 0 → ω s ∉ level 0
  swap
  · rw [if_neg hc] at hω; exact absurd rfl hω
  rw [if_pos hc] at hω
  obtain ⟨h0, hl, hav⟩ := hc
  cases t with
  | zero =>
    exfalso
    have : ω 0 = ω (Fin.last 0) := rfl
    rw [h0, hl] at this
    simp at this
  | succ t =>
    have hpos : ∀ s : Fin (t + 1), 0 < qbdP B A₀ A₁ A₂ (ω s.castSucc) (ω s.succ) := by
      intro s
      unfold pathWeightE at hω
      rw [Finset.prod_ne_zero_iff] at hω
      exact ENNReal.ofReal_pos.mp (pos_iff_ne_zero.mpr (hω s (Finset.mem_univ _)))
    have hlev : ∀ s : Fin (t + 2), s ≠ 0 → 1 ≤ (ω s).1 := fun s hs => by
      have := hav s hs
      simp only [level, Set.mem_setOf_eq] at this
      omega
    have hR : ∀ s (hs : s ≤ t), Relation.ReflTransGen (R0 B A₀ A₁ A₂) (ω ⟨1, by omega⟩)
        (ω ⟨s + 1, by omega⟩) := by
      intro s
      induction s with
      | zero => intro _; exact .refl
      | succ s ih =>
        intro hs
        refine (ih (by omega)).tail ⟨hpos ⟨s + 1, by omega⟩, hlev _ ?_, hlev _ ?_⟩
        · intro he; have := congrArg Fin.val he; simp at this
        · intro he; have := congrArg Fin.val he; simp at this
    refine ⟨ω ⟨1, by omega⟩, ?_, hlev _ (by intro he; have := congrArg Fin.val he; simp at this),
      ?_⟩
    · rw [← h0]; exact hpos ⟨0, by omega⟩
    · rw [← hl]; exact hR t le_rfl

end RPart
end GSX

open MatrixAnalytic.Stability in
theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B A₀ A₁ A₂ : ι → ι → ℝ)
    (hP : IsStochasticC (qbdP B A₀ A₁ A₂))
    (hirr : IrreducibleC (qbdP B A₀ A₁ A₂))
    (hA : IrreducibleC (matA A₀ A₁ A₂)) :
    IrreducibleE (matR (qbdP B A₀ A₁ A₂)) ∨
      ∃ (σ : ι ≃ Fin (Fintype.card ι)) (k : ℕ), 0 < k ∧ k ≤ Fintype.card ι ∧
        (∀ i j : ι, k ≤ (σ i : ℕ) → (σ j : ℕ) < k → matR (qbdP B A₀ A₁ A₂) i j = 0) ∧
        IrreducibleE (fun a b : {i : ι // (σ i : ℕ) < k} => matR (qbdP B A₀ A₁ A₂) a.1 b.1) ∧
        (∀ i j : ι, k ≤ (σ i : ℕ) → k ≤ (σ j : ℕ) → σ j ≤ σ i →
          matR (qbdP B A₀ A₁ A₂) i j = 0) := by
  classical
  rcases isEmpty_or_nonempty ι with hι | hι
  · left; intro i; exact isEmptyElim i
  right
  set E : ι → ι → Prop := fun a b => matR (qbdP B A₀ A₁ A₂) a b ≠ 0 with hE
  have hER : ∀ a b, E a b ↔ GSX.Rr B A₀ A₁ A₂ a b := fun a b =>
    ⟨GSX.up_of_R_ne B A₀ A₁ A₂ a b, GSX.R_ne_of_up B A₀ A₁ A₂ a b⟩
  set E' : ι → ι → Prop := fun a b => E b a with hE'
  have hrow : ∀ i, ∃ j, E' i j := by
    intro i
    obtain ⟨t, ht⟩ := hirr (0, i) (1, i)
    have := GSX.rtg_of_stepPow (qbdP B A₀ A₁ A₂) hP.1 t _ _ ht
    obtain ⟨c, hc⟩ := GSX.up_of_rtg B A₀ A₁ A₂ this rfl le_rfl
    exact ⟨c, (hER c i).mpr hc⟩
  have hreach : ∀ i, Relation.TransGen E' i i → ∀ j, Relation.TransGen E' j i := by
    intro i hi j
    have hi1 : Relation.TransGen E i i := Relation.transGen_swap.mp hi
    have hi' : Relation.TransGen (GSX.Rr B A₀ A₁ A₂) i i :=
      Relation.TransGen.mono (fun a b h => (hER a b).mp h) _ _ hi1
    have h2 : Relation.TransGen E i j := Relation.TransGen.mono (fun a b h => (hER a b).mpr h) _ _
      (GSX.reachR B A₀ A₁ A₂ hP hA i hi' j)
    exact Relation.transGen_swap.mpr h2
  obtain ⟨σ, k, hk0, hkn, h1, h2, h3⟩ := GSX.comb E' hrow hreach
  refine ⟨σ, k, hk0, hkn, fun i j hi hj => not_not.mp (h1 j i hj hi), ?_,
    fun i j hi hj hle => not_not.mp (h3 j i hj hi hle)⟩
  exact GSX.irr_of_transGen _ (fun a b => Relation.transGen_swap.mp (h2 b a))
