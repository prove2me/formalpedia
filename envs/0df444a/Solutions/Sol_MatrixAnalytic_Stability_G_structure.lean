-- Prove2me | solution 1 for MatrixAnalytic.Stability.G_structure
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T09:49:03.67956+00:00
-- url     : https://prove2.me/submissions/88bfa3fe-b043-4940-870d-b3fe8ed09f31

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

/-! ### `G`-specific paths -/
section GPart
variable {ι : Type*} [Fintype ι] [DecidableEq ι] (B A₀ A₁ A₂ : ι → ι → ℝ)

def Down0 (x : ℕ × ι) (c : ι) : Prop :=
  ∃ y, Relation.ReflTransGen (R0 B A₀ A₁ A₂) x y ∧ 0 < qbdP B A₀ A₁ A₂ y (0, c)

def Gr (a c : ι) : Prop := Down0 B A₀ A₁ A₂ (1, a) c

def GrPow : ℕ → ι → ι → Prop
  | 0, a, b => a = b
  | L + 1, a, b => ∃ c, Gr B A₀ A₁ A₂ a c ∧ GrPow L c b

lemma y_lev1 {y : ℕ × ι} {c : ι} (hy : 1 ≤ y.1) (h : 0 < qbdP B A₀ A₁ A₂ y (0, c)) :
    y = (1, y.2) ∧ 0 < A₂ y.2 c := by
  obtain ⟨L, a⟩ := y
  simp only at hy ⊢
  rcases q_cases B A₀ A₁ A₂ L 0 a c hy h with h | h | h
  · omega
  · omega
  · exact ⟨by rw [← h.1], h.2⟩

lemma down_prepend {x x' : ℕ × ι} {c : ι} (h : R0 B A₀ A₁ A₂ x x')
    (hd : Down0 B A₀ A₁ A₂ x' c) : Down0 B A₀ A₁ A₂ x c :=
  let ⟨y, hy, hp⟩ := hd
  ⟨y, .head h hy, hp⟩

lemma down_trans {x x' : ℕ × ι} {c : ι} (h : Relation.ReflTransGen (R0 B A₀ A₁ A₂) x x')
    (hd : Down0 B A₀ A₁ A₂ x' c) : Down0 B A₀ A₁ A₂ x c :=
  let ⟨y, hy, hp⟩ := hd
  ⟨y, h.trans hy, hp⟩

lemma down_comp {m : ℕ} (hm : 1 ≤ m) {a c b : ι} (hg : Gr B A₀ A₁ A₂ a c)
    (hd : Down0 B A₀ A₁ A₂ (m, c) b) : Down0 B A₀ A₁ A₂ (m + 1, a) b := by
  obtain ⟨y, hy, hp⟩ := hg
  have hyl := rtg_lev B A₀ A₁ A₂ hy (by simp)
  obtain ⟨hy1, hA2⟩ := y_lev1 B A₀ A₁ A₂ hyl hp
  have hs : Relation.ReflTransGen (R0 B A₀ A₁ A₂) (m + 1, a) (m + 1, y.2) := by
    have := rtg_shift B A₀ A₁ A₂ m hy
    rw [hy1] at this
    simpa [add_comm] using this
  obtain ⟨y', hy', hp'⟩ := hd
  refine ⟨y', ?_, hp'⟩
  refine (hs.tail ⟨?_, by simp, by simp only; omega⟩).trans hy'
  rw [q_down]; exact hA2

lemma comp : ∀ L a b, GrPow B A₀ A₁ A₂ (L + 1) a b → Down0 B A₀ A₁ A₂ (L + 1, a) b := by
  intro L
  induction L with
  | zero =>
    rintro a b ⟨c, hg, hcb⟩
    have hcb' : c = b := hcb
    subst hcb'
    exact hg
  | succ L ih =>
    rintro a b ⟨c, hg, hrest⟩
    exact down_comp B A₀ A₁ A₂ (m := L + 1) (by omega) hg (ih c b hrest)

lemma dec {x y : ℕ × ι} {b : ι} (hpy : 0 < qbdP B A₀ A₁ A₂ y (0, b))
    (h : Relation.ReflTransGen (R0 B A₀ A₁ A₂) x y) : 1 ≤ x.1 → GrPow B A₀ A₁ A₂ x.1 x.2 b := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl =>
    intro hx
    obtain ⟨hy1, _⟩ := y_lev1 B A₀ A₁ A₂ hx hpy
    have e : y.1 = 1 := by rw [hy1]
    rw [e]
    exact ⟨b, ⟨(1, y.2), .refl, by rw [← hy1]; exact hpy⟩, rfl⟩
  | @head x x' hxx' _ ih =>
    intro hx
    obtain ⟨L, a⟩ := x
    obtain ⟨M, a'⟩ := x'
    show GrPow B A₀ A₁ A₂ L a b
    simp only at hx ih
    have hM : 1 ≤ M := hxx'.2.2
    have ih' := ih hM
    rcases q_cases B A₀ A₁ A₂ L M a a' hx hxx'.1 with ⟨h1, hA⟩ | ⟨h1, hA⟩ | ⟨h1, hA⟩
    · subst h1
      obtain ⟨c, hgc, hrest⟩ := ih'
      obtain ⟨L', rfl⟩ : ∃ L', L = L' + 1 := ⟨L - 1, by omega⟩
      obtain ⟨c', hcc', hrest'⟩ := hrest
      refine ⟨c', ?_, hrest'⟩
      have h2 : Down0 B A₀ A₁ A₂ (1 + 1, a') c' := down_comp B A₀ A₁ A₂ le_rfl hgc hcc'
      exact down_prepend B A₀ A₁ A₂ ⟨by rw [q_up B A₀ A₁ A₂ 1 a a' le_rfl]; exact hA, le_rfl,
        by simp⟩ h2
    · rw [h1] at ih'
      obtain ⟨L', rfl⟩ : ∃ L', L = L' + 1 := ⟨L - 1, by omega⟩
      obtain ⟨c, hgc, hrest⟩ := ih'
      exact ⟨c, down_prepend B A₀ A₁ A₂ ⟨by rw [q_same B A₀ A₁ A₂ 1 a a' le_rfl]; exact hA,
        le_rfl, le_rfl⟩ hgc, hrest⟩
    · subst h1
      exact ⟨a', ⟨(1, a), .refl, by rw [show ((1 : ℕ), a) = (0 + 1, a) from rfl, q_down]; exact hA⟩,
        ih'⟩

lemma down_of_rtg {x z : ℕ × ι}
    (h : Relation.ReflTransGen (fun a b => 0 < qbdP B A₀ A₁ A₂ a b) x z) (hz : z.1 = 0) :
    1 ≤ x.1 → ∃ c, Down0 B A₀ A₁ A₂ x c := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => intro hx; omega
  | @head x x' hxx' _ ih =>
    intro hx
    by_cases h0 : x'.1 = 0
    · refine ⟨x'.2, x, .refl, ?_⟩
      have : x' = (0, x'.2) := Prod.ext h0 rfl
      rw [← this]; exact hxx'
    · obtain ⟨c, hc⟩ := ih (by omega)
      exact ⟨c, down_prepend B A₀ A₁ A₂ ⟨hxx', hx, by omega⟩ hc⟩

lemma tg_of_grpow : ∀ n a b, GrPow B A₀ A₁ A₂ (n + 1) a b →
    Relation.TransGen (Gr B A₀ A₁ A₂) a b := by
  intro n
  induction n with
  | zero =>
    rintro a b ⟨c, h, hcb⟩
    have hcb' : c = b := hcb
    subst hcb'; exact .single h
  | succ n ih =>
    rintro a b ⟨c, h, hr⟩
    exact .head h (ih c b hr)

lemma grpow_of_tg {a b : ι} (h : Relation.TransGen (Gr B A₀ A₁ A₂) a b) :
    ∃ n, GrPow B A₀ A₁ A₂ (n + 1) a b := by
  induction h using Relation.TransGen.head_induction_on with
  | single h => exact ⟨0, _, h, rfl⟩
  | head h _ ih =>
    obtain ⟨n, hn⟩ := ih
    exact ⟨n + 1, _, h, hn⟩

lemma grpow_add (l : ℕ) : ∀ m a b c, GrPow B A₀ A₁ A₂ m a b → GrPow B A₀ A₁ A₂ l b c →
    GrPow B A₀ A₁ A₂ (m + l) a c := by
  intro m
  induction m with
  | zero =>
    intro a b c hab hbc
    have hab' : a = b := hab
    subst hab'; rw [zero_add]; exact hbc
  | succ m ih =>
    rintro a b c ⟨d, h, hr⟩ hbc
    rw [show m + 1 + l = (m + l) + 1 by omega]
    exact ⟨d, h, ih d b c hr hbc⟩

lemma reachG (hP : IsStochasticC (qbdP B A₀ A₁ A₂)) (hA : IrreducibleC (matA A₀ A₁ A₂))
    (i : ι) (hi : Relation.TransGen (Gr B A₀ A₁ A₂) i i) (j : ι) :
    Relation.TransGen (Gr B A₀ A₁ A₂) j i := by
  obtain ⟨n, hn⟩ := grpow_of_tg B A₀ A₁ A₂ hi
  have hpow : ∀ q, GrPow B A₀ A₁ A₂ ((n + 1) * (q + 1)) i i := by
    intro q
    induction q with
    | zero => simpa using hn
    | succ q ih =>
      have := grpow_add B A₀ A₁ A₂ _ _ _ _ _ hn ih
      rw [show (n + 1) * (q + 1 + 1) = n + 1 + (n + 1) * (q + 1) by ring]
      exact this
  obtain ⟨n0, n1, n2⟩ := nonneg_A B A₀ A₁ A₂ hP
  obtain ⟨t, ht⟩ := hA j i
  have hrt := rtg_of_stepPow (matA A₀ A₁ A₂)
    (fun a b => by simp only [matA]; linarith [n0 a b, n1 a b, n2 a b]) t j i ht
  obtain ⟨u, v, huv⟩ := lift_A B A₀ A₁ A₂ hP hrt
  set N := (n + 1) * (v + 1) with hN
  have hvN : v + 1 ≤ N := Nat.le_mul_of_pos_left (v + 1) (by omega)
  have hd : Down0 B A₀ A₁ A₂ (N, i) i := by
    have := comp B A₀ A₁ A₂ (N - 1) i i (by rw [Nat.sub_add_cancel (by omega)]; exact hpow v)
    rwa [Nat.sub_add_cancel (by omega)] at this
  have hpath := huv (N - v) (by omega)
  rw [show N - v + v = N by omega] at hpath
  obtain ⟨y, hy, hpy⟩ := down_trans B A₀ A₁ A₂ hpath hd
  have hg := dec B A₀ A₁ A₂ hpy hy (by simp only; omega)
  simp only at hg
  exact tg_of_grpow B A₀ A₁ A₂ (N - v + u - 1) j i
    (by rw [show N - v + u - 1 + 1 = N - v + u by omega]; exact hg)

lemma G_ne_of_down (a c : ι) (h : Down0 B A₀ A₁ A₂ (1, a) c) :
    matG (qbdP B A₀ A₁ A₂) 0 a c ≠ 0 := by
  classical
  obtain ⟨y, hy, hpy⟩ := h
  obtain ⟨k, f, h0, hk, hs⟩ := npath_of_rtg hy
  have hlev : ∀ s ≤ k, 1 ≤ (f s).1 := by
    intro s hs'
    cases s with
    | zero => rw [h0]
    | succ s => exact (hs s (by omega)).2.2
  set g : ℕ → ℕ × ι := fun s => if s ≤ k then f s else (0, c) with hg
  set ω : Fin (k + 2) → ℕ × ι := fun s => g s.val with hω
  have hW : pathWeightE (qbdP B A₀ A₁ A₂) ω ≠ 0 := by
    unfold pathWeightE
    rw [Finset.prod_ne_zero_iff]
    intro s _
    apply ne_of_gt
    apply ENNReal.ofReal_pos.mpr
    simp only [hω, Fin.coe_castSucc, Fin.val_succ, hg]
    have hs1 : (s : ℕ) ≤ k := by omega
    rw [if_pos hs1]
    by_cases h2 : (s : ℕ) + 1 ≤ k
    · rw [if_pos h2]; exact (hs s (by omega)).1
    · rw [if_neg h2]
      have : (s : ℕ) = k := by omega
      rw [this, hk]; exact hpy
  have hcond : ω 0 = (0 + 1, a) ∧ ω (Fin.last (k + 1)) = (0, c) ∧
      ∀ s : Fin (k + 2), s ≠ Fin.last (k + 1) → ω s ∉ level 0 := by
    refine ⟨by simp [hω, hg, h0], by simp [hω, hg], fun s hs' => ?_⟩
    have hsk : (s : ℕ) ≤ k := by have := Fin.val_lt_last hs'; omega
    simp only [hω, hg, if_pos hsk, level, Set.mem_setOf_eq]
    have := hlev s hsk; omega
  intro h0'
  have h1 : passageProb (qbdP B A₀ A₁ A₂) 0 (k + 1) a c ≠ 0 := by
    intro hz
    unfold passageProb at hz
    have := ENNReal.tsum_eq_zero.mp hz ω
    rw [if_pos hcond] at this
    exact hW this
  exact h1 (ENNReal.tsum_eq_zero.mp h0' (k + 1))

lemma down_of_G_ne (a c : ι) (h : matG (qbdP B A₀ A₁ A₂) 0 a c ≠ 0) :
    Down0 B A₀ A₁ A₂ (1, a) c := by
  classical
  unfold matG at h
  obtain ⟨k, hk⟩ : ∃ k, passageProb (qbdP B A₀ A₁ A₂) 0 k a c ≠ 0 := by
    by_contra hc; push Not at hc; exact h (ENNReal.tsum_eq_zero.mpr hc)
  unfold passageProb at hk
  obtain ⟨ω, hω⟩ : ∃ ω : Fin (k + 1) → ℕ × ι, (if ω 0 = (0 + 1, a) ∧ ω (Fin.last k) = (0, c) ∧
        ∀ s : Fin (k + 1), s ≠ Fin.last k → ω s ∉ level 0
      then pathWeightE (qbdP B A₀ A₁ A₂) ω else 0) ≠ 0 := by
    by_contra hc; push Not at hc; exact hk (ENNReal.tsum_eq_zero.mpr hc)
  by_cases hc : ω 0 = (0 + 1, a) ∧ ω (Fin.last k) = (0, c) ∧
      ∀ s : Fin (k + 1), s ≠ Fin.last k → ω s ∉ level 0
  swap
  · rw [if_neg hc] at hω; exact absurd rfl hω
  rw [if_pos hc] at hω
  obtain ⟨h0, hl, hav⟩ := hc
  cases k with
  | zero =>
    exfalso
    have : ω 0 = ω (Fin.last 0) := rfl
    rw [h0, hl] at this
    simp at this
  | succ k =>
    have hpos : ∀ s : Fin (k + 1), 0 < qbdP B A₀ A₁ A₂ (ω s.castSucc) (ω s.succ) := by
      intro s
      unfold pathWeightE at hω
      rw [Finset.prod_ne_zero_iff] at hω
      exact ENNReal.ofReal_pos.mp (pos_iff_ne_zero.mpr (hω s (Finset.mem_univ _)))
    have hlev : ∀ s : Fin (k + 2), s ≠ Fin.last (k + 1) → 1 ≤ (ω s).1 := fun s hs => by
      have := hav s hs
      simp only [level, Set.mem_setOf_eq] at this
      omega
    have hR : ∀ s (hs : s ≤ k), Relation.ReflTransGen (R0 B A₀ A₁ A₂) (1, a) (ω ⟨s, by omega⟩) := by
      intro s
      induction s with
      | zero =>
        intro _
        have : (⟨0, by omega⟩ : Fin (k + 2)) = 0 := rfl
        rw [this, h0]
      | succ s ih =>
        intro hs
        refine (ih (by omega)).tail ⟨hpos ⟨s, by omega⟩, hlev _ ?_, hlev _ ?_⟩
        · intro he; have := congrArg Fin.val he; simp at this; omega
        · intro he; have := congrArg Fin.val he; simp at this; omega
    refine ⟨ω ⟨k, by omega⟩, hR k le_rfl, ?_⟩
    rw [← hl]
    exact hpos ⟨k, by omega⟩

end GPart
end GSX

open MatrixAnalytic.Stability in
theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B A₀ A₁ A₂ : ι → ι → ℝ)
    (hP : IsStochasticC (qbdP B A₀ A₁ A₂))
    (hirr : IrreducibleC (qbdP B A₀ A₁ A₂))
    (hA : IrreducibleC (matA A₀ A₁ A₂)) :
    IrreducibleE (matG (qbdP B A₀ A₁ A₂) 0) ∨
      ∃ (σ : ι ≃ Fin (Fintype.card ι)) (k : ℕ), 0 < k ∧ k ≤ Fintype.card ι ∧
        (∀ i j : ι, (σ i : ℕ) < k → k ≤ (σ j : ℕ) → matG (qbdP B A₀ A₁ A₂) 0 i j = 0) ∧
        IrreducibleE (fun a b : {i : ι // (σ i : ℕ) < k} => matG (qbdP B A₀ A₁ A₂) 0 a.1 b.1) ∧
        (∀ i j : ι, k ≤ (σ i : ℕ) → k ≤ (σ j : ℕ) → σ i ≤ σ j →
          matG (qbdP B A₀ A₁ A₂) 0 i j = 0) := by
  classical
  rcases isEmpty_or_nonempty ι with hι | hι
  · left; intro i; exact isEmptyElim i
  right
  set E : ι → ι → Prop := fun a b => matG (qbdP B A₀ A₁ A₂) 0 a b ≠ 0 with hE
  have hEG : ∀ a b, E a b ↔ GSX.Gr B A₀ A₁ A₂ a b := fun a b =>
    ⟨GSX.down_of_G_ne B A₀ A₁ A₂ a b, GSX.G_ne_of_down B A₀ A₁ A₂ a b⟩
  have hrow : ∀ i, ∃ j, E i j := by
    intro i
    obtain ⟨t, ht⟩ := hirr (1, i) (0, i)
    have := GSX.rtg_of_stepPow (qbdP B A₀ A₁ A₂) hP.1 t _ _ ht
    obtain ⟨c, hc⟩ := GSX.down_of_rtg B A₀ A₁ A₂ this rfl le_rfl
    exact ⟨c, (hEG i c).mpr hc⟩
  have hreach : ∀ i, Relation.TransGen E i i → ∀ j, Relation.TransGen E j i := by
    intro i hi j
    have hi' : Relation.TransGen (GSX.Gr B A₀ A₁ A₂) i i :=
      Relation.TransGen.mono (fun a b h => (hEG a b).mp h) _ _ hi
    exact Relation.TransGen.mono (fun a b h => (hEG a b).mpr h) _ _
      (GSX.reachG B A₀ A₁ A₂ hP hA i hi' j)
  obtain ⟨σ, k, hk0, hkn, h1, h2, h3⟩ := GSX.comb E hrow hreach
  exact ⟨σ, k, hk0, hkn, fun i j hi hj => not_not.mp (h1 i j hi hj),
    GSX.irr_of_transGen _ h2, fun i j hi hj hle => not_not.mp (h3 i j hi hj hle)⟩
