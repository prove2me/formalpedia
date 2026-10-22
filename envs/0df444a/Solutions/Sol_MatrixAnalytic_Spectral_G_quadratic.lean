-- Prove2me | solution 1 for MatrixAnalytic.Spectral.G_quadratic
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T17:54:49.761806+00:00
-- url     : https://prove2.me/submissions/a9670481-5af5-492a-99cc-c97c8c80f675

import Mathlib
import Definitions.Def_MatrixAnalytic_Spectral_Chain
import Definitions.Def_MatrixAnalytic_Spectral_QBD
import Definitions.Def_MatrixAnalytic_Spectral_Polynomial
open scoped ENNReal
open Polynomial Matrix
open MatrixAnalytic.Spectral

noncomputable def g72ma_W {V : Type*} (P : V → V → ℝ) {t : ℕ} (ω : Fin (t + 1) → V) : ℝ≥0∞ :=
  ∏ s : Fin t, ENNReal.ofReal (P (ω s.castSucc) (ω s.succ))

open Classical in
noncomputable def g72ma_PS {V : Type*} (P : V → V → ℝ) (x : V) (L : ℕ) (y : V) (A : V → Prop) :
    ℝ≥0∞ :=
  ∑' ω : Fin (L + 1) → V,
    if ω 0 = x ∧ ω (Fin.last L) = y ∧ ∀ m : Fin (L + 1), m ≠ 0 → m ≠ Fin.last L → A (ω m)
    then g72ma_W P ω else 0

section Gen
variable {V : Type*} (P : V → V → ℝ)

lemma g72ma_W_cons {n : ℕ} (ω : Fin (n + 1) → V) (k : V) :
    g72ma_W P (Fin.cons k ω : Fin (n + 2) → V) = ENNReal.ofReal (P k (ω 0)) * g72ma_W P ω := by
  unfold g72ma_W
  rw [Fin.prod_univ_succ]
  congr 1

lemma g72ma_W_snoc {n : ℕ} (ω : Fin (n + 1) → V) (k : V) :
    g72ma_W P (Fin.snoc ω k : Fin (n + 2) → V) = g72ma_W P ω * ENNReal.ofReal (P (ω (Fin.last n)) k) := by
  unfold g72ma_W
  rw [Fin.prod_univ_castSucc]
  congr 1
  · refine Finset.prod_congr rfl fun m _ => ?_
    have h1 : m.castSucc.succ = m.succ.castSucc := by ext; simp
    rw [h1, Fin.snoc_castSucc, Fin.snoc_castSucc]
  · have h1 : (Fin.last n).succ = Fin.last (n+1) := by ext; simp
    rw [h1, Fin.snoc_last, Fin.snoc_castSucc]

lemma g72ma_tsum_snoc {n : ℕ} (f : (Fin (n + 2) → V) → ℝ≥0∞) :
    ∑' ω : Fin (n + 2) → V, f ω = ∑' ω : Fin (n + 1) → V, ∑' k : V, f (Fin.snoc ω k) := by
  rw [← (Fin.snocEquiv (fun _ => V)).tsum_eq, ENNReal.tsum_prod', ENNReal.tsum_comm]
  rfl

lemma g72ma_tsum_cons {n : ℕ} (f : (Fin (n + 2) → V) → ℝ≥0∞) :
    ∑' ω : Fin (n + 2) → V, f ω = ∑' k : V, ∑' ω : Fin (n + 1) → V, f (Fin.cons k ω) := by
  rw [← (Fin.consEquiv (fun _ => V)).tsum_eq, ENNReal.tsum_prod']
  rfl

lemma g72ma_ite_tsum {α : Type*} (c : Prop) [Decidable c] (f : α → ℝ≥0∞) :
    (if c then ∑' i, f i else 0) = ∑' i, if c then f i else 0 := by
  split_ifs <;> simp

open Classical in
lemma g72ma_PS_zero (x y : V) (A : V → Prop) :
    g72ma_PS P x 0 y A = if x = y then 1 else 0 := by
  classical
  unfold g72ma_PS
  rw [← (Equiv.funUnique (Fin 1) V).symm.tsum_eq]
  simp only [Equiv.funUnique_symm_apply]
  by_cases hxy : x = y
  · subst hxy
    rw [tsum_eq_single x]
    · simp [g72ma_W]
    · intro b hb; simp [hb]
  · rw [if_neg hxy]
    apply ENNReal.tsum_eq_zero.mpr
    intro b
    rw [if_neg]
    rintro ⟨h1, h2, -⟩
    exact hxy (h1.symm.trans (by simpa using h2))

lemma g72ma_cond_cons {L : ℕ} (x y : V) (A : V → Prop) (ω : Fin (L + 1) → V) :
    ((Fin.cons x ω : Fin (L + 2) → V) 0 = x ∧ (Fin.cons x ω : Fin (L + 2) → V) (Fin.last (L + 1)) = y ∧
      ∀ m : Fin (L + 2), m ≠ 0 → m ≠ Fin.last (L + 1) → A ((Fin.cons x ω : Fin (L + 2) → V) m)) ↔
    ((L = 0 ∨ A (ω 0)) ∧ ω 0 = ω 0 ∧ ω (Fin.last L) = y ∧
      ∀ m : Fin (L + 1), m ≠ 0 → m ≠ Fin.last L → A (ω m)) := by
  rw [← Fin.succ_last, Fin.cons_succ, Fin.cons_zero, Fin.forall_fin_succ]
  simp only [ne_eq, not_true_eq_false, IsEmpty.forall_iff, true_and, Fin.cons_succ,
    Fin.succ_ne_zero, not_false_eq_true, true_implies, Fin.succ_inj]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, h1, fun m _ hm => h2 m hm⟩
    by_cases hL : L = 0
    · exact Or.inl hL
    · refine Or.inr (h2 0 ?_)
      intro h; apply hL; have := congrArg Fin.val h; simp at this; omega
  · rintro ⟨h0, h1, h2⟩
    refine ⟨h1, fun m hm => ?_⟩
    by_cases hm0 : m = 0
    · subst hm0
      rcases h0 with h0 | h0
      · subst h0; exact absurd rfl hm
      · exact h0
    · exact h2 m hm0 hm

lemma g72ma_PS_cons (x : V) (L : ℕ) (y : V) (A : V → Prop) [DecidablePred A] :
    g72ma_PS P x (L + 1) y A =
      ∑' z, ENNReal.ofReal (P x z) * (if L = 0 ∨ A z then g72ma_PS P z L y A else 0) := by
  classical
  unfold g72ma_PS
  rw [g72ma_tsum_cons, tsum_eq_single x]
  · simp_rw [g72ma_ite_tsum, ← ENNReal.tsum_mul_left]
    rw [ENNReal.tsum_comm]
    refine tsum_congr fun ω => ?_
    rw [tsum_eq_single (ω 0)]
    · have hcc := g72ma_cond_cons x y A ω
      rw [g72ma_W_cons]
      split_ifs with h1 h2 h3
      · rfl
      · exact absurd (hcc.mp h1).2 h3
      · exact absurd (hcc.mp h1).1 h2
      · exact absurd (hcc.mpr ⟨by assumption, by assumption⟩) (by assumption)
      · simp
      · simp
    · intro z hz
      simp [Ne.symm hz]
  · intro k hk
    apply ENNReal.tsum_eq_zero.mpr
    intro ω
    rw [if_neg]
    rintro ⟨h, -⟩
    exact hk (by simpa using h)

lemma g72ma_PS_one (x y : V) (A : V → Prop) :
    g72ma_PS P x 1 y A = ENNReal.ofReal (P x y) := by
  classical
  rw [g72ma_PS_cons P, tsum_eq_single y]
  · simp [g72ma_PS_zero]
  · intro z hz; simp [g72ma_PS_zero, hz]

open Classical in
noncomputable def g72ma_AV (x : V) (A : V → Prop) (t : ℕ) : ℝ≥0∞ :=
  ∑' ω : Fin (t + 1) → V, if ω 0 = x ∧ ∀ i : Fin (t + 1), i ≠ 0 → A (ω i) then g72ma_W P ω else 0

open Classical in
noncomputable def g72ma_EX (x : V) (A : V → Prop) (k : ℕ) : ℝ≥0∞ :=
  ∑' ω : Fin (k + 1) → V,
    if ω 0 = x ∧ ¬ A (ω (Fin.last k)) ∧ (∀ m : Fin (k + 1), m ≠ 0 → m ≠ Fin.last k → A (ω m))
    then g72ma_W P ω else 0

lemma g72ma_step (hrow : ∀ z, ∑' y, ENNReal.ofReal (P z y) = 1) (x : V) (A : V → Prop) (t : ℕ) :
    g72ma_AV P x A (t + 1) + g72ma_EX P x A (t + 1) = g72ma_AV P x A t := by
  classical
  unfold g72ma_AV g72ma_EX
  rw [g72ma_tsum_snoc, g72ma_tsum_snoc, ← ENNReal.tsum_add]
  refine tsum_congr fun ω => ?_
  rw [← ENNReal.tsum_add]
  have hz : ∀ k, (Fin.snoc ω k : Fin (t + 2) → V) 0 = ω 0 := fun k => by
    have : (0 : Fin (t + 2)) = (0 : Fin (t + 1)).castSucc := rfl
    rw [this, Fin.snoc_castSucc]
  have e1 : ∀ m : Fin (t + 1), (m.castSucc = 0) ↔ m = 0 := fun m => by
    constructor
    · intro h; exact Fin.ext (by simpa using congrArg Fin.val h)
    · rintro rfl; rfl
  have hA : ∀ k, (∀ i : Fin (t + 2), i ≠ 0 → A ((Fin.snoc ω k : Fin (t + 2) → V) i)) ↔
      (∀ i : Fin (t + 1), i ≠ 0 → A (ω i)) ∧ A k := fun k => by
    rw [Fin.forall_fin_succ']
    simp only [Fin.snoc_castSucc, Fin.snoc_last]
    have e2 : Fin.last (t + 1) ≠ 0 := by simp [Fin.ext_iff]
    simp only [ne_eq, e1, e2, not_false_eq_true, true_implies]
  have hB : ∀ k, (∀ m : Fin (t + 2), m ≠ 0 → m ≠ Fin.last (t + 1) →
      A ((Fin.snoc ω k : Fin (t + 2) → V) m)) ↔ (∀ i : Fin (t + 1), i ≠ 0 → A (ω i)) := fun k => by
    rw [Fin.forall_fin_succ']
    simp only [Fin.snoc_castSucc, ne_eq, not_true_eq_false, IsEmpty.forall_iff, imp_true_iff,
      and_true]
    refine forall_congr' fun m => ?_
    have e2 : m.castSucc ≠ Fin.last (t+1) := Fin.castSucc_ne_last m
    simp only [e1, e2, not_false_eq_true, true_implies]
  simp_rw [hz, hA, hB, Fin.snoc_last, g72ma_W_snoc]
  by_cases hc : ω 0 = x ∧ ∀ i : Fin (t + 1), i ≠ 0 → A (ω i)
  · rw [if_pos hc]
    have : ∀ k, ((if ω 0 = x ∧ (∀ i : Fin (t + 1), i ≠ 0 → A (ω i)) ∧ A k then
        g72ma_W P ω * ENNReal.ofReal (P (ω (Fin.last t)) k) else 0) +
        if ω 0 = x ∧ ¬ A k ∧ ∀ i : Fin (t + 1), i ≠ 0 → A (ω i) then
        g72ma_W P ω * ENNReal.ofReal (P (ω (Fin.last t)) k) else 0) =
        g72ma_W P ω * ENNReal.ofReal (P (ω (Fin.last t)) k) := by
      intro k
      by_cases hk : A k
      · rw [if_pos ⟨hc.1, hc.2, hk⟩, if_neg (by tauto), add_zero]
      · rw [if_neg (by tauto), if_pos ⟨hc.1, hk, hc.2⟩, zero_add]
    simp_rw [this]
    rw [ENNReal.tsum_mul_left, hrow, mul_one]
  · rw [if_neg hc]
    apply ENNReal.tsum_eq_zero.mpr
    intro k
    rw [if_neg (by tauto), if_neg (by tauto), add_zero]

lemma g72ma_mass (hrow : ∀ z, ∑' y, ENNReal.ofReal (P z y) = 1) (x : V) (A : V → Prop) (t : ℕ) :
    g72ma_AV P x A t + ∑ k ∈ Finset.range t, g72ma_EX P x A (k + 1) = 1 := by
  classical
  induction t with
  | zero =>
    simp only [Finset.range_zero, Finset.sum_empty, add_zero]
    unfold g72ma_AV
    rw [← (Equiv.funUnique (Fin 1) V).symm.tsum_eq]
    simp only [Equiv.funUnique_symm_apply]
    rw [tsum_eq_single x]
    · simp [g72ma_W]
    · intro b hb; simp [hb]
  | succ t ih =>
    rw [Finset.sum_range_succ, ← add_assoc, add_comm _ (g72ma_EX P x A (t + 1)), ← add_assoc,
      add_comm (g72ma_EX P x A (t + 1)), g72ma_step P hrow x A t, ih]

lemma g72ma_PS_le_EX (x y : V) (A : V → Prop) (hy : ¬ A y) (k : ℕ) :
    g72ma_PS P x k y A ≤ g72ma_EX P x A k := by
  classical
  unfold g72ma_PS g72ma_EX
  refine ENNReal.tsum_le_tsum fun ω => ?_
  split_ifs with h1 h2
  · exact le_rfl
  · exact absurd ⟨h1.1, h1.2.1 ▸ hy, h1.2.2⟩ h2
  · simp
  · exact le_rfl

lemma g72ma_sum_PS_le (hrow : ∀ z, ∑' y, ENNReal.ofReal (P z y) = 1) (x y : V) (A : V → Prop)
    (hy : ¬ A y) : ∑' k, g72ma_PS P x (k + 1) y A ≤ 1 := by
  refine ENNReal.tsum_le_of_sum_range_le fun t => ?_
  rw [← g72ma_mass P hrow x A t]
  exact (Finset.sum_le_sum fun k _ => g72ma_PS_le_EX P x y A hy (k + 1)).trans le_add_self

/-- first-passage convolution for a skip-free-down chain with level function `lev`. -/
lemma g72ma_conv (lev : V → ℕ) (hskip : ∀ x z, lev z + 1 < lev x → P x z = 0) (m : ℕ) (y : V)
    (hy : lev y = m) :
    ∀ L x, m + 2 ≤ lev x → g72ma_PS P x (L + 1) y (fun z => m < lev z) =
      ∑ s ∈ Finset.range L, ∑' z, (if lev z = m + 1 then
        g72ma_PS P x (s + 1) z (fun z => m + 1 < lev z) * g72ma_PS P z (L - s) y (fun z => m < lev z)
        else 0) := by
  classical
  intro L
  induction L with
  | zero =>
    intro x hx
    rw [g72ma_PS_one, hskip x y (by omega)]
    simp
  | succ L ih =>
    intro x hx
    rw [Finset.sum_range_succ', g72ma_PS_cons P x (L + 1)]
    have h0 : ∀ z, (if lev z = m + 1 then g72ma_PS P x (0 + 1) z (fun z => m + 1 < lev z) *
        g72ma_PS P z (L + 1 - 0) y (fun z => m < lev z) else 0) =
        if lev z = m + 1 then ENNReal.ofReal (P x z) * g72ma_PS P z (L + 1) y (fun z => m < lev z)
        else 0 := fun z => by
      rw [g72ma_PS_one, Nat.sub_zero]
    simp_rw [h0]
    have h1 : ∀ s ∈ Finset.range L, ∑' z, (if lev z = m + 1 then
        g72ma_PS P x (s + 1 + 1) z (fun z => m + 1 < lev z) *
        g72ma_PS P z (L + 1 - (s + 1)) y (fun z => m < lev z) else 0) =
        ∑' w, ENNReal.ofReal (P x w) * (if m + 1 < lev w then ∑' z, (if lev z = m + 1 then
          g72ma_PS P w (s + 1) z (fun z => m + 1 < lev z) *
          g72ma_PS P z (L - s) y (fun z => m < lev z) else 0) else 0) := by
      intro s _
      have e : ∀ z, (if lev z = m + 1 then
          g72ma_PS P x (s + 1 + 1) z (fun z => m + 1 < lev z) *
          g72ma_PS P z (L + 1 - (s + 1)) y (fun z => m < lev z) else 0) =
          ∑' w, ENNReal.ofReal (P x w) * (if m + 1 < lev w then (if lev z = m + 1 then
          g72ma_PS P w (s + 1) z (fun z => m + 1 < lev z) *
          g72ma_PS P z (L - s) y (fun z => m < lev z) else 0) else 0) := by
        intro z
        rw [g72ma_PS_cons P x (s + 1), show L + 1 - (s + 1) = L - s by omega]
        by_cases hz : lev z = m + 1
        · simp only [hz, if_true]
          rw [← ENNReal.tsum_mul_right]
          refine tsum_congr fun w => ?_
          by_cases hw : m + 1 < lev w
          · simp [hw, mul_assoc]
          · simp [hw]
        · simp [hz]
      simp_rw [e]
      rw [ENNReal.tsum_comm]
      refine tsum_congr fun w => ?_
      rw [ENNReal.tsum_mul_left]
      by_cases hw : m + 1 < lev w
      · simp only [hw, if_true]
      · simp [hw]
    rw [Finset.sum_congr rfl h1, ← Summable.tsum_finsetSum (fun _ _ => ENNReal.summable),
      ← ENNReal.tsum_add]
    refine tsum_congr fun w => ?_
    rw [← Finset.mul_sum]
    by_cases hw1 : lev w = m + 1
    · simp [hw1]
    · by_cases hw2 : m + 1 < lev w
      · rw [if_pos (Or.inr (by omega)), ih w (by omega)]
        simp [hw1, hw2]
      · have hw3 : ¬ m < lev w := by omega
        simp [hw1, hw2, hw3]
end Gen

section QBD
variable {ι : Type*} [Countable ι] [DecidableEq ι] (B A₀ A₁ A₂ : ι → ι → ℝ)

lemma g72ma_skip (x z : ℕ × ι) (h : z.1 + 1 < x.1) : qbdP B A₀ A₁ A₂ x z = 0 := by
  unfold qbdP; split_ifs <;> first | rfl | (exfalso; omega)

lemma g72ma_qshift (a b : ℕ) (i j : ι) (ha : 1 ≤ a) :
    qbdP B A₀ A₁ A₂ (a + 1, i) (b + 1, j) = qbdP B A₀ A₁ A₂ (a, i) (b, j) := by
  unfold qbdP; simp only; split_ifs <;> first | rfl | (exfalso; omega)

def g72ma_sh {L : ℕ} (ω : Fin (L + 1) → ℕ × ι) : Fin (L + 1) → ℕ × ι :=
  fun s => ((ω s).1 + 1, (ω s).2)

lemma g72ma_sh_inj {L : ℕ} : Function.Injective (g72ma_sh (ι := ι) (L := L)) := by
  intro ω ω' h
  funext s
  have := congrFun h s
  simp only [g72ma_sh, Prod.mk.injEq] at this
  exact Prod.ext (by omega) this.2

lemma g72ma_PS_shift (a b : ℕ) (i j : ι) (ha : 1 ≤ a) (L : ℕ) :
    g72ma_PS (qbdP B A₀ A₁ A₂) (a + 1, i) L (b + 1, j) (fun z => 1 < z.1) =
      g72ma_PS (qbdP B A₀ A₁ A₂) (a, i) L (b, j) (fun z => 0 < z.1) := by
  classical
  unfold g72ma_PS
  rw [← g72ma_sh_inj.tsum_eq]
  · refine tsum_congr fun ω => ?_
    have hc : ((g72ma_sh ω) 0 = (a + 1, i) ∧ (g72ma_sh ω) (Fin.last L) = (b + 1, j) ∧
        ∀ m : Fin (L + 1), m ≠ 0 → m ≠ Fin.last L → 1 < ((g72ma_sh ω) m).1) ↔
        (ω 0 = (a, i) ∧ ω (Fin.last L) = (b, j) ∧
        ∀ m : Fin (L + 1), m ≠ 0 → m ≠ Fin.last L → 0 < (ω m).1) := by
      simp only [g72ma_sh, Prod.ext_iff, add_left_inj, Nat.lt_add_left_iff_pos]
    by_cases h : ω 0 = (a, i) ∧ ω (Fin.last L) = (b, j) ∧
        ∀ m : Fin (L + 1), m ≠ 0 → m ≠ Fin.last L → 0 < (ω m).1
    · rw [if_pos (hc.mpr h), if_pos h]
      unfold g72ma_W
      refine Finset.prod_congr rfl fun s _ => ?_
      have hl : 1 ≤ (ω s.castSucc).1 := by
        by_cases hs : s.castSucc = 0
        · rw [hs, h.1]; exact ha
        · have := h.2.2 s.castSucc hs (Fin.castSucc_ne_last s); omega
      simp only [g72ma_sh]
      rw [show ((ω s.castSucc).1 + 1, (ω s.castSucc).2) = ((ω s.castSucc).1 + 1, (ω s.castSucc).2)
        from rfl, g72ma_qshift B A₀ A₁ A₂ _ _ _ _ hl]
    · rw [if_neg (fun h' => h (hc.mp h')), if_neg h]
  · intro ω hω
    rw [Function.mem_support] at hω
    have hcond : ω 0 = (a + 1, i) ∧ ω (Fin.last L) = (b + 1, j) ∧
        ∀ m : Fin (L + 1), m ≠ 0 → m ≠ Fin.last L → 1 < (ω m).1 := by
      by_contra hn; exact hω (if_neg hn)
    refine ⟨fun s => ((ω s).1 - 1, (ω s).2), funext fun s => ?_⟩
    have : 1 ≤ (ω s).1 := by
      by_cases h0 : s = 0
      · rw [h0, hcond.1]; omega
      by_cases hl : s = Fin.last L
      · rw [hl, hcond.2.1]; omega
      have := hcond.2.2 s h0 hl; omega
    simp only [g72ma_sh]
    exact Prod.ext (by simp; omega) rfl

lemma g72ma_passage (k : ℕ) (i j : ι) :
    passageProb (qbdP B A₀ A₁ A₂) k i j =
      g72ma_PS (qbdP B A₀ A₁ A₂) (1, i) k (0, j) (fun z => 0 < z.1) := by
  classical
  unfold passageProb g72ma_PS
  refine tsum_congr fun ω => ?_
  have hc : (ω 0 = (1, i) ∧ ω (Fin.last k) = (0, j) ∧ ∀ s : Fin (k + 1), s ≠ Fin.last k → ω s ∉ level 0) ↔
      (ω 0 = (1, i) ∧ ω (Fin.last k) = (0, j) ∧
        ∀ m : Fin (k + 1), m ≠ 0 → m ≠ Fin.last k → 0 < (ω m).1) := by
    simp only [level, Set.mem_setOf_eq]
    constructor
    · rintro ⟨h1, h2, h3⟩; exact ⟨h1, h2, fun m _ hm => Nat.pos_of_ne_zero (h3 m hm)⟩
    · rintro ⟨h1, h2, h3⟩
      refine ⟨h1, h2, fun s hs => ?_⟩
      by_cases h0 : s = 0
      · rw [h0, h1]; simp
      · have := h3 s h0 hs; omega
  by_cases h : ω 0 = (1, i) ∧ ω (Fin.last k) = (0, j) ∧
      ∀ m : Fin (k + 1), m ≠ 0 → m ≠ Fin.last k → 0 < (ω m).1
  · rw [if_pos (hc.mpr h), if_pos h]; rfl
  · rw [if_neg (fun h' => h (hc.mp h')), if_neg h]

end QBD

section Main
variable {ι : Type*} [Countable ι] [DecidableEq ι] (B A₀ A₁ A₂ : ι → ι → ℝ)

lemma g72ma_skipU (x z : ℕ × ι) (h : x.1 + 1 < z.1) : qbdP B A₀ A₁ A₂ x z = 0 := by
  unfold qbdP; split_ifs <;> first | rfl | (exfalso; omega)

omit [Countable ι] [DecidableEq ι] in
lemma g72ma_lev1 (f : ℕ × ι → ℝ≥0∞) :
    ∑' z : ℕ × ι, (if z.1 = 0 + 1 then f z else 0) = ∑' l, f (1, l) := by
  rw [ENNReal.tsum_prod', tsum_eq_single 1]
  · simp
  · intro n hn; simp [hn]

lemma g72ma_step2 (k : ℕ) (i j : ι) :
    g72ma_PS (qbdP B A₀ A₁ A₂) (1, i) (k + 2) (0, j) (fun z => 0 < z.1) =
      ∑' l, ENNReal.ofReal (A₁ i l) *
          g72ma_PS (qbdP B A₀ A₁ A₂) (1, l) (k + 1) (0, j) (fun z => 0 < z.1) +
      ∑' l, ENNReal.ofReal (A₀ i l) * ∑ s ∈ Finset.range k, ∑' l',
        g72ma_PS (qbdP B A₀ A₁ A₂) (1, l) (s + 1) (0, l') (fun z => 0 < z.1) *
        g72ma_PS (qbdP B A₀ A₁ A₂) (1, l') (k - s) (0, j) (fun z => 0 < z.1) := by
  classical
  set P := qbdP B A₀ A₁ A₂ with hPd
  rw [show k + 2 = (k + 1) + 1 by ring, g72ma_PS_cons P (1, i) (k + 1), ENNReal.tsum_prod',
    tsum_eq_zero_add' ENNReal.summable, tsum_eq_zero_add' ENNReal.summable,
    tsum_eq_zero_add' ENNReal.summable]
  have hF0 : ∑' l, ENNReal.ofReal (P (1, i) (0, l)) *
      (if k + 1 = 0 ∨ 0 < ((0, l) : ℕ × ι).1 then g72ma_PS P (0, l) (k + 1) (0, j) (fun z => 0 < z.1)
        else 0) = 0 := by simp
  have hF3 : ∑' n : ℕ, ∑' l, ENNReal.ofReal (P (1, i) (n + 1 + 1 + 1, l)) *
      (if k + 1 = 0 ∨ 0 < ((n + 1 + 1 + 1, l) : ℕ × ι).1 then
        g72ma_PS P (n + 1 + 1 + 1, l) (k + 1) (0, j) (fun z => 0 < z.1) else 0) = 0 := by
    refine ENNReal.tsum_eq_zero.mpr fun n => ENNReal.tsum_eq_zero.mpr fun l => ?_
    rw [hPd, g72ma_skipU B A₀ A₁ A₂ (1, i) (n + 1 + 1 + 1, l) (by simp)]; simp
  rw [hF0, hF3, zero_add, add_zero]
  refine congrArg₂ (· + ·) ?_ ?_
  · refine tsum_congr fun l => ?_
    simp [hPd, qbdP]
  · refine tsum_congr fun l => ?_
    have hP2 : P (1, i) (0 + 1 + 1, l) = A₀ i l := by simp [hPd, qbdP]
    rw [hP2, if_pos (Or.inr (by simp))]
    congr 1
    have hc := g72ma_conv P Prod.fst (fun x z h => by rw [hPd]; exact g72ma_skip B A₀ A₁ A₂ x z h)
      0 (0, j) rfl k (0 + 1 + 1, l) le_rfl
    rw [hc]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [g72ma_lev1]
    refine tsum_congr fun l' => ?_
    have := g72ma_PS_shift B A₀ A₁ A₂ 1 0 l l' le_rfl (s + 1)
    rw [← hPd] at this
    simp only [zero_add] at this ⊢
    rw [this]

end Main

lemma g72ma_cauchy (a b : ℕ → ℝ≥0∞) :
    ∑' k, ∑ s ∈ Finset.range k, a (s + 1) * b (k - s) = (∑' s, a (s + 1)) * ∑' t, b (t + 1) := by
  rw [tsum_eq_zero_add' ENNReal.summable]
  simp only [Finset.range_zero, Finset.sum_empty, zero_add]
  rw [← ENNReal.tsum_mul_right]
  simp_rw [← ENNReal.tsum_mul_left]
  rw [← ENNReal.tsum_prod (f := fun s t => a (s + 1) * b (t + 1)),
    ← (Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd (A := ℕ)).tsum_eq, ENNReal.tsum_sigma']
  refine tsum_congr fun k => ?_
  simp only [Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd_apply]
  rw [Finset.tsum_subtype (Finset.HasAntidiagonal.antidiagonal k)
    (fun p : ℕ × ℕ => a (p.1 + 1) * b (p.2 + 1)), Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun s t => a (s + 1) * b (t + 1))]
  refine Finset.sum_congr rfl fun s hs => ?_
  have : s ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hs)
  rw [show k + 1 - s = k - s + 1 by omega]

section Main2
variable {ι : Type*} [Countable ι] [DecidableEq ι] (B A₀ A₁ A₂ : ι → ι → ℝ)

lemma g72ma_matG (i j : ι) : matG (qbdP B A₀ A₁ A₂) i j =
    ∑' k, g72ma_PS (qbdP B A₀ A₁ A₂) (1, i) (k + 1) (0, j) (fun z => 0 < z.1) := by
  unfold matG
  simp_rw [g72ma_passage]
  rw [tsum_eq_zero_add' ENNReal.summable, g72ma_PS_zero]
  simp

lemma g72ma_Geq (i j : ι) : matG (qbdP B A₀ A₁ A₂) i j =
    ENNReal.ofReal (A₂ i j) + ∑' l, ENNReal.ofReal (A₁ i l) * matG (qbdP B A₀ A₁ A₂) l j +
      ∑' l, ENNReal.ofReal (A₀ i l) *
        ∑' l', matG (qbdP B A₀ A₁ A₂) l l' * matG (qbdP B A₀ A₁ A₂) l' j := by
  simp_rw [g72ma_matG]
  rw [tsum_eq_zero_add' ENNReal.summable, g72ma_PS_one]
  simp_rw [show ∀ k : ℕ, k + 1 + 1 = k + 2 from fun k => rfl, g72ma_step2]
  rw [ENNReal.tsum_add, add_assoc]
  congr 1
  congr 1
  · rw [ENNReal.tsum_comm]
    refine tsum_congr fun l => ?_
    rw [ENNReal.tsum_mul_left]
  · rw [ENNReal.tsum_comm]
    refine tsum_congr fun l => ?_
    rw [ENNReal.tsum_mul_left]
    congr 1
    simp_rw [← Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
    rw [ENNReal.tsum_comm]
    refine tsum_congr fun l' => ?_
    exact g72ma_cauchy
      (fun s => g72ma_PS (qbdP B A₀ A₁ A₂) (1, l) s (0, l') (fun z => 0 < z.1))
      (fun t => g72ma_PS (qbdP B A₀ A₁ A₂) (1, l') t (0, j) (fun z => 0 < z.1))

lemma g72ma_G_le (hP : IsStochasticC (qbdP B A₀ A₁ A₂)) (i j : ι) :
    matG (qbdP B A₀ A₁ A₂) i j ≤ 1 := by
  rw [g72ma_matG]
  refine g72ma_sum_PS_le _ (fun z => ?_) _ _ _ (by simp)
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun y => hP.1 z y) (hP.2 z).summable, (hP.2 z).tsum_eq,
    ENNReal.ofReal_one]

end Main2

theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (B A₀ A₁ A₂ : ι → ι → ℝ)
    (hP : IsStochasticC (qbdP B A₀ A₁ A₂))
    (hirr : IrreducibleC (qbdP B A₀ A₁ A₂)) :
    cMat A₀ * matGc (qbdP B A₀ A₁ A₂) ^ 2 + (cMat A₁ - 1) * matGc (qbdP B A₀ A₁ A₂)
      + cMat A₂ = 0 := by
  have h0 : ∀ i j, 0 ≤ A₀ i j := fun i j => by simpa [qbdP] using hP.1 (1, i) (2, j)
  have h1 : ∀ i j, 0 ≤ A₁ i j := fun i j => by simpa [qbdP] using hP.1 (1, i) (1, j)
  have h2 : ∀ i j, 0 ≤ A₂ i j := fun i j => by simpa [qbdP] using hP.1 (1, i) (0, j)
  have hfin : ∀ i j, matG (qbdP B A₀ A₁ A₂) i j ≠ ⊤ := fun i j =>
    ne_top_of_le_ne_top ENNReal.one_ne_top (g72ma_G_le B A₀ A₁ A₂ hP i j)
  have Geq := g72ma_Geq B A₀ A₁ A₂
  have hGc : matGc (qbdP B A₀ A₁ A₂) =
      Matrix.of fun i j => (((matG (qbdP B A₀ A₁ A₂) i j).toReal : ℝ) : ℂ) := rfl
  rw [hGc]
  obtain ⟨gr, hgr0, hG⟩ : ∃ gr : ι → ι → ℝ, (∀ i j, 0 ≤ gr i j) ∧
      ∀ i j, matG (qbdP B A₀ A₁ A₂) i j = ENNReal.ofReal (gr i j) :=
    ⟨fun i j => (matG (qbdP B A₀ A₁ A₂) i j).toReal, fun _ _ => ENNReal.toReal_nonneg,
      fun i j => (ENNReal.ofReal_toReal (hfin i j)).symm⟩
  simp_rw [hG, ENNReal.toReal_ofReal (hgr0 _ _)] 
  simp_rw [hG] at Geq
  have Er : ∀ i j, gr i j = A₂ i j + ∑ l, A₁ i l * gr l j + ∑ l, A₀ i l * ∑ l', gr l l' * gr l' j := by
    intro i j
    have := Geq i j
    simp only [tsum_fintype] at this
    have n3 : ∀ l, 0 ≤ ∑ l', gr l l' * gr l' j := fun l =>
      Finset.sum_nonneg (fun l' _ => mul_nonneg (hgr0 l l') (hgr0 l' j))
    have n1 : 0 ≤ ∑ l, A₁ i l * gr l j := Finset.sum_nonneg (fun l _ => mul_nonneg (h1 i l) (hgr0 l j))
    have n2 : 0 ≤ ∑ l, A₀ i l * ∑ l', gr l l' * gr l' j :=
      Finset.sum_nonneg (fun l _ => mul_nonneg (h0 i l) (n3 l))
    have key : ENNReal.ofReal (A₂ i j + ∑ l, A₁ i l * gr l j + ∑ l, A₀ i l * ∑ l', gr l l' * gr l' j) =
        ENNReal.ofReal (A₂ i j) + ∑ l, ENNReal.ofReal (A₁ i l) * ENNReal.ofReal (gr l j) +
        ∑ l, ENNReal.ofReal (A₀ i l) * ∑ l', ENNReal.ofReal (gr l l') * ENNReal.ofReal (gr l' j) := by
      rw [ENNReal.ofReal_add (add_nonneg (h2 i j) n1) n2, ENNReal.ofReal_add (h2 i j) n1,
        ENNReal.ofReal_sum_of_nonneg (fun l _ => mul_nonneg (h1 i l) (hgr0 l j)),
        ENNReal.ofReal_sum_of_nonneg (fun l _ => mul_nonneg (h0 i l) (n3 l))]
      congr 1
      · congr 1
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [ENNReal.ofReal_mul (h1 i l)]
      · refine Finset.sum_congr rfl fun l _ => ?_
        rw [ENNReal.ofReal_mul (h0 i l), ENNReal.ofReal_sum_of_nonneg
          (fun l' _ => mul_nonneg (hgr0 l l') (hgr0 l' j))]
        congr 1
        refine Finset.sum_congr rfl fun l' _ => ?_
        rw [ENNReal.ofReal_mul (hgr0 l l')]
    rw [← key] at this
    exact (ENNReal.ofReal_eq_ofReal_iff (hgr0 i j) (add_nonneg (add_nonneg (h2 i j) n1) n2)).mp this
  ext i j
  have := Er i j
  simp only [Matrix.add_apply, Matrix.mul_apply, sq, Matrix.sub_apply, Matrix.one_apply, cMat,
    Matrix.of_apply, Matrix.zero_apply]
  simp only [sub_mul, Finset.sum_sub_distrib, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq,
    Finset.mem_univ, if_true]
  have hc := congrArg (fun x : ℝ => (x : ℂ)) this
  push_cast at hc
  linear_combination -hc
