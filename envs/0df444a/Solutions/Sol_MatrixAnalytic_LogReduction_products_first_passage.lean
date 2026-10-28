-- Prove2me | solution 1 for MatrixAnalytic.LogReduction.products_first_passage
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T11:55:50.689819+00:00
-- url     : https://prove2.me/submissions/addcecea-ad2d-4daf-ad96-6dcac32cddac

import Mathlib
import Definitions.Def_MatrixAnalytic_LogReduction_Chain
import Definitions.Def_MatrixAnalytic_LogReduction_QBD
import Definitions.Def_MatrixAnalytic_LogReduction_Passage

open scoped ENNReal

set_option linter.unusedSectionVars false

namespace S202PF
open MatrixAnalytic.LogReduction

noncomputable def g72mab_W {V : Type*} (P : V → V → ℝ) {t : ℕ} (ω : Fin (t + 1) → V) : ℝ≥0∞ :=
  ∏ s : Fin t, ENNReal.ofReal (P (ω s.castSucc) (ω s.succ))

open Classical in
noncomputable def g72mab_PS {V : Type*} (P : V → V → ℝ) (x : V) (L : ℕ) (y : V) (A : V → Prop) :
    ℝ≥0∞ :=
  ∑' ω : Fin (L + 1) → V,
    if ω 0 = x ∧ ω (Fin.last L) = y ∧ ∀ m : Fin (L + 1), m ≠ 0 → m ≠ Fin.last L → A (ω m)
    then g72mab_W P ω else 0

section Gen
variable {V : Type*} (P : V → V → ℝ)

lemma g72mab_W_cons {n : ℕ} (ω : Fin (n + 1) → V) (k : V) :
    g72mab_W P (Fin.cons k ω : Fin (n + 2) → V) = ENNReal.ofReal (P k (ω 0)) * g72mab_W P ω := by
  unfold g72mab_W
  rw [Fin.prod_univ_succ]
  congr 1

lemma g72mab_W_snoc {n : ℕ} (ω : Fin (n + 1) → V) (k : V) :
    g72mab_W P (Fin.snoc ω k : Fin (n + 2) → V) = g72mab_W P ω * ENNReal.ofReal (P (ω (Fin.last n)) k) := by
  unfold g72mab_W
  rw [Fin.prod_univ_castSucc]
  congr 1
  · refine Finset.prod_congr rfl fun m _ => ?_
    have h1 : m.castSucc.succ = m.succ.castSucc := by ext; simp
    rw [h1, Fin.snoc_castSucc, Fin.snoc_castSucc]
  · have h1 : (Fin.last n).succ = Fin.last (n+1) := by ext; simp
    rw [h1, Fin.snoc_last, Fin.snoc_castSucc]

lemma g72mab_tsum_snoc {n : ℕ} (f : (Fin (n + 2) → V) → ℝ≥0∞) :
    ∑' ω : Fin (n + 2) → V, f ω = ∑' ω : Fin (n + 1) → V, ∑' k : V, f (Fin.snoc ω k) := by
  rw [← (Fin.snocEquiv (fun _ => V)).tsum_eq, ENNReal.tsum_prod', ENNReal.tsum_comm]
  rfl

lemma g72mab_tsum_cons {n : ℕ} (f : (Fin (n + 2) → V) → ℝ≥0∞) :
    ∑' ω : Fin (n + 2) → V, f ω = ∑' k : V, ∑' ω : Fin (n + 1) → V, f (Fin.cons k ω) := by
  rw [← (Fin.consEquiv (fun _ => V)).tsum_eq, ENNReal.tsum_prod']
  rfl

lemma g72mab_ite_tsum {α : Type*} (c : Prop) [Decidable c] (f : α → ℝ≥0∞) :
    (if c then ∑' i, f i else 0) = ∑' i, if c then f i else 0 := by
  split_ifs <;> simp

open Classical in
lemma g72mab_PS_zero (x y : V) (A : V → Prop) :
    g72mab_PS P x 0 y A = if x = y then 1 else 0 := by
  classical
  unfold g72mab_PS
  rw [← (Equiv.funUnique (Fin 1) V).symm.tsum_eq]
  simp only [Equiv.funUnique_symm_apply]
  by_cases hxy : x = y
  · subst hxy
    rw [tsum_eq_single x]
    · simp [g72mab_W]
    · intro b hb; simp [hb]
  · rw [if_neg hxy]
    apply ENNReal.tsum_eq_zero.mpr
    intro b
    rw [if_neg]
    rintro ⟨h1, h2, -⟩
    exact hxy (h1.symm.trans (by simpa using h2))

lemma g72mab_cond_cons {L : ℕ} (x y : V) (A : V → Prop) (ω : Fin (L + 1) → V) :
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

lemma g72mab_PS_cons (x : V) (L : ℕ) (y : V) (A : V → Prop) [DecidablePred A] :
    g72mab_PS P x (L + 1) y A =
      ∑' z, ENNReal.ofReal (P x z) * (if L = 0 ∨ A z then g72mab_PS P z L y A else 0) := by
  classical
  unfold g72mab_PS
  rw [g72mab_tsum_cons, tsum_eq_single x]
  · simp_rw [g72mab_ite_tsum, ← ENNReal.tsum_mul_left]
    rw [ENNReal.tsum_comm]
    refine tsum_congr fun ω => ?_
    rw [tsum_eq_single (ω 0)]
    · have hcc := g72mab_cond_cons x y A ω
      rw [g72mab_W_cons]
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

lemma g72mab_PS_one (x y : V) (A : V → Prop) :
    g72mab_PS P x 1 y A = ENNReal.ofReal (P x y) := by
  classical
  rw [g72mab_PS_cons P, tsum_eq_single y]
  · simp [g72mab_PS_zero]
  · intro z hz; simp [g72mab_PS_zero, hz]

end Gen

section Gen3
variable {V : Type*} (P : V → V → ℝ)

lemma g72mab_cond_snoc {L : ℕ} (x y : V) (A : V → Prop) (ω : Fin (L + 1) → V) :
    ((Fin.snoc ω y : Fin (L + 2) → V) 0 = x ∧ (Fin.snoc ω y : Fin (L + 2) → V) (Fin.last (L + 1)) = y ∧
      ∀ m : Fin (L + 2), m ≠ 0 → m ≠ Fin.last (L + 1) → A ((Fin.snoc ω y : Fin (L + 2) → V) m)) ↔
    ((L = 0 ∨ A (ω (Fin.last L))) ∧ (ω 0 = x ∧ ω (Fin.last L) = ω (Fin.last L) ∧
      ∀ m : Fin (L + 1), m ≠ 0 → m ≠ Fin.last L → A (ω m))) := by
  have hz : (Fin.snoc ω y : Fin (L + 2) → V) 0 = ω 0 := by
    have : (0 : Fin (L + 2)) = (0 : Fin (L + 1)).castSucc := rfl
    rw [this, Fin.snoc_castSucc]
  rw [hz, Fin.snoc_last, Fin.forall_fin_succ']
  simp only [Fin.snoc_castSucc, ne_eq, not_true_eq_false, IsEmpty.forall_iff, imp_true_iff, and_true,
    true_and]
  have e1 : ∀ m : Fin (L + 1), (m.castSucc = 0) ↔ m = 0 := fun m => by
    constructor
    · intro h; exact Fin.ext (by simpa using congrArg Fin.val h)
    · rintro rfl; rfl
  have e2 : ∀ m : Fin (L + 1), m.castSucc ≠ Fin.last (L+1) := Fin.castSucc_ne_last
  simp only [e1, e2, not_false_eq_true, true_implies]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, h1, fun m hm _ => h2 m hm⟩
    by_cases hL : L = 0
    · exact Or.inl hL
    · refine Or.inr (h2 _ ?_)
      intro h; apply hL; have := congrArg Fin.val h; simp at this; omega
  · rintro ⟨h0, h1, h2⟩
    refine ⟨h1, fun m hm => ?_⟩
    by_cases hml : m = Fin.last L
    · subst hml
      rcases h0 with h0 | h0
      · subst h0; exact absurd rfl hm
      · exact h0
    · exact h2 m hm hml

lemma g72mab_PS_snoc (x : V) (L : ℕ) (y : V) (A : V → Prop) [DecidablePred A] :
    g72mab_PS P x (L + 1) y A =
      ∑' z, (if L = 0 ∨ A z then g72mab_PS P x L z A else 0) * ENNReal.ofReal (P z y) := by
  classical
  unfold g72mab_PS
  rw [g72mab_tsum_snoc]
  simp_rw [g72mab_ite_tsum, ← ENNReal.tsum_mul_right]
  conv_rhs => rw [ENNReal.tsum_comm]
  refine tsum_congr fun ω => ?_
  rw [tsum_eq_single y, tsum_eq_single (ω (Fin.last L))]
  · have hcc := g72mab_cond_snoc x y A ω
    rw [g72mab_W_snoc]
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
    rw [if_neg]
    rintro ⟨-, h, -⟩
    exact hk (by simpa using h)
end Gen3

section UGRgen
variable {V : Type*} (P : V → V → ℝ)

lemma g72mab_PS_congr (I A A' : V → Prop) (y : V)
    (hstep : ∀ w z, I w → P w z ≠ 0 → (A z ↔ A' z) ∧ (A z → I z)) :
    ∀ L x, I x → g72mab_PS P x L y A = g72mab_PS P x L y A' := by
  classical
  intro L
  induction L with
  | zero => intro x _; rw [g72mab_PS_zero, g72mab_PS_zero]
  | succ L ih =>
    intro x hx
    rw [g72mab_PS_cons P x L y A, g72mab_PS_cons P x L y A']
    refine tsum_congr fun z => ?_
    by_cases hP0 : P x z = 0
    · simp [hP0]
    obtain ⟨hiff, hI⟩ := hstep x z hx hP0
    rcases Nat.eq_zero_or_pos L with hL | hL
    · subst hL; simp only [true_or, if_true, g72mab_PS_zero]
    · by_cases hz : A z
      · rw [if_pos (Or.inr hz), if_pos (Or.inr (hiff.mp hz)), ih z (hI hz)]
      · rw [if_neg (by rintro (h | h) <;> [omega; exact hz h]),
          if_neg (by rintro (h | h) <;> [omega; exact hz (hiff.mpr h)])]
end UGRgen

section QBDm
variable {ι : Type*} [Countable ι] [DecidableEq ι] (B A₀ A₁ A₂ : ι → ι → ℝ)

lemma g72mab_qnz (x w : ℕ × ι) (h : qbdP B A₀ A₁ A₂ x w ≠ 0) : w.1 ≤ x.1 + 1 ∧ x.1 ≤ w.1 + 1 := by
  unfold qbdP at h
  split_ifs at h <;> first | omega | exact absurd rfl h

end QBDm

section UGRq
variable {ι : Type*} [Countable ι] [DecidableEq ι]

lemma g72mab_fe (P : ℕ × ι → ℕ × ι → ℝ) (T : Set (ℕ × ι)) (x y : ℕ × ι) (hy : y ∈ T) :
    firstEntrance P T x y = ∑' t, g72mab_PS P x (t + 1) y (fun z => z ∉ T) := by
  classical
  unfold firstEntrance g72mab_PS
  refine tsum_congr fun t => tsum_congr fun ω => ?_
  by_cases h : ω 0 = x ∧ ω (Fin.last (t + 1)) = y ∧
      ∀ m : Fin (t + 1 + 1), m ≠ 0 → m ≠ Fin.last (t + 1) → ω m ∉ T
  · rw [if_pos ⟨h.1, h.2.1, hy, h.2.2⟩, if_pos h]; rfl
  · rw [if_neg (fun h' => h ⟨h'.1, h'.2.1, h'.2.2.2⟩), if_neg h]
end UGRq

structure Ker (V : Type*) where
  f : V → V → ℝ≥0∞

noncomputable section

section KerAlg
variable {V : Type*} [DecidableEq V]

instance : CoeFun (Ker V) (fun _ => V → V → ℝ≥0∞) := ⟨Ker.f⟩

lemma Ker.ext {M N : Ker V} (h : ∀ x y, M x y = N x y) : M = N := by
  cases M; cases N; congr; funext x y; exact h x y

instance : Add (Ker V) := ⟨fun M N => ⟨fun x y => M x y + N x y⟩⟩
instance : Zero (Ker V) := ⟨⟨fun _ _ => 0⟩⟩

lemma add_ap (M N : Ker V) (x y : V) : (M + N) x y = M x y + N x y := rfl
lemma zero_ap (x y : V) : (0 : Ker V) x y = 0 := rfl

instance : AddCommMonoid (Ker V) where
  add_assoc a b c := Ker.ext fun x y => by simp only [add_ap, add_assoc]
  zero_add a := Ker.ext fun x y => by simp only [add_ap, zero_ap, zero_add]
  add_zero a := Ker.ext fun x y => by simp only [add_ap, zero_ap, add_zero]
  add_comm a b := Ker.ext fun x y => by simp only [add_ap, add_comm]
  nsmul := nsmulRec

instance : PartialOrder (Ker V) where
  le M N := ∀ x y, M x y ≤ N x y
  le_refl M x y := le_rfl
  le_trans A B C h1 h2 x y := le_trans (h1 x y) (h2 x y)
  le_antisymm A B h1 h2 := Ker.ext fun x y => le_antisymm (h1 x y) (h2 x y)

lemma le_iff (M N : Ker V) : M ≤ N ↔ ∀ x y, M x y ≤ N x y := Iff.rfl

instance : Mul (Ker V) := ⟨fun M N => ⟨fun x y => ∑' z, M x z * N z y⟩⟩
instance : One (Ker V) := ⟨⟨fun x y => if x = y then 1 else 0⟩⟩

lemma mul_ap (M N : Ker V) (x y : V) : (M * N) x y = ∑' z, M x z * N z y := rfl
lemma one_ap (x y : V) : (1 : Ker V) x y = if x = y then 1 else 0 := rfl

instance : Semiring (Ker V) where
  left_distrib M N O := Ker.ext fun x y => by
    simp only [mul_ap, add_ap, mul_add, ENNReal.tsum_add]
  right_distrib M N O := Ker.ext fun x y => by
    simp only [mul_ap, add_ap, add_mul, ENNReal.tsum_add]
  zero_mul M := Ker.ext fun x y => by simp [mul_ap, zero_ap]
  mul_zero M := Ker.ext fun x y => by simp [mul_ap, zero_ap]
  mul_assoc M N O := Ker.ext fun x y => by
    simp only [mul_ap]
    simp_rw [← ENNReal.tsum_mul_right, ← ENNReal.tsum_mul_left, mul_assoc]
    exact ENNReal.tsum_comm
  one_mul M := Ker.ext fun x y => by
    simp only [mul_ap, one_ap]
    rw [tsum_eq_single x]
    · simp
    · intro b hb; simp [Ne.symm hb]
  mul_one M := Ker.ext fun x y => by
    simp only [mul_ap, one_ap]
    rw [tsum_eq_single y]
    · simp
    · intro b hb; simp [hb]

lemma sum_ap {α : Type*} (s : Finset α) (f : α → Ker V) (x y : V) :
    (∑ n ∈ s, f n) x y = ∑ n ∈ s, f n x y := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [zero_ap]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, add_ap, ih]

lemma kmul_mono {M M' N N' : Ker V} (h1 : M ≤ M') (h2 : N ≤ N') : M * N ≤ M' * N' := by
  intro x y
  exact ENNReal.tsum_le_tsum fun z => mul_le_mul' (h1 x z) (h2 z y)

lemma kadd_mono {M M' N N' : Ker V} (h1 : M ≤ M') (h2 : N ≤ N') : M + N ≤ M' + N' := by
  intro x y
  exact add_le_add (h1 x y) (h2 x y)

/-- `Σ_ν M^ν` -/
def ser (M : Ker V) : Ker V := ⟨fun x y => ∑' n : ℕ, (M ^ n) x y⟩

lemma ser_ap (M : Ker V) (x y : V) : ser M x y = ∑' n : ℕ, (M ^ n) x y := rfl

lemma mul_ser_ap (M N : Ker V) (x y : V) : (M * ser N) x y = ∑' n, (M * N ^ n) x y := by
  simp only [mul_ap, ser_ap]
  simp_rw [← ENNReal.tsum_mul_left]
  exact ENNReal.tsum_comm

lemma ser_mul_ap (M N : Ker V) (x y : V) : (ser N * M) x y = ∑' n, (N ^ n * M) x y := by
  simp only [mul_ap, ser_ap]
  simp_rw [← ENNReal.tsum_mul_right]
  exact ENNReal.tsum_comm

lemma ser_fp (M : Ker V) : ser M = 1 + M * ser M := by
  apply Ker.ext; intro x y
  rw [add_ap, mul_ser_ap, ser_ap, tsum_eq_zero_add' ENNReal.summable]
  congr 1
  try (refine tsum_congr fun n => ?_; rw [pow_succ'])

lemma ser_fp' (M : Ker V) : ser M = 1 + ser M * M := by
  apply Ker.ext; intro x y
  rw [add_ap, ser_mul_ap, ser_ap, tsum_eq_zero_add' ENNReal.summable]
  congr 1
  try (refine tsum_congr fun n => ?_; rw [pow_succ])

lemma ser_comm (M : Ker V) : M * ser M = ser M * M := by
  apply Ker.ext; intro x y
  rw [mul_ser_ap, ser_mul_ap]
  simp only [← pow_succ, ← pow_succ']

lemma one_le_ser (M : Ker V) : 1 ≤ ser M := by
  rw [ser_fp M]; intro x y; rw [add_ap]; exact le_self_add

lemma ser_min {C M W : Ker V} (h : C + M * W ≤ W) : ser M * C ≤ W := by
  have hpart : ∀ N : ℕ, (∑ n ∈ Finset.range N, M ^ n) * C ≤ W := by
    intro N
    induction N with
    | zero => simp only [Finset.range_zero, Finset.sum_empty, zero_mul]; intro x y; exact bot_le
    | succ N ih =>
      rw [Finset.sum_range_succ', pow_zero]
      simp_rw [pow_succ']
      rw [← Finset.mul_sum, add_mul, one_mul, mul_assoc, add_comm]
      exact le_trans (kadd_mono le_rfl (kmul_mono le_rfl ih)) h
  rw [le_iff]; intro x y
  rw [ser_mul_ap]
  refine ENNReal.tsum_le_of_sum_range_le fun N => ?_
  have := (le_iff _ _).mp (hpart N) x y
  rwa [Finset.sum_mul, sum_ap] at this

lemma ser_min' {C M W : Ker V} (h : C + W * M ≤ W) : C * ser M ≤ W := by
  have hpart : ∀ N : ℕ, C * (∑ n ∈ Finset.range N, M ^ n) ≤ W := by
    intro N
    induction N with
    | zero => simp only [Finset.range_zero, Finset.sum_empty, mul_zero]; intro x y; exact bot_le
    | succ N ih =>
      rw [Finset.sum_range_succ', pow_zero]
      simp_rw [pow_succ]
      rw [← Finset.sum_mul, mul_add, mul_one, ← mul_assoc, add_comm]
      exact le_trans (kadd_mono le_rfl (kmul_mono ih le_rfl)) h
  rw [le_iff]; intro x y
  rw [mul_ser_ap]
  refine ENNReal.tsum_le_of_sum_range_le fun N => ?_
  have := (le_iff _ _).mp (hpart N) x y
  rwa [Finset.mul_sum, sum_ap] at this

lemma pow_mono {M N : Ker V} (h : M ≤ N) : ∀ n, M ^ n ≤ N ^ n := by
  intro n
  induction n with
  | zero => exact le_rfl
  | succ n ih => rw [pow_succ, pow_succ]; exact kmul_mono ih h

lemma ser_mono {M N : Ker V} (h : M ≤ N) : ser M ≤ ser N := by
  rw [le_iff]; intro x y
  exact ENNReal.tsum_le_tsum fun n => (le_iff _ _).mp (pow_mono h n) x y

/-- resolvent identity `Σ(Q+D)^ν = Σ(Σ Q^ν D)^μ Σ Q^ν` -/
lemma ser_resolvent (Q D : Ker V) : ser (Q + D) = ser (ser Q * D) * ser Q := by
  set S' := ser Q with hS'
  set K := S' * D with hK
  set Y := ser K * S' with hY
  have hS : S' = 1 + Q * S' := ser_fp Q
  have hYe : Y = S' + K * Y := by
    rw [hY]
    conv_lhs => rw [ser_fp K]
    rw [add_mul, one_mul, mul_assoc]
  apply le_antisymm
  · have : ser (Q + D) * 1 ≤ Y := by
      apply ser_min
      apply le_of_eq
      have e1 : (Q + D) * Y = Q * S' + Q * (K * Y) + D * Y := by
        conv_lhs => rw [hYe]
        rw [add_mul, mul_add]
        conv_lhs => rw [← hYe]
      rw [e1]
      conv_rhs => rw [hYe]
      have e2 : K * Y = S' * (D * Y) := by rw [hK, mul_assoc]
      rw [e2]
      conv_rhs => rw [hS]
      rw [add_mul, one_mul, ← mul_assoc Q S' (D * Y)]
      simp only [add_assoc, add_comm, add_left_comm]
    simpa using this
  · apply ser_min
    rw [hK, mul_assoc]
    have h2 : S' * (1 + D * ser (Q + D)) ≤ ser (Q + D) := by
      apply ser_min
      apply le_of_eq
      conv_rhs => rw [ser_fp (Q + D)]
      rw [add_mul]
      simp only [add_assoc, add_comm, add_left_comm]
    calc S' + S' * (D * ser (Q + D)) = S' * (1 + D * ser (Q + D)) := by rw [mul_add, mul_one]
      _ ≤ _ := h2

end KerAlg
end

/-! ## Diagonal projections, all-ones kernel, chain kernel -/

noncomputable section
section Chain
variable {V : Type*} [DecidableEq V]
open Classical

def E (S : Set V) : Ker V := ⟨fun x y => if x = y ∧ x ∈ S then 1 else 0⟩
def J : Ker V := ⟨fun _ _ => 1⟩
def Pk (P : V → V → ℝ) : Ker V := ⟨fun x y => ENNReal.ofReal (P x y)⟩

lemma E_ap (S : Set V) (x y : V) : E S x y = if x = y ∧ x ∈ S then 1 else 0 := rfl
lemma J_ap (x y : V) : (J : Ker V) x y = 1 := rfl
lemma Pk_ap (P : V → V → ℝ) (x y : V) : Pk P x y = ENNReal.ofReal (P x y) := rfl

lemma mulE_ap (M : Ker V) (S : Set V) (x y : V) :
    (M * E S) x y = if y ∈ S then M x y else 0 := by
  rw [mul_ap, tsum_eq_single y]
  · by_cases hy : y ∈ S <;> simp [E_ap, hy]
  · intro z hz; simp [E_ap, hz]

lemma Emul_ap (M : Ker V) (S : Set V) (x y : V) :
    (E S * M) x y = if x ∈ S then M x y else 0 := by
  rw [mul_ap, tsum_eq_single x]
  · by_cases hx : x ∈ S <;> simp [E_ap, hx]
  · intro z hz; simp [E_ap, Ne.symm hz]

lemma E_mul_E (S S' : Set V) : E S * E S' = E (S ∩ S') := by
  apply Ker.ext; intro x y
  rw [mulE_ap]
  by_cases h1 : y ∈ S' <;> by_cases h2 : x = y
  · subst h2; by_cases h3 : x ∈ S <;> simp [E_ap, h1, h3]
  · simp [E_ap, h2]
  · subst h2; simp [E_ap, h1]
  · simp [E_ap, h2]

lemma E_split {T T' : Set V} (h : T ⊆ T') : E Tᶜ = E T'ᶜ + E (T' \ T) := by
  apply Ker.ext; intro x y
  rw [add_ap]
  by_cases hxy : x = y
  · subst hxy
    by_cases h1 : x ∈ T
    · have := h h1; simp [E_ap, h1, this]
    · by_cases h2 : x ∈ T' <;> simp [E_ap, h1, h2]
  · simp [E_ap, hxy]

lemma E_compl (T : Set V) : E T + E Tᶜ = 1 := by
  apply Ker.ext; intro x y
  rw [add_ap, one_ap]
  by_cases hxy : x = y
  · subst hxy; by_cases h1 : x ∈ T <;> simp [E_ap, h1]
  · simp [E_ap, hxy]

lemma Pk_split (P : V → V → ℝ) (T : Set V) : Pk P = Pk P * E T + Pk P * E Tᶜ := by
  rw [← mul_add, E_compl, mul_one]

lemma PS_eq (P : V → V → ℝ) (A : V → Prop) (x : V) :
    ∀ (n : ℕ) (y : V), g72mab_PS P x (n + 1) y A = ((Pk P * E {z | A z}) ^ n * Pk P) x y := by
  intro n
  induction n with
  | zero => intro y; rw [g72mab_PS_one, pow_zero, one_mul]; rfl
  | succ n ih =>
    intro y
    rw [g72mab_PS_snoc P x (n + 1) y A]
    have e : (Pk P * E {z | A z}) ^ (n + 1) * Pk P =
        ((Pk P * E {z | A z}) ^ n * Pk P) * E {z | A z} * Pk P := by
      rw [pow_succ]; simp only [mul_assoc]
    rw [e, mul_ap]
    refine tsum_congr fun z => ?_
    rw [mulE_ap, ← ih z, Pk_ap]
    by_cases hz : A z <;> simp [hz]

/-- first entrance kernel -/
def Fk (P : V → V → ℝ) (T : Set V) : Ker V := ser (Pk P * E Tᶜ) * Pk P * E T

lemma ser_split (P : V → V → ℝ) {T T' : Set V} (h : T ⊆ T') :
    ser (Pk P * E Tᶜ) = ser (Fk P T' * E (T' \ T)) * ser (Pk P * E T'ᶜ) := by
  have h1 : Pk P * E Tᶜ = Pk P * E T'ᶜ + Pk P * E (T' \ T) := by rw [E_split h, mul_add]
  have h2 : Fk P T' * E (T' \ T) = ser (Pk P * E T'ᶜ) * (Pk P * E (T' \ T)) := by
    unfold Fk
    rw [mul_assoc _ (E T'), E_mul_E, Set.inter_eq_right.mpr Set.diff_subset, mul_assoc]
  rw [h1, ser_resolvent, h2]

lemma Fk_CM (P : V → V → ℝ) {T T' : Set V} (h : T ⊆ T') :
    Fk P T = ser (Fk P T' * E (T' \ T)) * (Fk P T' * E T) := by
  have h3 : Fk P T' * E T = ser (Pk P * E T'ᶜ) * Pk P * E T := by
    unfold Fk
    rw [mul_assoc _ (E T'), E_mul_E, Set.inter_eq_right.mpr h]
  rw [h3]
  conv_lhs => unfold Fk; rw [ser_split P h]
  simp only [mul_assoc]

lemma Fk_CS (P : V → V → ℝ) {T T' : Set V} (h : T ⊆ T') :
    Fk P T = Fk P T' * E T + Fk P T' * E (T' \ T) * Fk P T := by
  calc Fk P T = ser (Fk P T' * E (T' \ T)) * (Fk P T' * E T) := Fk_CM P h
    _ = (1 + Fk P T' * E (T' \ T) * ser (Fk P T' * E (T' \ T))) * (Fk P T' * E T) := by
        rw [← ser_fp]
    _ = Fk P T' * E T + Fk P T' * E (T' \ T) *
          (ser (Fk P T' * E (T' \ T)) * (Fk P T' * E T)) := by rw [add_mul, one_mul, mul_assoc]
    _ = _ := by rw [← Fk_CM P h]

lemma le_mulJ (M : Ker V) : M ≤ M * J := by
  intro x y
  show M x y ≤ (M * J).f x y
  rw [mul_ap]; simp only [J_ap, mul_one]
  exact ENNReal.le_tsum y

lemma W_id (M C : Ker V) (hMC : C + M * J = J) :
    ∀ R : ℕ, (∑ n ∈ Finset.range R, M ^ n * C) + M ^ R * J = J := by
  intro R
  induction R with
  | zero => simp
  | succ R ih =>
    rw [Finset.sum_range_succ, add_assoc, pow_succ, mul_assoc (M ^ R) M J, ← mul_add, hMC, ih]

lemma CJ_id (P : V → V → ℝ) (hrow : Pk P * J = J) (T : Set V) :
    Pk P * E T * J + Pk P * E Tᶜ * J = J := by
  rw [← add_mul, ← Pk_split, hrow]

lemma Fk_row (P : V → V → ℝ) (hrow : Pk P * J = J) (T : Set V) : Fk P T * J ≤ J := by
  intro x y
  show (Fk P T * J).f x y ≤ (J : Ker V).f x y
  have e : Fk P T * J = ser (Pk P * E Tᶜ) * (Pk P * E T * J) := by
    unfold Fk; simp only [mul_assoc]
  rw [e, ser_mul_ap, J_ap]
  refine ENNReal.tsum_le_of_sum_range_le fun R => ?_
  rw [← sum_ap]
  have hW := W_id (Pk P * E Tᶜ) (Pk P * E T * J) (CJ_id P hrow T) R
  have h2 := congrArg (fun K : Ker V => K.f x y) hW
  simp only [add_ap] at h2
  exact le_self_add.trans_eq h2

lemma pow_J (P : V → V → ℝ) (hrow : Pk P * J = J) : ∀ t : ℕ, Pk P ^ t * J = J := by
  intro t
  induction t with
  | zero => rw [pow_zero, one_mul]
  | succ t ih => rw [pow_succ, mul_assoc, hrow, ih]

lemma pow_hit (P : V → V → ℝ) (hrow : Pk P * J = J) (T : Set V) :
    ∀ t : ℕ, Pk P ^ t ≤ (∑ n ∈ Finset.range t, (Pk P * E Tᶜ) ^ n * (Pk P * E T * J)) +
      (Pk P * E Tᶜ) ^ t := by
  intro t
  induction t with
  | zero => intro x y; simp
  | succ t ih =>
    have hW : (∑ n ∈ Finset.range (t + 1), (Pk P * E Tᶜ) ^ n * (Pk P * E T * J)) =
        Pk P * E T * J + (Pk P * E Tᶜ) * ∑ n ∈ Finset.range t, (Pk P * E Tᶜ) ^ n * (Pk P * E T * J) := by
      rw [Finset.sum_range_succ', Finset.mul_sum, pow_zero, one_mul, add_comm]
      congr 1
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [pow_succ', mul_assoc]
    rw [hW, pow_succ', pow_succ']
    have hs := Pk_split P T
    calc Pk P * Pk P ^ t = (Pk P * E T + Pk P * E Tᶜ) * Pk P ^ t := by rw [← hs]
      _ ≤ _ := ?_
    rw [add_mul, add_assoc, ← mul_add]
    refine kadd_mono ?_ (kmul_mono le_rfl ih)
    rw [mul_assoc, mul_assoc]
    refine kmul_mono le_rfl (kmul_mono le_rfl ?_)
    calc Pk P ^ t ≤ Pk P ^ t * J := le_mulJ _
      _ = J := pow_J P hrow t

lemma ser_mul_pow_le (M : Ker V) : ∀ n : ℕ, ser M * M ^ n ≤ ser M := by
  intro n
  induction n with
  | zero => rw [pow_zero, mul_one]
  | succ n ih =>
    rw [pow_succ, ← mul_assoc]
    calc ser M * M ^ n * M ≤ ser M * M := kmul_mono ih le_rfl
      _ ≤ 1 + ser M * M := fun a b => by rw [add_ap]; exact le_add_self
      _ = ser M := (ser_fp' M).symm

lemma ser_fin (P : V → V → ℝ) (hrow : Pk P * J = J) (T : Set V) (y z : V) (hy : y ∉ T)
    (hz : z ∈ T) (t : ℕ) (ht : (Pk P ^ t) y z ≠ 0) (x : V) :
    ser (Pk P * E Tᶜ) x y ≠ ⊤ := by
  set M := Pk P * E Tᶜ with hM
  set C := Pk P * E T * J with hC
  set W := ∑ n ∈ Finset.range t, M ^ n * C with hWdef
  have hcol : ∀ a b b', W a b = W a b' := by
    intro a b b'
    rw [hWdef, sum_ap, sum_ap]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [hC, ← mul_assoc, mul_ap, mul_ap]
    simp only [J_ap]
  have hMt : (M ^ t) y z = 0 := by
    cases t with
    | zero => rw [pow_zero, one_ap, if_neg]; rintro rfl; exact hy hz
    | succ t =>
      rw [pow_succ, mul_ap]
      refine ENNReal.tsum_eq_zero.mpr fun w => ?_
      rw [hM, mulE_ap, if_neg (by simpa using hz), mul_zero]
  have hWyz : W y z ≠ 0 := by
    intro h0
    have := (pow_hit P hrow T t) y z
    rw [add_ap, ← hWdef, h0, hMt, add_zero] at this
    exact ht (le_antisymm this bot_le)
  have hWyy : W y y ≠ 0 := by rwa [hcol y y z]
  have hb : (ser M * W) x y ≤ t := by
    rw [hWdef, Finset.mul_sum, sum_ap]
    calc ∑ n ∈ Finset.range t, (ser M * (M ^ n * C)) x y ≤ ∑ n ∈ Finset.range t, (1 : ℝ≥0∞) := by
          refine Finset.sum_le_sum fun n _ => ?_
          rw [← mul_assoc]
          refine le_trans (kmul_mono (ser_mul_pow_le M n) le_rfl x y) ?_
          have e : ser M * C = Fk P T * J := by rw [hM, hC]; unfold Fk; simp only [mul_assoc]
          rw [e]
          exact Fk_row P hrow T x y
      _ = t := by simp
  have hle : ser M x y * W y y ≤ (ser M * W) x y := by
    rw [mul_ap]; exact ENNReal.le_tsum (f := fun w => ser M x w * W w y) y
  intro htop
  rw [htop, ENNReal.top_mul hWyy] at hle
  exact ENNReal.natCast_ne_top t (top_le_iff.mp (hle.trans hb))

end Chain
end

/-! ## QBD-specific path lemmas -/

noncomputable section
section QBD
variable {ι : Type*} [Countable ι] [DecidableEq ι] (B A₀ A₁ A₂ : ι → ι → ℝ)
open Classical

lemma fe_eq (P : ℕ × ι → ℕ × ι → ℝ) (T : Set (ℕ × ι)) (x y : ℕ × ι) :
    firstEntrance P T x y = Fk P T x y := by
  unfold Fk
  rw [mulE_ap]
  by_cases hy : y ∈ T
  · rw [if_pos hy, g72mab_fe P T x y hy, ser_mul_ap]
    refine tsum_congr fun t => ?_
    rw [PS_eq]; rfl
  · rw [if_neg hy]
    unfold firstEntrance
    exact ENNReal.tsum_eq_zero.mpr fun t => ENNReal.tsum_eq_zero.mpr fun ω =>
      if_neg (fun h => hy h.2.2.1)

lemma fe_not_mem (P : ℕ × ι → ℕ × ι → ℝ) (T : Set (ℕ × ι)) (x y : ℕ × ι) (hy : y ∉ T) :
    firstEntrance P T x y = 0 := by
  unfold firstEntrance
  exact ENNReal.tsum_eq_zero.mpr fun t => ENNReal.tsum_eq_zero.mpr fun ω =>
    if_neg (fun h => hy h.2.2.1)

omit [Countable ι] [DecidableEq ι] in
lemma qshift (a b c : ℕ) (i j : ι) (ha : 1 ≤ a) :
    qbdP B A₀ A₁ A₂ (a + c, i) (b + c, j) = qbdP B A₀ A₁ A₂ (a, i) (b, j) := by
  unfold qbdP; simp only; split_ifs <;> first | rfl | (exfalso; omega)

def shc (c : ℕ) {L : ℕ} (ω : Fin (L + 1) → ℕ × ι) : Fin (L + 1) → ℕ × ι :=
  fun s => ((ω s).1 + c, (ω s).2)

omit [Countable ι] [DecidableEq ι] in
lemma shc_inj (c : ℕ) {L : ℕ} : Function.Injective (shc (ι := ι) c (L := L)) := by
  intro ω ω' h
  funext s
  have := congrFun h s
  simp only [shc, Prod.mk.injEq] at this
  exact Prod.ext (by omega) this.2

lemma PS_shift (R : ℕ → Prop) (hR : ∀ n, R n → 1 ≤ n) (a b c : ℕ) (i j : ι) (ha : 1 ≤ a)
    (L : ℕ) :
    g72mab_PS (qbdP B A₀ A₁ A₂) (a + c, i) L (b + c, j) (fun z => c ≤ z.1 ∧ R (z.1 - c)) =
      g72mab_PS (qbdP B A₀ A₁ A₂) (a, i) L (b, j) (fun z => R z.1) := by
  unfold g72mab_PS
  rw [← (shc_inj c).tsum_eq]
  · refine tsum_congr fun ω => ?_
    have hc : ((shc c ω) 0 = (a + c, i) ∧ (shc c ω) (Fin.last L) = (b + c, j) ∧
        ∀ m : Fin (L + 1), m ≠ 0 → m ≠ Fin.last L →
          c ≤ ((shc c ω) m).1 ∧ R (((shc c ω) m).1 - c)) ↔
        (ω 0 = (a, i) ∧ ω (Fin.last L) = (b, j) ∧
        ∀ m : Fin (L + 1), m ≠ 0 → m ≠ Fin.last L → R (ω m).1) := by
      simp only [shc, Prod.ext_iff, add_left_inj, Nat.add_sub_cancel, le_add_iff_nonneg_left,
        zero_le, true_and]
    by_cases h : ω 0 = (a, i) ∧ ω (Fin.last L) = (b, j) ∧
        ∀ m : Fin (L + 1), m ≠ 0 → m ≠ Fin.last L → R (ω m).1
    · rw [if_pos (hc.mpr h), if_pos h]
      unfold g72mab_W
      refine Finset.prod_congr rfl fun s _ => ?_
      have hl : 1 ≤ (ω s.castSucc).1 := by
        by_cases hs : s.castSucc = 0
        · rw [hs, h.1]; exact ha
        · exact hR _ (h.2.2 s.castSucc hs (Fin.castSucc_ne_last s))
      simp only [shc]
      rw [qshift B A₀ A₁ A₂ _ _ _ _ _ hl]
    · rw [if_neg (fun h' => h (hc.mp h')), if_neg h]
  · intro ω hω
    rw [Function.mem_support] at hω
    have hcond : ω 0 = (a + c, i) ∧ ω (Fin.last L) = (b + c, j) ∧
        ∀ m : Fin (L + 1), m ≠ 0 → m ≠ Fin.last L → c ≤ (ω m).1 ∧ R ((ω m).1 - c) := by
      by_contra hn; exact hω (if_neg hn)
    refine ⟨fun s => ((ω s).1 - c, (ω s).2), funext fun s => ?_⟩
    have : c ≤ (ω s).1 := by
      by_cases h0 : s = 0
      · rw [h0, hcond.1]; omega
      by_cases hl : s = Fin.last L
      · rw [hl, hcond.2.1]; omega
      exact (hcond.2.2 s h0 hl).1
    simp only [shc]
    exact Prod.ext (by simp; omega) rfl

lemma qzero (lo hi : ℕ) (z y : ℕ × ι) (hz : lo < z.1 ∧ z.1 < hi) (hy : y.1 < lo ∨ hi < y.1) :
    qbdP B A₀ A₁ A₂ z y = 0 := by
  by_contra h
  have := g72mab_qnz B A₀ A₁ A₂ z y h
  omega

lemma PS_band_zero (lo hi : ℕ) (R : ℕ × ι → Prop) (x : ℕ × ι) (hx : lo < x.1 ∧ x.1 < hi)
    (L : ℕ) (y : ℕ × ι) (hy : y.1 < lo ∨ hi < y.1) :
    g72mab_PS (qbdP B A₀ A₁ A₂) x (L + 1) y (fun z => (lo < z.1 ∧ z.1 < hi) ∧ R z) = 0 := by
  rw [g72mab_PS_snoc]
  refine ENNReal.tsum_eq_zero.mpr fun z => ?_
  by_cases hz : lo < z.1 ∧ z.1 < hi
  · rw [qzero B A₀ A₁ A₂ lo hi z y hz hy]; simp
  · split_ifs with hc
    · rcases hc with hL | hA
      · subst hL
        rw [g72mab_PS_zero, if_neg (fun h => hz (by subst h; exact hx))]; simp
      · exact absurd hA.1 hz
    · simp

lemma PS_band_eq (p : ℕ → Prop) (lo hi : ℕ) (hplo : p lo) (hphi : p hi) (x : ℕ × ι)
    (hx : lo < x.1 ∧ x.1 < hi) (L : ℕ) (y : ℕ × ι) :
    g72mab_PS (qbdP B A₀ A₁ A₂) x L y (fun z => z ∉ {w : ℕ × ι | p w.1}) =
      g72mab_PS (qbdP B A₀ A₁ A₂) x L y (fun z => (lo < z.1 ∧ z.1 < hi) ∧ ¬ p z.1) := by
  refine g72mab_PS_congr _ (fun z => lo < z.1 ∧ z.1 < hi) _ _ y ?_ L x hx
  intro w z hw hP
  have := g72mab_qnz B A₀ A₁ A₂ w z hP
  simp only [Set.mem_setOf_eq]
  have key : ¬ p z.1 → lo < z.1 ∧ z.1 < hi := by
    intro h
    refine ⟨?_, ?_⟩
    · by_contra h'; exact h (by rw [show z.1 = lo by omega]; exact hplo)
    · by_contra h'; exact h (by rw [show z.1 = hi by omega]; exact hphi)
  exact ⟨⟨fun h => ⟨key h, h⟩, fun h => h.2⟩, key⟩

def lv (p : ℕ → Prop) : Set (ℕ × ι) := {z | p z.1}

lemma fe_zero (p : ℕ → Prop) (lo hi : ℕ) (hplo : p lo) (hphi : p hi) (a : ℕ) (hlo : lo < a)
    (hhi : a < hi) (i : ι) (b : ℕ) (j : ι) (hb : b < lo ∨ hi < b) :
    firstEntrance (qbdP B A₀ A₁ A₂) (lv p) (a, i) (b, j) = 0 := by
  by_cases hpb : p b
  · rw [g72mab_fe _ _ _ _ (show (b, j) ∈ lv p from hpb)]
    refine ENNReal.tsum_eq_zero.mpr fun t => ?_
    unfold lv
    rw [PS_band_eq B A₀ A₁ A₂ p lo hi hplo hphi (a, i) ⟨hlo, hhi⟩]
    exact PS_band_zero B A₀ A₁ A₂ lo hi _ (a, i) ⟨hlo, hhi⟩ t (b, j) hb
  · exact fe_not_mem _ _ _ _ hpb

lemma band_shift (p q : ℕ → Prop) (lo hi a c : ℕ) (hlo : lo < a) (hhi : a < hi) (hplo : p lo)
    (hphi : p hi) (hpq : ∀ n, lo ≤ n → n ≤ hi → (p n ↔ q (n + c))) (i : ι) (b : ℕ) (j : ι) :
    firstEntrance (qbdP B A₀ A₁ A₂) (lv p) (a, i) (b, j) =
      firstEntrance (qbdP B A₀ A₁ A₂) (lv q) (a + c, i) (b + c, j) := by
  have hqlo : q (lo + c) := (hpq lo le_rfl (by omega)).mp hplo
  have hqhi : q (hi + c) := (hpq hi (by omega) le_rfl).mp hphi
  by_cases hb : lo ≤ b ∧ b ≤ hi
  · by_cases hpb : p b
    · have hqb := (hpq b hb.1 hb.2).mp hpb
      rw [g72mab_fe _ _ _ _ (show (b, j) ∈ lv p from hpb),
        g72mab_fe _ _ _ _ (show (b + c, j) ∈ lv q from hqb)]
      refine tsum_congr fun t => ?_
      unfold lv
      rw [PS_band_eq B A₀ A₁ A₂ p lo hi hplo hphi (a, i) ⟨hlo, hhi⟩,
        PS_band_eq B A₀ A₁ A₂ q (lo + c) (hi + c) hqlo hqhi (a + c, i) ⟨by simp; omega, by simp; omega⟩]
      have hpred : (fun z : ℕ × ι => (lo + c < z.1 ∧ z.1 < hi + c) ∧ ¬ q z.1) =
          (fun z => c ≤ z.1 ∧ ((lo < z.1 - c ∧ z.1 - c < hi) ∧ ¬ p (z.1 - c))) := by
        funext z; apply propext; constructor
        · rintro ⟨⟨h1, h2⟩, h3⟩
          refine ⟨by omega, ⟨by omega, by omega⟩, fun hp => h3 ?_⟩
          have := (hpq (z.1 - c) (by omega) (by omega)).mp hp
          rwa [Nat.sub_add_cancel (by omega)] at this
        · rintro ⟨h0, ⟨h1, h2⟩, h3⟩
          refine ⟨⟨by omega, by omega⟩, fun hq => h3 ?_⟩
          apply (hpq (z.1 - c) (by omega) (by omega)).mpr
          rwa [Nat.sub_add_cancel h0]
      rw [hpred]
      exact (PS_shift B A₀ A₁ A₂ (fun n => (lo < n ∧ n < hi) ∧ ¬ p n)
        (fun n hn => by omega) a b c i j (by omega) (t + 1)).symm
    · have hqb : ¬ q (b + c) := fun h => hpb ((hpq b hb.1 hb.2).mpr h)
      rw [fe_not_mem _ _ _ _ (show (b, j) ∉ lv p from hpb),
        fe_not_mem _ _ _ _ (show (b + c, j) ∉ lv q from hqb)]
  · rw [fe_zero B A₀ A₁ A₂ p lo hi hplo hphi a hlo hhi i b j (by omega),
      fe_zero B A₀ A₁ A₂ q (lo + c) (hi + c) hqlo hqhi (a + c) (by omega) (by omega) i (b + c) j
        (by omega)]

lemma lev_sum (f : ℕ × ι → ℝ≥0∞) (n : ℕ) (hf : ∀ z : ℕ × ι, z.1 ≠ n → f z = 0) :
    ∑' z, f z = ∑' l, f (n, l) := by
  rw [ENNReal.tsum_prod', tsum_eq_single n]
  intro m hm
  exact ENNReal.tsum_eq_zero.mpr fun l => hf (m, l) hm

lemma two_lev (f : ℕ × ι → ℝ≥0∞) (n m : ℕ) (hnm : n ≠ m) :
    ∑' z : ℕ × ι, (if z.1 = n ∨ z.1 = m then f z else 0) = ∑' l, f (n, l) + ∑' l, f (m, l) := by
  have e : ∀ z : ℕ × ι, (if z.1 = n ∨ z.1 = m then f z else 0) =
      (if z.1 = n then f z else 0) + (if z.1 = m then f z else 0) := by
    intro z
    by_cases h1 : z.1 = n
    · have : ¬ z.1 = m := by omega
      simp [h1, hnm]
    · by_cases h2 : z.1 = m <;> simp [h1, h2, Ne.symm hnm]
  simp_rw [e]
  rw [ENNReal.tsum_add, lev_sum _ n (fun z hz => if_neg hz), lev_sum _ m (fun z hz => if_neg hz)]
  simp

/-- block of a kernel on level `n` -/
def blk (X : Ker (ℕ × ι)) (n : ℕ) : Ker ι := ⟨fun a b => X (n, a) (n, b)⟩

lemma blk_pow (X : Ker (ℕ × ι)) (n : ℕ) (hX : ∀ w z : ℕ × ι, z.1 ≠ n → X w z = 0) (i : ι) :
    ∀ m : ℕ, (∀ z : ℕ × ι, z.1 ≠ n → (X ^ m) (n, i) z = 0) ∧
      ∀ l, (X ^ m) (n, i) (n, l) = (blk X n ^ m) i l := by
  intro m
  induction m with
  | zero =>
    refine ⟨fun z hz => ?_, fun l => ?_⟩
    · rw [pow_zero, one_ap, if_neg]; rintro rfl; exact hz rfl
    · rw [pow_zero, pow_zero, one_ap, one_ap]
      by_cases h : i = l <;> simp [h]
  | succ m ih =>
    refine ⟨fun z hz => ?_, fun l => ?_⟩
    · rw [pow_succ, mul_ap]
      exact ENNReal.tsum_eq_zero.mpr fun w => by rw [hX w z hz, mul_zero]
    · rw [pow_succ, pow_succ, mul_ap, mul_ap,
        lev_sum _ n (fun z hz => by rw [ih.1 z hz, zero_mul])]
      refine tsum_congr fun l' => ?_
      rw [ih.2 l']; rfl

lemma blk_ser_mul (X Y : Ker (ℕ × ι)) (n : ℕ) (hX : ∀ w z : ℕ × ι, z.1 ≠ n → X w z = 0)
    (i : ι) (y : ℕ × ι) : (ser X * Y) (n, i) y = ∑' l, ser (blk X n) i l * Y (n, l) y := by
  rw [mul_ap, lev_sum _ n]
  · refine tsum_congr fun l => ?_
    rw [ser_ap, ser_ap]
    congr 1
    exact tsum_congr fun m => (blk_pow X n hX i m).2 l
  · intro z hz
    rw [ser_ap]
    simp [(blk_pow X n hX i _).1 z hz]

lemma blk_ser (X : Ker (ℕ × ι)) (n : ℕ) (hX : ∀ w z : ℕ × ι, z.1 ≠ n → X w z = 0)
    (i l : ι) : ser X (n, i) (n, l) = ser (blk X n) i l := by
  rw [ser_ap, ser_ap]
  exact tsum_congr fun m => (blk_pow X n hX i m).2 l

lemma stepPow_nonneg' (P : ℕ × ι → ℕ × ι → ℝ) (hP0 : ∀ x y, 0 ≤ P x y) :
    ∀ t x y, 0 ≤ stepPow P t x y := by
  intro t
  induction t with
  | zero => intro x y; simp only [stepPow]; split_ifs <;> norm_num
  | succ t ih => intro x y; exact tsum_nonneg fun z => mul_nonneg (ih x z) (hP0 z y)

lemma stepPow_le (P : ℕ × ι → ℕ × ι → ℝ) (hP0 : ∀ x y, 0 ≤ P x y) :
    ∀ t x y, ENNReal.ofReal (stepPow P t x y) ≤ (Pk P ^ t) x y := by
  intro t
  induction t with
  | zero =>
    intro x y
    rw [pow_zero, one_ap]
    simp only [stepPow]
    by_cases h : x = y
    · subst h; simp
    · simp [h, Ne.symm h]
  | succ t ih =>
    intro x y
    simp only [stepPow]
    by_cases hs : Summable (fun z => stepPow P t x z * P z y)
    · rw [ENNReal.ofReal_tsum_of_nonneg (fun z => mul_nonneg (stepPow_nonneg' P hP0 t x z)
        (hP0 z y)) hs, pow_succ, mul_ap]
      refine ENNReal.tsum_le_tsum fun z => ?_
      rw [ENNReal.ofReal_mul (stepPow_nonneg' P hP0 t x z)]
      exact mul_le_mul' (ih x z) le_rfl
    · rw [tsum_eq_zero_of_not_summable hs]; simp

end QBD
end

/-! ## Censored blocks at levels `0, N, 2N` -/

noncomputable section
section Blocks
variable {ι : Type*} [Countable ι] [DecidableEq ι] (B A₀ A₁ A₂ : ι → ι → ℝ)
open Classical

omit [Countable ι] [DecidableEq ι] in
lemma mem_lv (p : ℕ → Prop) (z : ℕ × ι) : z ∈ lv p ↔ p z.1 := Iff.rfl

def T2 (N : ℕ) : Set (ℕ × ι) := lv (fun n => n = 0 ∨ n = 2 * N)
def T3 (N : ℕ) : Set (ℕ × ι) := lv (fun n => n = 0 ∨ n = N ∨ n = 2 * N)
def T5 (N : ℕ) : Set (ℕ × ι) := lv (fun n => n = 0 ∨ n = N ∨ n = 2 * N ∨ n = 3 * N ∨ n = 4 * N)

def K0 (N : ℕ) : Ker ι := ⟨fun i j => firstEntrance (qbdP B A₀ A₁ A₂) (T3 N) (N, i) (2 * N, j)⟩
def K1 (N : ℕ) : Ker ι := ⟨fun i j => firstEntrance (qbdP B A₀ A₁ A₂) (T3 N) (N, i) (N, j)⟩
def K2 (N : ℕ) : Ker ι := ⟨fun i j => firstEntrance (qbdP B A₀ A₁ A₂) (T3 N) (N, i) (0, j)⟩
def HH (N : ℕ) : Ker ι := ⟨fun i j => firstEntrance (qbdP B A₀ A₁ A₂) (T2 N) (N, i) (2 * N, j)⟩
def LL (N : ℕ) : Ker ι := ⟨fun i j => firstEntrance (qbdP B A₀ A₁ A₂) (T2 N) (N, i) (0, j)⟩

lemma T2_sub (N : ℕ) : (T2 N : Set (ℕ × ι)) ⊆ T3 N := by
  intro z hz
  simp only [T2, T3, mem_lv] at *
  omega

lemma X_zero (N : ℕ) (hN : 1 ≤ N) (w z : ℕ × ι) (hz : z.1 ≠ N) :
    (Fk (qbdP B A₀ A₁ A₂) (T3 N) * E (T3 N \ T2 N)).f w z = 0 := by
  rw [mulE_ap, if_neg]
  simp only [T2, T3, Set.mem_sdiff, mem_lv]
  omega

lemma blkX (N : ℕ) (hN : 1 ≤ N) :
    blk (Fk (qbdP B A₀ A₁ A₂) (T3 N) * E (T3 N \ T2 N)) N = K1 B A₀ A₁ A₂ N := by
  apply Ker.ext; intro a b
  show (Fk (qbdP B A₀ A₁ A₂) (T3 N) * E (T3 N \ T2 N)).f (N, a) (N, b) = _
  rw [mulE_ap, if_pos (by simp only [T2, T3, Set.mem_sdiff, mem_lv, true_or, or_true, true_and] <;> omega), ← fe_eq]
  rfl

lemma KA (N : ℕ) (hN : 1 ≤ N) :
    HH B A₀ A₁ A₂ N = ser (K1 B A₀ A₁ A₂ N) * K0 B A₀ A₁ A₂ N ∧
      LL B A₀ A₁ A₂ N = ser (K1 B A₀ A₁ A₂ N) * K2 B A₀ A₁ A₂ N := by
  have key : ∀ (i : ι) (y : ℕ × ι), firstEntrance (qbdP B A₀ A₁ A₂) (T2 N) (N, i) y =
      ∑' l, ser (K1 B A₀ A₁ A₂ N) i l *
        (if y ∈ T2 N then firstEntrance (qbdP B A₀ A₁ A₂) (T3 N) (N, l) y else 0) := by
    intro i y
    rw [fe_eq, Fk_CM _ (T2_sub N), blk_ser_mul _ _ N (X_zero B A₀ A₁ A₂ N hN), blkX B A₀ A₁ A₂ N hN]
    refine tsum_congr fun l => ?_
    rw [mulE_ap, ← fe_eq]
  constructor
  · apply Ker.ext; intro i j
    show firstEntrance _ _ _ _ = _
    rw [key, mul_ap]
    refine tsum_congr fun l => ?_
    rw [if_pos (by simp only [T2, mem_lv, true_or, or_true, true_and] <;> omega)]
    rfl
  · apply Ker.ext; intro i j
    show firstEntrance _ _ _ _ = _
    rw [key, mul_ap]
    refine tsum_congr fun l => ?_
    rw [if_pos (by simp only [T2, mem_lv, true_or, or_true, true_and] <;> omega)]
    rfl

lemma KC (N : ℕ) (hN : 1 ≤ N) :
    K0 B A₀ A₁ A₂ (2 * N) = K0 B A₀ A₁ A₂ N * HH B A₀ A₁ A₂ N ∧
    K1 B A₀ A₁ A₂ (2 * N) = K1 B A₀ A₁ A₂ N +
      (K2 B A₀ A₁ A₂ N * HH B A₀ A₁ A₂ N + K0 B A₀ A₁ A₂ N * LL B A₀ A₁ A₂ N) ∧
    K2 B A₀ A₁ A₂ (2 * N) = K2 B A₀ A₁ A₂ N * LL B A₀ A₁ A₂ N := by
  set P := qbdP B A₀ A₁ A₂ with hPdef
  have hsub : (T3 (2 * N) : Set (ℕ × ι)) ⊆ T5 N := by
    intro z hz; simp only [T3, T5, mem_lv] at *; omega
  have hdiff : ∀ z : ℕ × ι, z ∈ T5 N \ T3 (2 * N) ↔ z.1 = N ∨ z.1 = 3 * N := by
    intro z; simp only [T3, T5, Set.mem_sdiff, mem_lv, true_or, or_true, true_and] <;> omega
  have key : ∀ (i : ι) (y : ℕ × ι), firstEntrance P (T3 (2 * N)) (2 * N, i) y =
      (if y ∈ T3 (2 * N) then firstEntrance P (T5 N) (2 * N, i) y else 0) +
      (∑' l, firstEntrance P (T5 N) (2 * N, i) (N, l) * firstEntrance P (T3 (2 * N)) (N, l) y +
       ∑' l, firstEntrance P (T5 N) (2 * N, i) (3 * N, l) *
         firstEntrance P (T3 (2 * N)) (3 * N, l) y) := by
    intro i y
    rw [fe_eq P (T3 (2 * N)) (2 * N, i) y, Fk_CS P hsub, add_ap, mulE_ap, mul_ap, ← fe_eq]
    congr 1
    have e : ∀ z, (Fk P (T5 N) * E (T5 N \ T3 (2 * N))).f (2 * N, i) z * Fk P (T3 (2 * N)) z y =
        if z.1 = N ∨ z.1 = 3 * N then
          firstEntrance P (T5 N) (2 * N, i) z * firstEntrance P (T3 (2 * N)) z y else 0 := by
      intro z
      rw [mulE_ap, fe_eq, fe_eq]
      by_cases hz : z.1 = N ∨ z.1 = 3 * N
      · rw [if_pos ((hdiff z).mpr hz), if_pos hz]
      · rw [if_neg (fun h => hz ((hdiff z).mp h)), if_neg hz, zero_mul]
    rw [tsum_congr e, two_lev _ N (3 * N) (by omega)]
  -- shifted values
  have S1 : ∀ (i : ι) (b : ℕ) (j : ι), firstEntrance P (T5 N) (N + N, i) (b + N, j) =
      firstEntrance P (T3 N) (N, i) (b, j) := by
    intro i b j
    refine (band_shift B A₀ A₁ A₂ (fun n => n = 0 ∨ n = N ∨ n = 2 * N)
      (fun n => n = 0 ∨ n = N ∨ n = 2 * N ∨ n = 3 * N ∨ n = 4 * N) 0 (2 * N) N N (by omega)
      (by omega) (Or.inl rfl) (Or.inr (Or.inr rfl)) (fun n _ _ => ?_) i b j).symm
    constructor <;> intro h <;> omega
  have S2 : ∀ (l : ι) (b : ℕ) (j : ι), firstEntrance P (T3 (2 * N)) (N + 0, l) (b + 0, j) =
      firstEntrance P (T2 N) (N, l) (b, j) := by
    intro l b j
    refine (band_shift B A₀ A₁ A₂ (fun n => n = 0 ∨ n = 2 * N)
      (fun n => n = 0 ∨ n = 2 * N ∨ n = 2 * (2 * N)) 0 (2 * N) N 0 (by omega)
      (by omega) (Or.inl rfl) (Or.inr rfl) (fun n _ _ => ?_) l b j).symm
    constructor <;> intro h <;> omega
  have S3 : ∀ (l : ι) (b : ℕ) (j : ι), firstEntrance P (T3 (2 * N)) (N + 2 * N, l) (b + 2 * N, j) =
      firstEntrance P (T2 N) (N, l) (b, j) := by
    intro l b j
    refine (band_shift B A₀ A₁ A₂ (fun n => n = 0 ∨ n = 2 * N)
      (fun n => n = 0 ∨ n = 2 * N ∨ n = 2 * (2 * N)) 0 (2 * N) N (2 * N) (by omega)
      (by omega) (Or.inl rfl) (Or.inr rfl) (fun n _ _ => ?_) l b j).symm
    constructor <;> intro h <;> omega
  have e2 : N + N = 2 * N := by ring
  have e3 : 2 * N + N = 3 * N := by ring
  have e3' : N + 2 * N = 3 * N := by ring
  have e4 : 2 * N + 2 * N = 2 * (2 * N) := by ring
  have f1 : ∀ i l, firstEntrance P (T5 N) (2 * N, i) (N, l) = K2 B A₀ A₁ A₂ N i l := by
    intro i l; have := S1 i 0 l; rw [e2, zero_add] at this; exact this
  have f2 : ∀ i l, firstEntrance P (T5 N) (2 * N, i) (3 * N, l) = K0 B A₀ A₁ A₂ N i l := by
    intro i l; have := S1 i (2 * N) l; rw [e2, e3] at this; exact this
  have f3 : ∀ i l, firstEntrance P (T5 N) (2 * N, i) (2 * N, l) = K1 B A₀ A₁ A₂ N i l := by
    intro i l; have := S1 i N l; rw [e2] at this; exact this
  have f4 : ∀ i j, firstEntrance P (T5 N) (2 * N, i) (0, j) = 0 := by
    intro i j
    exact fe_zero B A₀ A₁ A₂ (fun n => n = 0 ∨ n = N ∨ n = 2 * N ∨ n = 3 * N ∨ n = 4 * N) N (3 * N)
      (Or.inr (Or.inl rfl)) (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) (2 * N) (by omega) (by omega)
      i 0 j (by omega)
  have f5 : ∀ i j, firstEntrance P (T5 N) (2 * N, i) (2 * (2 * N), j) = 0 := by
    intro i j
    exact fe_zero B A₀ A₁ A₂ (fun n => n = 0 ∨ n = N ∨ n = 2 * N ∨ n = 3 * N ∨ n = 4 * N) N (3 * N)
      (Or.inr (Or.inl rfl)) (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) (2 * N) (by omega) (by omega)
      i (2 * (2 * N)) j (by omega)
  have g1 : ∀ l j, firstEntrance P (T3 (2 * N)) (N, l) (2 * N, j) = HH B A₀ A₁ A₂ N l j := by
    intro l j; have := S2 l (2 * N) j; simp only [add_zero] at this; exact this
  have g2 : ∀ l j, firstEntrance P (T3 (2 * N)) (N, l) (0, j) = LL B A₀ A₁ A₂ N l j := by
    intro l j; have := S2 l 0 j; simp only [add_zero] at this; exact this
  have g3 : ∀ l j, firstEntrance P (T3 (2 * N)) (N, l) (2 * (2 * N), j) = 0 := by
    intro l j; have := S2 l (2 * (2 * N)) j; simp only [add_zero] at this
    rw [this]; exact fe_not_mem _ _ _ _ (by simp only [T2, mem_lv, true_or, or_true, true_and] <;> omega)
  have h1 : ∀ l j, firstEntrance P (T3 (2 * N)) (3 * N, l) (2 * (2 * N), j) = HH B A₀ A₁ A₂ N l j := by
    intro l j; have := S3 l (2 * N) j; rw [e3', e4] at this; exact this
  have h2 : ∀ l j, firstEntrance P (T3 (2 * N)) (3 * N, l) (2 * N, j) = LL B A₀ A₁ A₂ N l j := by
    intro l j; have := S3 l 0 j; rw [e3', zero_add] at this; exact this
  have h3 : ∀ l j, firstEntrance P (T3 (2 * N)) (3 * N, l) (0, j) = 0 := by
    intro l j
    exact fe_zero B A₀ A₁ A₂ (fun n => n = 0 ∨ n = 2 * N ∨ n = 2 * (2 * N)) (2 * N) (2 * (2 * N))
      (Or.inr (Or.inl rfl)) (Or.inr (Or.inr rfl)) (3 * N) (by omega) (by omega) l 0 j (by omega)
  refine ⟨?_, ?_, ?_⟩
  · apply Ker.ext; intro i j
    show firstEntrance P (T3 (2 * N)) (2 * N, i) (2 * (2 * N), j) = _
    rw [key, if_pos (by simp only [T3, mem_lv, true_or, or_true, true_and] <;> omega), mul_ap]
    simp only [f1, f2, f5, g3, h1, mul_zero, tsum_zero, zero_add]
  · apply Ker.ext; intro i j
    show firstEntrance P (T3 (2 * N)) (2 * N, i) (2 * N, j) = _
    rw [key, if_pos (by simp only [T3, mem_lv, true_or, or_true, true_and] <;> omega), add_ap, add_ap, mul_ap, mul_ap]
    simp only [f1, f2, f3, g1, h2]
  · apply Ker.ext; intro i j
    show firstEntrance P (T3 (2 * N)) (2 * N, i) (0, j) = _
    rw [key, if_pos (by simp only [T3, mem_lv, true_or, or_true, true_and] <;> omega), mul_ap]
    simp only [f1, f2, f4, g2, h3, mul_zero, tsum_zero, zero_add, add_zero]

lemma fe_one (b : ℕ) (hb : b ≤ 2) (i j : ι) :
    firstEntrance (qbdP B A₀ A₁ A₂) (T3 1) (1, i) (b, j) =
      ENNReal.ofReal (qbdP B A₀ A₁ A₂ (1, i) (b, j)) := by
  rw [g72mab_fe _ _ _ _ (show (b, j) ∈ T3 1 by simp only [T3, mem_lv, true_or, or_true, true_and] <;> omega), tsum_eq_single 0]
  · exact g72mab_PS_one _ _ _ _
  · intro t ht
    obtain ⟨s, rfl⟩ := Nat.exists_eq_succ_of_ne_zero ht
    rw [g72mab_PS_cons]
    refine ENNReal.tsum_eq_zero.mpr fun z => ?_
    by_cases hz : qbdP B A₀ A₁ A₂ (1, i) z = 0
    · simp [hz]
    · have := g72mab_qnz B A₀ A₁ A₂ (1, i) z hz
      rw [if_neg, mul_zero]
      rintro (h | h)
      · omega
      · apply h; simp only [T3, mem_lv]; simp only at this; omega

lemma K_one : K0 B A₀ A₁ A₂ 1 = ⟨ennMat A₀⟩ ∧ K1 B A₀ A₁ A₂ 1 = ⟨ennMat A₁⟩ ∧
    K2 B A₀ A₁ A₂ 1 = ⟨ennMat A₂⟩ := by
  refine ⟨Ker.ext fun i j => ?_, Ker.ext fun i j => ?_, Ker.ext fun i j => ?_⟩
  · show firstEntrance _ _ _ _ = _
    rw [fe_one B A₀ A₁ A₂ _ (by norm_num)]
    simp [qbdP, ennMat]
  · show firstEntrance _ _ _ _ = _
    rw [fe_one B A₀ A₁ A₂ _ (by norm_num)]
    simp [qbdP, ennMat]
  · show firstEntrance _ _ _ _ = _
    rw [fe_one B A₀ A₁ A₂ _ (by norm_num)]
    simp [qbdP, ennMat]

end Blocks
end

/-! ## Main argument -/

noncomputable section
section Main
variable {ι : Type*} [Countable ι] [DecidableEq ι] (B A₀ A₁ A₂ : ι → ι → ℝ)

lemma pow_f (M : ι → ι → ℝ≥0∞) : ∀ n : ℕ, ((⟨M⟩ : Ker ι) ^ n).f = matPowE M n
  | 0 => rfl
  | n + 1 => by
    rw [pow_succ]
    show matMulE ((⟨M⟩ : Ker ι) ^ n).f M = _
    rw [pow_f M n]; rfl

lemma ser_f (M : ι → ι → ℝ≥0∞) : (ser (⟨M⟩ : Ker ι)).f = seriesInvE M := by
  funext i j
  show ∑' n, ((⟨M⟩ : Ker ι) ^ n).f i j = _
  unfold seriesInvE
  simp only [pow_f]

lemma alg (K0 K1 K2 H L : Ker ι) (hH : H = ser K1 * K0) (hL : L = ser K1 * K2) :
    ser (K1 + (K2 * H + K0 * L)) * (K0 * H) = ser (H * L + L * H) * (H * H) ∧
    ser (K1 + (K2 * H + K0 * L)) * (K2 * L) = ser (H * L + L * H) * (L * L) ∧
    ser (H * L + L * H) ≤ ser (K1 + (K2 * H + K0 * L)) := by
  have hD : ser K1 * (K2 * H + K0 * L) = H * L + L * H := by
    rw [mul_add, ← mul_assoc, ← mul_assoc, ← hH, ← hL, add_comm]
  rw [ser_resolvent, hD]
  refine ⟨?_, ?_, ?_⟩
  · rw [mul_assoc, ← mul_assoc (ser K1), ← hH]
  · rw [mul_assoc, ← mul_assoc (ser K1), ← hL]
  · calc ser (H * L + L * H) = ser (H * L + L * H) * 1 := (mul_one _).symm
      _ ≤ _ := kmul_mono le_rfl (one_le_ser K1)

lemma hHL (k : ℕ) : logH A₀ A₁ A₂ k = (HH B A₀ A₁ A₂ (2 ^ k)).f ∧
    logL A₀ A₁ A₂ k = (LL B A₀ A₁ A₂ (2 ^ k)).f := by
  induction k with
  | zero =>
    obtain ⟨h0, h1, h2⟩ := K_one B A₀ A₁ A₂
    obtain ⟨hH, hL⟩ := KA B A₀ A₁ A₂ 1 le_rfl
    rw [pow_zero, hH, hL, h0, h1, h2]
    constructor
    · show matMulE (seriesInvE (ennMat A₁)) (ennMat A₀) =
        matMulE (ser (⟨ennMat A₁⟩ : Ker ι)).f (ennMat A₀)
      rw [ser_f]
    · show matMulE (seriesInvE (ennMat A₁)) (ennMat A₂) =
        matMulE (ser (⟨ennMat A₁⟩ : Ker ι)).f (ennMat A₂)
      rw [ser_f]
  | succ k ih =>
    have hN : 1 ≤ 2 ^ k := Nat.one_le_two_pow
    have e : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [pow_succ]; ring
    rw [e]
    obtain ⟨hH, hL⟩ := KA B A₀ A₁ A₂ (2 * 2 ^ k) (by omega)
    obtain ⟨c0, c1, c2⟩ := KC B A₀ A₁ A₂ (2 ^ k) hN
    obtain ⟨hH', hL'⟩ := KA B A₀ A₁ A₂ (2 ^ k) hN
    obtain ⟨a1, a2, -⟩ := alg _ _ _ _ _ hH' hL'
    rw [hH, hL, c0, c1, c2, a1, a2]
    have hU : logU A₀ A₁ A₂ k = (HH B A₀ A₁ A₂ (2 ^ k) * LL B A₀ A₁ A₂ (2 ^ k) +
        LL B A₀ A₁ A₂ (2 ^ k) * HH B A₀ A₁ A₂ (2 ^ k)).f := by
      unfold logU; rw [ih.1, ih.2]; rfl
    constructor
    · show matMulE (seriesInvE (logU A₀ A₁ A₂ k)) (matMulE (logH A₀ A₁ A₂ k) (logH A₀ A₁ A₂ k)) = _
      rw [hU, ih.1, ← ser_f]; rfl
    · show matMulE (seriesInvE (logU A₀ A₁ A₂ k)) (matMulE (logL A₀ A₁ A₂ k) (logL A₀ A₁ A₂ k)) = _
      rw [hU, ih.2, ← ser_f]; rfl

theorem main (hP : IsStochasticC (qbdP B A₀ A₁ A₂)) (hirr : IrreducibleC (qbdP B A₀ A₁ A₂)) :
    (∀ i j : ι, seriesInvE (ennMat A₁) i j ≠ ⊤) ∧
    ∀ k : ℕ,
      logH A₀ A₁ A₂ k = hitUp (qbdP B A₀ A₁ A₂) k ∧
      logL A₀ A₁ A₂ k = hitDown (qbdP B A₀ A₁ A₂) k ∧
      (∀ i : ι, ∑' j : ι, logU A₀ A₁ A₂ k i j ≤ 1) ∧
      ∀ i j : ι, seriesInvE (logU A₀ A₁ A₂ k) i j ≠ ⊤ := by
  have hrow : Pk (qbdP B A₀ A₁ A₂) * J = J := by
    apply Ker.ext; intro x y
    rw [mul_ap]
    simp only [J_ap, mul_one, Pk_ap]
    rw [← ENNReal.ofReal_tsum_of_nonneg (hP.1 x) (hP.2 x).summable, (hP.2 x).tsum_eq,
      ENNReal.ofReal_one]
  have K1fin : ∀ N, 1 ≤ N → ∀ i j, ser (K1 B A₀ A₁ A₂ N) i j ≠ ⊤ := by
    intro N hN i j
    rw [← blkX B A₀ A₁ A₂ N hN, ← blk_ser _ N (X_zero B A₀ A₁ A₂ N hN)]
    obtain ⟨t, ht⟩ := hirr (N, j) (0, j)
    have hne : (Pk (qbdP B A₀ A₁ A₂) ^ t).f (N, j) (0, j) ≠ 0 := by
      intro h0
      have := stepPow_le _ hP.1 t (N, j) (0, j)
      rw [h0] at this
      exact (ENNReal.ofReal_pos.mpr ht).ne' (le_antisymm this bot_le)
    have hfin := ser_fin _ hrow (T2 N) (N, j) (0, j)
      (by simp only [T2, mem_lv, true_or, or_true, true_and] <;> omega)
      (by simp only [T2, mem_lv, true_or, or_true, true_and] <;> omega) t hne (N, i)
    refine ne_top_of_le_ne_top hfin ?_
    rw [ser_split _ (T2_sub N)]
    calc (ser (Fk (qbdP B A₀ A₁ A₂) (T3 N) * E (T3 N \ T2 N))).f (N, i) (N, j)
        = (ser (Fk (qbdP B A₀ A₁ A₂) (T3 N) * E (T3 N \ T2 N)) * 1).f (N, i) (N, j) := by
          rw [mul_one]
      _ ≤ _ := kmul_mono le_rfl (one_le_ser _) _ _
  have rowHL : ∀ N, 1 ≤ N → ∀ l,
      ∑' j, HH B A₀ A₁ A₂ N l j + ∑' j, LL B A₀ A₁ A₂ N l j ≤ 1 := by
    intro N hN l
    have h := Fk_row _ hrow (T2 N) (N, l) (N, l)
    have h' : (Fk (qbdP B A₀ A₁ A₂) (T2 N) * J).f (N, l) (N, l) =
        ∑' z, Fk (qbdP B A₀ A₁ A₂) (T2 N) (N, l) z := by
      rw [mul_ap]; simp only [J_ap, mul_one]
    rw [h'] at h
    calc ∑' j, HH B A₀ A₁ A₂ N l j + ∑' j, LL B A₀ A₁ A₂ N l j
        = ∑' z : ℕ × ι, (if z.1 = 2 * N ∨ z.1 = 0 then
            firstEntrance (qbdP B A₀ A₁ A₂) (T2 N) (N, l) z else 0) :=
          (two_lev (fun z => firstEntrance (qbdP B A₀ A₁ A₂) (T2 N) (N, l) z) (2 * N) 0
            (by omega)).symm
      _ ≤ ∑' z, Fk (qbdP B A₀ A₁ A₂) (T2 N) (N, l) z :=
          ENNReal.tsum_le_tsum fun z => by rw [← fe_eq]; split_ifs <;> simp
      _ ≤ 1 := h
  refine ⟨fun i j => ?_, fun k => ?_⟩
  · have := K1fin 1 le_rfl i j
    rw [(K_one B A₀ A₁ A₂).2.1, ser_f] at this
    exact this
  have hN : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  have e : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [pow_succ]; ring
  obtain ⟨eH, eL⟩ := hHL B A₀ A₁ A₂ k
  have hset : (level 0 ∪ level (2 ^ (k + 1)) : Set (ℕ × ι)) = T2 (2 ^ k) := by
    rw [e]; ext z; simp [level, T2, lv]
  have hU : logU A₀ A₁ A₂ k = (HH B A₀ A₁ A₂ (2 ^ k) * LL B A₀ A₁ A₂ (2 ^ k) +
      LL B A₀ A₁ A₂ (2 ^ k) * HH B A₀ A₁ A₂ (2 ^ k)).f := by
    unfold logU; rw [eH, eL]; rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [eH]; funext i j
    show firstEntrance _ (T2 (2 ^ k)) (2 ^ k, i) (2 * 2 ^ k, j) = _
    unfold hitUp; rw [e, ← hset, e]
  · rw [eL]; funext i j
    show firstEntrance _ (T2 (2 ^ k)) (2 ^ k, i) (0, j) = _
    unfold hitDown; rw [← hset]
  · intro i
    have hr := rowHL (2 ^ k) hN
    rw [hU]
    show ∑' j, ((HH B A₀ A₁ A₂ (2 ^ k) * LL B A₀ A₁ A₂ (2 ^ k)).f i j +
      (LL B A₀ A₁ A₂ (2 ^ k) * HH B A₀ A₁ A₂ (2 ^ k)).f i j) ≤ 1
    simp only [mul_ap]
    have e1 : ∀ X Y : Ker ι, ∑' j, ∑' l, X i l * Y l j = ∑' l, X i l * ∑' j, Y l j := by
      intro X Y
      rw [ENNReal.tsum_comm]
      simp_rw [ENNReal.tsum_mul_left]
    rw [ENNReal.tsum_add, e1, e1]
    calc ∑' l, HH B A₀ A₁ A₂ (2 ^ k) i l * ∑' j, LL B A₀ A₁ A₂ (2 ^ k) l j +
          ∑' l, LL B A₀ A₁ A₂ (2 ^ k) i l * ∑' j, HH B A₀ A₁ A₂ (2 ^ k) l j
        ≤ ∑' l, HH B A₀ A₁ A₂ (2 ^ k) i l * 1 + ∑' l, LL B A₀ A₁ A₂ (2 ^ k) i l * 1 := by
          gcongr with l l
          · exact le_trans le_add_self (hr l)
          · exact le_trans le_self_add (hr l)
      _ ≤ 1 := by simp only [mul_one]; exact hr i
  · intro i j
    have c1 := (KC B A₀ A₁ A₂ (2 ^ k) hN).2.1
    obtain ⟨hH', hL'⟩ := KA B A₀ A₁ A₂ (2 ^ k) hN
    have a3 := (alg _ _ _ _ _ hH' hL').2.2
    rw [← c1] at a3
    rw [hU, ← ser_f]
    exact ne_top_of_le_ne_top (K1fin (2 * 2 ^ k) (by omega) i j) (a3 i j)

end Main
end


/-! ## Products of `H^{[i]}` as first passages from level 1 -/

noncomputable section
section PF
variable {ι : Type*} [Countable ι] [DecidableEq ι] (B A₀ A₁ A₂ : ι → ι → ℝ)
open Classical

lemma fe_split (P : ℕ × ι → ℕ × ι → ℝ) (T W : Set (ℕ × ι)) (x y : ℕ × ι) (hx : x ∉ W)
    (hy : y ∈ T) :
    firstEntrance P T x y = firstEntranceAfter P T W x y + firstEntrance P (T ∪ W) x y := by
  unfold firstEntrance firstEntranceAfter
  rw [← ENNReal.tsum_add]
  refine tsum_congr fun t => ?_
  rw [← ENNReal.tsum_add]
  refine tsum_congr fun ω => ?_
  by_cases hA : ω 0 = x ∧ ω (Fin.last (t + 1)) = y ∧ y ∈ T ∧
      ∀ m : Fin (t + 2), m ≠ 0 → m ≠ Fin.last (t + 1) → ω m ∉ T
  · by_cases hc : ∃ s : Fin (t + 2), s ≠ Fin.last (t + 1) ∧ ω s ∈ W
    · rw [if_pos hA, if_pos ⟨hA.1, hA.2.1, hA.2.2.1, hA.2.2.2, hc⟩, if_neg, add_zero]
      rintro ⟨h0, -, -, hm⟩
      obtain ⟨s, hs, hsW⟩ := hc
      by_cases hs0 : s = 0
      · subst hs0; exact hx (by rw [← h0]; exact hsW)
      · exact hm s hs0 hs (Or.inr hsW)
    · rw [if_pos hA, if_neg (fun h => hc h.2.2.2.2), if_pos, zero_add]
      refine ⟨hA.1, hA.2.1, Or.inl hA.2.2.1, fun m h0 hl hm => ?_⟩
      rcases hm with hm | hm
      · exact hA.2.2.2 m h0 hl hm
      · exact hc ⟨m, hl, hm⟩
  · rw [if_neg hA, if_neg (fun h => hA ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩), if_neg, zero_add]
    rintro ⟨h0, h1, -, hm⟩
    exact hA ⟨h0, h1, hy, fun m a b c => hm m a b (Or.inl c)⟩

lemma after_self (P : ℕ × ι → ℕ × ι → ℝ) (T W : Set (ℕ × ι)) (x y : ℕ × ι) (hx : x ∈ W) :
    firstEntranceAfter P T W x y = firstEntrance P T x y := by
  unfold firstEntrance firstEntranceAfter
  refine tsum_congr fun t => tsum_congr fun ω => ?_
  by_cases hA : ω 0 = x ∧ ω (Fin.last (t + 1)) = y ∧ y ∈ T ∧
      ∀ m : Fin (t + 2), m ≠ 0 → m ≠ Fin.last (t + 1) → ω m ∉ T
  · rw [if_pos hA, if_pos ⟨hA.1, hA.2.1, hA.2.2.1, hA.2.2.2, 0,
      by simp [Fin.ext_iff], by rw [hA.1]; exact hx⟩]
  · rw [if_neg hA, if_neg (fun h => hA ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩)]

lemma Fk_le_one (P : ℕ × ι → ℕ × ι → ℝ) (hrow : Pk P * J = J) (T : Set (ℕ × ι))
    (x y : ℕ × ι) : Fk P T x y ≤ 1 := by
  have h := Fk_row P hrow T x x
  have h' : (Fk P T * J).f x x = ∑' z, Fk P T x z := by
    rw [mul_ap]; simp only [J_ap, mul_one]
  rw [h'] at h
  exact le_trans (ENNReal.le_tsum y) h

lemma setT2 (N : ℕ) : (level 0 ∪ level (2 * N) : Set (ℕ × ι)) = T2 N := by
  ext z; simp only [level, T2, lv, Set.mem_union, Set.mem_setOf_eq]

lemma setT3 (N : ℕ) : (level 0 ∪ level (2 * N) ∪ level N : Set (ℕ × ι)) = T3 N := by
  ext z; simp only [level, T3, lv, Set.mem_union, Set.mem_setOf_eq]; tauto

lemma setL (N : ℕ) : (level 0 ∪ level N : Set (ℕ × ι)) = lv (fun n => n = 0 ∨ n = N) := by
  ext z; simp only [level, lv, Set.mem_union, Set.mem_setOf_eq]

lemma low_eq (N : ℕ) (hN : 2 ≤ N) (i l : ι) :
    firstEntrance (qbdP B A₀ A₁ A₂) (level 0 ∪ level N) (1, i) (N, l) =
      firstEntrance (qbdP B A₀ A₁ A₂) (T3 N) (1, i) (N, l) := by
  rw [setL]
  have := band_shift B A₀ A₁ A₂ (fun n => n = 0 ∨ n = N) (fun n => n = 0 ∨ n = N ∨ n = 2 * N)
    0 N 1 0 (by omega) (by omega) (Or.inl rfl) (Or.inr rfl)
    (fun n _ hn => by constructor <;> intro h <;> omega) i N l
  simp only [add_zero] at this
  exact this

lemma split (N : ℕ) (hN : 2 ≤ N) (i : ι) (y : ℕ × ι) (hy : y.1 = 0 ∨ y.1 = 2 * N) :
    firstEntrance (qbdP B A₀ A₁ A₂) (level 0 ∪ level (2 * N)) (1, i) y =
      firstEntrance (qbdP B A₀ A₁ A₂) (level 0 ∪ level (2 * N) ∪ level N) (1, i) y +
      ∑' l, firstEntrance (qbdP B A₀ A₁ A₂) (level 0 ∪ level N) (1, i) (N, l) *
        firstEntrance (qbdP B A₀ A₁ A₂) (level 0 ∪ level (2 * N)) (N, l) y := by
  rw [setT3, setT2, fe_eq, fe_eq]
  conv_lhs => rw [Fk_CS _ (T2_sub N)]
  rw [add_ap]
  have hyT : y ∈ T2 N := by
    show y.1 = 0 ∨ y.1 = 2 * N; exact hy
  have hD : ∀ z : ℕ × ι, z ∈ (T3 N \ T2 N) ↔ z.1 = N := by
    intro z
    simp only [T3, T2, lv, Set.mem_diff, Set.mem_setOf_eq]
    omega
  congr 1
  · rw [mulE_ap, if_pos hyT]
  · rw [mul_ap, lev_sum _ N]
    · refine tsum_congr fun l => ?_
      rw [mulE_ap, if_pos ((hD _).mpr rfl), low_eq B A₀ A₁ A₂ N hN, fe_eq, fe_eq]
    · intro z hz
      rw [mulE_ap, if_neg (fun h => hz ((hD z).mp h)), zero_mul]

lemma up_step (N : ℕ) (hN : 2 ≤ N) (i j : ι) :
    firstEntrance (qbdP B A₀ A₁ A₂) (level 0 ∪ level (2 * N)) (1, i) (2 * N, j) =
      ∑' l, firstEntrance (qbdP B A₀ A₁ A₂) (level 0 ∪ level N) (1, i) (N, l) *
        firstEntrance (qbdP B A₀ A₁ A₂) (level 0 ∪ level (2 * N)) (N, l) (2 * N, j) := by
  rw [split B A₀ A₁ A₂ N hN i _ (Or.inr rfl), setT3]
  have := fe_zero B A₀ A₁ A₂ (fun n => n = 0 ∨ n = N ∨ n = 2 * N) 0 N (Or.inl rfl)
    (Or.inr (Or.inl rfl)) 1 (by omega) (by omega) i (2 * N) j (by omega)
  rw [show T3 N = lv (fun n => n = 0 ∨ n = N ∨ n = 2 * N) from rfl, this, zero_add]

lemma down_step (hrow : Pk (qbdP B A₀ A₁ A₂) * J = J) (N : ℕ) (hN : 2 ≤ N) (i j : ι) :
    firstEntranceAfter (qbdP B A₀ A₁ A₂) (level 0 ∪ level (2 * N)) (level N) (1, i) (0, j) =
      ∑' l, firstEntrance (qbdP B A₀ A₁ A₂) (level 0 ∪ level N) (1, i) (N, l) *
        firstEntrance (qbdP B A₀ A₁ A₂) (level 0 ∪ level (2 * N)) (N, l) (0, j) := by
  have h1 := fe_split (qbdP B A₀ A₁ A₂) (level 0 ∪ level (2 * N)) (level N) (1, i) (0, j)
    (by show ¬ (1 = N); omega) (Or.inl rfl)
  have h2 := split B A₀ A₁ A₂ N hN i (0, j) (Or.inl rfl)
  rw [h1] at h2
  have hfin : firstEntrance (qbdP B A₀ A₁ A₂) (level 0 ∪ level (2 * N) ∪ level N) (1, i) (0, j)
      ≠ ⊤ := by
    rw [fe_eq]; exact ne_top_of_le_ne_top ENNReal.one_ne_top (Fk_le_one _ hrow _ _ _)
  rw [add_comm (firstEntrance _ _ _ _) (tsum _)] at h2
  exact (ENNReal.add_left_inj hfin).mp h2

lemma one_mulE (M : ι → ι → ℝ≥0∞) : matMulE matOneE M = M := by
  funext i j
  unfold matMulE matOneE
  rw [tsum_eq_single i]
  · simp
  · intro b hb; simp [Ne.symm hb]

theorem pf_main (hP : IsStochasticC (qbdP B A₀ A₁ A₂)) (hirr : IrreducibleC (qbdP B A₀ A₁ A₂)) :
    ∀ k : ℕ,
      prodH A₀ A₁ A₂ (k + 1) = hitUpFromOne (qbdP B A₀ A₁ A₂) k ∧
      matMulE (prodH A₀ A₁ A₂ k) (logL A₀ A₁ A₂ k) =
        hitDownInBand (qbdP B A₀ A₁ A₂) k := by
  have hrow : Pk (qbdP B A₀ A₁ A₂) * J = J := by
    apply Ker.ext; intro x y
    rw [mul_ap]
    simp only [J_ap, mul_one, Pk_ap]
    rw [← ENNReal.ofReal_tsum_of_nonneg (hP.1 x) (hP.2 x).summable, (hP.2 x).tsum_eq,
      ENNReal.ofReal_one]
  have HM := (main B A₀ A₁ A₂ hP hirr).2
  have up : ∀ k, prodH A₀ A₁ A₂ (k + 1) = hitUpFromOne (qbdP B A₀ A₁ A₂) k := by
    intro k
    induction k with
    | zero =>
      show matMulE matOneE (logH A₀ A₁ A₂ 0) = _
      rw [one_mulE, (HM 0).1]
      funext i j
      simp only [hitUp, hitUpFromOne, pow_zero]
    | succ k ih =>
      show matMulE (prodH A₀ A₁ A₂ (k + 1)) (logH A₀ A₁ A₂ (k + 1)) = _
      rw [ih, (HM (k + 1)).1]
      funext i j
      have e : 2 ^ (k + 1 + 1) = 2 * 2 ^ (k + 1) := by rw [pow_succ]; ring
      simp only [hitUp, hitUpFromOne, matMulE]
      rw [e]
      exact (up_step B A₀ A₁ A₂ (2 ^ (k + 1)) (by
        have := Nat.one_le_two_pow (n := k); rw [pow_succ]; omega) i j).symm
  intro k
  refine ⟨up k, ?_⟩
  cases k with
  | zero =>
    show matMulE matOneE (logL A₀ A₁ A₂ 0) = _
    rw [one_mulE, (HM 0).2.1]
    funext i j
    simp only [hitDown, hitDownInBand, pow_zero]
    rw [after_self]
    rfl
  | succ k =>
    rw [up k, (HM (k + 1)).2.1]
    funext i j
    have e : 2 ^ (k + 1 + 1) = 2 * 2 ^ (k + 1) := by rw [pow_succ]; ring
    simp only [hitDown, hitDownInBand, hitUpFromOne, matMulE]
    rw [e]
    exact (down_step B A₀ A₁ A₂ hrow (2 ^ (k + 1)) (by
      have := Nat.one_le_two_pow (n := k); rw [pow_succ]; omega) i j).symm

end PF
end

end S202PF

open MatrixAnalytic.LogReduction in
open scoped ENNReal in
theorem solution {ι : Type*} [Countable ι] [DecidableEq ι]
    (B A₀ A₁ A₂ : ι → ι → ℝ)
    (hP : IsStochasticC (qbdP B A₀ A₁ A₂))
    (hirr : IrreducibleC (qbdP B A₀ A₁ A₂)) :
    ∀ k : ℕ,
      prodH A₀ A₁ A₂ (k + 1) = hitUpFromOne (qbdP B A₀ A₁ A₂) k ∧
      matMulE (prodH A₀ A₁ A₂ k) (logL A₀ A₁ A₂ k) =
        hitDownInBand (qbdP B A₀ A₁ A₂) k :=
  S202PF.pf_main B A₀ A₁ A₂ hP hirr
