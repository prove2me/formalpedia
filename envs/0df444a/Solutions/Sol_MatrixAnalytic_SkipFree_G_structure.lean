-- Prove2me | solution 1 for MatrixAnalytic.SkipFree.G_structure
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T04:32:09.686796+00:00
-- url     : https://prove2.me/submissions/695f07a7-8459-43d4-b12b-f32836eb3446

import Mathlib
import Definitions.Def_MatrixAnalytic_SkipFree_Chain
import Definitions.Def_MatrixAnalytic_SkipFree_QBD
import Definitions.Def_MatrixAnalytic_SkipFree_Passage
import Definitions.Def_MatrixAnalytic_SkipFree_Models

open scoped ENNReal
open MatrixAnalytic.SkipFree
open Classical in
noncomputable def g77b_fe {V : Type*} (P : V → V → ℝ) (T : Set V) (t : ℕ) (x y : V) : ℝ≥0∞ :=
  ∑' ω : Fin (t + 2) → V,
    if ω 0 = x ∧ ω (Fin.last (t + 1)) = y ∧ y ∈ T ∧
        ∀ m : Fin (t + 2), m ≠ 0 → m ≠ Fin.last (t + 1) → ω m ∉ T
    then pathWeightE P ω else 0

lemma g77b_FE {V : Type*} (P : V → V → ℝ) (T : Set V) (x y : V) :
    firstEntrance P T x y = ∑' t, g77b_fe P T t x y := rfl

lemma g77b_pw_cons {V : Type*} (P : V → V → ℝ) {n : ℕ} (ω : Fin (n + 1) → V) (k : V) :
    pathWeightE P (Fin.cons k ω : Fin (n + 2) → V) = ENNReal.ofReal (P k (ω 0)) * pathWeightE P ω := by
  unfold pathWeightE
  rw [Fin.prod_univ_succ]
  congr 1

open Classical in
lemma g77b_fe_zero {V : Type*} (P : V → V → ℝ) (T : Set V) (x y : V) :
    g77b_fe P T 0 x y = if y ∈ T then ENNReal.ofReal (P x y) else 0 := by
  unfold g77b_fe
  rw [tsum_eq_single (fun m : Fin 2 => if m = 0 then x else y)]
  · by_cases hy : y ∈ T
    · have hI : ∀ m : Fin 2, m ≠ 0 → m ≠ Fin.last 1 →
          (fun m : Fin 2 => if m = 0 then x else y) m ∉ T := by
        intro m h0 h1; exfalso; fin_cases m <;> simp_all
      rw [if_pos ⟨by simp, by simp, hy, hI⟩, if_pos hy]
      simp [pathWeightE]
    · rw [if_neg (by tauto), if_neg hy]
  · intro ω hω
    rw [if_neg]
    rintro ⟨h0, h1, -, -⟩
    apply hω; funext m; fin_cases m
    · simpa using h0
    · simpa using h1

open Classical in
lemma g77b_fe_succ {V : Type*} (P : V → V → ℝ) (T : Set V) (t : ℕ) (x y : V) :
    g77b_fe P T (t + 1) x y =
      ∑' z, ENNReal.ofReal (P x z) * (if z ∈ T then 0 else g77b_fe P T t z y) := by
  unfold g77b_fe
  rw [← (Fin.consEquiv (fun _ => V)).tsum_eq, ENNReal.tsum_prod']
  rw [tsum_eq_single x]
  · have hR : ∀ z, ENNReal.ofReal (P x z) * (if z ∈ T then 0 else ∑' ω : Fin (t + 2) → V,
        if ω 0 = z ∧ ω (Fin.last (t + 1)) = y ∧ y ∈ T ∧
          ∀ m : Fin (t + 2), m ≠ 0 → m ≠ Fin.last (t + 1) → ω m ∉ T
        then pathWeightE P ω else 0) =
        ∑' ω : Fin (t + 2) → V, (if z ∈ T then 0 else
          if ω 0 = z ∧ ω (Fin.last (t + 1)) = y ∧ y ∈ T ∧
          ∀ m : Fin (t + 2), m ≠ 0 → m ≠ Fin.last (t + 1) → ω m ∉ T
          then ENNReal.ofReal (P x z) * pathWeightE P ω else 0) := by
      intro z
      split_ifs with hz
      · simp
      · rw [← ENNReal.tsum_mul_left]
        refine tsum_congr fun ω => ?_
        split_ifs <;> simp
    simp_rw [hR]
    rw [ENNReal.tsum_comm]
    refine tsum_congr fun ω => ?_
    rw [tsum_eq_single (ω 0)]
    · rw [show (Fin.consEquiv (fun _ => V)) (x, ω) = Fin.cons x ω from rfl]
      simp only [Fin.cons_zero, true_and]
      rw [g77b_pw_cons]
      have hl : (Fin.last (t + 2) : Fin (t + 3)) = (Fin.last (t + 1)).succ := rfl
      by_cases h0 : ω 0 ∈ T
      · rw [if_pos h0, if_neg]
        rintro ⟨-, -, hI⟩
        have h1 : (1 : Fin (t + 3)) ≠ Fin.last (t + 2) := by
          intro h; have := congrArg Fin.val h; simp at this
        exact hI 1 (by simp) h1 (by simpa using h0)
      · rw [if_neg h0]
        congr 1
        apply propext
        rw [hl, Fin.cons_succ]
        constructor
        · rintro ⟨h1, h2, h3⟩
          exact ⟨h1, h2, fun m hm hm' => by
            have := h3 m.succ (Fin.succ_ne_zero _) (fun h => hm' (Fin.succ_injective _ h))
            simpa using this⟩
        · rintro ⟨h1, h2, h3⟩
          refine ⟨h1, h2, fun m hm hm' => ?_⟩
          cases m using Fin.cases with
          | zero => exact absurd rfl hm
          | succ m =>
            rw [Fin.cons_succ]
            by_cases hm0 : m = 0
            · subst hm0; exact h0
            · exact h3 m hm0 (fun h => hm' (by rw [h]))
    · intro z hz
      split_ifs with h1 h2
      · rfl
      · exact absurd h2.1 (Ne.symm hz)
      · rfl
  · intro a ha
    apply ENNReal.tsum_eq_zero.mpr
    intro ω
    rw [if_neg]
    rintro ⟨h, -⟩
    exact ha (by simpa using h)

lemma g77b_skip {κ : Type*} (B A0 A1 A2 : κ → κ → ℝ) (x y : ℕ × κ)
    (h : qbdP B A0 A1 A2 x y ≠ 0) : x.1 ≤ y.1 + 1 := by
  unfold qbdP at h
  split_ifs at h <;> first | omega | exact absurd rfl h

lemma g77b_hom {κ : Type*} (B A0 A1 A2 : κ → κ → ℝ) (a b c : ℕ) (p q : κ) (ha : 1 ≤ a) :
    qbdP B A0 A1 A2 (a + c, p) (b + c, q) = qbdP B A0 A1 A2 (a, p) (b, q) := by
  unfold qbdP
  simp only
  split_ifs <;> first | rfl | omega

lemma g77b_reindex {κ : Type*} (f : ℕ × κ → ℝ≥0∞) (K : ℕ) (hf : ∀ z, z.1 < K → f z = 0) :
    ∑' z, f z = ∑' w : ℕ × κ, f (w.1 + K, w.2) := by
  symm
  apply Function.Injective.tsum_eq (g := fun w : ℕ × κ => (w.1 + K, w.2))
  · intro a b h
    simp only [Prod.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    ext
    · omega
    · exact h2
  · intro z hz
    refine ⟨(z.1 - K, z.2), ?_⟩
    by_cases h : z.1 < K
    · exact absurd (hf z h) hz
    · ext
      · dsimp only; omega
      · rfl

lemma g77b_mem_level {κ : Type*} (n : ℕ) (z : ℕ × κ) : z ∈ (level n : Set (ℕ × κ)) ↔ z.1 = n :=
  Iff.rfl

open Classical in
lemma g77b_shift {κ : Type*} (B A0 A1 A2 : κ → κ → ℝ) (L : ℕ) :
    ∀ (t e : ℕ) (p q : κ), g77b_fe (qbdP B A0 A1 A2) (level L) t (L + 1 + e, p) (L, q) =
      g77b_fe (qbdP B A0 A1 A2) (level 0) t (1 + e, p) (0, q) := by
  intro t
  induction t with
  | zero =>
    intro e p q
    rw [g77b_fe_zero, g77b_fe_zero, if_pos (by rfl), if_pos (by rfl)]
    congr 1
    have := g77b_hom B A0 A1 A2 (1 + e) 0 L p q (by omega)
    rw [← this]; congr 2 <;> omega
  | succ t ih =>
    intro e p q
    rw [g77b_fe_succ, g77b_fe_succ]
    have eL := g77b_reindex (fun z => ENNReal.ofReal (qbdP B A0 A1 A2 (L + 1 + e, p) z) *
      (if z ∈ level L then 0 else g77b_fe (qbdP B A0 A1 A2) (level L) t z (L, q))) (L + 1) (by
        intro z hz
        by_cases h : z.1 = L
        · rw [if_pos (show z ∈ level L from h)]; simp
        · have : qbdP B A0 A1 A2 (L + 1 + e, p) z = 0 := by
            by_contra hne; have := g77b_skip B A0 A1 A2 _ _ hne; simp at this; omega
          rw [this]; simp)
    have eR := g77b_reindex (fun z => ENNReal.ofReal (qbdP B A0 A1 A2 (1 + e, p) z) *
      (if z ∈ level 0 then 0 else g77b_fe (qbdP B A0 A1 A2) (level 0) t z (0, q))) 1 (by
        intro z hz
        have h : z.1 = 0 := by omega
        rw [if_pos (show z ∈ level 0 from h)]; simp)
    rw [eL, eR]
    refine tsum_congr fun w => ?_
    rw [if_neg (by rw [g77b_mem_level]; dsimp only; omega),
      if_neg (by rw [g77b_mem_level]; dsimp only; omega)]
    have h1 := g77b_hom B A0 A1 A2 (1 + e) (w.1 + 1) L p w.2 (by omega)
    have h2 : (w.1 + (L + 1), w.2) = (L + 1 + w.1, w.2) := by
      ext
      · dsimp only; omega
      · rfl
    have h3 : (w.1 + 1, w.2) = (1 + w.1, w.2) := by
      ext
      · dsimp only; omega
      · rfl
    rw [h2, ih w.1 w.2 q, h3]
    congr 2
    rw [← h3, ← h1]; congr 2 <;> omega

lemma g77b_fe0_far {κ : Type*} (B A0 A1 A2 : κ → κ → ℝ) (T : Set (ℕ × κ)) (x y : ℕ × κ)
    (h : y.1 + 2 ≤ x.1) : g77b_fe (qbdP B A0 A1 A2) T 0 x y = 0 := by
  rw [g77b_fe_zero]
  have : qbdP B A0 A1 A2 x y = 0 := by
    by_contra hne; have := g77b_skip B A0 A1 A2 _ _ hne; omega
  rw [this]; simp

open Classical in
lemma g77b_split {κ : Type*} (B A0 A1 A2 : κ → κ → ℝ) (L M : ℕ) (hLM : L < M)
    (y : ℕ × κ) (hy : y.1 = L) :
    ∀ t (x : ℕ × κ), M + 1 ≤ x.1 → g77b_fe (qbdP B A0 A1 A2) (level L) (t + 1) x y =
      ∑ p ∈ Finset.HasAntidiagonal.antidiagonal t, ∑' a, g77b_fe (qbdP B A0 A1 A2) (level M) p.1 x a *
        g77b_fe (qbdP B A0 A1 A2) (level L) p.2 a y := by
  intro t
  induction t with
  | zero =>
    intro x hx
    rw [g77b_fe_succ]
    simp only [Finset.Nat.antidiagonal_zero, Finset.sum_singleton]
    refine tsum_congr fun z => ?_
    rw [g77b_fe_zero _ (level M) x z]
    by_cases hP : qbdP B A0 A1 A2 x z = 0
    · simp [hP]
    · have hz := g77b_skip B A0 A1 A2 _ _ hP
      by_cases hzM : z.1 = M
      · rw [if_pos (show z ∈ level M from hzM), if_neg (show z ∉ level L from by
          rw [g77b_mem_level]; omega)]
      · rw [if_neg (show z ∉ level M from hzM), if_neg (show z ∉ level L from by
          rw [g77b_mem_level]; omega), g77b_fe0_far _ _ _ _ _ _ _ (by omega)]
        simp
  | succ t ih =>
    intro x hx
    rw [Finset.Nat.sum_antidiagonal_succ]
    have h2 : ∑ p ∈ Finset.HasAntidiagonal.antidiagonal t, ∑' a,
        g77b_fe (qbdP B A0 A1 A2) (level M) (p.1 + 1) x a *
          g77b_fe (qbdP B A0 A1 A2) (level L) p.2 a y =
        ∑' z, ENNReal.ofReal (qbdP B A0 A1 A2 x z) * (if z ∈ level M then 0 else
          ∑ p ∈ Finset.HasAntidiagonal.antidiagonal t, ∑' a,
            g77b_fe (qbdP B A0 A1 A2) (level M) p.1 z a *
              g77b_fe (qbdP B A0 A1 A2) (level L) p.2 a y) := by
      have : ∀ z, ENNReal.ofReal (qbdP B A0 A1 A2 x z) * (if z ∈ level M then 0 else
          ∑ p ∈ Finset.HasAntidiagonal.antidiagonal t, ∑' a,
            g77b_fe (qbdP B A0 A1 A2) (level M) p.1 z a *
              g77b_fe (qbdP B A0 A1 A2) (level L) p.2 a y) =
          ∑ p ∈ Finset.HasAntidiagonal.antidiagonal t, ∑' a,
            ENNReal.ofReal (qbdP B A0 A1 A2 x z) * (if z ∈ level M then 0 else
              g77b_fe (qbdP B A0 A1 A2) (level M) p.1 z a) *
              g77b_fe (qbdP B A0 A1 A2) (level L) p.2 a y := by
        intro z
        split_ifs <;> simp [Finset.mul_sum, ENNReal.tsum_mul_left, mul_assoc]
      rw [tsum_congr this, Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [ENNReal.tsum_comm]
      refine tsum_congr fun a => ?_
      rw [g77b_fe_succ, ENNReal.tsum_mul_right]
    rw [h2, ← ENNReal.tsum_add, g77b_fe_succ]
    refine tsum_congr fun z => ?_
    rw [g77b_fe_zero _ (level M) x z]
    by_cases hP : qbdP B A0 A1 A2 x z = 0
    · simp [hP]
    · have hz := g77b_skip B A0 A1 A2 _ _ hP
      by_cases hzM : z.1 = M
      · rw [if_pos (show z ∈ level M from hzM), if_neg (show z ∉ level L from by
          rw [g77b_mem_level]; omega), if_pos (show z ∈ level M from hzM)]
        simp
      · rw [if_neg (show z ∉ level M from hzM), if_neg (show z ∉ level L from by
          rw [g77b_mem_level]; omega), if_neg (show z ∉ level M from hzM), ih z (by omega)]
        simp

lemma g77b_antidiag (F : ℕ × ℕ → ℝ≥0∞) :
    ∑' t, ∑ p ∈ Finset.HasAntidiagonal.antidiagonal t, F p = ∑' p, F p := by
  rw [← (Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd).tsum_eq, ENNReal.tsum_sigma']
  refine tsum_congr fun t => ?_
  rw [← Finset.tsum_subtype]
  rfl

lemma g77b_splitFE {κ : Type*} (B A0 A1 A2 : κ → κ → ℝ) (L M : ℕ) (hLM : L < M)
    (y : ℕ × κ) (hy : y.1 = L) (x : ℕ × κ) (hx : M + 1 ≤ x.1) :
    firstEntrance (qbdP B A0 A1 A2) (level L) x y =
      ∑' a, firstEntrance (qbdP B A0 A1 A2) (level M) x a *
        firstEntrance (qbdP B A0 A1 A2) (level L) a y := by
  rw [g77b_FE, tsum_eq_zero_add' ENNReal.summable, g77b_fe0_far _ _ _ _ _ _ _ (by omega), zero_add]
  simp_rw [g77b_split B A0 A1 A2 L M hLM y hy _ x hx]
  rw [g77b_antidiag (fun p => ∑' a, g77b_fe (qbdP B A0 A1 A2) (level M) p.1 x a *
        g77b_fe (qbdP B A0 A1 A2) (level L) p.2 a y), ENNReal.tsum_prod']
  simp_rw [g77b_FE, ← ENNReal.tsum_mul_right, ← ENNReal.tsum_mul_left]
  conv_rhs => rw [ENNReal.tsum_comm]
  refine tsum_congr fun s => ?_
  exact ENNReal.tsum_comm

lemma g77b_shiftFE {κ : Type*} (B A0 A1 A2 : κ → κ → ℝ) (L e : ℕ) (p q : κ) :
    firstEntrance (qbdP B A0 A1 A2) (level L) (L + 1 + e, p) (L, q) =
      firstEntrance (qbdP B A0 A1 A2) (level 0) (1 + e, p) (0, q) := by
  rw [g77b_FE, g77b_FE]
  exact tsum_congr fun t => g77b_shift B A0 A1 A2 L t e p q

lemma g77b_vanish {ι : Type*} [DecidableEq ι] (D C : ℕ → ι → ι → ℝ) (L d : ℕ) (j : ι)
    (hd : 1 ≤ d) : ∀ t (x : ℕ × (ℕ × ι)), L + 1 ≤ x.1 →
      g77b_fe (mg1QBD D C) (level L) t x (L, (d, j)) = 0 := by
  intro t
  induction t with
  | zero =>
    intro x hx
    rw [g77b_fe_zero]
    have : mg1QBD D C x (L, (d, j)) = 0 := by
      unfold mg1QBD qbdP augA2
      split_ifs with h1 h2 h3 h4 h5 <;> simp_all <;> omega
    rw [this]; simp
  | succ t ih =>
    intro x hx
    rw [g77b_fe_succ]
    apply ENNReal.tsum_eq_zero.mpr
    intro z
    by_cases hP : mg1QBD D C x z = 0
    · simp [hP]
    · have hz := g77b_skip _ _ _ _ _ _ hP
      by_cases hzL : z.1 = L
      · rw [if_pos (show z ∈ level L from hzL)]; simp
      · rw [if_neg (show z ∉ level L from hzL), ih z (by omega)]; simp

lemma g77b_climbP {ι : Type*} [DecidableEq ι] (C : ℕ → ι → ι → ℝ) (D : ℕ → ι → ι → ℝ)
    (m k : ℕ) (i : ι) (hm : 1 ≤ m) (z : ℕ × (ℕ × ι)) :
    mg1QBD D C (m, (k + 1, i)) z = if z = (m + 1, (k, i)) then 1 else 0 := by
  obtain ⟨z1, z2, z3⟩ := z
  unfold mg1QBD qbdP augA0 augA1 augA2
  simp only [Prod.mk.injEq]
  split_ifs <;> first | rfl | (exfalso; omega) | simp_all

lemma g77b_FE_notmem {V : Type*} (P : V → V → ℝ) (T : Set V) (x y : V) (hy : y ∉ T) :
    firstEntrance P T x y = 0 := by
  rw [g77b_FE]
  refine ENNReal.tsum_eq_zero.mpr fun t => ENNReal.tsum_eq_zero.mpr fun ω => ?_
  rw [if_neg]
  rintro ⟨-, -, h, -⟩
  exact hy h

lemma g77b_climbFE {ι : Type*} [DecidableEq ι] (D C : ℕ → ι → ι → ℝ) (L m k : ℕ) (i : ι)
    (hm : L + 1 ≤ m) (y : ℕ × (ℕ × ι)) (hy : y.1 = L) :
    firstEntrance (mg1QBD D C) (level L) (m, (k + 1, i)) y =
      firstEntrance (mg1QBD D C) (level L) (m + 1, (k, i)) y := by
  have hne : y ≠ (m + 1, (k, i)) := by intro h; rw [h] at hy; simp at hy; omega
  rw [g77b_FE, g77b_FE, tsum_eq_zero_add' ENNReal.summable, g77b_fe_zero,
    g77b_climbP C D m k i (by omega), if_neg hne]
  simp only [ENNReal.ofReal_zero, ite_self, zero_add]
  refine tsum_congr fun t => ?_
  rw [g77b_fe_succ, tsum_eq_single (m + 1, (k, i))]
  · rw [g77b_climbP C D m k i (by omega), if_pos rfl,
      if_neg (show (m + 1, (k, i)) ∉ level L from by rw [g77b_mem_level]; dsimp only; omega)]
    simp
  · intro z hz
    rw [g77b_climbP C D m k i (by omega), if_neg hz]
    simp

lemma g77b_shiftFE' {ι : Type*} [DecidableEq ι] (D C : ℕ → ι → ι → ℝ) (L e : ℕ) (p q : ℕ × ι) :
    firstEntrance (mg1QBD D C) (level L) (L + 1 + e, p) (L, q) =
      firstEntrance (mg1QBD D C) (level 0) (1 + e, p) (0, q) :=
  g77b_shiftFE (augB D) augA0 (augA1 C) (augA2 C) L e p q

lemma g77b_splitFE' {ι : Type*} [DecidableEq ι] (D C : ℕ → ι → ι → ℝ) (L M : ℕ) (hLM : L < M)
    (y : ℕ × (ℕ × ι)) (hy : y.1 = L) (x : ℕ × (ℕ × ι)) (hx : M + 1 ≤ x.1) :
    firstEntrance (mg1QBD D C) (level L) x y =
      ∑' a, firstEntrance (mg1QBD D C) (level M) x a *
        firstEntrance (mg1QBD D C) (level L) a y :=
  g77b_splitFE (augB D) augA0 (augA1 C) (augA2 C) L M hLM y hy x hx


/-- Theorem 13.1.3 (pp. 271–272). For the QBD (13.3) with blocks (13.4)–(13.7) embedding an
M/G/1-type chain (13.1), and every level `n ≥ 1`, the first-passage matrix `G` from `ℓ(n)` to
`ℓ(n − 1)` has the structure (13.8): its block column for sublevel `0` is `H, H², H³, …` and all
its other block columns are zero, i.e. `G_{(k,i),(d,j)} = (H^{k+1})_{ij}` if `d = 0` and `0`
otherwise, where `H` is the matrix (13.9) at level `n`. Products are computed in `ℝ≥0∞`. -/
theorem solution {ι : Type*} [Countable ι] [DecidableEq ι]
    (D C : ℕ → ι → ι → ℝ)
    (hP : IsStochasticC (mg1P D C)) (n : ℕ) (hn : 1 ≤ n) :
    ∀ (k : ℕ) (i : ι) (d : ℕ) (j : ι),
      matG (mg1QBD D C) n (k, i) (d, j) =
        if d = 0 then matPowE (matH D C n) (k + 1) i j else 0 := by
  intro k i d j
  have hFE : matG (mg1QBD D C) n (k, i) (d, j) =
      firstEntrance (mg1QBD D C) (level (n - 1)) (n, (k, i)) (n - 1, (d, j)) := rfl
  rw [hFE]
  split_ifs with hd
  · subst hd
    have climb : ∀ k m, n ≤ m → firstEntrance (mg1QBD D C) (level (n - 1)) (m, (k, i))
        (n - 1, (0, j)) = firstEntrance (mg1QBD D C) (level (n - 1)) (m + k, (0, i))
        (n - 1, (0, j)) := by
      intro k
      induction k with
      | zero => intro m _; rfl
      | succ k ih =>
        intro m hm
        rw [g77b_climbFE D C (n - 1) m k i (by omega) _ rfl, ih (m + 1) (by omega)]
        congr 2
        omega
    have Φ : ∀ k i j, firstEntrance (mg1QBD D C) (level (n - 1)) (n + k, (0, i)) (n - 1, (0, j)) =
        matPowE (matH D C n) (k + 1) i j := by
      clear climb hFE
      intro k
      induction k with
      | zero =>
        intro i j
        show _ = ∑' l, matPowE (matH D C n) 0 i l * matH D C n l j
        rw [tsum_eq_single i]
        · simp [matPowE, matOneE]; rfl
        · intro l hl; simp [matPowE, matOneE, Ne.symm hl]
      | succ k ih =>
        intro i j
        rw [g77b_splitFE' D C (n - 1) n (by omega) (n - 1, (0, j)) rfl (n + (k + 1), (0, i))
          (show n + 1 ≤ n + (k + 1) by omega)]
        show _ = ∑' l, matPowE (matH D C n) (k + 1) i l * matH D C n l j
        rw [← Function.Injective.tsum_eq (g := fun l : ι => ((n, (0, l)) : ℕ × (ℕ × ι)))]
        · refine tsum_congr fun l => ?_
          have h1 := ih i l
          rw [show n + k = n - 1 + 1 + k by omega, g77b_shiftFE'] at h1
          rw [show n + (k + 1) = n + 1 + k by omega, g77b_shiftFE', h1]
          rfl
        · intro a b h; simpa using h
        · intro a ha
          obtain ⟨a1, a2, a3⟩ := a
          by_cases h1 : a1 = n
          · by_cases h2 : a2 = 0
            · exact ⟨a3, by simp [h1, h2]⟩
            · exfalso; apply ha
              simp only
              rw [g77b_FE, ENNReal.tsum_eq_zero.mpr fun t =>
                (by subst h1; exact g77b_vanish D C a1 a2 a3 (by omega) t _ (by dsimp only; omega))]
              simp
          · exfalso; apply ha
            simp only
            rw [g77b_FE_notmem _ _ _ _ (by rw [g77b_mem_level]; exact h1)]
            simp
    rw [climb k n le_rfl, Φ]
  · rw [g77b_FE]
    exact ENNReal.tsum_eq_zero.mpr fun t =>
      g77b_vanish D C (n - 1) d j (by omega) t _ (by dsimp only; omega)


