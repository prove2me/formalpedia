-- Prove2me | solution 1 for MatrixAnalytic.SkipFree.H_minimal_solution
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T04:42:18.746915+00:00
-- url     : https://prove2.me/submissions/54810614-2d8e-4a26-9151-ac99ee765ef8

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

open Classical in
lemma g77b_fe_range_succ {V : Type*} (P : V → V → ℝ) (T : Set V) (N : ℕ) (x y : V) :
    ∑ t ∈ Finset.range (N + 1), g77b_fe P T t x y = g77b_fe P T 0 x y +
      ∑' z, ENNReal.ofReal (P x z) * (if z ∈ T then 0 else ∑ t ∈ Finset.range N, g77b_fe P T t z y) := by
  rw [Finset.sum_range_succ', add_comm]
  congr 1
  simp_rw [g77b_fe_succ]
  rw [← Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
  refine tsum_congr fun z => ?_
  split_ifs <;> simp [Finset.mul_sum]

open Classical in
lemma g77b_mass {V : Type*} (P : V → V → ℝ) (T S : Set V)
    (hrow : ∀ x ∈ S, ∑' z, ENNReal.ofReal (P x z) ≤ 1)
    (hcl : ∀ x ∈ S, ∀ z, P x z ≠ 0 → z ∉ T → z ∈ S) :
    ∀ x ∈ S, ∑' y, firstEntrance P T x y ≤ 1 := by
  have key : ∀ N, ∀ x ∈ S, ∑' y, ∑ t ∈ Finset.range N, g77b_fe P T t x y ≤ 1 := by
    intro N
    induction N with
    | zero => intro x _; simp
    | succ N ih =>
      intro x hx
      simp_rw [g77b_fe_range_succ]
      rw [ENNReal.tsum_add, ENNReal.tsum_comm]
      simp_rw [g77b_fe_zero]
      calc (∑' y, if y ∈ T then ENNReal.ofReal (P x y) else 0) + ∑' z, ∑' y,
              ENNReal.ofReal (P x z) * (if z ∈ T then 0 else
                ∑ t ∈ Finset.range N, g77b_fe P T t z y)
          ≤ (∑' z, ENNReal.ofReal (P x z) * (if z ∈ T then 1 else 0)) +
            ∑' z, ENNReal.ofReal (P x z) * (if z ∈ T then 0 else 1) := by
            gcongr with z z
            · split_ifs <;> simp
            · rw [ENNReal.tsum_mul_left]
              by_cases hP : P x z = 0
              · simp [hP]
              · gcongr
                split_ifs with hz
                · simp
                · exact ih z (hcl x hx z hP hz)
        _ = ∑' z, ENNReal.ofReal (P x z) := by
            rw [← ENNReal.tsum_add]
            refine tsum_congr fun z => ?_
            split_ifs <;> simp
        _ ≤ 1 := hrow x hx
  intro x hx
  simp_rw [g77b_FE]
  rw [ENNReal.tsum_comm, ENNReal.tsum_eq_iSup_nat]
  refine iSup_le fun N => ?_
  rw [← Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
  exact key N x hx

lemma g77b_mulE_assoc {κ : Type*} (A B C : κ → κ → ℝ≥0∞) :
    matMulE (matMulE A B) C = matMulE A (matMulE B C) := by
  funext i j
  simp only [matMulE]
  simp_rw [← ENNReal.tsum_mul_right, ← ENNReal.tsum_mul_left, mul_assoc]
  exact ENNReal.tsum_comm

lemma g77b_mulE_one {κ : Type*} [DecidableEq κ] (A : κ → κ → ℝ≥0∞) :
    matMulE A matOneE = A := by
  funext i j
  simp only [matMulE, matOneE]
  rw [tsum_eq_single j]
  · simp
  · intro l hl; simp [hl]

lemma g77b_one_mulE {κ : Type*} [DecidableEq κ] (A : κ → κ → ℝ≥0∞) :
    matMulE matOneE A = A := by
  funext i j
  simp only [matMulE, matOneE]
  rw [tsum_eq_single i]
  · simp
  · intro l hl; simp [Ne.symm hl]

lemma g77b_powE_add {κ : Type*} [DecidableEq κ] (M : κ → κ → ℝ≥0∞) (k r : ℕ) :
    matPowE M (k + r) = matMulE (matPowE M k) (matPowE M r) := by
  induction r with
  | zero => simp only [Nat.add_zero]; rw [show matPowE M 0 = matOneE from rfl, g77b_mulE_one]
  | succ r ih =>
    rw [← Nat.add_assoc, show matPowE M (k + r + 1) = matMulE (matPowE M (k + r)) M from rfl, ih,
      g77b_mulE_assoc]
    rfl

lemma g77b_powE_one {κ : Type*} [DecidableEq κ] (M : κ → κ → ℝ≥0∞) : matPowE M 1 = M := by
  rw [show matPowE M 1 = matMulE (matPowE M 0) M from rfl,
    show matPowE M 0 = matOneE from rfl, g77b_one_mulE]

open Classical in
lemma g77b_FE_step {V : Type*} (P : V → V → ℝ) (T : Set V) (x y : V) :
    firstEntrance P T x y = (if y ∈ T then ENNReal.ofReal (P x y) else 0) +
      ∑' z, ENNReal.ofReal (P x z) * (if z ∈ T then 0 else firstEntrance P T z y) := by
  rw [g77b_FE, tsum_eq_zero_add' ENNReal.summable, g77b_fe_zero]
  congr 1
  simp_rw [g77b_fe_succ]
  rw [ENNReal.tsum_comm]
  refine tsum_congr fun z => ?_
  rw [ENNReal.tsum_mul_left]
  split_ifs <;> simp [g77b_FE]

lemma g77b_P0 {ι : Type*} [DecidableEq ι] (D C : ℕ → ι → ι → ℝ) (m : ℕ) (hm : 1 ≤ m) (l : ι)
    (z : ℕ × (ℕ × ι)) :
    mg1QBD D C (m, (0, l)) z = (if z.1 + 1 = m ∧ z.2.1 = 0 then C 0 l z.2.2 else 0) +
      (if z.1 = m then C (z.2.1 + 1) l z.2.2 else 0) := by
  obtain ⟨z1, z2, z3⟩ := z
  unfold mg1QBD qbdP augA0 augA1 augA2
  simp only
  split_ifs <;> first | rfl | (exfalso; omega) | simp_all | omega

lemma g77b_row0 {ι : Type*} [DecidableEq ι] (D C : ℕ → ι → ι → ℝ) (hC : ∀ k i j, 0 ≤ C k i j)
    (m : ℕ) (hm : 1 ≤ m) (l : ι) (g : ℕ × (ℕ × ι) → ℝ≥0∞) :
    ∑' z, ENNReal.ofReal (mg1QBD D C (m, (0, l)) z) * g z =
      ∑' l', ENNReal.ofReal (C 0 l l') * g (m - 1, (0, l')) +
        ∑' c, ∑' l', ENNReal.ofReal (C (c + 1) l l') * g (m, (c, l')) := by
  simp_rw [g77b_P0 D C m hm l]
  have h0 : ∀ z : ℕ × (ℕ × ι), 0 ≤ (if z.1 + 1 = m ∧ z.2.1 = 0 then C 0 l z.2.2 else 0) := by
    intro z; split_ifs <;> simp [hC]
  have h1 : ∀ z : ℕ × (ℕ × ι), 0 ≤ (if z.1 = m then C (z.2.1 + 1) l z.2.2 else 0) := by
    intro z; split_ifs <;> simp [hC]
  simp_rw [ENNReal.ofReal_add (h0 _) (h1 _), add_mul]
  rw [ENNReal.tsum_add]
  congr 1
  · rw [← Function.Injective.tsum_eq (g := fun l' : ι => ((m - 1, (0, l')) : ℕ × (ℕ × ι)))]
    · refine tsum_congr fun l' => ?_
      rw [if_pos ⟨by dsimp only; omega, rfl⟩]
    · intro a b h; simpa using h
    · intro z hz
      obtain ⟨z1, z2, z3⟩ := z
      by_cases h : z1 + 1 = m ∧ z2 = 0
      · refine ⟨z3, ?_⟩
        obtain ⟨h1, h2⟩ := h
        show ((m - 1, (0, z3)) : ℕ × (ℕ × ι)) = (z1, z2, z3)
        rw [h2, show m - 1 = z1 by omega]
      · exfalso; apply hz; simp only; rw [if_neg h]; simp
  · rw [← ENNReal.tsum_prod' (f := fun p : ℕ × ι => ENNReal.ofReal (C (p.1 + 1) l p.2) *
      g (m, p.1, p.2)), ← Function.Injective.tsum_eq
      (g := fun p : ℕ × ι => ((m, (p.1, p.2)) : ℕ × (ℕ × ι)))]
    · refine tsum_congr fun p => ?_
      rw [if_pos rfl]
    · intro a b h; simp only [Prod.mk.injEq] at h; ext <;> simp [h.2.1, h.2.2]
    · intro z hz
      obtain ⟨z1, z2, z3⟩ := z
      by_cases h : z1 = m
      · exact ⟨(z2, z3), by simp [h]⟩
      · exfalso; apply hz; simp only; rw [if_neg h]; simp

lemma g77b_rowsum {ι : Type*} [DecidableEq ι] (D C : ℕ → ι → ι → ℝ)
    (hP : IsStochasticC (mg1P D C)) (x : ℕ × (ℕ × ι)) (hx : 1 ≤ x.1) :
    ∑' z, ENNReal.ofReal (mg1QBD D C x z) ≤ 1 := by
  have hC : ∀ k i j, 0 ≤ C k i j := by
    intro k i j
    have := hP.1 (1, i) (k, j)
    simpa [mg1P] using this
  obtain ⟨m, c, l⟩ := x
  cases c with
  | zero =>
    have := g77b_row0 D C hC m hx l (fun _ => 1)
    simp only [mul_one] at this
    rw [this]
    have hs : HasSum (fun p : ℕ × ι => C p.1 l p.2) 1 := by
      have := hP.2 (1, l)
      convert this using 1
      funext p; simp [mg1P]
    have hE : ∑' p : ℕ × ι, ENNReal.ofReal (C p.1 l p.2) = 1 := by
      rw [← ENNReal.ofReal_tsum_of_nonneg (fun p => hC _ _ _) hs.summable, hs.tsum_eq]
      simp
    rw [ENNReal.tsum_prod', tsum_eq_zero_add' ENNReal.summable] at hE
    exact le_of_eq hE
  | succ c =>
    simp_rw [g77b_climbP C D m c l hx]
    rw [tsum_eq_single (m + 1, (c, l))]
    · simp
    · intro z hz; simp [hz]

lemma g77b_Gstruct {ι : Type*} [Countable ι] [DecidableEq ι]
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


/-- Theorem 13.1.4 (p. 273). For an M/G/1-type Markov chain (13.1) and every level `n ≥ 1`, the
matrix `H` (13.9) (first passage from `(n, 0, i)` to `ℓ(n − 1)` in the QBD (13.3), entered at
`(n − 1, 0, j)`) is the minimal nonnegative solution of `H = Σ_{n≥0} C_n Hⁿ` (13.10): its
entries are finite, it solves (13.10), and it lies entrywise below every nonnegative real
solution. Products and series are computed in `ℝ≥0∞`. -/
theorem solution {ι : Type*} [Countable ι] [DecidableEq ι]
    (D C : ℕ → ι → ι → ℝ)
    (hP : IsStochasticC (mg1P D C)) (n : ℕ) (hn : 1 ≤ n) :
    (∀ i j, matH D C n i j ≠ ⊤) ∧
      matH D C n = shiftSeriesE C (matH D C n) 0 ∧
      ∀ Y : ι → ι → ℝ, (∀ i j, 0 ≤ Y i j) →
        ennMat Y = shiftSeriesE C (ennMat Y) 0 →
        ∀ i j, matH D C n i j ≤ ennMat Y i j := by
  classical
  have hC : ∀ k i j, 0 ≤ C k i j := by
    intro k i j
    have := hP.1 (1, i) (k, j)
    simpa [mg1P] using this
  have hH : ∀ i j, matH D C n i j =
      firstEntrance (mg1QBD D C) (level (n - 1)) (n, (0, i)) (n - 1, (0, j)) := fun _ _ => rfl
  refine ⟨?_, ?_, ?_⟩
  · intro i j
    have hm := g77b_mass (mg1QBD D C) (level (n - 1)) {z | n ≤ z.1}
      (fun x hx => g77b_rowsum D C hP x (by simp only [Set.mem_setOf_eq] at hx; omega)) (by
        intro x hx z hPz hz
        have := g77b_skip _ _ _ _ _ _ hPz
        simp only [Set.mem_setOf_eq] at hx ⊢
        rw [g77b_mem_level] at hz; omega) (n, (0, i)) (by simp)
    rw [hH]
    exact ne_top_of_le_ne_top ENNReal.one_ne_top ((ENNReal.le_tsum _).trans hm)
  · funext i j
    rw [hH, g77b_FE_step, if_pos (show ((n - 1, (0, j)) : ℕ × (ℕ × ι)) ∈ level (n - 1) from rfl),
      g77b_row0 D C hC n hn i, g77b_P0 D C n hn i]
    have e1 : ∀ l' : ι, (if ((n - 1, (0, l')) : ℕ × (ℕ × ι)) ∈ level (n - 1) then 0 else
        firstEntrance (mg1QBD D C) (level (n - 1)) (n - 1, (0, l')) (n - 1, (0, j))) = 0 :=
      fun l' => if_pos rfl
    have e2 : ∀ (c : ℕ) (l' : ι), (if ((n, (c, l')) : ℕ × (ℕ × ι)) ∈ level (n - 1) then 0 else
        firstEntrance (mg1QBD D C) (level (n - 1)) (n, (c, l')) (n - 1, (0, j))) =
        matPowE (matH D C n) (c + 1) l' j := by
      intro c l'
      rw [if_neg (by rw [g77b_mem_level]; dsimp only; omega)]
      have := g77b_Gstruct D C hP n hn c l' 0 j
      exact this
    simp only [e1, e2, mul_zero, tsum_zero, zero_add]
    unfold shiftSeriesE
    conv_rhs => rw [tsum_eq_zero_add' ENNReal.summable]
    congr 1
    · simp only [Nat.add_zero, show matPowE (matH D C n) 0 = matOneE from rfl, g77b_mulE_one]
      simp [ennMat, show n - 1 + 1 = n by omega, show n - 1 ≠ n by omega]
    · refine tsum_congr fun c => ?_
      simp only [matMulE, ennMat, Nat.zero_add]
  · intro Y hY0 hYeq i j
    have hW : ∀ l l'', ennMat Y l l'' =
        ∑' k, ∑' l', ENNReal.ofReal (C k l l') * matPowE (ennMat Y) k l' l'' := by
      intro l l''
      have := congrFun (congrFun hYeq l) l''
      rw [this]
      simp only [shiftSeriesE, matMulE, ennMat, Nat.zero_add]
    have star : ∀ r l j, matPowE (ennMat Y) (r + 1) l j =
        ∑' k, ∑' l', ENNReal.ofReal (C k l l') * matPowE (ennMat Y) (k + r) l' j := by
      intro r l j
      rw [show r + 1 = 1 + r by omega, g77b_powE_add, g77b_powE_one]
      simp only [matMulE]
      have : ∀ l'', ennMat Y l l'' * matPowE (ennMat Y) r l'' j =
          ∑' k, ∑' l', ENNReal.ofReal (C k l l') * (matPowE (ennMat Y) k l' l'' *
            matPowE (ennMat Y) r l'' j) := by
        intro l''
        rw [hW l l'', ← ENNReal.tsum_mul_right]
        refine tsum_congr fun k => ?_
        rw [← ENNReal.tsum_mul_right]
        refine tsum_congr fun l' => ?_
        rw [mul_assoc]
      rw [tsum_congr this, ENNReal.tsum_comm]
      refine tsum_congr fun k => ?_
      rw [ENNReal.tsum_comm]
      refine tsum_congr fun l' => ?_
      rw [ENNReal.tsum_mul_left, g77b_powE_add]
      rfl
    have claim : ∀ N m c l, n ≤ m → ∑ t ∈ Finset.range N,
        g77b_fe (mg1QBD D C) (level (n - 1)) t (m, (c, l)) (n - 1, (0, j)) ≤
          matPowE (ennMat Y) (m - n + 1 + c) l j := by
      intro N
      induction N with
      | zero => intro m c l _; simp
      | succ N ih =>
        intro m c l hm
        rw [g77b_fe_range_succ]
        cases c with
        | succ c =>
          rw [g77b_fe_zero, tsum_eq_single (m + 1, (c, l))]
          · have hne : ((n - 1, (0, j)) : ℕ × (ℕ × ι)) ≠ (m + 1, (c, l)) := by
              intro h; simp only [Prod.mk.injEq] at h; omega
            simp only [g77b_climbP C D m c l (by omega), hne, ↓reduceIte,
              if_neg (show ((m + 1, (c, l)) : ℕ × (ℕ × ι)) ∉ level (n - 1) by
                rw [g77b_mem_level]; dsimp only; omega)]
            simp only [ENNReal.ofReal_zero, ite_self, ENNReal.ofReal_one, one_mul, zero_add]
            rw [show m - n + 1 + (c + 1) = m + 1 - n + 1 + c by omega]
            exact ih (m + 1) c l (by omega)
          · intro z hz; rw [g77b_climbP C D m c l (by omega), if_neg hz]; simp
        | zero =>
          rw [g77b_fe_zero, g77b_row0 D C hC m (by omega) l, g77b_P0 D C m (by omega) l,
            show m - n + 1 + 0 = (m - n) + 1 by omega, star (m - n) l j]
          conv_rhs => rw [tsum_eq_zero_add' ENNReal.summable]
          rw [if_pos (show ((n - 1, (0, j)) : ℕ × (ℕ × ι)) ∈ level (n - 1) from rfl), ← add_assoc]
          refine add_le_add ?_ ?_
          · by_cases hmn : m = n
            · subst hmn
              simp only [show m - 1 + 1 = m by omega, and_self, if_true,
                show m - 1 ≠ m by omega, if_false, add_zero, Nat.sub_self, Nat.zero_add]
              simp only [show matPowE (ennMat Y) 0 = matOneE from rfl, matOneE]
              have : ∀ l' : ι, (if ((m - 1, (0, l')) : ℕ × (ℕ × ι)) ∈ level (m - 1) then 0 else
                  ∑ t ∈ Finset.range N, g77b_fe (mg1QBD D C) (level (m - 1)) t (m - 1, (0, l'))
                    (m - 1, (0, j))) = 0 := fun l' => if_pos rfl
              simp only [this, mul_zero, tsum_zero, add_zero]
              rw [tsum_eq_single j]
              · simp
              · intro l' hl'; simp [hl']
            · simp only [show ¬ (n - 1 + 1 = m ∧ True) by omega, show n - 1 ≠ m by omega,
                if_false, add_zero, ENNReal.ofReal_zero, zero_add, and_true]
              gcongr with l'
              rw [if_neg (show ((m - 1, (0, l')) : ℕ × (ℕ × ι)) ∉ level (n - 1) by
                rw [g77b_mem_level]; dsimp only; omega)]
              have := ih (m - 1) 0 l' (by omega)
              rw [show m - 1 - n + 1 + 0 = m - n by omega] at this
              exact this
          · gcongr with c l'
            rw [if_neg (show ((m, (c, l')) : ℕ × (ℕ × ι)) ∉ level (n - 1) by
                rw [g77b_mem_level]; dsimp only; omega)]
            have := ih m c l' hm
            rw [show m - n + 1 + c = c + 1 + (m - n) by omega] at this
            exact this
    rw [hH, g77b_FE, ENNReal.tsum_eq_iSup_nat]
    refine iSup_le fun N => (claim N n 0 i le_rfl).trans (le_of_eq ?_)
    rw [show n - n + 1 + 0 = 1 by omega, g77b_powE_one]


