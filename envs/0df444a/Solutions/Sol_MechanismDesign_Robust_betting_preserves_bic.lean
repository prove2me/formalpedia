-- Prove2me | solution 1 for MechanismDesign.Robust.betting_preserves_bic
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T10:36:43.633119+00:00
-- url     : https://prove2.me/submissions/cb41953c-ded2-4573-9f7e-579e38a6ef96

import Mathlib
import Definitions.Def_MechanismDesign_Robust_Mechanisms

open scoped ENNReal


namespace MechanismDesign.Robust

section core
open Classical
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
variable {ι : Type} [Fintype ι] [DecidableEq ι] {Θ T : ι → Type*} {A : Type*}

theorem join_self (i : ι) (r : T i) (τo : Others T i) : join i r τo i = r := by
  simp [join]

theorem join_ne (i : ι) (r : T i) (τo : Others T i) (j : ι) (h : j ≠ i) :
    join i r τo j = τo ⟨j, h⟩ := by
  simp [join, h]

theorem join_others (i : ι) (τ : ∀ j, T j) : join i (τ i) (others τ i) = τ := by
  funext j
  by_cases h : j = i
  · subst h; simp [join]
  · simp [join, h, others]

theorem join_eq_iff (i : ι) (r : T i) (τo : Others T i) (s : ∀ j, T j) :
    s = join i r τo ↔ s i = r ∧ ∀ j (h : j ≠ i), s j = τo ⟨j, h⟩ := by
  constructor
  · rintro rfl; exact ⟨join_self _ _ _, fun j h => join_ne _ _ _ _ h⟩
  · rintro ⟨h1, h2⟩
    funext j
    by_cases h : j = i
    · subst h; rw [join_self]; exact h1
    · rw [join_ne _ _ _ _ h]; exact h2 j h

/-- the embedding of (others' types, own report) into the index type of the interim family -/
noncomputable def qlEmb (ts : TypeSpace Θ T) (q : (∀ i, T i) → A) (t : ι → (∀ i, T i) → ℝ)
    (i : ι) : Others T i × T i → Others T i × (∀ j, T j) × (A × (ι → ℝ)) :=
  fun p => (p.1, join i p.2 p.1, (q (join i p.2 p.1), fun k => t k (join i p.2 p.1)))

theorem qlEmb_injective (ts : TypeSpace Θ T) (q : (∀ i, T i) → A) (t : ι → (∀ i, T i) → ℝ)
    (i : ι) : Function.Injective (qlEmb ts q t i) := by
  rintro ⟨a, r⟩ ⟨a', r'⟩ h
  simp only [qlEmb, Prod.mk.injEq] at h
  obtain ⟨h1, h2, -⟩ := h
  subst h1
  have := congrFun h2 i
  simp only [join_self] at this
  subst this; rfl

theorem profileProb_truthful (i : ι) (τi : T i) (m : PMF (T i)) (τo : Others T i)
    (s : ∀ j, T j) :
    profileProb (Function.update (fun j => truthful T j (join i τi τo j)) i m) s =
      if s = join i (s i) τo then m (s i) else 0 := by
  unfold profileProb
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
  simp only [Function.update_self]
  split_ifs with h
  · rw [Finset.prod_eq_one, mul_one]
    intro j hj
    have hji : j ≠ i := Finset.ne_of_mem_erase hj
    rw [Function.update_of_ne hji]
    simp only [truthful]
    rw [join_ne _ _ _ _ hji]
    have := congrFun h j
    rw [join_ne _ _ _ _ hji] at this
    rw [this]; simp
  · rw [join_eq_iff] at h
    push_neg at h
    obtain ⟨j, hj, hs⟩ := h rfl
    rw [Finset.prod_eq_zero (i := j) (Finset.mem_erase.2 ⟨hj, Finset.mem_univ _⟩), mul_zero]
    rw [Function.update_of_ne hj]
    simp only [truthful]
    rw [join_ne _ _ _ _ hj]
    simp [PMF.pure_apply, hs]

theorem family_emb (ts : TypeSpace Θ T) (vu : ι → A → (∀ i, Θ i) → ℝ) (q : (∀ i, T i) → A)
    (t : ι → (∀ i, T i) → ℝ) (i : ι) (τi : T i) (m : PMF (T i)) (p : Others T i × T i) :
    interimFamily ts (qlUtility vu) (qlDirect ts q t) (truthful T) i τi m (qlEmb ts q t i p) =
      (ts.β i τi p.1).toReal * (m p.2).toReal *
        (vu i (q (join i p.2 p.1)) (ts.payoff (join i τi p.1)) - t i (join i p.2 p.1)) := by
  simp only [interimFamily, qlEmb, profileProb_truthful, join_self, if_true, qlDirect,
    PMF.pure_apply, qlUtility, ENNReal.toReal_mul]
  simp

theorem family_zero (ts : TypeSpace Θ T) (vu : ι → A → (∀ i, Θ i) → ℝ) (q : (∀ i, T i) → A)
    (t : ι → (∀ i, T i) → ℝ) (i : ι) (τi : T i) (m : PMF (T i))
    (p : Others T i × (∀ j, T j) × (A × (ι → ℝ))) (hp : p ∉ Set.range (qlEmb ts q t i)) :
    interimFamily ts (qlUtility vu) (qlDirect ts q t) (truthful T) i τi m p = 0 := by
  obtain ⟨τo, s, x⟩ := p
  simp only [interimFamily, profileProb_truthful, qlDirect, PMF.pure_apply]
  by_cases h1 : s = join i (s i) τo
  · by_cases h2 : x = (q s, fun k => t k s)
    · exfalso; apply hp
      refine ⟨(τo, s i), ?_⟩
      simp only [qlEmb]
      rw [← h1, h2]
    · simp [h2]
  · simp [h1]

theorem summable_iff_emb (ts : TypeSpace Θ T) (vu : ι → A → (∀ i, Θ i) → ℝ)
    (q : (∀ i, T i) → A) (t : ι → (∀ i, T i) → ℝ) (i : ι) (τi : T i) (m : PMF (T i)) :
    Summable (interimFamily ts (qlUtility vu) (qlDirect ts q t) (truthful T) i τi m) ↔
      Summable (fun p : Others T i × T i => (ts.β i τi p.1).toReal * (m p.2).toReal *
        (vu i (q (join i p.2 p.1)) (ts.payoff (join i τi p.1)) - t i (join i p.2 p.1))) := by
  rw [← (qlEmb_injective ts q t i).summable_iff (family_zero ts vu q t i τi m)]
  simp only [Function.comp_def, family_emb]

theorem eu_eq_emb (ts : TypeSpace Θ T) (vu : ι → A → (∀ i, Θ i) → ℝ)
    (q : (∀ i, T i) → A) (t : ι → (∀ i, T i) → ℝ) (i : ι) (τi : T i) (m : PMF (T i)) :
    interimEU ts (qlUtility vu) (qlDirect ts q t) (truthful T) i τi m =
      ∑' p : Others T i × T i, (ts.β i τi p.1).toReal * (m p.2).toReal *
        (vu i (q (join i p.2 p.1)) (ts.payoff (join i τi p.1)) - t i (join i p.2 p.1)) := by
  unfold interimEU
  rw [← (qlEmb_injective ts q t i).tsum_eq (f := interimFamily ts (qlUtility vu) (qlDirect ts q t) (truthful T) i τi m)]
  · simp only [family_emb]
  · intro p hp
    by_contra h
    exact hp (family_zero ts vu q t i τi m p h)


theorem pmf_summable_toReal {α : Type*} (m : PMF α) : Summable fun a => (m a).toReal :=
  ENNReal.summable_toReal (by rw [m.tsum_coe]; simp)

theorem pmf_tsum_toReal {α : Type*} (m : PMF α) : ∑' a, (m a).toReal = 1 := by
  rw [← ENNReal.tsum_toReal_eq (fun a => PMF.apply_ne_top m a), m.tsum_coe]; simp

theorem bet_step (ts : TypeSpace Θ T) (vu : ι → A → (∀ i, Θ i) → ℝ)
    (q : (∀ i, T i) → A) (t t' : ι → (∀ i, T i) → ℝ) (k : ι) (R : Set (T k))
    (b : Others T k → ℝ) (B : ℝ) (hB : ∀ τo, |b τo| ≤ B)
    (ht' : ∀ r τo, t' k (join k r τo) = t k (join k r τo) - (if r ∈ R then b τo else 0))
    (hbic : ∀ (τk : T k) (m : PMF (T k)),
      Summable (interimFamily ts (qlUtility vu) (qlDirect ts q t) (truthful T) k τk m) ∧
      interimEU ts (qlUtility vu) (qlDirect ts q t) (truthful T) k τk m ≤
        interimEU ts (qlUtility vu) (qlDirect ts q t) (truthful T) k τk (truthful T k τk))
    (τk : T k)
    (hG : (τk ∈ R → 0 ≤ ∑' τo, (ts.β k τk τo).toReal * b τo) ∧
      (τk ∉ R → ∑' τo, (ts.β k τk τo).toReal * b τo ≤ 0))
    (m : PMF (T k)) :
    Summable (interimFamily ts (qlUtility vu) (qlDirect ts q t') (truthful T) k τk m) ∧
      interimEU ts (qlUtility vu) (qlDirect ts q t') (truthful T) k τk m ≤
        interimEU ts (qlUtility vu) (qlDirect ts q t') (truthful T) k τk (truthful T k τk) := by
  -- decomposition for any mixed report
  have key : ∀ m' : PMF (T k),
      Summable (interimFamily ts (qlUtility vu) (qlDirect ts q t) (truthful T) k τk m') →
      Summable (interimFamily ts (qlUtility vu) (qlDirect ts q t') (truthful T) k τk m') ∧
      interimEU ts (qlUtility vu) (qlDirect ts q t') (truthful T) k τk m' =
        interimEU ts (qlUtility vu) (qlDirect ts q t) (truthful T) k τk m' +
          (∑' τo, (ts.β k τk τo).toReal * b τo) *
            ∑' r, (m' r).toReal * (if r ∈ R then 1 else 0) := by
    intro m' hs
    rw [summable_iff_emb] at hs
    set f1 : Others T k → ℝ := fun τo => (ts.β k τk τo).toReal * b τo with hf1
    set g1 : T k → ℝ := fun r => (m' r).toReal * (if r ∈ R then 1 else 0) with hg1
    have hf1s : Summable fun τo => ‖f1 τo‖ := by
      refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun τo => ?_)
        ((pmf_summable_toReal (ts.β k τk)).mul_right B)
      simp only [hf1, Real.norm_eq_abs, abs_mul, abs_of_nonneg ENNReal.toReal_nonneg]
      exact mul_le_mul_of_nonneg_left (hB τo) ENNReal.toReal_nonneg
    have hg1s : Summable fun r => ‖g1 r‖ := by
      refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun r => ?_)
        (pmf_summable_toReal m')
      simp only [hg1, Real.norm_eq_abs, abs_mul, abs_of_nonneg ENNReal.toReal_nonneg]
      split_ifs <;> simp
    have hprod : Summable fun z : Others T k × T k => f1 z.1 * g1 z.2 :=
      (summable_mul_of_summable_norm hf1s hg1s)
    have hrw : ∀ p : Others T k × T k,
        (ts.β k τk p.1).toReal * (m' p.2).toReal *
          (vu k (q (join k p.2 p.1)) (ts.payoff (join k τk p.1)) - t' k (join k p.2 p.1)) =
        (ts.β k τk p.1).toReal * (m' p.2).toReal *
          (vu k (q (join k p.2 p.1)) (ts.payoff (join k τk p.1)) - t k (join k p.2 p.1)) +
        f1 p.1 * g1 p.2 := by
      intro p
      rw [ht']
      simp only [hf1, hg1]
      split_ifs <;> ring
    refine ⟨?_, ?_⟩
    · rw [summable_iff_emb]
      simp only [hrw]
      exact hs.add hprod
    · rw [eu_eq_emb, eu_eq_emb]
      simp only [hrw]
      rw [hs.tsum_add hprod, tsum_mul_tsum_of_summable_norm hf1s hg1s]
  obtain ⟨hs1, he1⟩ := key m (hbic τk m).1
  obtain ⟨-, he2⟩ := key (truthful T k τk) (hbic τk (truthful T k τk)).1
  refine ⟨hs1, ?_⟩
  rw [he1, he2]
  have hM1 : ∑' r, ((truthful T k τk) r).toReal * (if r ∈ R then (1:ℝ) else 0) =
      if τk ∈ R then 1 else 0 := by
    rw [tsum_eq_single τk]
    · simp [truthful]
    · intro r hr; simp [truthful, PMF.pure_apply, hr]
  have hMle : ∑' r, (m r).toReal * (if r ∈ R then (1:ℝ) else 0) ≤ 1 := by
    refine le_of_le_of_eq ?_ (pmf_tsum_toReal m)
    refine Summable.tsum_le_tsum (fun r => ?_) ?_ (pmf_summable_toReal m)
    · by_cases h : r ∈ R <;> simp [h]
    · refine Summable.of_nonneg_of_le (fun r => ?_) (fun r => ?_) (pmf_summable_toReal m)
      · by_cases h : r ∈ R <;> simp [h]
      · by_cases h : r ∈ R <;> simp [h]
  have hM0 : 0 ≤ ∑' r, (m r).toReal * (if r ∈ R then (1:ℝ) else 0) :=
    tsum_nonneg fun r => by by_cases h : r ∈ R <;> simp [h]
  have h3 := (hbic τk m).2
  rw [hM1]
  by_cases hk : τk ∈ R
  · rw [if_pos hk]
    have := hG.1 hk
    nlinarith
  · rw [if_neg hk]
    have := hG.2 hk
    nlinarith


theorem ms_eq {α : Type*} (μ : PMF α) (S : Set α) :
    (μ.toOuterMeasure S).toReal = ∑' a, (μ a).toReal * (if a ∈ S then 1 else 0) := by
  rw [PMF.toOuterMeasure_apply, ENNReal.tsum_toReal_eq]
  · refine tsum_congr fun a => ?_
    by_cases h : a ∈ S <;> simp [h, Set.indicator]
  · intro a; by_cases h : a ∈ S <;> simp [h, Set.indicator, PMF.apply_ne_top]

theorem ms_summable {α : Type*} (μ : PMF α) (S : Set α) :
    Summable fun a => (μ a).toReal * (if a ∈ S then (1:ℝ) else 0) :=
  Summable.of_nonneg_of_le (fun a => by by_cases h : a ∈ S <;> simp [h])
    (fun a => by by_cases h : a ∈ S <;> simp [h]) (pmf_summable_toReal μ)

theorem G_eval {α : Type*} (μ : PMF α) (E F : Set α) (hF : 0 < μ.toOuterMeasure F) (x y : ℝ) :
    ∑' a, (μ a).toReal * (if a ∈ F then (if a ∈ E then x else y) else 0) =
      (μ.toOuterMeasure F).toReal * (x * (condProb μ E F).toReal +
        y * (1 - (condProb μ E F).toReal)) ∧
      0 < (μ.toOuterMeasure F).toReal ∧ 0 ≤ (condProb μ E F).toReal ∧
      (condProb μ E F).toReal ≤ 1 := by
  have hfin : ∀ S, μ.toOuterMeasure S ≠ ⊤ := fun S =>
    ne_top_of_le_ne_top ENNReal.one_ne_top (by
      rw [PMF.toOuterMeasure_apply, ← μ.tsum_coe]
      exact ENNReal.tsum_le_tsum fun a => Set.indicator_le_self _ _ a)
  have hfpos : 0 < (μ.toOuterMeasure F).toReal := ENNReal.toReal_pos hF.ne' (hfin F)
  have hP : (condProb μ E F).toReal =
      (μ.toOuterMeasure (E ∩ F)).toReal / (μ.toOuterMeasure F).toReal := by
    unfold condProb; rw [ENNReal.toReal_div]
  have hsplit : (μ.toOuterMeasure F).toReal =
      (μ.toOuterMeasure (E ∩ F)).toReal + (μ.toOuterMeasure (F \ E)).toReal := by
    rw [ms_eq, ms_eq, ms_eq, ← (ms_summable μ _).tsum_add (ms_summable μ _)]
    refine tsum_congr fun a => ?_
    by_cases h1 : a ∈ F <;> by_cases h2 : a ∈ E <;> simp [h1, h2]
  have hG : ∑' a, (μ a).toReal * (if a ∈ F then (if a ∈ E then x else y) else 0) =
      x * (μ.toOuterMeasure (E ∩ F)).toReal + y * (μ.toOuterMeasure (F \ E)).toReal := by
    rw [ms_eq, ms_eq, ← tsum_mul_left, ← tsum_mul_left,
      ← ((ms_summable μ _).mul_left x).tsum_add ((ms_summable μ _).mul_left y)]
    refine tsum_congr fun a => ?_
    by_cases h1 : a ∈ F <;> by_cases h2 : a ∈ E <;> simp [h1, h2] <;> ring
  have hd : 0 ≤ (μ.toOuterMeasure (F \ E)).toReal := ENNReal.toReal_nonneg
  have ha : 0 ≤ (μ.toOuterMeasure (E ∩ F)).toReal := ENNReal.toReal_nonneg
  refine ⟨?_, hfpos, ENNReal.toReal_nonneg, ?_⟩
  · rw [hG, hP]
    field_simp
    rw [hsplit]; ring
  · rw [hP, div_le_one hfpos]; linarith

theorem bet_ineq (p ε c : ℝ) (hp : p ∈ Set.Ioo (0 : ℝ) 1) (hε : ε ∈ Set.Ioo (0 : ℝ) 1)
    (hc : (p - ε) / (1 - (p - ε)) < c ∧ c < (p + ε) / (1 - (p + ε))) :
    (∀ P : ℝ, P ≤ p - ε → 0 ≤ -P + c * (1 - P)) ∧
      (∀ P : ℝ, p + ε ≤ P → P ≤ 1 → -P + c * (1 - P) ≤ 0) := by
  obtain ⟨hp0, hp1⟩ := hp
  obtain ⟨he0, he1⟩ := hε
  have hd : 0 < 1 - (p - ε) := by linarith
  have hlow : p - ε < c * (1 - (p - ε)) := by
    have := hc.1; rwa [div_lt_iff₀ hd] at this
  have hc1 : 0 < c + 1 := by nlinarith
  refine ⟨fun P hP => by nlinarith, fun P hP hP1 => ?_⟩
  by_cases hd2 : 0 < 1 - (p + ε)
  · have hup : c * (1 - (p + ε)) < p + ε := by
      have := hc.2; rwa [lt_div_iff₀ hd2] at this
    nlinarith
  · have : P = 1 := by linarith
    subst this; linarith

theorem betting_core {Θ T : ι → Type*}
    {A : Type*} (ts : TypeSpace Θ T) (vu : ι → A → (∀ i, Θ i) → ℝ)
    (hN : 3 ≤ Fintype.card ι) (i j : ι) (hij : i ≠ j) (p ε : ℝ)
    (hp : p ∈ Set.Ioo (0 : ℝ) 1) (hε : ε ∈ Set.Ioo (0 : ℝ) 1)
    (Ti : Set (T i)) (Tj : Set (T j)) (Tij : Set (∀ k : {k : ι // k ≠ i ∧ k ≠ j}, T k))
    (hTij : Tij ≠ Set.univ)
    (h1i : ∀ τi : T i, 0 < (ts.β i τi).toOuterMeasure {τo | τo ⟨j, hij.symm⟩ ∈ Tj})
    (h1j : ∀ τj : T j, 0 < (ts.β j τj).toOuterMeasure {τo | τo ⟨i, hij⟩ ∈ Ti})
    (h2i_in : ∀ τi ∈ Ti, (condProb (ts.β i τi) {τo | (fun k : {k : ι // k ≠ i ∧ k ≠ j} => τo ⟨k.1, k.2.1⟩) ∈ Tij}
      {τo | τo ⟨j, hij.symm⟩ ∈ Tj}).toReal ≤ p - ε)
    (h2i_out : ∀ τi ∉ Ti, p + ε ≤ (condProb (ts.β i τi) {τo | (fun k : {k : ι // k ≠ i ∧ k ≠ j} => τo ⟨k.1, k.2.1⟩) ∈ Tij}
      {τo | τo ⟨j, hij.symm⟩ ∈ Tj}).toReal)
    (h2j_in : ∀ τj ∈ Tj, p + ε ≤ (condProb (ts.β j τj) {τo | (fun k : {k : ι // k ≠ i ∧ k ≠ j} => τo ⟨k.1, k.2.2⟩) ∈ Tij}
      {τo | τo ⟨i, hij⟩ ∈ Ti}).toReal)
    (h2j_out : ∀ τj ∉ Tj, (condProb (ts.β j τj) {τo | (fun k : {k : ι // k ≠ i ∧ k ≠ j} => τo ⟨k.1, k.2.2⟩) ∈ Tij}
      {τo | τo ⟨i, hij⟩ ∈ Ti}).toReal ≤ p - ε)
    (q : (∀ k, T k) → A) (t : ι → (∀ k, T k) → ℝ)
    (hbic : IsBayesEq ts (qlUtility vu) (qlDirect ts q t) (truthful T))
    (c : ℝ) (hc : (p - ε) / (1 - (p - ε)) < c ∧ c < (p + ε) / (1 - (p + ε)))
    (t' : ι → (∀ k, T k) → ℝ)
    (h4 : ∀ k, k ≠ i → k ≠ j → t' k = t k)
    (h5in : ∀ τ : ∀ k, T k, τ i ∈ Ti → τ j ∈ Tj → (fun k : {k : ι // k ≠ i ∧ k ≠ j} => τ k) ∈ Tij →
      t' i τ = t i τ + 1 ∧ t' j τ = t j τ - 1)
    (h5out : ∀ τ : ∀ k, T k, τ i ∈ Ti → τ j ∈ Tj → (fun k : {k : ι // k ≠ i ∧ k ≠ j} => τ k) ∉ Tij →
      t' i τ = t i τ - c ∧ t' j τ = t j τ + c)
    (h6 : ∀ τ : ∀ k, T k, (τ i ∉ Ti ∨ τ j ∉ Tj) → t' i τ = t i τ ∧ t' j τ = t j τ) :
    IsBayesEq ts (qlUtility vu) (qlDirect ts q t') (truthful T) := by
  obtain ⟨hI1, hI2⟩ := bet_ineq p ε c hp hε hc
  intro k τk m
  by_cases hki : k = i
  · subst hki
    let E : Set (Others T k) := {τo | (fun l : {l : ι // l ≠ k ∧ l ≠ j} => τo ⟨l.1, l.2.1⟩) ∈ Tij}
    let F : Set (Others T k) := {τo | τo ⟨j, hij.symm⟩ ∈ Tj}
    refine bet_step ts vu q t t' k Ti
      (fun τo => if τo ∈ F then (if τo ∈ E then -1 else c) else 0) (1 + |c|) ?_ ?_
      (fun τk m => hbic k τk m) τk ?_ m
    · intro τo
      by_cases h1 : τo ∈ F <;> by_cases h2 : τo ∈ E <;> simp [h1, h2] <;>
        linarith [abs_nonneg c, le_abs_self c, neg_abs_le c]
    · intro r τo
      have hjk : j ≠ k := hij.symm
      have e1 : join k r τo k = r := join_self _ _ _
      have e2 : join k r τo j = τo ⟨j, hjk⟩ := join_ne _ _ _ _ hjk
      have e3 : (fun l : {l : ι // l ≠ k ∧ l ≠ j} => join k r τo l) =
          (fun l : {l : ι // l ≠ k ∧ l ≠ j} => τo ⟨l.1, l.2.1⟩) := by
        funext l; exact join_ne _ _ _ _ l.2.1
      by_cases hr : r ∈ Ti
      · by_cases h1 : τo ∈ F
        · by_cases h2 : τo ∈ E
          · have := (h5in (join k r τo) (by rw [e1]; exact hr) (by rw [e2]; exact h1)
              (by rw [e3]; exact h2)).1
            simp only [hr, h1, h2, if_true]; rw [this]; try ring
          · have := (h5out (join k r τo) (by rw [e1]; exact hr) (by rw [e2]; exact h1)
              (by rw [e3]; exact h2)).1
            simp only [hr, h1, h2, if_true, if_false]; rw [this]; try ring
        · have := (h6 (join k r τo) (Or.inr (by rw [e2]; exact h1))).1
          simp only [hr, h1, if_true, if_false]; rw [this]; try ring
      · have := (h6 (join k r τo) (Or.inl (by rw [e1]; exact hr))).1
        simp only [hr, if_false]; rw [this]; try ring
    · obtain ⟨hG, hf, -, hP1⟩ := G_eval (ts.β k τk) E F (h1i τk) (-1) c
      rw [hG]
      constructor
      · intro h
        have := hI1 _ (h2i_in τk h)
        nlinarith
      · intro h
        have := hI2 _ (h2i_out τk h) hP1
        nlinarith
  by_cases hkj : k = j
  · subst hkj
    let E : Set (Others T k) := {τo | (fun l : {l : ι // l ≠ i ∧ l ≠ k} => τo ⟨l.1, l.2.2⟩) ∈ Tij}
    let F : Set (Others T k) := {τo | τo ⟨i, hij⟩ ∈ Ti}
    refine bet_step ts vu q t t' k Tj
      (fun τo => if τo ∈ F then (if τo ∈ E then 1 else -c) else 0) (1 + |c|) ?_ ?_
      (fun τk m => hbic k τk m) τk ?_ m
    · intro τo
      by_cases h1 : τo ∈ F <;> by_cases h2 : τo ∈ E <;> simp [h1, h2] <;>
        linarith [abs_nonneg c, le_abs_self c, neg_abs_le c]
    · intro r τo
      have e1 : join k r τo k = r := join_self _ _ _
      have e2 : join k r τo i = τo ⟨i, hij⟩ := join_ne _ _ _ _ hij
      have e3 : (fun l : {l : ι // l ≠ i ∧ l ≠ k} => join k r τo l) =
          (fun l : {l : ι // l ≠ i ∧ l ≠ k} => τo ⟨l.1, l.2.2⟩) := by
        funext l; exact join_ne _ _ _ _ l.2.2
      by_cases hr : r ∈ Tj
      · by_cases h1 : τo ∈ F
        · by_cases h2 : τo ∈ E
          · have := (h5in (join k r τo) (by rw [e2]; exact h1) (by rw [e1]; exact hr)
              (by rw [e3]; exact h2)).2
            simp only [hr, h1, h2, if_true]; rw [this]; try ring
          · have := (h5out (join k r τo) (by rw [e2]; exact h1) (by rw [e1]; exact hr)
              (by rw [e3]; exact h2)).2
            simp only [hr, h1, h2, if_true, if_false]; rw [this]; try ring
        · have := (h6 (join k r τo) (Or.inl (by rw [e2]; exact h1))).2
          simp only [hr, h1, if_true, if_false]; rw [this]; try ring
      · have := (h6 (join k r τo) (Or.inr (by rw [e1]; exact hr))).2
        simp only [hr, if_false]; rw [this]; try ring
    · obtain ⟨hG, hf, -, hP1⟩ := G_eval (ts.β k τk) E F (h1j τk) 1 (-c)
      rw [hG]
      constructor
      · intro h
        have := hI2 _ (h2j_in τk h) hP1
        nlinarith
      · intro h
        have := hI1 _ (h2j_out τk h)
        nlinarith
  · have ht : t' k = t k := h4 k hki hkj
    have hs := hbic k τk m
    have e : ∀ m', interimEU ts (qlUtility vu) (qlDirect ts q t') (truthful T) k τk m' =
        interimEU ts (qlUtility vu) (qlDirect ts q t) (truthful T) k τk m' := by
      intro m'; rw [eu_eq_emb, eu_eq_emb, ht]
    refine ⟨?_, ?_⟩
    · rw [summable_iff_emb, ht, ← summable_iff_emb]; exact hs.1
    · rw [e, e]; exact hs.2

end core
end MechanismDesign.Robust

open MechanismDesign.Robust


theorem solution {ι : Type} [Fintype ι] [DecidableEq ι] {Θ T : ι → Type*}
    {A : Type*} (ts : TypeSpace Θ T) (vu : ι → A → (∀ i, Θ i) → ℝ)
    (hN : 3 ≤ Fintype.card ι) (i j : ι) (hij : i ≠ j) (p ε : ℝ)
    (hp : p ∈ Set.Ioo (0 : ℝ) 1) (hε : ε ∈ Set.Ioo (0 : ℝ) 1)
    (Ti : Set (T i)) (Tj : Set (T j)) (Tij : Set (∀ k : {k : ι // k ≠ i ∧ k ≠ j}, T k))
    (hTij : Tij ≠ Set.univ)
    (h1i : ∀ τi : T i, 0 < (ts.β i τi).toOuterMeasure {τo | τo ⟨j, hij.symm⟩ ∈ Tj})
    (h1j : ∀ τj : T j, 0 < (ts.β j τj).toOuterMeasure {τo | τo ⟨i, hij⟩ ∈ Ti})
    (h2i_in : ∀ τi ∈ Ti, (condProb (ts.β i τi) {τo | (fun k : {k : ι // k ≠ i ∧ k ≠ j} => τo ⟨k.1, k.2.1⟩) ∈ Tij}
      {τo | τo ⟨j, hij.symm⟩ ∈ Tj}).toReal ≤ p - ε)
    (h2i_out : ∀ τi ∉ Ti, p + ε ≤ (condProb (ts.β i τi) {τo | (fun k : {k : ι // k ≠ i ∧ k ≠ j} => τo ⟨k.1, k.2.1⟩) ∈ Tij}
      {τo | τo ⟨j, hij.symm⟩ ∈ Tj}).toReal)
    (h2j_in : ∀ τj ∈ Tj, p + ε ≤ (condProb (ts.β j τj) {τo | (fun k : {k : ι // k ≠ i ∧ k ≠ j} => τo ⟨k.1, k.2.2⟩) ∈ Tij}
      {τo | τo ⟨i, hij⟩ ∈ Ti}).toReal)
    (h2j_out : ∀ τj ∉ Tj, (condProb (ts.β j τj) {τo | (fun k : {k : ι // k ≠ i ∧ k ≠ j} => τo ⟨k.1, k.2.2⟩) ∈ Tij}
      {τo | τo ⟨i, hij⟩ ∈ Ti}).toReal ≤ p - ε)
    (q : (∀ k, T k) → A) (t : ι → (∀ k, T k) → ℝ)
    (hbic : IsBayesEq ts (qlUtility vu) (qlDirect ts q t) (truthful T))
    (c : ℝ) (hc : (p - ε) / (1 - (p - ε)) < c ∧ c < (p + ε) / (1 - (p + ε)))
    (t' : ι → (∀ k, T k) → ℝ)
    (h4 : ∀ k, k ≠ i → k ≠ j → t' k = t k)
    (h5in : ∀ τ : ∀ k, T k, τ i ∈ Ti → τ j ∈ Tj → (fun k : {k : ι // k ≠ i ∧ k ≠ j} => τ k) ∈ Tij →
      t' i τ = t i τ + 1 ∧ t' j τ = t j τ - 1)
    (h5out : ∀ τ : ∀ k, T k, τ i ∈ Ti → τ j ∈ Tj → (fun k : {k : ι // k ≠ i ∧ k ≠ j} => τ k) ∉ Tij →
      t' i τ = t i τ - c ∧ t' j τ = t j τ + c)
    (h6 : ∀ τ : ∀ k, T k, (τ i ∉ Ti ∨ τ j ∉ Tj) → t' i τ = t i τ ∧ t' j τ = t j τ) :
    IsBayesEq ts (qlUtility vu) (qlDirect ts q t') (truthful T) := by
  exact betting_core ts vu hN i j hij p ε hp hε Ti Tj Tij hTij h1i h1j h2i_in h2i_out h2j_in h2j_out q t hbic c hc t' h4 h5in h5out h6
