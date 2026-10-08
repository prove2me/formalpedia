-- Prove2me | solution 1 for MechanismDesign.Robust.belief_revelation
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T10:31:07.806028+00:00
-- url     : https://prove2.me/submissions/aef034b4-7acd-4a37-96e3-f48081264e0d

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


theorem others_join (i : ι) (r : T i) (τo : Others T i) : others (join i r τo) i = τo := by
  funext j
  simp only [others]
  exact join_ne i r τo j.1 j.2

noncomputable def Wv (ts : TypeSpace Θ T) [∀ i, Fintype (T i)] (vu : ι → A → (∀ i, Θ i) → ℝ)
    (q : (∀ i, T i) → A) (t : ι → (∀ i, T i) → ℝ) (i : ι) (τi r : T i) : ℝ :=
  ∑ τo : Others T i, (ts.β i τi τo).toReal *
    (vu i (q (join i r τo)) (ts.payoff (join i τi τo)) - t i (join i r τo))

theorem eu_fin (ts : TypeSpace Θ T) [∀ i, Fintype (T i)] (vu : ι → A → (∀ i, Θ i) → ℝ)
    (q : (∀ i, T i) → A) (t : ι → (∀ i, T i) → ℝ) (i : ι) (τi : T i) (m : PMF (T i)) :
    interimEU ts (qlUtility vu) (qlDirect ts q t) (truthful T) i τi m =
      ∑ r, (m r).toReal * Wv ts vu q t i τi r := by
  rw [eu_eq_emb, tsum_fintype, Fintype.sum_prod_type_right]
  unfold Wv
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun τo _ => ?_
  ring

theorem eu_pure (ts : TypeSpace Θ T) [∀ i, Fintype (T i)] (vu : ι → A → (∀ i, Θ i) → ℝ)
    (q : (∀ i, T i) → A) (t : ι → (∀ i, T i) → ℝ) (i : ι) (τi r : T i) :
    interimEU ts (qlUtility vu) (qlDirect ts q t) (truthful T) i τi (PMF.pure r) =
      Wv ts vu q t i τi r := by
  rw [eu_fin, Finset.sum_eq_single r]
  · simp
  · intro b _ hb; simp [PMF.pure_apply, hb]
  · simp

theorem pmf_sum_toReal {α : Type*} [Fintype α] (m : PMF α) : ∑ a, (m a).toReal = 1 := by
  rw [← ENNReal.toReal_sum (fun a _ => PMF.apply_ne_top m a)]
  have := m.tsum_coe
  rw [tsum_fintype] at this
  rw [this]; simp

theorem separation {κ : Type*} [Fintype κ] {α : Type*} [Finite α] (b : α → κ → ℝ)
    (hb : ∀ a, ∑ k, b a k = 1) (S : Set α) (r : α) (hr : b r ∉ convexHull ℝ (b '' S))
    (C : ℝ) (hC : 0 ≤ C) :
    ∃ z : κ → ℝ, ∑ k, b r k * z k = 0 ∧ ∀ a ∈ S, C ≤ ∑ k, b a k * z k := by
  have hK : IsClosed (convexHull ℝ (b '' S)) :=
    (Set.Finite.isCompact_convexHull (𝕜 := ℝ) ((Set.toFinite S).image b)).isClosed
  obtain ⟨f, u, hfu, hK2⟩ := geometric_hahn_banach_point_closed (convex_convexHull ℝ _) hK hr
  set c : κ → ℝ := fun k => f (fun j => if k = j then 1 else 0) with hc
  have hf : ∀ y, f y = ∑ k, y k * c k := by
    intro y
    have := LinearMap.pi_apply_eq_sum_univ (f : (κ → ℝ) →ₗ[ℝ] ℝ) y
    simpa [hc, smul_eq_mul] using this
  set δ := u - f (b r) with hδ
  have hδpos : 0 < δ := by rw [hδ]; linarith
  refine ⟨fun k => (C / δ) * (c k - f (b r)), ?_, ?_⟩
  · have : ∑ k, b r k * ((C / δ) * (c k - f (b r))) =
        (C / δ) * (∑ k, b r k * c k - f (b r) * ∑ k, b r k) := by
      rw [mul_sub, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      ring
    rw [this, hb, ← hf]; ring
  · intro a ha
    have hmem : b a ∈ convexHull ℝ (b '' S) := subset_convexHull ℝ _ ⟨a, ha, rfl⟩
    have h1 := hK2 _ hmem
    have : ∑ k, b a k * ((C / δ) * (c k - f (b r))) =
        (C / δ) * (∑ k, b a k * c k - f (b r) * ∑ k, b a k) := by
      rw [mul_sub, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      ring
    rw [this, hb, ← hf, mul_one]
    have hCd : 0 ≤ C / δ := div_nonneg hC hδpos.le
    calc C = (C / δ) * δ := by field_simp
      _ ≤ (C / δ) * (f (b a) - f (b r)) := by
        apply mul_le_mul_of_nonneg_left _ hCd; rw [hδ]; linarith

theorem belief_revelation_core {Θ T : ι → Type*} {A : Type*}
    [∀ i, Fintype (T i)] (ts : TypeSpace Θ T) (vu : ι → A → (∀ i, Θ i) → ℝ)
    (hconv : ∀ i (τi : T i), (fun τo => (ts.β i τi τo).toReal) ∉
      convexHull ℝ ((fun τi' : T i => fun τo => (ts.β i τi' τo).toReal) ''
        {τi' | ts.β i τi' ≠ ts.β i τi}))
    (q : (∀ i, T i) → A) (t : ι → (∀ i, T i) → ℝ)
    (hsame : ∀ i (τi τi' : T i), ts.β i τi = ts.β i τi' →
      interimEU ts (qlUtility vu) (qlDirect ts q t) (truthful T) i τi (PMF.pure τi') ≤
        interimEU ts (qlUtility vu) (qlDirect ts q t) (truthful T) i τi (PMF.pure τi)) :
    ∃ (q' : (∀ i, T i) → A) (t' : ι → (∀ i, T i) → ℝ),
      IsBayesEq ts (qlUtility vu) (qlDirect ts q' t') (truthful T) ∧
      (∀ τ, q' τ = q τ) ∧
      ∀ i (τi : T i), interimPayment ts t' i τi = interimPayment ts t i τi := by
  have hz : ∀ i (r : T i), ∃ z : Others T i → ℝ,
      ∑ τo, (ts.β i r τo).toReal * z τo = 0 ∧
      ∀ τi ∈ {τi' | ts.β i τi' ≠ ts.β i r},
        (∑ τi' : T i, |Wv ts vu q t i τi' r - Wv ts vu q t i τi' τi'|) ≤
          ∑ τo, (ts.β i τi τo).toReal * z τo := by
    intro i r
    exact separation (fun τi' τo => (ts.β i τi' τo).toReal) (fun a => pmf_sum_toReal _) _ r
      (hconv i r) _ (Finset.sum_nonneg fun _ _ => abs_nonneg _)
  choose z hz0 hzC using hz
  refine ⟨q, fun i τ => t i τ + z i (τ i) (others τ i), ?_, fun _ => rfl, ?_⟩
  · intro i τi m
    refine ⟨(summable_iff_emb ts vu _ _ i τi m).2 Summable.of_finite, ?_⟩
    have hW : ∀ r, Wv ts vu q (fun i τ => t i τ + z i (τ i) (others τ i)) i τi r =
        Wv ts vu q t i τi r - ∑ τo, (ts.β i τi τo).toReal * z i r τo := by
      intro r
      unfold Wv
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun τo _ => ?_
      dsimp only
      rw [join_self, others_join]; ring
    have hle : ∀ r, Wv ts vu q (fun i τ => t i τ + z i (τ i) (others τ i)) i τi r ≤
        Wv ts vu q (fun i τ => t i τ + z i (τ i) (others τ i)) i τi τi := by
      intro r
      rw [hW, hW, hz0, sub_zero]
      by_cases hb : ts.β i τi = ts.β i r
      · have := hsame i τi r hb
        rw [eu_pure, eu_pure] at this
        have h0 : ∑ τo, (ts.β i τi τo).toReal * z i r τo = 0 := by rw [hb]; exact hz0 i r
        rw [h0]; linarith
      · have h1 := hzC i r τi hb
        have h2 : Wv ts vu q t i τi r - Wv ts vu q t i τi τi ≤
            ∑ τi' : T i, |Wv ts vu q t i τi' r - Wv ts vu q t i τi' τi'| :=
          (le_abs_self _).trans (Finset.single_le_sum (f := fun τi' =>
            |Wv ts vu q t i τi' r - Wv ts vu q t i τi' τi'|) (fun _ _ => abs_nonneg _)
            (Finset.mem_univ τi))
        linarith
    rw [eu_fin, eu_fin]
    calc ∑ r, (m r).toReal * Wv ts vu q (fun i τ => t i τ + z i (τ i) (others τ i)) i τi r
        ≤ ∑ r, (m r).toReal * Wv ts vu q (fun i τ => t i τ + z i (τ i) (others τ i)) i τi τi :=
          Finset.sum_le_sum fun r _ => mul_le_mul_of_nonneg_left (hle r) ENNReal.toReal_nonneg
      _ = ∑ r, ((truthful T i τi) r).toReal *
            Wv ts vu q (fun i τ => t i τ + z i (τ i) (others τ i)) i τi r := by
          rw [← Finset.sum_mul, pmf_sum_toReal, one_mul, Finset.sum_eq_single τi]
          · simp [truthful]
          · intro b _ hb; simp [truthful, PMF.pure_apply, hb]
          · simp
  · intro i τi
    unfold interimPayment
    rw [tsum_fintype, tsum_fintype]
    simp only [join_self, others_join, mul_add, Finset.sum_add_distrib, hz0, add_zero]

end core
end MechanismDesign.Robust

open MechanismDesign.Robust


theorem solution {ι : Type} [Fintype ι] [DecidableEq ι] {Θ T : ι → Type*} {A : Type*}
    [∀ i, Fintype (T i)] (ts : TypeSpace Θ T) (vu : ι → A → (∀ i, Θ i) → ℝ)
    (hconv : ∀ i (τi : T i), (fun τo => (ts.β i τi τo).toReal) ∉
      convexHull ℝ ((fun τi' : T i => fun τo => (ts.β i τi' τo).toReal) ''
        {τi' | ts.β i τi' ≠ ts.β i τi}))
    (q : (∀ i, T i) → A) (t : ι → (∀ i, T i) → ℝ)
    (hsame : ∀ i (τi τi' : T i), ts.β i τi = ts.β i τi' →
      interimEU ts (qlUtility vu) (qlDirect ts q t) (truthful T) i τi (PMF.pure τi') ≤
        interimEU ts (qlUtility vu) (qlDirect ts q t) (truthful T) i τi (PMF.pure τi)) :
    ∃ (q' : (∀ i, T i) → A) (t' : ι → (∀ i, T i) → ℝ),
      IsBayesEq ts (qlUtility vu) (qlDirect ts q' t') (truthful T) ∧
      (∀ τ, q' τ = q τ) ∧
      ∀ i (τi : T i), interimPayment ts t' i τi = interimPayment ts t i τi := by
  exact belief_revelation_core ts vu hconv q t hsame
