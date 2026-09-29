-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.transitionStable_family_one_ne_bot_of_odd_signClass
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/99425fc5-b5bc-541c-baca-d1605cc52db9

import Mathlib
import Theorems.Thm_LanglandsTunnell_CubicInduction_compactPicture_eq_zero_of_lowering_eq_zero_of_three_le
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_transitionStable_family_one_ne_bot_of_odd_signClass

set_option autoImplicit false

open MvPolynomial

namespace O1B

theorem degree_fin3 (d : Fin 3 →₀ ℕ) : Finsupp.degree d = d 0 + d 1 + d 2 := by
  have h : Finsupp.degree d = ∑ i : Fin 3, d i := by
    show ∑ i ∈ d.support, d i = _
    exact Finset.sum_subset (Finset.subset_univ _) (fun i _ hi => by simpa using hi)
  rw [h, Fin.sum_univ_three]

theorem coeff_aeval_scale (u : Fin 3 → ℂ) (p : MvPolynomial (Fin 3) ℂ) (d : Fin 3 →₀ ℕ) :
    coeff d (aeval (fun b : Fin 3 => C (u b) * X b) p) = (∏ b : Fin 3, u b ^ d b) * coeff d p := by
  classical
  induction p using MvPolynomial.induction_on' with
  | monomial d' r =>
    rw [aeval_monomial, Finsupp.prod_fintype _ _ (fun i => by simp)]
    simp only [mul_pow, ← map_pow, Finset.prod_mul_distrib, ← map_prod, MvPolynomial.algebraMap_eq]
    have hmono : (∏ i : Fin 3, (X i : MvPolynomial (Fin 3) ℂ) ^ d' i) = monomial d' 1 := by
      rw [monomial_eq, C_1, one_mul, Finsupp.prod_fintype _ _ (fun i => by simp)]
    rw [hmono, ← mul_assoc, ← map_mul, C_mul_monomial, mul_one, coeff_monomial, coeff_monomial]
    by_cases h : d' = d
    · subst h; simp [mul_comm]
    · simp [h]
  | add p q hp hq => simp only [map_add, coeff_add, hp, hq, mul_add]

theorem parity_of_flip {p : MvPolynomial (Fin 3) ℂ} (a : Fin 3) (s : ℂ)
    (h : aeval (fun b : Fin 3 => C (if b = a then (-1 : ℂ) else 1) * X b) p = C s * p)
    (d : Fin 3 →₀ ℕ) (hd : coeff d p ≠ 0) : (-1 : ℂ) ^ d a = s := by
  classical
  have h2 := congrArg (coeff d) h
  rw [coeff_aeval_scale, coeff_C_mul] at h2
  have hprod : (∏ b : Fin 3, (if b = a then (-1 : ℂ) else 1) ^ d b) = (-1) ^ d a := by
    rw [Fintype.prod_eq_single a (fun b hb => by simp [hb])]; simp
  rw [hprod] at h2
  exact mul_right_cancel₀ hd h2

theorem neg_one_pow_of_mod_two (n : ℕ) : (-1 : ℂ) ^ n = (-1) ^ (n % 2) := by
  conv_lhs => rw [← Nat.div_add_mod n 2, pow_add, pow_mul]
  simp

theorem mod_two_eq_one_of_pow {n : ℕ} (h : (-1 : ℂ) ^ n = -1) : n % 2 = 1 := by
  rcases Nat.mod_two_eq_zero_or_one n with h0 | h1
  · rw [neg_one_pow_of_mod_two, h0] at h; norm_num at h
  · exact h1

theorem mod_two_eq_zero_of_pow {n : ℕ} (h : (-1 : ℂ) ^ n = 1) : n % 2 = 0 := by
  rcases Nat.mod_two_eq_zero_or_one n with h0 | h1
  · exact h0
  · rw [neg_one_pow_of_mod_two, h1] at h; norm_num at h

end O1B

open O1B in
theorem solution
    (σ σ₃ : ℝ) (b₀ c₀ : Fin 3) (hb₀ : b₀ ≠ 0) (hc₀ : c₀ ≠ 0) (hbc : b₀ ≠ c₀)
    (ν : Fin 3 → ℂ) (hν0 : ν 0 = -1 / 2 + σ * Complex.I) (hνb : ν b₀ = 1 / 2 + σ * Complex.I)
    (hνc : ν c₀ = σ₃ * Complex.I)
    (ε : Fin 3 → Fin 2) (hodd : ε 0 ≠ ε b₀)
    (S : ℕ → Submodule ℂ (MvPolynomial (Fin 3) ℂ)) :
    let Ξ : (Fin 3 → ℂ) → MvPolynomial (Fin 3) ℂ → Matrix (Fin 3) (Fin 3) (MvPolynomial (Fin 3) ℂ) :=
      fun ν p => Matrix.of fun c d =>
        if c = d then MvPolynomial.C (2 * (ν c + (![1, 0, -1] : Fin 3 → ℂ) c)) * p
        else -(MvPolynomial.X (max c d) * MvPolynomial.pderiv (min c d) p -
          MvPolynomial.X (min c d) * MvPolynomial.pderiv (max c d) p)
    let lower₂ : Matrix (Fin 3) (Fin 3) (MvPolynomial (Fin 3) ℂ) → MvPolynomial (Fin 3) ℂ :=
      fun M => ∑ c : Fin 3, ∑ d : Fin 3, MvPolynomial.pderiv c (MvPolynomial.pderiv d (M c d))
    let lower₁ : Matrix (Fin 3) (Fin 3) (MvPolynomial (Fin 3) ℂ) → MvPolynomial (Fin 3) ℂ :=
      fun M => ∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3, ∑ d : Fin 3,
        MvPolynomial.C ((((a : ℕ) : ℂ) - ((c : ℕ) : ℂ)) * (((c : ℕ) : ℂ) - ((d : ℕ) : ℂ)) *
          (((d : ℕ) : ℂ) - ((a : ℕ) : ℂ)) / 2) *
          (MvPolynomial.X c * MvPolynomial.pderiv b (MvPolynomial.pderiv d (M a b)))
    (∀ ℓ, ∀ p : MvPolynomial (Fin 3) ℂ, p ∈ S ℓ →
            p.IsHomogeneous ℓ ∧ (∑ i : Fin 3, MvPolynomial.pderiv i (MvPolynomial.pderiv i p)) = 0) →
    (∀ ℓ, ∀ p ∈ S ℓ, ∀ σ : Fin 3 → Fin 2,
        MvPolynomial.aeval (fun a : Fin 3 => MvPolynomial.C ((-1 : ℂ) ^ (σ a : ℕ)) * MvPolynomial.X a) p =
          MvPolynomial.C ((-1 : ℂ) ^ (∑ a : Fin 3, ((ε a : ℕ) + ℓ + ∑ b : Fin 3, (ε b : ℕ)) * (σ a : ℕ))) * p) →
    (∀ ℓ, ∀ p ∈ S ℓ, lower₂ (Ξ ν p) ∈ S (ℓ - 2) ∧ lower₁ (Ξ ν p) ∈ S (ℓ - 1)) →
    (∃ ℓ, S ℓ ≠ ⊥) → S 1 ≠ ⊥ := by
  intro Ξ lower₂ lower₁ h1 h2 h3 hex
  classical
  have hΞ : Ξ = fun ν p => Matrix.of fun c d =>
        if c = d then MvPolynomial.C (2 * (ν c + (![1, 0, -1] : Fin 3 → ℂ) c)) * p
        else -(MvPolynomial.X (max c d) * MvPolynomial.pderiv (min c d) p -
          MvPolynomial.X (min c d) * MvPolynomial.pderiv (max c d) p) := rfl
  have hlower₁ : lower₁ = fun M => ∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3, ∑ d : Fin 3,
        MvPolynomial.C ((((a : ℕ) : ℂ) - ((c : ℕ) : ℂ)) * (((c : ℕ) : ℂ) - ((d : ℕ) : ℂ)) *
          (((d : ℕ) : ℂ) - ((a : ℕ) : ℂ)) / 2) *
          (MvPolynomial.X c * MvPolynomial.pderiv b (MvPolynomial.pderiv d (M a b))) := rfl

  have hval : ∀ a, (ε a : ℕ) = 0 ∨ (ε a : ℕ) = 1 := fun a => by have := (ε a).isLt; omega
  have h01 : (ε 0 : ℕ) ≠ (ε b₀ : ℕ) := fun h => hodd (Fin.ext h)
  have hcases : (b₀ = 1 ∧ c₀ = 2) ∨ (b₀ = 2 ∧ c₀ = 1) := by
    have hb' : (b₀ : ℕ) ≠ 0 := fun h => hb₀ (Fin.ext h)
    have hc' : (c₀ : ℕ) ≠ 0 := fun h => hc₀ (Fin.ext h)
    have hbc' : (b₀ : ℕ) ≠ (c₀ : ℕ) := fun h => hbc (Fin.ext h)
    have hbl := b₀.isLt
    have hcl := c₀.isLt
    rcases (show ((b₀ : ℕ) = 1 ∧ (c₀ : ℕ) = 2) ∨ ((b₀ : ℕ) = 2 ∧ (c₀ : ℕ) = 1) by omega) with ⟨hb, hc⟩ | ⟨hb, hc⟩
    · exact Or.inl ⟨Fin.ext (by simp [hb]), Fin.ext (by simp [hc])⟩
    · exact Or.inr ⟨Fin.ext (by simp [hb]), Fin.ext (by simp [hc])⟩
  set N : ℕ := ∑ b : Fin 3, (ε b : ℕ) with hN
  have hNeq : N = (ε 0 : ℕ) + (ε 1 : ℕ) + (ε 2 : ℕ) := by rw [hN, Fin.sum_univ_three]

  have hflip : ∀ ℓ, ∀ p ∈ S ℓ, ∀ a : Fin 3,
      aeval (fun b : Fin 3 => C (if b = a then (-1 : ℂ) else 1) * X b) p = C ((-1 : ℂ) ^ ((ε a : ℕ) + ℓ + N)) * p := by
    intro ℓ p hp a
    have h := h2 ℓ p hp (fun b => if b = a then 1 else 0)
    have hexp : (∑ x : Fin 3, ((ε x : ℕ) + ℓ + ∑ b : Fin 3, (ε b : ℕ)) * (((fun b => if b = a then (1 : Fin 2) else 0) x : Fin 2) : ℕ)) =
        (ε a : ℕ) + ℓ + N := by
      rw [Fintype.sum_eq_single a (fun b hb => by simp [hb])]; simp [hN]
    have hfun : (fun b : Fin 3 => C ((-1 : ℂ) ^ (((fun b => if b = a then (1 : Fin 2) else 0) b : Fin 2) : ℕ)) * X b) =
        fun b : Fin 3 => C (if b = a then (-1 : ℂ) else 1) * X b := by
      funext b; by_cases hb : b = a <;> simp [hb]
    rw [hexp, hfun] at h
    exact h

  have hS0 : S 0 = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro p hp
    obtain ⟨hhom, -⟩ := h1 0 p hp
    have hpar : ((ε c₀ : ℕ) + 0 + N) % 2 = 1 := by
      rcases hcases with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
        rcases hval 0 with h0 | h0 <;> rcases hval 1 with hb | hb <;> rcases hval 2 with hc | hc <;> omega
    have hs : ((-1 : ℂ) ^ ((ε c₀ : ℕ) + 0 + N)) = -1 := by rw [neg_one_pow_of_mod_two, hpar]; norm_num
    ext d
    rw [coeff_zero]
    by_contra hd
    have hdeg : Finsupp.degree d = 0 := by
      by_contra hne; exact hd (hhom.coeff_eq_zero hne)
    have hd0 : d = 0 := (Finsupp.degree_eq_zero_iff d).1 hdeg
    have q := parity_of_flip c₀ _ (hflip 0 p hp c₀) d hd
    rw [hs, hd0] at q
    norm_num at q

  have key : (S 2 ≠ ⊥ → S 1 ≠ ⊥) → (∀ ℓ, 3 ≤ ℓ → S ℓ ≠ ⊥ → S (ℓ - 2) ≠ ⊥ ∨ S (ℓ - 1) ≠ ⊥) → S 1 ≠ ⊥ := by
    intro h21 hdesc
    suffices hall : ∀ ℓ, S ℓ ≠ ⊥ → S 1 ≠ ⊥ from hex.elim fun ℓ h => hall ℓ h
    intro ℓ
    induction ℓ using Nat.strong_induction_on with
    | _ ℓ ih =>
      intro h
      rcases (show ℓ = 0 ∨ ℓ = 1 ∨ ℓ = 2 ∨ 3 ≤ ℓ by omega) with rfl | rfl | rfl | hℓ
      · exact absurd hS0 h
      · exact h
      · exact h21 h
      · rcases hdesc ℓ hℓ h with h' | h'
        · exact ih (ℓ - 2) (by omega) h'
        · exact ih (ℓ - 1) (by omega) h'
  rcases hcases with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  ·
    have hν : ν = ![-1 / 2 + σ * Complex.I, 1 / 2 + σ * Complex.I, σ₃ * Complex.I] := by
      funext i; fin_cases i <;> simp [hν0, hνb, hνc]
    subst hν
    refine key ?_ ?_
    · intro hS2
      obtain ⟨p, hp, hp0⟩ := (Submodule.ne_bot_iff _).1 hS2
      obtain ⟨hhom, -⟩ := h1 2 p hp
      have hs2 : ((-1 : ℂ) ^ ((ε 2 : ℕ) + 2 + N)) = -1 := by
        rw [neg_one_pow_of_mod_two, show ((ε 2 : ℕ) + 2 + N) % 2 = 1 by
          rcases hval 0 with h0 | h0 <;> rcases hval 1 with hb | hb <;> rcases hval 2 with hc | hc <;> omega]; norm_num
      by_cases he : (ε 0 : ℕ) = (ε 2 : ℕ)
      ·
        have hs0 : ((-1 : ℂ) ^ ((ε 0 : ℕ) + 2 + N)) = -1 := by
          rw [neg_one_pow_of_mod_two, show ((ε 0 : ℕ) + 2 + N) % 2 = 1 by
            rcases hval 0 with h0 | h0 <;> rcases hval 1 with hb | hb <;> rcases hval 2 with hc | hc <;> omega]; norm_num
        have hs1 : ((-1 : ℂ) ^ ((ε 1 : ℕ) + 2 + N)) = 1 := by
          rw [neg_one_pow_of_mod_two, show ((ε 1 : ℕ) + 2 + N) % 2 = 0 by
            rcases hval 0 with h0 | h0 <;> rcases hval 1 with hb | hb <;> rcases hval 2 with hc | hc <;> omega]; norm_num

        set d₀ : Fin 3 →₀ ℕ := Finsupp.single 2 1 + Finsupp.single 0 1 with hd₀
        have hsupp : ∀ d : Fin 3 →₀ ℕ, coeff d p ≠ 0 → d = d₀ := by
          intro d hd
          have hdeg : Finsupp.degree d = 2 := by
            by_contra hne; exact hd (hhom.coeff_eq_zero hne)
          rw [degree_fin3] at hdeg
          have q2 := mod_two_eq_one_of_pow (parity_of_flip 2 _ (hflip 2 p hp 2) d hd ▸ hs2)
          have q0 := mod_two_eq_one_of_pow (parity_of_flip 0 _ (hflip 2 p hp 0) d hd ▸ hs0)
          have q1 := mod_two_eq_zero_of_pow (parity_of_flip 1 _ (hflip 2 p hp 1) d hd ▸ hs1)
          have e0 : d 0 = d₀ 0 := by simp [hd₀]; omega
          have e1 : d 1 = d₀ 1 := by simp [hd₀]; omega
          have e2 : d 2 = d₀ 2 := by simp [hd₀]; omega
          exact Finsupp.ext fun i => by fin_cases i <;> assumption
        have hpeq : p = C (coeff d₀ p) * (X 2 * X 0) := by
          have : p = monomial d₀ (coeff d₀ p) := by
            ext d
            rw [coeff_monomial]
            by_cases h : d₀ = d
            · subst h; simp
            · rw [if_neg h]
              by_contra hne
              exact h (hsupp d hne).symm
          rw [this, hd₀, X, X, monomial_mul, C_mul_monomial]; simp
        have hc : coeff d₀ p ≠ 0 := by
          intro h0; apply hp0; rw [hpeq, h0, C_0, zero_mul]

        have hlow : lower₁ (Ξ ![-1 / 2 + σ * Complex.I, 1 / 2 + σ * Complex.I, σ₃ * Complex.I] (C (coeff d₀ p) * (X 2 * X 0))) =
            C (coeff d₀ p * (-3 + 2 * ((σ : ℂ) - σ₃) * Complex.I)) * X 1 := by
          simp only [hΞ, hlower₁]
          simp only [Fin.sum_univ_three, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
            Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
          simp [pderiv_X]
          apply MvPolynomial.funext; intro x
          simp
          ring
        have hκ : (-3 + 2 * ((σ : ℂ) - σ₃) * Complex.I : ℂ) ≠ 0 := by
          intro h; have h' := congrArg Complex.re h; norm_num at h'
        have hmem := (h3 2 p hp).2
        rw [hpeq, hlow] at hmem
        refine (Submodule.ne_bot_iff _).2 ⟨_, hmem, ?_⟩
        intro h0
        have := congrArg (coeff (Finsupp.single 1 1)) h0
        rw [coeff_C_mul, coeff_X, if_pos rfl, mul_one, coeff_zero] at this
        exact mul_ne_zero hc hκ this
      ·
        have hs1 : ((-1 : ℂ) ^ ((ε 1 : ℕ) + 2 + N)) = -1 := by
          rw [neg_one_pow_of_mod_two, show ((ε 1 : ℕ) + 2 + N) % 2 = 1 by
            rcases hval 0 with h0 | h0 <;> rcases hval 1 with hb | hb <;> rcases hval 2 with hc | hc <;> omega]; norm_num
        have hs0 : ((-1 : ℂ) ^ ((ε 0 : ℕ) + 2 + N)) = 1 := by
          rw [neg_one_pow_of_mod_two, show ((ε 0 : ℕ) + 2 + N) % 2 = 0 by
            rcases hval 0 with h0 | h0 <;> rcases hval 1 with hb | hb <;> rcases hval 2 with hc | hc <;> omega]; norm_num

        set d₀ : Fin 3 →₀ ℕ := Finsupp.single 2 1 + Finsupp.single 1 1 with hd₀
        have hsupp : ∀ d : Fin 3 →₀ ℕ, coeff d p ≠ 0 → d = d₀ := by
          intro d hd
          have hdeg : Finsupp.degree d = 2 := by
            by_contra hne; exact hd (hhom.coeff_eq_zero hne)
          rw [degree_fin3] at hdeg
          have q2 := mod_two_eq_one_of_pow (parity_of_flip 2 _ (hflip 2 p hp 2) d hd ▸ hs2)
          have q1 := mod_two_eq_one_of_pow (parity_of_flip 1 _ (hflip 2 p hp 1) d hd ▸ hs1)
          have q0 := mod_two_eq_zero_of_pow (parity_of_flip 0 _ (hflip 2 p hp 0) d hd ▸ hs0)
          have e0 : d 0 = d₀ 0 := by simp [hd₀]; omega
          have e1 : d 1 = d₀ 1 := by simp [hd₀]; omega
          have e2 : d 2 = d₀ 2 := by simp [hd₀]; omega
          exact Finsupp.ext fun i => by fin_cases i <;> assumption
        have hpeq : p = C (coeff d₀ p) * (X 2 * X 1) := by
          have : p = monomial d₀ (coeff d₀ p) := by
            ext d
            rw [coeff_monomial]
            by_cases h : d₀ = d
            · subst h; simp
            · rw [if_neg h]
              by_contra hne
              exact h (hsupp d hne).symm
          rw [this, hd₀, X, X, monomial_mul, C_mul_monomial]; simp
        have hc : coeff d₀ p ≠ 0 := by
          intro h0; apply hp0; rw [hpeq, h0, C_0, zero_mul]

        have hlow : lower₁ (Ξ ![-1 / 2 + σ * Complex.I, 1 / 2 + σ * Complex.I, σ₃ * Complex.I] (C (coeff d₀ p) * (X 2 * X 1))) =
            C (coeff d₀ p * (1 - 2 * ((σ : ℂ) - σ₃) * Complex.I)) * X 0 := by
          simp only [hΞ, hlower₁]
          simp only [Fin.sum_univ_three, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
            Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
          simp [pderiv_X]
          apply MvPolynomial.funext; intro x
          simp
          ring
        have hκ : (1 - 2 * ((σ : ℂ) - σ₃) * Complex.I : ℂ) ≠ 0 := by
          intro h; have h' := congrArg Complex.re h; norm_num at h'
        have hmem := (h3 2 p hp).2
        rw [hpeq, hlow] at hmem
        refine (Submodule.ne_bot_iff _).2 ⟨_, hmem, ?_⟩
        intro h0
        have := congrArg (coeff (Finsupp.single 0 1)) h0
        rw [coeff_C_mul, coeff_X, if_pos rfl, mul_one, coeff_zero] at this
        exact mul_ne_zero hc hκ this
    · intro ℓ hℓ h
      obtain ⟨p, hp, hp0⟩ := (Submodule.ne_bot_iff _).1 h
      obtain ⟨hhom, hharm⟩ := h1 ℓ p hp
      have h15 := (LanglandsTunnell.CubicInduction.compactPicture_eq_zero_of_lowering_eq_zero_of_three_le σ σ₃ ℓ hℓ
        p hhom hharm).1
      by_contra hboth
      push Not at hboth
      obtain ⟨hb2, hb1⟩ := hboth
      have hz2 : lower₂ (Ξ ![-1 / 2 + σ * Complex.I, 1 / 2 + σ * Complex.I, σ₃ * Complex.I] p) = 0 :=
        (Submodule.eq_bot_iff _).1 hb2 _ (h3 ℓ p hp).1
      have hz1 : lower₁ (Ξ ![-1 / 2 + σ * Complex.I, 1 / 2 + σ * Complex.I, σ₃ * Complex.I] p) = 0 :=
        (Submodule.eq_bot_iff _).1 hb1 _ (h3 ℓ p hp).2
      exact hp0 (h15 hz2 hz1)
  ·
    have hν : ν = ![-1 / 2 + σ * Complex.I, σ₃ * Complex.I, 1 / 2 + σ * Complex.I] := by
      funext i; fin_cases i <;> simp [hν0, hνb, hνc]
    subst hν
    refine key ?_ ?_
    · intro hS2
      obtain ⟨p, hp, hp0⟩ := (Submodule.ne_bot_iff _).1 hS2
      obtain ⟨hhom, -⟩ := h1 2 p hp
      have hs1 : ((-1 : ℂ) ^ ((ε 1 : ℕ) + 2 + N)) = -1 := by
        rw [neg_one_pow_of_mod_two, show ((ε 1 : ℕ) + 2 + N) % 2 = 1 by
          rcases hval 0 with h0 | h0 <;> rcases hval 1 with hb | hb <;> rcases hval 2 with hc | hc <;> omega]; norm_num
      by_cases he : (ε 0 : ℕ) = (ε 1 : ℕ)
      ·
        have hs0 : ((-1 : ℂ) ^ ((ε 0 : ℕ) + 2 + N)) = -1 := by
          rw [neg_one_pow_of_mod_two, show ((ε 0 : ℕ) + 2 + N) % 2 = 1 by
            rcases hval 0 with h0 | h0 <;> rcases hval 1 with hb | hb <;> rcases hval 2 with hc | hc <;> omega]; norm_num
        have hs2 : ((-1 : ℂ) ^ ((ε 2 : ℕ) + 2 + N)) = 1 := by
          rw [neg_one_pow_of_mod_two, show ((ε 2 : ℕ) + 2 + N) % 2 = 0 by
            rcases hval 0 with h0 | h0 <;> rcases hval 1 with hb | hb <;> rcases hval 2 with hc | hc <;> omega]; norm_num

        set d₀ : Fin 3 →₀ ℕ := Finsupp.single 1 1 + Finsupp.single 0 1 with hd₀
        have hsupp : ∀ d : Fin 3 →₀ ℕ, coeff d p ≠ 0 → d = d₀ := by
          intro d hd
          have hdeg : Finsupp.degree d = 2 := by
            by_contra hne; exact hd (hhom.coeff_eq_zero hne)
          rw [degree_fin3] at hdeg
          have q1 := mod_two_eq_one_of_pow (parity_of_flip 1 _ (hflip 2 p hp 1) d hd ▸ hs1)
          have q0 := mod_two_eq_one_of_pow (parity_of_flip 0 _ (hflip 2 p hp 0) d hd ▸ hs0)
          have q2 := mod_two_eq_zero_of_pow (parity_of_flip 2 _ (hflip 2 p hp 2) d hd ▸ hs2)
          have e0 : d 0 = d₀ 0 := by simp [hd₀]; omega
          have e1 : d 1 = d₀ 1 := by simp [hd₀]; omega
          have e2 : d 2 = d₀ 2 := by simp [hd₀]; omega
          exact Finsupp.ext fun i => by fin_cases i <;> assumption
        have hpeq : p = C (coeff d₀ p) * (X 1 * X 0) := by
          have : p = monomial d₀ (coeff d₀ p) := by
            ext d
            rw [coeff_monomial]
            by_cases h : d₀ = d
            · subst h; simp
            · rw [if_neg h]
              by_contra hne
              exact h (hsupp d hne).symm
          rw [this, hd₀, X, X, monomial_mul, C_mul_monomial]; simp
        have hc : coeff d₀ p ≠ 0 := by
          intro h0; apply hp0; rw [hpeq, h0, C_0, zero_mul]

        have hlow : lower₁ (Ξ ![-1 / 2 + σ * Complex.I, σ₃ * Complex.I, 1 / 2 + σ * Complex.I] (C (coeff d₀ p) * (X 1 * X 0))) =
            C (coeff d₀ p * (3 - 2 * ((σ : ℂ) - σ₃) * Complex.I)) * X 2 := by
          simp only [hΞ, hlower₁]
          simp only [Fin.sum_univ_three, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
            Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
          simp [pderiv_X]
          apply MvPolynomial.funext; intro x
          simp
          ring
        have hκ : (3 - 2 * ((σ : ℂ) - σ₃) * Complex.I : ℂ) ≠ 0 := by
          intro h; have h' := congrArg Complex.re h; norm_num at h'
        have hmem := (h3 2 p hp).2
        rw [hpeq, hlow] at hmem
        refine (Submodule.ne_bot_iff _).2 ⟨_, hmem, ?_⟩
        intro h0
        have := congrArg (coeff (Finsupp.single 2 1)) h0
        rw [coeff_C_mul, coeff_X, if_pos rfl, mul_one, coeff_zero] at this
        exact mul_ne_zero hc hκ this
      ·
        have hs2 : ((-1 : ℂ) ^ ((ε 2 : ℕ) + 2 + N)) = -1 := by
          rw [neg_one_pow_of_mod_two, show ((ε 2 : ℕ) + 2 + N) % 2 = 1 by
            rcases hval 0 with h0 | h0 <;> rcases hval 1 with hb | hb <;> rcases hval 2 with hc | hc <;> omega]; norm_num
        have hs0 : ((-1 : ℂ) ^ ((ε 0 : ℕ) + 2 + N)) = 1 := by
          rw [neg_one_pow_of_mod_two, show ((ε 0 : ℕ) + 2 + N) % 2 = 0 by
            rcases hval 0 with h0 | h0 <;> rcases hval 1 with hb | hb <;> rcases hval 2 with hc | hc <;> omega]; norm_num

        set d₀ : Fin 3 →₀ ℕ := Finsupp.single 1 1 + Finsupp.single 2 1 with hd₀
        have hsupp : ∀ d : Fin 3 →₀ ℕ, coeff d p ≠ 0 → d = d₀ := by
          intro d hd
          have hdeg : Finsupp.degree d = 2 := by
            by_contra hne; exact hd (hhom.coeff_eq_zero hne)
          rw [degree_fin3] at hdeg
          have q1 := mod_two_eq_one_of_pow (parity_of_flip 1 _ (hflip 2 p hp 1) d hd ▸ hs1)
          have q2 := mod_two_eq_one_of_pow (parity_of_flip 2 _ (hflip 2 p hp 2) d hd ▸ hs2)
          have q0 := mod_two_eq_zero_of_pow (parity_of_flip 0 _ (hflip 2 p hp 0) d hd ▸ hs0)
          have e0 : d 0 = d₀ 0 := by simp [hd₀]; omega
          have e1 : d 1 = d₀ 1 := by simp [hd₀]; omega
          have e2 : d 2 = d₀ 2 := by simp [hd₀]; omega
          exact Finsupp.ext fun i => by fin_cases i <;> assumption
        have hpeq : p = C (coeff d₀ p) * (X 1 * X 2) := by
          have : p = monomial d₀ (coeff d₀ p) := by
            ext d
            rw [coeff_monomial]
            by_cases h : d₀ = d
            · subst h; simp
            · rw [if_neg h]
              by_contra hne
              exact h (hsupp d hne).symm
          rw [this, hd₀, X, X, monomial_mul, C_mul_monomial]; simp
        have hc : coeff d₀ p ≠ 0 := by
          intro h0; apply hp0; rw [hpeq, h0, C_0, zero_mul]

        have hlow : lower₁ (Ξ ![-1 / 2 + σ * Complex.I, σ₃ * Complex.I, 1 / 2 + σ * Complex.I] (C (coeff d₀ p) * (X 1 * X 2))) =
            C (coeff d₀ p * (3 + 2 * ((σ : ℂ) - σ₃) * Complex.I)) * X 0 := by
          simp only [hΞ, hlower₁]
          simp only [Fin.sum_univ_three, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
            Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
          simp [pderiv_X]
          apply MvPolynomial.funext; intro x
          simp
          ring
        have hκ : (3 + 2 * ((σ : ℂ) - σ₃) * Complex.I : ℂ) ≠ 0 := by
          intro h; have h' := congrArg Complex.re h; norm_num at h'
        have hmem := (h3 2 p hp).2
        rw [hpeq, hlow] at hmem
        refine (Submodule.ne_bot_iff _).2 ⟨_, hmem, ?_⟩
        intro h0
        have := congrArg (coeff (Finsupp.single 0 1)) h0
        rw [coeff_C_mul, coeff_X, if_pos rfl, mul_one, coeff_zero] at this
        exact mul_ne_zero hc hκ this
    · intro ℓ hℓ h
      obtain ⟨p, hp, hp0⟩ := (Submodule.ne_bot_iff _).1 h
      obtain ⟨hhom, hharm⟩ := h1 ℓ p hp
      have h15 := (LanglandsTunnell.CubicInduction.compactPicture_eq_zero_of_lowering_eq_zero_of_three_le σ σ₃ ℓ hℓ
        p hhom hharm).2
      by_contra hboth
      push Not at hboth
      obtain ⟨hb2, hb1⟩ := hboth
      have hz2 : lower₂ (Ξ ![-1 / 2 + σ * Complex.I, σ₃ * Complex.I, 1 / 2 + σ * Complex.I] p) = 0 :=
        (Submodule.eq_bot_iff _).1 hb2 _ (h3 ℓ p hp).1
      have hz1 : lower₁ (Ξ ![-1 / 2 + σ * Complex.I, σ₃ * Complex.I, 1 / 2 + σ * Complex.I] p) = 0 :=
        (Submodule.eq_bot_iff _).1 hb1 _ (h3 ℓ p hp).2
      exact hp0 (h15 hz2 hz1)

end S_LanglandsTunnell_CubicInduction_transitionStable_family_one_ne_bot_of_odd_signClass
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_transitionStable_family_one_ne_bot_of_odd_signClass (solution)
