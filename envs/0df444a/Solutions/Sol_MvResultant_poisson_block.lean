-- Prove2me | solution 1 for MvResultant.poisson_block
-- status  : ACCEPTED   (prove)
-- author  : @milia
-- created : 2026-11-13T03:05:35.480355+00:00
-- url     : https://prove2.me/submissions/0ea7b121-5783-4f2d-97ce-24d44cd59596

import Mathlib
import Definitions.Def_HararySachs_Hyper_CharPoly
import Theorems.Thm_MvResultant_isWeightedHomogeneous_block
import Theorems.Thm_MvResultant_blockDegree_le
import Theorems.Thm_MvResultant_blockDegree_ge

open HararySachs.Hyper MvPolynomial Finset

namespace PoissonAux

variable {n : ℕ} {D : Fin n → ℕ}

/-- the coefficient variables of block `i` -/
abbrev Blk (D : Fin n → ℕ) (i : Fin n) := {a : Fin n →₀ ℕ // a.degree = D i}

instance finite_blk (i : Fin n) : Finite (Blk D i) := by
  refine Finite.of_injective
    (fun a : Blk D i => fun j : Fin n =>
      (⟨a.1 j, Nat.lt_succ_of_le (by
        have := Finsupp.le_degree j a.1; rw [a.2] at this; exact this)⟩ : Fin (D i + 1))) ?_
  intro a b h
  apply Subtype.ext
  ext j
  have := congrFun h j
  simpa using congrArg Fin.val this

noncomputable instance fintype_blk (i : Fin n) : Fintype (Blk D i) := Fintype.ofFinite _

/-- the form of degree `D i` with coefficients `u` -/
noncomputable def form (i : Fin n) (u : Blk D i → ℂ) : MvPolynomial (Fin n) ℂ :=
  ∑ b, monomial b.1 (u b)

lemma coeff_form (i : Fin n) (u : Blk D i → ℂ) (b : Blk D i) : coeff b.1 (form i u) = u b := by
  classical
  unfold form
  rw [coeff_sum]
  simp only [coeff_monomial]
  rw [sum_eq_single b]
  · simp
  · intro c _ hc
    rw [if_neg]
    intro h; exact hc (Subtype.ext h)
  · simp

lemma form_hom (i : Fin n) (u : Blk D i → ℂ) : (form i u).IsHomogeneous (D i) :=
  IsHomogeneous.sum _ _ _ fun b _ => isHomogeneous_monomial _ b.2

lemma form_coeff (i : Fin n) {φ : MvPolynomial (Fin n) ℂ} (hφ : φ.IsHomogeneous (D i)) :
    form i (fun b : Blk D i => coeff b.1 φ) = φ := by
  classical
  ext a
  by_cases ha : a.degree = D i
  · exact coeff_form i _ ⟨a, ha⟩
  · rw [hφ.coeff_eq_zero ha]
    unfold form
    rw [coeff_sum]
    refine sum_eq_zero fun b _ => ?_
    rw [coeff_monomial, if_neg]
    rintro rfl; exact ha b.2

/-- value of the monomial `b` at `p` -/
noncomputable def pw (i : Fin n) (p : Fin n → ℂ) (b : Blk D i) : ℂ := eval p (monomial b.1 1)

lemma eval_form (i : Fin n) (p : Fin n → ℂ) (u : Blk D i → ℂ) :
    eval p (form i u) = ∑ b, pw i p b * u b := by
  unfold form pw
  rw [map_sum]
  refine sum_congr rfl fun b _ => ?_
  simp only [eval_monomial]; ring

/-- the linear form `φ ↦ φ(p)` on block `i` -/
noncomputable def L (i : Fin n) (p : Fin n → ℂ) : MvPolynomial (Blk D i) ℂ :=
  ∑ b, C (pw i p b) * X b

lemma eval_L (i : Fin n) (p : Fin n → ℂ) (u : Blk D i → ℂ) :
    eval u (L i p) = eval p (form i u) := by
  rw [eval_form]
  unfold L
  simp

lemma coeff_L (i : Fin n) (p : Fin n → ℂ) (b : Blk D i) :
    coeff (Finsupp.single b 1) (L i p) = pw i p b := by
  classical
  unfold L
  rw [coeff_sum]
  simp only [coeff_C_mul, coeff_X]
  rw [sum_eq_single b]
  · simp
  · intro c _ hc
    rw [if_neg, mul_zero]
    intro h
    exact hc ((Finsupp.single_left_inj one_ne_zero).mp h)
  · simp

lemma L_hom (i : Fin n) (p : Fin n → ℂ) : (L (D := D) i p).IsHomogeneous 1 :=
  IsHomogeneous.sum _ _ _ fun b _ => by
    simpa using (isHomogeneous_C _ (pw i p b)).mul (isHomogeneous_X ℂ b)

/-- the distinguished monomial `x_i ^ D i` -/
noncomputable def b0 (i : Fin n) : Blk D i := ⟨Finsupp.single i (D i), Finsupp.degree_single _ _⟩

lemma pw_b0 (i : Fin n) (p : Fin n → ℂ) : pw i p (b0 (D := D) i) = p i ^ D i := by
  simp [pw, b0, eval_monomial]

lemma coeff_L_b0 (i : Fin n) (p : Fin n → ℂ) (hp : p i = 1) :
    coeff (Finsupp.single (b0 (D := D) i) 1) (L i p) = 1 := by
  rw [coeff_L, pw_b0, hp, one_pow]

lemma L_ne_zero (i : Fin n) (p : Fin n → ℂ) (hp : p i = 1) : L (D := D) i p ≠ 0 := by
  intro h
  have := coeff_L_b0 (D := D) i p hp
  rw [h, coeff_zero] at this
  exact zero_ne_one this

lemma L_prime (i : Fin n) (p : Fin n → ℂ) (hp : p i = 1) : Prime (L (D := D) i p) := by
  have hdeg : (L (D := D) i p).totalDegree = 1 := (L_hom i p).totalDegree (L_ne_zero i p hp)
  have hirr : Irreducible (L (D := D) i p) := by
    refine irreducible_of_totalDegree_eq_one hdeg fun x hx => ?_
    have := hx (Finsupp.single (b0 i) 1)
    rw [coeff_L_b0 i p hp] at this
    exact isUnit_of_dvd_one this

  exact hirr.prime

/-- the monomial `x_i ^ (D i - 1) x_j` -/
noncomputable def bj (i : Fin n) (hDi : 1 ≤ D i) (j : Fin n) : Blk D i :=
  ⟨Finsupp.single i (D i - 1) + Finsupp.single j 1, by
    rw [map_add, Finsupp.degree_single, Finsupp.degree_single]; omega⟩

lemma pw_bj (i : Fin n) (hDi : 1 ≤ D i) (p : Fin n → ℂ) (hp : p i = 1) (j : Fin n) :
    pw i p (bj i hDi j) = p j := by
  have : (monomial (Finsupp.single i (D i - 1) + Finsupp.single j 1) (1 : ℂ) :
      MvPolynomial (Fin n) ℂ) = X i ^ (D i - 1) * X j := by
    rw [X_pow_eq_monomial, X, monomial_mul, one_mul]
  simp only [pw, bj]
  rw [this]
  simp [hp]

lemma L_inj (i : Fin n) (hDi : 1 ≤ D i) (p q : Fin n → ℂ) (hp : p i = 1) (hq : q i = 1)
    (h : L (D := D) i p ∣ L i q) : p = q := by
  obtain ⟨h, hh⟩ := h
  have hh0 : h ≠ 0 := by
    rintro rfl; rw [mul_zero] at hh; exact L_ne_zero i q hq hh
  have hdeg := congrArg totalDegree hh
  rw [totalDegree_mul_of_isDomain (L_ne_zero i p hp) hh0,
    (L_hom i p).totalDegree (L_ne_zero i p hp),
    (L_hom i q).totalDegree (L_ne_zero i q hq)] at hdeg
  have hC := (totalDegree_eq_zero_iff_eq_C (p := h)).mp (by omega)
  rw [hC] at hh
  have h1 := congrArg (coeff (Finsupp.single (b0 (D := D) i) 1)) hh
  rw [mul_comm, coeff_C_mul, coeff_L_b0 i p hp, coeff_L_b0 i q hq, mul_one] at h1
  rw [← h1, C_1, mul_one] at hh
  funext j
  have := congrArg (coeff (Finsupp.single (bj i hDi j) 1)) hh
  rw [coeff_L, coeff_L, pw_bj i hDi p hp, pw_bj i hDi q hq] at this
  exact this.symm

/-- block `i` left as variables, the other blocks specialised to `F` -/
noncomputable def sub (i : Fin n) (F : Fin n → MvPolynomial (Fin n) ℂ) (v : ResVar n D) :
    MvPolynomial (Blk D i) ℂ :=
  if h : v.1 = i then X ⟨v.2.1, by rw [v.2.2, h]⟩ else C (coeff v.2.1 (F v.1))

lemma sub_hom (i : Fin n) (F : Fin n → MvPolynomial (Fin n) ℂ) (v : ResVar n D) :
    (sub i F v).IsHomogeneous (if v.1 = i then 1 else 0) := by
  unfold sub
  split_ifs
  · exact isHomogeneous_X _ _
  · exact isHomogeneous_C _ _

lemma eval_aeval_sub (i : Fin n) (F : Fin n → MvPolynomial (Fin n) ℂ)
    (R : MvPolynomial (ResVar n D) ℂ) (u : Blk D i → ℂ) :
    eval u (aeval (sub i F) R) =
      aeval (fun v : ResVar n D => coeff v.2.1 (Function.update F i (form i u) v.1)) R := by
  rw [← coe_aeval_eq_eval]
  refine (comp_aeval_apply (f := sub i F) (φ := aeval u) (p := R)).trans ?_
  congr 2
  funext v
  obtain ⟨j, a⟩ := v
  unfold sub
  by_cases h : j = i
  · subst h
    simp only [dif_pos, aeval_X, Function.update_self]
    exact (coeff_form j u ⟨a.1, _⟩).symm
  · simp only [dif_neg h, aeval_C, Algebra.algebraMap_self, RingHom.id_apply,
      Function.update_of_ne h]

end PoissonAux

open PoissonAux in
theorem solution {n : ℕ} {D : Fin n → ℕ} (hD : ∀ j, 1 ≤ D j)
    (res : MvPolynomial (ResVar n D) ℤ) (hres : IsResultant n D res) (i : Fin n)
    (F : Fin n → MvPolynomial (Fin n) ℂ) (hF : ∀ j, j ≠ i → (F j).IsHomogeneous (D j))
    (P : Finset (Fin n → ℂ)) (hcard : P.card = ∏ j ∈ Finset.univ.erase i, D j)
    (hP : ∀ p ∈ P, p i = 1 ∧ ∀ j, j ≠ i → MvPolynomial.eval p (F j) = 0)
    (φ : MvPolynomial (Fin n) ℂ) (hφ : φ.IsHomogeneous (D i)) :
    MvPolynomial.aeval
        (fun v : ResVar n D => MvPolynomial.coeff v.2.1 (Function.update F i φ v.1))
        (MvPolynomial.map (Int.castRingHom ℂ) res) =
      MvPolynomial.aeval (fun v : ResVar n D =>
          MvPolynomial.coeff v.2.1 (Function.update F i (MvPolynomial.X i ^ D i) v.1))
        (MvPolynomial.map (Int.castRingHom ℂ) res) *
      ∏ p ∈ P, MvPolynomial.eval p φ := by
  classical
  set resC := MvPolynomial.map (Int.castRingHom ℂ) res with hresC
  set Q : MvPolynomial (Blk D i) ℂ := aeval (sub i F) resC with hQdef
  -- evaluating `Q` at the coefficients of a form of degree `D i`
  have hevalQ : ∀ ψ : MvPolynomial (Fin n) ℂ, ψ.IsHomogeneous (D i) →
      aeval (fun v : ResVar n D => coeff v.2.1 (Function.update F i ψ v.1)) resC =
        eval (fun b : Blk D i => coeff b.1 ψ) Q := by
    intro ψ hψ
    rw [hQdef, eval_aeval_sub, form_coeff i hψ]
  rw [hevalQ φ hφ, hevalQ _ (isHomogeneous_X_pow _ _)]
  -- `Q` vanishes on the hyperplane of each `p ∈ P`
  have hvan : ∀ p ∈ P, ∀ u : Blk D i → ℂ, eval u (L i p) = 0 → eval u Q = 0 := by
    intro p hp u hu
    rw [hQdef, eval_aeval_sub]
    refine (hres.1 _ fun j => ?_).mp ⟨p, ?_, fun j => ?_⟩
    · by_cases h : j = i
      · subst h; rw [Function.update_self]; exact form_hom j u
      · rw [Function.update_of_ne h]; exact hF j h
    · intro h0
      have := congrFun h0 i
      rw [(hP p hp).1] at this
      exact one_ne_zero this
    · by_cases h : j = i
      · subst h; rw [Function.update_self, ← eval_L]; exact hu
      · rw [Function.update_of_ne h]; exact (hP p hp).2 j h
  -- hence each `L p` divides `Q`
  have hdvd : ∀ p ∈ P, L i p ∣ Q := by
    intro p hp
    have hpr := L_prime (D := D) i p (hP p hp).1
    have hprime : (Ideal.span {L (D := D) i p}).IsPrime :=
      (Ideal.span_singleton_prime hpr.ne_zero).mpr hpr
    have key : Q ∈ vanishingIdeal ℂ (zeroLocus ℂ (Ideal.span {L (D := D) i p})) := by
      rw [mem_vanishingIdeal_iff]
      intro u hu
      rw [mem_zeroLocus_iff] at hu
      exact hvan p hp u (hu _ (Ideal.subset_span rfl))
    rw [IsPrime.vanishingIdeal_zeroLocus] at key
    exact Ideal.mem_span_singleton.mp key
  -- and so does their product
  have hprod : ∀ s ⊆ P, (∏ p ∈ s, L i p) ∣ Q := by
    intro s
    induction s using Finset.induction_on with
    | empty => intro _; simp
    | insert a s ha ih =>
      intro hs
      have haP : a ∈ P := hs (mem_insert_self a s)
      obtain ⟨S, hS⟩ := ih fun x hx => hs (mem_insert_of_mem hx)
      have hpr := L_prime (D := D) i a (hP a haP).1
      have : L i a ∣ (∏ p ∈ s, L i p) * S := hS ▸ hdvd a haP
      rcases hpr.dvd_or_dvd this with h | h
      · exfalso
        obtain ⟨q, hq, hdq⟩ := (hpr.dvd_finsetProd_iff _).mp h
        have hqP : q ∈ P := hs (mem_insert_of_mem hq)
        have := L_inj i (hD i) a q (hP a haP).1 (hP q hqP).1 hdq
        exact ha (this ▸ hq)
      · obtain ⟨T, hT⟩ := h
        refine ⟨T, ?_⟩
        rw [hS, hT, prod_insert ha]; ring
  obtain ⟨S, hS⟩ := hprod P subset_rfl
  -- degree of `Q`
  have hD' : ∀ j, 1 ≤ D j := hD
  obtain ⟨δ, hδ⟩ := MvResultant.isWeightedHomogeneous_block res hres i
  have h1 := MvResultant.blockDegree_le hD' res hres i δ hδ
  have h2 := MvResultant.blockDegree_ge hD' res hres i δ hδ
  have hδeq : δ = P.card := by rw [hcard]; omega
  have hQhom : Q.IsHomogeneous P.card := by
    rw [hQdef, aeval_def, eval₂_eq]
    refine IsHomogeneous.sum _ _ _ fun d hd => ?_
    have hw : (Finsupp.weight (fun v : ResVar n D => if v.1 = i then 1 else 0)) d = δ := by
      apply hδ
      intro h0
      apply (mem_support_iff.mp hd)
      rw [hresC, coeff_map, h0, map_zero]
    have hsum : 0 + ∑ v ∈ d.support, (if v.1 = i then 1 else 0) * d v = P.card := by
      rw [← hδeq, ← hw, Finsupp.weight_apply, Finsupp.sum, zero_add]
      refine sum_congr rfl fun v _ => ?_
      rw [smul_eq_mul, mul_comm]
    rw [← hsum]
    exact (isHomogeneous_C _ _).mul
      (IsHomogeneous.prod _ _ _ fun v _ => (sub_hom i F v).pow (d v))
  have hLprod_hom : (∏ p ∈ P, L (D := D) i p).IsHomogeneous P.card := by
    have := IsHomogeneous.prod P (fun p => L (D := D) i p) (fun _ => 1)
      fun p _ => L_hom i p
    simpa using this
  have hLprod_ne : (∏ p ∈ P, L (D := D) i p) ≠ 0 :=
    prod_ne_zero_iff.mpr fun p hp => L_ne_zero i p (hP p hp).1
  have hevalL : ∀ ψ : MvPolynomial (Fin n) ℂ, ψ.IsHomogeneous (D i) →
      eval (fun b : Blk D i => coeff b.1 ψ) (∏ p ∈ P, L i p) = ∏ p ∈ P, eval p ψ := by
    intro ψ hψ
    rw [map_prod]
    refine prod_congr rfl fun p _ => ?_
    rw [eval_L, form_coeff i hψ]
  have hX : ∏ p ∈ P, eval p (X i ^ D i : MvPolynomial (Fin n) ℂ) = 1 := by
    refine prod_eq_one fun p hp => ?_
    simp [(hP p hp).1]
  by_cases hQ : Q = 0
  · rw [hQ]; simp
  · have hS0 : S ≠ 0 := by rintro rfl; rw [mul_zero] at hS; exact hQ hS
    have hdeg := congrArg totalDegree hS
    rw [totalDegree_mul_of_isDomain hLprod_ne hS0, hQhom.totalDegree hQ,
      hLprod_hom.totalDegree hLprod_ne] at hdeg
    have hC := (totalDegree_eq_zero_iff_eq_C (p := S)).mp (by omega)
    rw [hS, hC, eval_mul, eval_mul, hevalL φ hφ, hevalL _ (isHomogeneous_X_pow _ _), hX,
      eval_C, eval_C]
    ring
