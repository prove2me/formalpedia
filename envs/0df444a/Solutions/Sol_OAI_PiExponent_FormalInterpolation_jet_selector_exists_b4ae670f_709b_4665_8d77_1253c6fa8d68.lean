-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.jet_selector_exists_b4ae670f_709b_4665_8d77_1253c6fa8d68
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T19:28:19.835993+00:00
-- url     : https://prove2.me/submissions/881d0523-c629-4452-8c98-3f358b72ad2b

import Mathlib

open scoped BigOperators

namespace PiL39

variable {n : ℕ}

/-- polynomials with vanishing coefficients in total degree `< N` -/
def T (n N : ℕ) : Ideal (MvPolynomial (Fin n) ℂ) where
  carrier := {f | ∀ β : Fin n →₀ ℕ, (∑ i, β i) < N → f.coeff β = 0}
  add_mem' := by intro f g hf hg β hβ; simp [hf β hβ, hg β hβ]
  zero_mem' := by intro β _; simp
  smul_mem' := by
    intro a f hf β hβ
    simp only [smul_eq_mul, MvPolynomial.coeff_mul]
    apply Finset.sum_eq_zero
    intro p hp
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
    have : (∑ i, p.2 i) < N := by
      have h : ∑ i, β i = ∑ i, p.1 i + ∑ i, p.2 i := by
        rw [← Finset.sum_add_distrib]; congr 1; ext i; rw [← hp]; simp
      omega
    simp [hf p.2 this]

lemma T_mul (a b : ℕ) : T n a * T n b ≤ T n (a + b) := by
  rw [Ideal.mul_le]
  intro f hf g hg β hβ
  rw [MvPolynomial.coeff_mul]
  apply Finset.sum_eq_zero
  intro p hp
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
  have h : ∑ i, β i = ∑ i, p.1 i + ∑ i, p.2 i := by
    rw [← Finset.sum_add_distrib]; congr 1; ext i; rw [← hp]; simp
  by_cases h1 : (∑ i, p.1 i) < a
  · simp [hf p.1 h1]
  · have h2 : (∑ i, p.2 i) < b := by omega
    simp [hg p.2 h2]

lemma ker0_le : RingHom.ker (MvPolynomial.eval (0 : Fin n → ℂ)) ≤ T n 1 := by
  intro f hf β hβ
  have : β = 0 := by
    ext i; have := Finset.single_le_sum (f := fun i => β i) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ i); simp at this ⊢; omega
  subst this
  rw [RingHom.mem_ker, MvPolynomial.eval_zero] at hf
  simpa [MvPolynomial.constantCoeff] using hf

lemma ker0_pow_le (N : ℕ) : RingHom.ker (MvPolynomial.eval (0 : Fin n → ℂ)) ^ N ≤ T n N := by
  induction N with
  | zero => intro f _ β hβ; simp at hβ
  | succ N ih =>
    rw [pow_succ]
    exact (Ideal.mul_mono ih ker0_le).trans (T_mul N 1)

noncomputable def ψ (p : Fin n → ℂ) : MvPolynomial (Fin n) ℂ →ₐ[ℂ] MvPolynomial (Fin n) ℂ :=
  MvPolynomial.aeval (fun i => MvPolynomial.C (p i) + MvPolynomial.X i)

noncomputable def M (p : Fin n → ℂ) : Ideal (MvPolynomial (Fin n) ℂ) := RingHom.ker (MvPolynomial.eval p)

lemma ψ_M (p : Fin n → ℂ) (N : ℕ) (f : MvPolynomial (Fin n) ℂ) (hf : f ∈ M p ^ N) :
    ψ p f ∈ T n N := by
  apply ker0_pow_le
  have h1 : Ideal.map (ψ p).toRingHom (M p) ≤
      RingHom.ker (MvPolynomial.eval (0 : Fin n → ℂ)) := by
    rw [Ideal.map_le_iff_le_comap]
    intro g hg
    rw [Ideal.mem_comap, RingHom.mem_ker]
    have : (MvPolynomial.eval (0 : Fin n → ℂ)).comp (ψ p).toRingHom =
        MvPolynomial.eval p := by
      apply MvPolynomial.ringHom_ext
      · intro r; simp [ψ]
      · intro i; simp [ψ]
    have h := congrArg (fun F => F g) this
    simp only [RingHom.comp_apply] at h
    rw [h]; exact hg
  have h2 := Ideal.mem_map_of_mem (ψ p).toRingHom hf
  rw [Ideal.map_pow] at h2
  exact Ideal.pow_right_mono h1 N h2

lemma M_coprime (p q : Fin n → ℂ) (hpq : p ≠ q) : IsCoprime (M p) (M q) := by
  rw [Ideal.isCoprime_iff_sup_eq]
  obtain ⟨i, hi⟩ : ∃ i, p i ≠ q i := by
    by_contra h; push Not at h; exact hpq (funext h)
  have h1 : MvPolynomial.X i - MvPolynomial.C (p i) ∈ M p := by simp [M]
  have h2 : MvPolynomial.X i - MvPolynomial.C (q i) ∈ M q := by simp [M]
  have h3 : (MvPolynomial.C (p i - q i) : MvPolynomial (Fin n) ℂ) ∈ M p ⊔ M q := by
    have := Ideal.sub_mem _ (Ideal.mem_sup_right h2 : _ ∈ M p ⊔ M q)
      (Ideal.mem_sup_left h1 : _ ∈ M p ⊔ M q)
    convert this using 1
    rw [map_sub]; ring
  exact Ideal.eq_top_of_isUnit_mem _ h3
    ((isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr hi)).map MvPolynomial.C)

theorem main {J : Type} [Fintype J] [DecidableEq J]
    (c : J → Fin n → Complex) (hc : Function.Injective c)
    (D : Nat) (j : J) (α : Fin n →₀ Nat) :
    ∃ E : MvPolynomial (Fin n) Complex,
      ∀ (k : J) (β : Fin n →₀ Nat),
        (∑ i : Fin n, β i) ≤ D →
        (MvPolynomial.aeval
          (fun i : Fin n => MvPolynomial.C (c k i) + MvPolynomial.X i) E).coeff β
          = if k = j ∧ β = α then 1 else 0 := by
  classical
  let I : J → Ideal (MvPolynomial (Fin n) ℂ) := fun k => M (c k) ^ (D + 1)
  have hcop : Pairwise fun k l => IsCoprime (I k) (I l) :=
    fun k l hkl => (M_coprime _ _ (hc.ne hkl)).pow
  let P : MvPolynomial (Fin n) ℂ := ∏ i, (MvPolynomial.X i - MvPolynomial.C (c j i)) ^ α i
  let tgt : J → MvPolynomial (Fin n) ℂ := fun k => if k = j then P else 0
  obtain ⟨E', hE'⟩ := Ideal.quotientInfToPiQuotient_surj hcop (fun k => Ideal.Quotient.mk (I k) (tgt k))
  obtain ⟨E, rfl⟩ := Ideal.Quotient.mk_surjective E'
  refine ⟨E, fun k β hβ => ?_⟩
  have hk := congrFun hE' k
  simp only [Ideal.quotientInfToPiQuotient_mk'] at hk
  rw [Ideal.Quotient.eq] at hk
  have hT := ψ_M (c k) (D + 1) _ hk
  have := hT β (by omega)
  rw [map_sub, MvPolynomial.coeff_sub, sub_eq_zero] at this
  change (ψ (c k) E).coeff β = _
  rw [this]
  by_cases hkj : k = j
  · subst hkj
    have hPψ : ψ (c k) P = MvPolynomial.monomial α 1 := by
      simp only [P, map_prod, map_pow, map_sub, ψ, MvPolynomial.aeval_X, MvPolynomial.aeval_C,
        MvPolynomial.algebraMap_eq, add_sub_cancel_left]
      rw [MvPolynomial.monomial_eq, map_one, one_mul, Finsupp.prod_fintype _ _ (by simp)]
    simp only [tgt, if_pos rfl, hPψ, MvPolynomial.coeff_monomial, true_and]
    by_cases h : α = β
    · simp [h]
    · simp [h, Ne.symm h]
  · simp [tgt, hkj]

end PiL39

theorem solution
    {n : Nat} {J : Type} [Fintype J] [DecidableEq J]
    (c : J → Fin n → Complex) (hc : Function.Injective c)
    (D : Nat) (j : J) (α : Fin n →₀ Nat) :
    ∃ E : MvPolynomial (Fin n) Complex,
      ∀ (k : J) (β : Fin n →₀ Nat),
        (∑ i ∈ (Finset.univ : Finset (Fin n)), β i) ≤ D →
        (MvPolynomial.aeval
          (fun i : Fin n => MvPolynomial.C (c k i) + MvPolynomial.X i) E).coeff β
          = if k = j ∧ β = α then 1 else 0 :=
  PiL39.main c hc D j α
