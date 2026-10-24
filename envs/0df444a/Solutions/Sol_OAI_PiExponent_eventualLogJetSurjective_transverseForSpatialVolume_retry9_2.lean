-- Prove2me | solution 2 for OAI.PiExponent.eventualLogJetSurjective_transverseForSpatialVolume_retry9
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T18:01:10.386983+00:00
-- url     : https://prove2.me/submissions/2b0d60a5-758f-45c2-b148-c3c7ae36ead4

import Definitions.Def_PiExponent_DeterminantSetup
import Definitions.Def_eventualTransverseJetSurjectiveForSpatialVolume_360483bd
import Mathlib

section

open MvPolynomial

namespace PiL23

variable {m : ℕ}

noncomputable def ψ : MvPolynomial (Fin (m + 1)) ℂ →ₐ[ℂ] MvPolynomial (Fin m) ℂ :=
  aeval (Fin.cases 0 X)

noncomputable def χ : MvPolynomial (Fin (m + 1)) ℂ →ₐ[ℂ] MvPolynomial (Fin m) ℂ :=
  aeval (Fin.cases 1 X)

lemma cons_eq_iff (u0 s : ℕ) (u' b : Fin m →₀ ℕ) :
    Finsupp.cons u0 u' = Finsupp.cons s b ↔ u0 = s ∧ u' = b := by
  constructor
  · intro h
    refine ⟨by simpa using congrArg (· 0) h, ?_⟩
    ext i; simpa using congrArg (· i.succ) h
  · rintro ⟨rfl, rfl⟩; rfl

lemma ψ_monomial (s : ℕ) (b : Fin m →₀ ℕ) (c : ℂ) :
    ψ (monomial (Finsupp.cons s b) c) = if s = 0 then monomial b c else 0 := by
  rw [ψ, aeval_monomial, Finsupp.prod_fintype _ _ (by simp), Fin.prod_univ_succ, monomial_eq,
    Finsupp.prod_fintype _ _ (by simp)]
  simp only [Fin.cases_zero, Fin.cases_succ, Finsupp.cons_zero, Finsupp.cons_succ,
    MvPolynomial.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
  split_ifs with hs
  · subst hs; simp
  · simp [zero_pow hs]

lemma χ_monomial (s : ℕ) (b : Fin m →₀ ℕ) (c : ℂ) :
    χ (monomial (Finsupp.cons s b) c) = monomial b c := by
  rw [χ, aeval_monomial, Finsupp.prod_fintype _ _ (by simp), Fin.prod_univ_succ, monomial_eq,
    Finsupp.prod_fintype _ _ (by simp)]
  simp

lemma coeff_ψ (p : MvPolynomial (Fin (m + 1)) ℂ) (b : Fin m →₀ ℕ) :
    (ψ p).coeff b = p.coeff (Finsupp.cons 0 b) := by
  classical
  induction p using MvPolynomial.induction_on' with
  | monomial u c =>
    obtain ⟨u0, u', rfl⟩ : ∃ u0 u', u = Finsupp.cons u0 u' :=
      ⟨u 0, Finsupp.tail u, (Finsupp.cons_tail u).symm⟩
    rw [ψ_monomial, coeff_monomial]
    by_cases hu0 : u0 = 0 <;> by_cases hb : u' = b <;> simp [hu0, hb, coeff_monomial, cons_eq_iff]
  | add p q hp hq => simp [hp, hq]

lemma supp_χ (p : MvPolynomial (Fin (m + 1)) ℂ) (e : Fin m →₀ ℕ) (he : e ∈ (χ p).support) :
    ∃ d ∈ p.support, Finsupp.tail d = e := by
  classical
  have hp : χ p = ∑ d ∈ p.support, monomial (Finsupp.tail d) (p.coeff d) := by
    conv_lhs => rw [p.as_sum]
    rw [map_sum]
    refine Finset.sum_congr rfl fun d _ => ?_
    have := χ_monomial (d 0) (Finsupp.tail d) (p.coeff d)
    rwa [Finsupp.cons_tail] at this
  rw [hp] at he
  have := MvPolynomial.support_sum he
  simp only [Finset.mem_biUnion] at this
  obtain ⟨d, hd, hed⟩ := this
  exact ⟨d, hd, (Finset.mem_singleton.1 (support_monomial_subset hed)).symm⟩

theorem log_to_trans
    (m K : Nat) (w0 v0 alpha : Rat)
    (hw0 : 0 < w0) (hv0 : 0 < v0) (halpha : 0 < alpha)
    (w : Fin m → Nat) (hw : ∀ i, 0 < w i)
    (c : Fin K → Fin m → Complex)
    (hjet : OAI.PiExponent.eventualLogJetSurjective m K w0 v0 alpha w c) :
    OAI.PiExponent.eventualTransverseJetSurjectiveForSpatialVolume_360483bd m K alpha w c := by
  obtain ⟨D, hD, H0, h⟩ := hjet
  refine ⟨D, hD, H0, fun H hH hDH J' => ?_⟩
  have hL := h H hH hDH (fun j d => J' j (Finsupp.tail d))
  dsimp only at hL
  obtain ⟨P, hP1, hP2⟩ := hL
  have hw0' : (0 : ℝ) ≤ w0 := by exact_mod_cast hw0.le
  refine ⟨χ P, fun e he => ?_, fun j e he => ?_⟩
  · obtain ⟨d, hd, rfl⟩ := supp_χ P e he
    have := hP1 d hd
    have h0 : (0 : ℝ) ≤ (w0 : ℝ) * (d 0 : ℝ) := mul_nonneg hw0' (Nat.cast_nonneg _)
    simp only [Finsupp.tail_apply]
    linarith
  · have hcomp : (aeval (fun i => C (c j i) + X i)).comp (χ (m := m)) =
        ψ.comp (aeval (Fin.cases (1 + X 0) (fun i => C (c j i) + X i.succ +
          ∑ k ∈ Finset.range (Nat.ceil ((H : ℝ) / (v0 : ℝ))),
            if k = 0 then 0 else C (((-1 : ℂ) ^ (k + 1)) / (k : ℂ)) * (X 0) ^ k))) := by
      apply MvPolynomial.algHom_ext
      intro i
      refine Fin.cases ?_ (fun i => ?_) i
      · simp [χ, ψ]
      · simp only [AlgHom.comp_apply, χ, ψ, aeval_X, Fin.cases_succ, map_add, map_sum]
        simp only [aeval_C, algebraMap_eq, Fin.cases_succ]
        symm
        rw [add_eq_left]
        refine Finset.sum_eq_zero fun k _ => ?_
        split_ifs with hk
        · simp
        · simp [zero_pow hk]
    have := congrArg (fun f => (f P).coeff e) hcomp
    simp only [AlgHom.comp_apply] at this
    rw [this, coeff_ψ, hP2 j _ ?_]
    · simp
    · simp only [Finsupp.cons_zero, Finsupp.cons_succ, Nat.cast_zero, mul_zero, zero_add]
      exact he

end PiL23

end

open OAI OAI.PiExponent
open scoped BigOperators

theorem solution
    (m K : Nat) (w0 v0 alpha : Rat)
    (hw0 : 0 < w0) (hv0 : 0 < v0) (halpha : 0 < alpha)
    (w : Fin m → Nat) (hw : ∀ i, 0 < w i)
    (c : Fin K → Fin m → Complex)
    (hjet : OAI.PiExponent.eventualLogJetSurjective m K w0 v0 alpha w c) :
    OAI.PiExponent.eventualTransverseJetSurjectiveForSpatialVolume_360483bd m K alpha w c := by
  exact PiL23.log_to_trans m K w0 v0 alpha hw0 hv0 halpha w hw c hjet
