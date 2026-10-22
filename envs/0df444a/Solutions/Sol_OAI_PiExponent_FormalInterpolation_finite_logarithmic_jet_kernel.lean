-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.finite_logarithmic_jet_kernel
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-21T13:50:19.522404+00:00
-- url     : https://prove2.me/submissions/8bcd045f-5798-4837-86dc-781aa100916e

import Definitions.Def_OAI_PiExponent_LogarithmicWordContact
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Pi

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.FormalInterpolation

theorem solution
    {m K : Nat} (c : Fin K → Fin m → Complex)
    (S T : Finset (Fin (m + 1) →₀ Nat))
    (hcard : K * T.card < S.card) :
    ∃ F : MvPolynomial (Fin (m + 1)) Complex,
      F ≠ 0 ∧ F.support ⊆ S ∧
        ∀ (j : Fin K) (a : Fin (m + 1) →₀ Nat), a ∈ T →
          MvPowerSeries.coeff a (formalJet (c j) F) = 0 := by
  classical
  -- Assemble a polynomial from its allowed monomial coefficients.
  let A : (↥S → Complex) →ₗ[Complex] MvPolynomial (Fin (m + 1)) Complex :=
    ∑ s : ↥S, (MvPolynomial.monomial s.val).comp
      (LinearMap.proj (R := Complex) s)
  have hcoeff (x : ↥S → Complex) (s : ↥S) :
      MvPolynomial.coeff s.val (A x) = x s := by
    simp only [A, LinearMap.sum_apply, LinearMap.comp_apply,
      LinearMap.proj_apply, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial]
    calc
      (∑ b : ↥S, if b.val = s.val then x b else 0) =
          (if s.val = s.val then x s else 0) := by
        apply Finset.sum_eq_single s
        · intro b hb hbs
          have hval : b.val ≠ s.val := fun h => hbs (Subtype.ext h)
          exact if_neg hval
        · simp
      _ = x s := if_pos rfl
  -- Each row of the finite system is a composition of linear maps.
  let L : (↥S → Complex) →ₗ[Complex] ((Fin K × ↥T) → Complex) :=
    LinearMap.pi fun p =>
      ((MvPowerSeries.coeff p.2.val).comp
        (formalJet (c p.1)).toLinearMap).comp A
  have hkernel : ∃ x : ↥S → Complex, x ≠ 0 ∧ L x = 0 := by
    by_contra h
    have hzero : ∀ x : ↥S → Complex, L x = 0 → x = 0 := by
      intro x hx
      by_contra hnx
      exact h ⟨x, hnx, hx⟩
    have hinj : Function.Injective L :=
      LinearMap.ker_eq_bot.mp (LinearMap.ker_eq_bot'.mpr hzero)
    have hle := LinearMap.finrank_le_finrank_of_injective hinj
    have hle' : S.card ≤ K * T.card := by
      simpa only [Module.finrank_pi, Fintype.card_prod,
        Fintype.card_fin, Fintype.card_coe] using hle
    exact (not_le_of_gt hcard) hle'
  obtain ⟨x, hx, hL⟩ := hkernel
  refine ⟨A x, ?_, ?_, ?_⟩
  · intro hAx
    apply hx
    funext s
    have hs := hcoeff x s
    rw [hAx, MvPolynomial.coeff_zero] at hs
    exact hs.symm
  · intro a ha
    by_contra hnot
    have hzero : MvPolynomial.coeff a (A x) = 0 := by
      simp only [A, LinearMap.sum_apply, LinearMap.comp_apply,
        LinearMap.proj_apply, MvPolynomial.coeff_sum,
        MvPolynomial.coeff_monomial]
      apply Finset.sum_eq_zero
      intro s hs
      have hne : s.val ≠ a := by
        intro he
        exact hnot (he ▸ s.property)
      simp [hne]
    exact (MvPolynomial.mem_support_iff.mp ha) hzero
  · intro j a ha
    have h := congrFun hL (j, ⟨a, ha⟩)
    change MvPowerSeries.coeff a (formalJet (c j) (A x)) = 0 at h
    exact h