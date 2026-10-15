-- Prove2me | solution 1 for OAI.PiExponent.LogarithmicJetIdeals.rectangularJetIdeals_comaximal_of_centers_differ
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-15T06:19:17.710749+00:00
-- url     : https://prove2.me/submissions/6f164817-3590-45be-a8ef-e754244b2ca6

import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals_RectangularJetIdeal
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.Tactic.Ring

open OAI.PiExponent.LogarithmicJetIdeals

theorem solution
    {m : Nat} (c d : Fin m -> Complex) (degree : Fin (m + 1) -> Nat)
    (hd : Exists fun k => Not (c k = d k)) :
    OAI.PiExponent.LogarithmicJetIdeals.rectangularJetIdeal c degree ⊔
      OAI.PiExponent.LogarithmicJetIdeals.rectangularJetIdeal d degree = ⊤ := by
  classical
  rcases hd with ⟨k, hkd⟩
  let P : MvPolynomial (Fin (m + 1)) Complex :=
    MvPolynomial.X (Fin.succ k) - MvPolynomial.C (c k)
  let Q : MvPolynomial (Fin (m + 1)) Complex :=
    MvPolynomial.X (Fin.succ k) - MvPolynomial.C (d k)
  let n := Nat.succ (degree (Fin.succ k))
  have hδ : c k - d k ≠ 0 := sub_ne_zero.mpr hkd
  have hQP : Q - P = MvPolynomial.C (c k - d k) := by
    dsimp [P, Q]
    rw [map_sub]
    ring
  have hlin : IsCoprime P Q := by
    refine ⟨-MvPolynomial.C (c k - d k)⁻¹,
      MvPolynomial.C (c k - d k)⁻¹, ?_⟩
    calc
      -MvPolynomial.C (c k - d k)⁻¹ * P +
          MvPolynomial.C (c k - d k)⁻¹ * Q =
          MvPolynomial.C (c k - d k)⁻¹ * (Q - P) := by ring
      _ = MvPolynomial.C ((c k - d k)⁻¹ * (c k - d k)) := by
        rw [hQP, ← map_mul]
      _ = 1 := by simp [hδ]
  let I : Ideal (MvPolynomial (Fin (m + 1)) Complex) := Ideal.span {P ^ n}
  let J : Ideal (MvPolynomial (Fin (m + 1)) Complex) := Ideal.span {Q ^ n}
  have hIJ : I ⊔ J = ⊤ := by
    exact Ideal.isCoprime_iff_sup_eq.mp
      ((Ideal.isCoprime_span_singleton_iff (P ^ n) (Q ^ n)).mpr hlin.pow)
  have hI : I ≤ rectangularJetIdeal c degree := by
    apply Ideal.span_le.mpr
    rintro x hx
    simp only [Set.mem_singleton_iff] at hx
    subst x
    exact Ideal.subset_span ⟨Fin.succ k, by simp [P, n]⟩
  have hJ : J ≤ rectangularJetIdeal d degree := by
    apply Ideal.span_le.mpr
    rintro x hx
    simp only [Set.mem_singleton_iff] at hx
    subst x
    exact Ideal.subset_span ⟨Fin.succ k, by simp [Q, n]⟩
  apply le_antisymm le_top
  rw [← hIJ]
  exact sup_le_sup hI hJ