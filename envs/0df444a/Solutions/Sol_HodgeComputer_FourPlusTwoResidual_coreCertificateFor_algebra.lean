-- Prove2me | solution 1 for HodgeComputer.FourPlusTwoResidual.coreCertificateFor_algebra
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-21T13:53:38.330123+00:00
-- url     : https://prove2.me/submissions/8c6d2034-852f-40e9-9c62-e7d3f939733f

import Definitions.Def_HodgeComputerFourPlusTwoSourceAlgebra
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

set_option autoImplicit false
noncomputable section

namespace FP3SourceAlgebra

open MvPolynomial HodgeComputer.FourPlusTwoResidual
open scoped BigOperators

private abbrev R4 := MvPolynomial (Fin 4) ℂ

private lemma coreResidual_linear_combination
    (c₁ c₂ : ℂ) (S₁ S₂ D₁ D₂ : R4) (N₁ N₂ : Fin 4 → R4) :
    coreResidual (C c₁ * S₁ + C c₂ * S₂) (D₁ * D₂)
        (fun i => C c₁ * D₂ * N₁ i + C c₂ * D₁ * N₂ i) =
      C c₁ * D₂ ^ 2 * coreResidual S₁ D₁ N₁ + C c₂ * D₁ ^ 2 * coreResidual S₂ D₂ N₂ := by
  have hpD : ∀ i : Fin 4, pderiv i (D₁ * D₂) = pderiv i D₁ * D₂ + D₁ * pderiv i D₂ :=
    fun i => pderiv_mul
  have hpN : ∀ i : Fin 4,
      pderiv i (C c₁ * D₂ * N₁ i + C c₂ * D₁ * N₂ i) =
        C c₁ * (pderiv i D₂ * N₁ i + D₂ * pderiv i (N₁ i)) +
          C c₂ * (pderiv i D₁ * N₂ i + D₁ * pderiv i (N₂ i)) := fun i => by
    simp only [map_add, pderiv_mul, pderiv_C, zero_mul, zero_add]; ring
  unfold coreResidual
  simp only [Fin.sum_univ_four, hpD, hpN]
  ring

private lemma coreResidual_mul_denom (P S D : R4) (N : Fin 4 → R4) :
    coreResidual S (P * D) (fun i => P * N i) = P ^ 2 * coreResidual S D N := by
  have hpD : ∀ i : Fin 4, pderiv i (P * D) = pderiv i P * D + P * pderiv i D :=
    fun _ => pderiv_mul
  have hpN : ∀ i : Fin 4, pderiv i (P * N i) = pderiv i P * N i + P * pderiv i (N i) :=
    fun _ => pderiv_mul
  unfold coreResidual
  simp only [Fin.sum_univ_four, hpD, hpN]
  ring

private lemma X0_ne_zero : (X 0 : R4) ≠ 0 := by
  intro h0
  have hev := congrArg (eval ![1, 0, 0, 0]) h0
  simp at hev

end FP3SourceAlgebra

theorem solution :
    (∀ (c₁ c₂ : ℂ) (S₁ S₂ D₁ D₂ : MvPolynomial (Fin 4) ℂ)
      (N₁ N₂ : Fin 4 → MvPolynomial (Fin 4) ℂ),
      HodgeComputer.FourPlusTwoResidual.CoreCertificateFor S₁ D₁ N₁ →
      HodgeComputer.FourPlusTwoResidual.CoreCertificateFor S₂ D₂ N₂ →
      HodgeComputer.FourPlusTwoResidual.CoreCertificateFor
        (MvPolynomial.C c₁ * S₁ + MvPolynomial.C c₂ * S₂)
        (D₁ * D₂)
        (fun i => MvPolynomial.C c₁ * D₂ * N₁ i + MvPolynomial.C c₂ * D₁ * N₂ i)) ∧
    (∀ (m : ℕ) (P S D : MvPolynomial (Fin 4) ℂ) (N : Fin 4 → MvPolynomial (Fin 4) ℂ),
      P ≠ 0 → P.IsHomogeneous m →
      HodgeComputer.FourPlusTwoResidual.CoreCertificateFor S D N →
      HodgeComputer.FourPlusTwoResidual.CoreCertificateFor S (P * D) (fun i => P * N i)) ∧
    ((∃ (D : MvPolynomial (Fin 4) ℂ) (N : Fin 4 → MvPolynomial (Fin 4) ℂ),
        HodgeComputer.FourPlusTwoResidual.CoreCertificateFor
          HodgeComputer.FourPlusTwoResidual.coreSource D N) ↔
      (∃ (D : MvPolynomial (Fin 4) ℂ) (N : Fin 4 → MvPolynomial (Fin 4) ℂ),
        HodgeComputer.FourPlusTwoResidual.CoreCertificate D N)) := by
  refine ⟨?_, ?_, ?_⟩
  · rintro c₁ c₂ S₁ S₂ D₁ D₂ N₁ N₂
      ⟨hD₁_ne, ⟨d₁, hD₁, hN₁⟩, hres₁⟩ ⟨hD₂_ne, ⟨d₂, hD₂, hN₂⟩, hres₂⟩
    refine ⟨mul_ne_zero hD₁_ne hD₂_ne, ⟨d₁ + d₂, hD₁.mul hD₂, ?_⟩, ?_⟩
    · intro i
      have h1 : (MvPolynomial.C c₁ * D₂ * N₁ i).IsHomogeneous (d₁ + d₂ + 1) := by
        have h := ((MvPolynomial.isHomogeneous_C (Fin 4) c₁).mul hD₂).mul (hN₁ i)
        have heq : 0 + d₂ + (d₁ + 1) = d₁ + d₂ + 1 := by omega
        rwa [heq] at h
      have h2 : (MvPolynomial.C c₂ * D₁ * N₂ i).IsHomogeneous (d₁ + d₂ + 1) := by
        have h := ((MvPolynomial.isHomogeneous_C (Fin 4) c₂).mul hD₁).mul (hN₂ i)
        have heq : 0 + d₁ + (d₂ + 1) = d₁ + d₂ + 1 := by omega
        rwa [heq] at h
      exact h1.add h2
    · rw [FP3SourceAlgebra.coreResidual_linear_combination, hres₁, hres₂, mul_zero, mul_zero, add_zero]
  · rintro m P S D N hP_ne hPm ⟨hD_ne, ⟨d, hDd, hNd⟩, hres⟩
    refine ⟨mul_ne_zero hP_ne hD_ne, ⟨m + d, hPm.mul hDd, ?_⟩, ?_⟩
    · intro i
      have h := hPm.mul (hNd i)
      have heq : m + (d + 1) = m + d + 1 := by omega
      rwa [heq] at h
    · rw [FP3SourceAlgebra.coreResidual_mul_denom, hres, mul_zero]
  · constructor
    · rintro ⟨D, N, hD_ne, ⟨d, hDd, hNd⟩, hres⟩
      cases d with
      | zero =>
          let P : MvPolynomial (Fin 4) ℂ := MvPolynomial.X 0
          have hP_hom : P.IsHomogeneous 1 := MvPolynomial.isHomogeneous_X ℂ (0 : Fin 4)
          refine ⟨P * D, fun i => P * N i, mul_ne_zero FP3SourceAlgebra.X0_ne_zero hD_ne,
            ⟨0, ?_, ?_⟩, ?_⟩
          · simpa using hP_hom.mul hDd
          · intro i
            have h := hP_hom.mul (hNd i)
            simpa using h
          · have hr := FP3SourceAlgebra.coreResidual_mul_denom P
              HodgeComputer.FourPlusTwoResidual.coreSource D N
            rw [hres, mul_zero] at hr
            exact hr
      | succ k =>
          exact ⟨D, N, hD_ne, ⟨k, hDd, hNd⟩, hres⟩
    · rintro ⟨D, N, hD_ne, ⟨k, hDk, hNk⟩, hres⟩
      exact ⟨D, N, hD_ne, ⟨k + 1, hDk, hNk⟩, hres⟩
