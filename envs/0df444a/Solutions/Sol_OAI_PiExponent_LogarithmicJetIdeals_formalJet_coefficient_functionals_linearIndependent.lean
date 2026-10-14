-- Prove2me | solution 1 for OAI.PiExponent.LogarithmicJetIdeals.formalJet_coefficient_functionals_linearIndependent
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-14T08:25:51.245101+00:00
-- url     : https://prove2.me/submissions/6f5c2e53-74d9-49c2-9b64-477f428a7a3a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals
import Mathlib.LinearAlgebra.LinearIndependent.Basic
import Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_exists_formalJet_coefficient_dualFamily

open OAI.PiExponent.AdmissibleFormalInterpolation
open scoped BigOperators

theorem solution
    {m : ℕ} {ι : Type} [Fintype ι]
    (c : ι → Fin m → ℂ)
    (exponent : ι → (Fin (m + 1) →₀ ℕ))
    (hindex : Function.Injective (fun x => (c x, exponent x))) :
    LinearIndependent ℂ
      (fun x =>
        ({ toFun := fun P : MvPolynomial (Fin (m + 1)) ℂ =>
              MvPowerSeries.coeff (exponent x) (formalJet (c x) P)
           map_add' := by simp [formalJet]
           map_smul' := by simp [formalJet] } :
          MvPolynomial (Fin (m + 1)) ℂ →ₗ[ℂ] ℂ)) := by
  classical
  obtain ⟨Q, hQ⟩ :=
    OAI.PiExponent.LogarithmicJetIdeals.exists_formalJet_coefficient_dualFamily
      c exponent hindex
  rw [Fintype.linearIndependent_iff]
  intro a ha i
  have h := congrArg
    (fun L : MvPolynomial (Fin (m + 1)) ℂ →ₗ[ℂ] ℂ => L (Q i)) ha
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.zero_apply] at h
  change (∑ x : ι,
    a x • MvPowerSeries.coeff (exponent x) (formalJet (c x) (Q i))) = 0 at h
  simpa [hQ, smul_eq_mul, mul_ite] using h