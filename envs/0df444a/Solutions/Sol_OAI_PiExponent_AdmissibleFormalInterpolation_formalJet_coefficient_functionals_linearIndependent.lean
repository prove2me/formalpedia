-- Prove2me | solution 1 for OAI.PiExponent.AdmissibleFormalInterpolation.formalJet_coefficient_functionals_linearIndependent
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-15T20:39:58.502643+00:00
-- url     : https://prove2.me/submissions/96202918-9d70-48e6-ae2a-424133c415b5
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Mathlib.LinearAlgebra.LinearIndependent.Basic
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.Data.Finset.Lattice.Fold
import Theorems.Thm_OAI_PiExponent_AdmissibleFormalInterpolation_ordinaryTaylor_coefficient_functionals_linearIndependent
import Theorems.Thm_OAI_PiExponent_AdmissibleFormalInterpolation_formalJet_finite_order_polynomial_pullback

open OAI.PiExponent.AdmissibleFormalInterpolation

theorem solution
    {m : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
    (c : ι → Fin m → ℂ)
    (exponent : ι → (Fin (m + 1) →₀ ℕ))
    (hindex : Function.Injective (fun x => (c x, exponent x))) :
    LinearIndependent ℂ
      (fun x => (MvPowerSeries.coeff (exponent x)).comp
        (formalJet (c x)).toLinearMap) := by
  let center : ι → Fin (m + 1) → ℂ :=
    fun x => (Fin.cases (1 : ℂ) (c x) : Fin (m + 1) → ℂ)
  have hcenter : Function.Injective (fun x => (center x, exponent x)) := by
    intro x y h
    apply hindex
    apply Prod.ext
    · funext i
      have hi := congrArg
        (fun p : (Fin (m + 1) → ℂ) × (Fin (m + 1) →₀ ℕ) =>
          p.1 i.succ) h
      simpa only [center, Fin.cases_succ] using hi
    · exact congrArg
        (fun p : (Fin (m + 1) → ℂ) × (Fin (m + 1) →₀ ℕ) => p.2) h
  have hTaylor :=
    OAI.PiExponent.AdmissibleFormalInterpolation.ordinaryTaylor_coefficient_functionals_linearIndependent
      center exponent hcenter
  let T : ℕ := (Finset.univ : Finset ι).sup (fun x => exponent x 0) + 1
  have hcut (x : ι) : exponent x 0 < T := by
    exact Nat.lt_succ_of_le
      (Finset.le_sup (f := fun y => exponent y 0) (Finset.mem_univ x))
  obtain ⟨A, hA⟩ :=
    OAI.PiExponent.AdmissibleFormalInterpolation.formalJet_finite_order_polynomial_pullback
      (m := m) T
  let jet : ι → Module.Dual ℂ (MvPolynomial (Fin (m + 1)) ℂ) :=
    fun x => (MvPowerSeries.coeff (exponent x)).comp
      (formalJet (c x)).toLinearMap
  have heq : A.toLinearMap.dualMap ∘ jet =
      (fun x => (MvPowerSeries.coeff (exponent x)).comp
        (MvPolynomial.aeval (fun i : Fin (m + 1) =>
          MvPowerSeries.C (center x i) + MvPowerSeries.X i)).toLinearMap) := by
    funext x
    apply LinearMap.ext
    intro P
    exact hA (c x) (exponent x) (hcut x) P
  have hcomp : LinearIndependent ℂ (A.toLinearMap.dualMap ∘ jet) := by
    rw [heq]
    exact hTaylor
  exact LinearIndependent.of_comp A.toLinearMap.dualMap hcomp