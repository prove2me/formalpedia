-- Prove2me | solution 1 for JHolomorphic.HasWeakPartialsOn.ae_eq
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-21T13:50:30.809817+00:00
-- url     : https://prove2.me/submissions/927bfae8-9377-4d7d-a13c-3d30bbcf98ed

import Definitions.Def_JHolomorphic_Setting
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Theorems.Thm_JHolomorphic_ae_eq_of_forall_integral_smul_eq



namespace JHolomorphic

open MeasureTheory Filter Topology
open scoped ContDiff

/-- Weak partial derivatives on an open set are unique almost everywhere. -/
theorem HasWeakPartialsOn.ae_eq_aux {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {U : Set ℂ} (hU : IsOpen U) {u us ut us' ut' : ℂ → E}
    (h : HasWeakPartialsOn U u us ut) (h' : HasWeakPartialsOn U u us' ut')
    (hint : ∀ K ⊆ U, IsCompact K →
      IntegrableOn us K ∧ IntegrableOn ut K ∧ IntegrableOn us' K ∧ IntegrableOn ut' K) :
    ∀ᵐ z ∂(volume.restrict U), us z = us' z ∧ ut z = ut' z := by
  refine (ae_eq_of_forall_integral_smul_eq hU (fun K hKU hK => (hint K hKU hK).1)
    (fun K hKU hK => (hint K hKU hK).2.2.1) fun φ hφ hφc hφU => ?_).and
    (ae_eq_of_forall_integral_smul_eq hU (fun K hKU hK => (hint K hKU hK).2.1)
    (fun K hKU hK => (hint K hKU hK).2.2.2) fun φ hφ hφc hφU => ?_)
  · have e1 := (h φ hφ hφc hφU).1
    have e2 := (h' φ hφ hφc hφU).1
    rw [e1] at e2; exact neg_inj.mp e2
  · have e1 := (h φ hφ hφc hφU).2
    have e2 := (h' φ hφ hφc hφU).2
    rw [e1] at e2; exact neg_inj.mp e2

end JHolomorphic

open JHolomorphic JHolomorphic.HasWeakPartialsOn

open MeasureTheory Filter Topology
open scoped ContDiff

theorem solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {U : Set ℂ} (hU : IsOpen U) {u us ut us' ut' : ℂ → E}
    (h : HasWeakPartialsOn U u us ut) (h' : HasWeakPartialsOn U u us' ut')
    (hint : ∀ K ⊆ U, IsCompact K →
      IntegrableOn us K ∧ IntegrableOn ut K ∧ IntegrableOn us' K ∧ IntegrableOn ut' K) :
    ∀ᵐ z ∂(volume.restrict U), us z = us' z ∧ ut z = ut' z :=
  HasWeakPartialsOn.ae_eq_aux hU h h' hint
