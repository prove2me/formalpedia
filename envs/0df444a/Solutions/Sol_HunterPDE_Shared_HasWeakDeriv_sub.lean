-- Prove2me | solution 1 for HunterPDE.Shared.HasWeakDeriv.sub
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-17T22:11:44.979978+00:00
-- url     : https://prove2.me/submissions/a34a4b94-72f9-4dda-a8ad-38a1220f1b68

import Definitions.Def_HunterPDE_Shared_WeakDeriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.FDeriv.Const
import Mathlib.MeasureTheory.Integral.Bochner.Set

open MeasureTheory HunterPDE.Shared
open scoped ContDiff
set_option autoImplicit false

theorem solution {n : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))}
    {α : Fin n → ℕ} {f g u v : EuclideanSpace ℝ (Fin n) → ℝ}
    (hu : HasWeakDeriv Ω α f u) (hv : HasWeakDeriv Ω α g v) :
    HasWeakDeriv Ω α (f - g) (u - v) := by
  have ht (ψ : EuclideanSpace ℝ (Fin n) → ℝ) (hψ : IsTestFunction Ω ψ)
      (l : List (Fin n)) : IsTestFunction Ω (iteratedPartial ψ l) := by
    induction l with
    | nil => exact hψ
    | cons i l ih =>
      refine ⟨?_, ih.2.1.fderiv_apply ℝ _,
        (tsupport_fderiv_apply_subset ℝ _).trans ih.2.2⟩
      exact (ih.1.contDiff_fderiv_apply (m := ∞) (by simp)).comp
        (contDiff_id.prodMk contDiff_const)
  have hi (a ψ : EuclideanSpace ℝ (Fin n) → ℝ)
      (ha : LocallyIntegrableOn a Ω) (hψ : IsTestFunction Ω ψ) :
      IntegrableOn (fun x => a x * ψ x) Ω := by
    have hh : Integrable (fun x => a x * ψ x) := by
      apply (integrableOn_iff_integrable_of_support_subset
        (s := tsupport ψ) (fun x hx => ?_)).mp
      · exact (ha.integrableOn_compact_subset hψ.2.2 hψ.2.1).mul_continuousOn
          hψ.1.continuous.continuousOn hψ.2.1
      · exact subset_tsupport ψ ((mul_ne_zero_iff.mp hx).2)
    exact hh.integrableOn
  refine ⟨hu.1.sub hv.1, hu.2.1.sub hv.2.1, ?_⟩
  intro ψ hψ
  simp only [Pi.sub_apply, sub_mul]
  rw [integral_sub (hi u ψ hu.2.1 hψ) (hi v ψ hv.2.1 hψ),
    integral_sub (hi f (multiDeriv ψ α) hu.1 (ht ψ hψ (multiIndexList α)))
      (hi g (multiDeriv ψ α) hv.1 (ht ψ hψ (multiIndexList α))),
    hu.2.2 ψ hψ, hv.2.2 ψ hψ, mul_sub]
