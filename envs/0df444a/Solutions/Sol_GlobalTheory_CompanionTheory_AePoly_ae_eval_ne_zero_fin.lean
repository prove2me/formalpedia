-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.AePoly.ae_eval_ne_zero_fin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:17:22.937925+00:00
-- url     : https://prove2.me/submissions/c3f13141-9ca3-4d16-9e3a-fbc08a1e4fdc

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_AePolynomialNonvanishing

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.AePoly
namespace GlobalTheory.CompanionTheory.AePoly
theorem _root_.solution : ∀ (d : ℕ) (Q : MvPolynomial (Fin d) ℂ), Q ≠ 0 →
    ∀ᵐ x ∂(volume : Measure (Fin d → ℂ)), MvPolynomial.eval x Q ≠ 0 := by
  intro d
  induction d with
  | zero =>
    intro Q hQ
    have hex : ∃ x : Fin 0 → ℂ, MvPolynomial.eval x Q ≠ 0 := by
      by_contra h
      push Not at h
      exact hQ (MvPolynomial.funext fun x => by simpa using h x)
    obtain ⟨x, hx⟩ := hex
    refine Filter.Eventually.of_forall fun y => ?_
    rwa [Subsingleton.elim y x]
  | succ d ih =>
    intro Q hQ
    have hP0 : MvPolynomial.finSuccEquiv ℂ d Q ≠ 0 :=
      (map_ne_zero_iff _ (MvPolynomial.finSuccEquiv ℂ d).injective).2 hQ
    have hlc := ih _ (Polynomial.leadingCoeff_ne_zero.2 hP0)
    have hF : Continuous fun z : ℂ × (Fin d → ℂ) => (Fin.cons z.1 z.2 : Fin (d + 1) → ℂ) := by
      refine continuous_pi fun i => ?_
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa using continuous_fst
      · simpa using (by fun_prop : Continuous fun a : ℂ × (Fin d → ℂ) => a.2 j)
    have hS : MeasurableSet
        {z : ℂ × (Fin d → ℂ) | MvPolynomial.eval (Fin.cons z.1 z.2 : Fin (d + 1) → ℂ) Q = 0} :=
      (isClosed_eq ((MvPolynomial.continuous_eval Q).comp hF) continuous_const).measurableSet
    have hprod : ∀ᵐ z ∂((volume : Measure ℂ).prod (volume : Measure (Fin d → ℂ))),
        MvPolynomial.eval (Fin.cons z.1 z.2 : Fin (d + 1) → ℂ) Q ≠ 0 := by
      rw [ae_iff]
      simp only [ne_eq, not_not]
      rw [Measure.prod_apply_symm hS]
      have hz : (fun s : Fin d → ℂ => (volume : Measure ℂ) ((fun y => (y, s)) ⁻¹'
          {z : ℂ × (Fin d → ℂ) | MvPolynomial.eval (Fin.cons z.1 z.2 : Fin (d + 1) → ℂ) Q = 0}))
          =ᵐ[volume] 0 := by
        refine hlc.mono fun s hs => ?_
        have hR : (MvPolynomial.finSuccEquiv ℂ d Q).map (MvPolynomial.eval s) ≠ 0 := by
          intro h0
          apply hs
          have := congrArg (fun p => Polynomial.coeff p
            (MvPolynomial.finSuccEquiv ℂ d Q).natDegree) h0
          simpa [Polynomial.coeff_map] using this
        refine measure_mono_null ?_ ((Polynomial.finite_setOf_isRoot hR).measure_zero volume)
        intro y hy
        simpa [Polynomial.IsRoot, MvPolynomial.eval_eq_eval_mv_eval'] using hy
      rw [lintegral_congr_ae hz]
      simp
    have h := (volume_preserving_piFinSuccAbove (fun _ : Fin (d + 1) => ℂ) 0).quasiMeasurePreserving.ae hprod
    filter_upwards [h] with x hx
    have hc : (Fin.cons (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (d + 1) => ℂ) 0 x).1
        (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (d + 1) => ℂ) 0 x).2 : Fin (d + 1) → ℂ) = x := by
      ext i
      refine Fin.cases ?_ (fun j => ?_) i <;> simp [MeasurableEquiv.piFinSuccAbove, Fin.tail]
    rwa [hc] at hx
end GlobalTheory.CompanionTheory.AePoly
