-- Prove2me | solution 1 for HunterPDE.Sobolev.HasWeakDeriv.ae_eq
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-10T22:41:54.663623+00:00
-- url     : https://prove2.me/submissions/aa167d3f-7ee3-4682-9d40-c2e636b1dbc5

import Definitions.Def_HunterPDE_Sobolev_SobolevSpace
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import Mathlib.Analysis.MeanInequalities

open MeasureTheory HunterPDE.Sobolev
open scoped ContDiff

namespace HunterPDE.Sobolev

lemma test_mul_integrable {n : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))}
    {f φ : EuclideanSpace ℝ (Fin n) → ℝ} (hf : LocallyIntegrableOn f Ω)
    (hφ : IsTestFunction Ω φ) : Integrable (fun x => f x * φ x) := by
  apply (integrableOn_iff_integrable_of_support_subset
    (s := tsupport φ) (fun x hx => ?_)).mp
  · exact (hf.integrableOn_compact_subset hφ.2.2 hφ.2.1).mul_continuousOn
      hφ.1.continuous.continuousOn hφ.2.1
  · apply subset_tsupport φ
    simpa only [Function.mem_support] using (mul_ne_zero_iff.mp hx).2

end HunterPDE.Sobolev

theorem solution {n : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))}
    (hΩ : IsOpen Ω) {α : Fin n → ℕ}
    {f u v : EuclideanSpace ℝ (Fin n) → ℝ}
    (hu : HasWeakDeriv Ω α f u) (hv : HasWeakDeriv Ω α f v) :
    u =ᵐ[volume.restrict Ω] v := by
  have hz := hΩ.ae_eq_zero_of_integral_contDiff_smul_eq_zero
    (hu.2.1.sub hv.2.1) ?_
  · rw [Filter.EventuallyEq, ae_restrict_iff' hΩ.measurableSet]
    filter_upwards [hz] with x hx hmem
    exact sub_eq_zero.mp (hx hmem)
  · intro φ hφ hc hs
    have ht : IsTestFunction Ω φ := ⟨hφ, hc, hs⟩
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Ω)]
    · simp only [Pi.sub_apply, smul_eq_mul, mul_sub]
      have heq : (∫ x in Ω, φ x * u x) = ∫ x in Ω, φ x * v x := by
        simpa only [mul_comm] using (hu.2.2 φ ht).trans (hv.2.2 φ ht).symm
      rw [integral_sub, heq, sub_self]
      · simpa only [IntegrableOn, mul_comm] using
          (test_mul_integrable hu.2.1 ht).integrableOn (s := Ω)
      · simpa only [IntegrableOn, mul_comm] using
          (test_mul_integrable hv.2.1 ht).integrableOn (s := Ω)
    · intro x hx
      have : φ x = 0 := image_eq_zero_of_notMem_tsupport (fun hx' => hx (hs hx'))
      simp [this]

