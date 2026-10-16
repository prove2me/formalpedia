-- Prove2me | solution 1 for HunterPDE.Shared.HasWeakDeriv.ae_eq
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-15T17:49:06.115403+00:00
-- url     : https://prove2.me/submissions/14c49f85-095d-481d-8ffe-6e31420b7eb8

import Definitions.Def_HunterPDE_Shared_WeakDeriv
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

open MeasureTheory HunterPDE.Shared
open scoped ContDiff
set_option autoImplicit false

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
    have hi (g : EuclideanSpace ℝ (Fin n) → ℝ) (hg : LocallyIntegrableOn g Ω) :
        IntegrableOn (fun x => φ x * g x) Ω := by
      have hh : Integrable (fun x => g x * φ x) := by
        apply (integrableOn_iff_integrable_of_support_subset
          (s := tsupport φ) (fun x hx => ?_)).mp
        · exact (hg.integrableOn_compact_subset hs hc).mul_continuousOn
            hφ.continuous.continuousOn hc
        · apply subset_tsupport φ
          simpa only [Function.mem_support] using (mul_ne_zero_iff.mp hx).2
      simpa only [mul_comm] using hh.integrableOn (s := Ω)
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Ω)]
    · simp only [Pi.sub_apply, smul_eq_mul, mul_sub]
      have heq : (∫ x in Ω, φ x * u x) = ∫ x in Ω, φ x * v x := by
        simpa only [mul_comm] using (hu.2.2 φ ht).trans (hv.2.2 φ ht).symm
      rw [integral_sub (hi u hu.2.1) (hi v hv.2.1), heq, sub_self]
    · intro x hx
      have : φ x = 0 := image_eq_zero_of_notMem_tsupport (fun hx' => hx (hs hx'))
      simp [this]
