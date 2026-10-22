-- Prove2me | solution 1 for JHolomorphic.ae_eq_of_forall_integral_smul_eq
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-21T13:48:51.732711+00:00
-- url     : https://prove2.me/submissions/00c1bedf-e151-4371-bb39-8813b2f77542

import Definitions.Def_JHolomorphic_Setting
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Theorems.Thm_JHolomorphic_integrable_smul_of_integrableOn_compact



namespace JHolomorphic

open MeasureTheory Filter Topology
open scoped ContDiff

/-- Two maps that are integrable on every compact subset of an open set `U` and have the same
integrals against every real `C^∞` function with compact support in `U` agree almost everywhere
on `U`. -/
theorem ae_eq_of_forall_integral_smul_eq_aux {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {U : Set ℂ} (hU : IsOpen U) {f f' : ℂ → E}
    (hf : ∀ K ⊆ U, IsCompact K → IntegrableOn f K)
    (hf' : ∀ K ⊆ U, IsCompact K → IntegrableOn f' K)
    (hφ : ∀ φ : ℂ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ U →
      ∫ z, φ z • f z = ∫ z, φ z • f' z) :
    ∀ᵐ z ∂(volume.restrict U), f z = f' z := by
  have hloc : LocallyIntegrableOn (fun z => f z - f' z) U := by
    rw [locallyIntegrableOn_iff hU.isLocallyClosed]
    exact fun K hKU hK => (hf K hKU hK).sub (hf' K hKU hK)
  have := hU.ae_eq_zero_of_integral_contDiff_smul_eq_zero hloc fun g hg hgc hgU => by
    simp_rw [smul_sub]
    rw [integral_sub (integrable_smul_of_integrableOn_compact hf hg.continuous.continuousOn hgc hgU)
      (integrable_smul_of_integrableOn_compact hf' hg.continuous.continuousOn hgc hgU),
      hφ g hg hgc hgU, sub_self]
  rw [ae_restrict_iff' hU.measurableSet]
  exact this.mono fun z hz hzU => sub_eq_zero.mp (hz hzU)

end JHolomorphic

open JHolomorphic

open MeasureTheory Filter Topology
open scoped ContDiff

theorem solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {U : Set ℂ} (hU : IsOpen U) {f f' : ℂ → E}
    (hf : ∀ K ⊆ U, IsCompact K → IntegrableOn f K)
    (hf' : ∀ K ⊆ U, IsCompact K → IntegrableOn f' K)
    (hφ : ∀ φ : ℂ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ U →
      ∫ z, φ z • f z = ∫ z, φ z • f' z) :
    ∀ᵐ z ∂(volume.restrict U), f z = f' z :=
  ae_eq_of_forall_integral_smul_eq_aux hU hf hf' hφ
