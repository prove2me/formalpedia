-- Prove2me | solution 1 for JHolomorphic.differentiableOn_of_hasWeakPartialsOn
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-22T10:59:36.62435+00:00
-- url     : https://prove2.me/submissions/cc496c8d-16c4-4cbc-8a7d-31fb9e07ce06

import Definitions.Def_JHolomorphic_Setting
import Mathlib.Analysis.Complex.Conformal
import Theorems.Thm_JHolomorphic_contDiffOn_of_isWeakJHolomorphicOn
import Theorems.Thm_JHolomorphic_HasWeakPartialsOn_ae_eq
import Theorems.Thm_JHolomorphic_HasWeakPartialsOn_of_contDiffOn
import Mathlib.Analysis.InnerProductSpace.PiL2



namespace JHolomorphic

open MeasureTheory Metric Filter Topology Set
open scoped ContDiff ENNReal

/-- A continuous `W^{1,p}_loc` map, `p > 2`, with `∂ₛf + i ∂ₜf = 0` a.e. is holomorphic. -/
theorem differentiableOn_of_hasWeakPartialsOn_aux (n : ℕ) (p : ℝ) (hp : 2 < p) {U : Set ℂ}
    (hU : IsOpen U) (f fs ft : ℂ → EuclideanSpace ℂ (Fin n)) (hf : ContinuousOn f U)
    (hw : HasWeakPartialsOn U f fs ft)
    (hLp : ∀ K ⊆ U, IsCompact K →
      MemLp f (ENNReal.ofReal p) (volume.restrict K) ∧
      MemLp fs (ENNReal.ofReal p) (volume.restrict K) ∧
      MemLp ft (ENNReal.ofReal p) (volume.restrict K))
    (heq : ∀ᵐ z ∂(volume.restrict U), fs z + Complex.I • ft z = 0) :
    DifferentiableOn ℂ f U := by
  let J0 : EuclideanSpace ℂ (Fin n) →L[ℝ] EuclideanSpace ℂ (Fin n) := (ContinuousLinearMap.lsmul ℝ ℂ : ℂ →L[ℝ] EuclideanSpace ℂ (Fin n) →L[ℝ] EuclideanSpace ℂ (Fin n)) Complex.I
  have hJ0 : ∀ v, J0 v = Complex.I • v := fun v => rfl
  have hAC : IsAlmostComplexOn (fun _ : EuclideanSpace ℂ (Fin n) => J0) univ := by
    refine ⟨isOpen_univ, contDiffOn_const, fun _ _ => ?_⟩
    ext v
    simp [hJ0, smul_smul]
  have hW : IsWeakJHolomorphicOn p (fun _ : EuclideanSpace ℂ (Fin n) => J0) univ U f :=
    ⟨hf, mapsTo_univ _ _, fs, ft, hw, hLp, by simpa [hJ0] using heq⟩
  have hcd : ContDiffOn ℝ ∞ f U :=
    contDiffOn_of_isWeakJHolomorphicOn p hp _ univ hAC U hU f hW
  have hc1 : ContDiffOn ℝ 1 f U := hcd.of_le (by norm_cast)
  have hcl := HasWeakPartialsOn.of_contDiffOn hU hc1
  have hcont : ContinuousOn (fun z => fderiv ℝ f z) U := hc1.continuousOn_fderiv_of_isOpen hU le_rfl
  have hc1' : ContinuousOn (fun z => fderiv ℝ f z 1) U :=
    (ContinuousLinearMap.apply ℝ (EuclideanSpace ℂ (Fin n)) (1 : ℂ)).continuous.comp_continuousOn hcont
  have hcI : ContinuousOn (fun z => fderiv ℝ f z Complex.I) U :=
    (ContinuousLinearMap.apply ℝ (EuclideanSpace ℂ (Fin n)) Complex.I).continuous.comp_continuousOn hcont
  have hint : ∀ K ⊆ U, IsCompact K →
      IntegrableOn fs K ∧ IntegrableOn ft K ∧ IntegrableOn (fun z => fderiv ℝ f z 1) K ∧
        IntegrableOn (fun z => fderiv ℝ f z Complex.I) K := by
    intro K hK hKc
    have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
      rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal (by linarith)
    haveI : IsFiniteMeasure (volume.restrict K) := isFiniteMeasure_restrict.2 hKc.measure_lt_top.ne
    obtain ⟨-, h2, h3⟩ := hLp K hK hKc
    exact ⟨(h2.mono_exponent hp1).integrable le_rfl, (h3.mono_exponent hp1).integrable le_rfl,
      (hc1'.mono hK).integrableOn_compact hKc, (hcI.mono hK).integrableOn_compact hKc⟩
  have hae := HasWeakPartialsOn.ae_eq hU hw hcl hint
  have hzero : ∀ᵐ z ∂(volume.restrict U),
      fderiv ℝ f z 1 + Complex.I • fderiv ℝ f z Complex.I = 0 := by
    filter_upwards [hae, heq] with z hz hz'
    rw [← hz.1, ← hz.2]; exact hz'
  have heqOn : EqOn (fun z => fderiv ℝ f z 1 + Complex.I • fderiv ℝ f z Complex.I) 0 U :=
    Measure.eqOn_open_of_ae_eq hzero hU (hc1'.add (hcI.const_smul Complex.I)) continuousOn_const
  intro z hz
  have hdz : DifferentiableAt ℝ f z :=
    (hc1.differentiableOn one_ne_zero z hz).differentiableAt (hU.mem_nhds hz)
  refine (differentiableAt_complex_iff_differentiableAt_real.2 ⟨hdz, ?_⟩).differentiableWithinAt
  have h0 : fderiv ℝ f z 1 + Complex.I • fderiv ℝ f z Complex.I = 0 := heqOn hz
  have h1 : fderiv ℝ f z 1 = -(Complex.I • fderiv ℝ f z Complex.I) := eq_neg_of_add_eq_zero_left h0
  rw [h1, smul_neg, smul_smul, Complex.I_mul_I, neg_one_smul, neg_neg]

end JHolomorphic

open JHolomorphic

open MeasureTheory Metric Filter Topology Set
open scoped ContDiff ENNReal

theorem solution (n : ℕ) (p : ℝ) (hp : 2 < p) {U : Set ℂ}
    (hU : IsOpen U) (f fs ft : ℂ → EuclideanSpace ℂ (Fin n)) (hf : ContinuousOn f U)
    (hw : HasWeakPartialsOn U f fs ft)
    (hLp : ∀ K ⊆ U, IsCompact K →
      MemLp f (ENNReal.ofReal p) (volume.restrict K) ∧
      MemLp fs (ENNReal.ofReal p) (volume.restrict K) ∧
      MemLp ft (ENNReal.ofReal p) (volume.restrict K))
    (heq : ∀ᵐ z ∂(volume.restrict U), fs z + Complex.I • ft z = 0) :
    DifferentiableOn ℂ f U :=
  differentiableOn_of_hasWeakPartialsOn_aux n p hp hU f fs ft hf hw hLp heq
