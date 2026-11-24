-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.EisTube.laplaceEntire
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T13:01:20.194003+00:00
-- url     : https://prove2.me/submissions/995f77fb-78a6-41f5-9ec9-8edf54ef69f0

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IntegrableExpNegSumAbs
import Theorems.Thm_GlobalTheory_CompanionTheory_EisTube_integrable_exp_neg_sum_abs
import Theorems.Thm_GlobalTheory_CompanionTheory_EisTube_uniform_bound
import Theorems.Thm_GlobalTheory_CompanionTheory_EisTube_dom_bound
import Theorems.Thm_GlobalTheory_CompanionTheory_EisTube_continuous_ker_right
import Theorems.Thm_GlobalTheory_CompanionTheory_EisTube_continuous_ker_left
import Theorems.Thm_GlobalTheory_CompanionTheory_EisTube_re_le_of_dist
import Theorems.Thm_GlobalTheory_CompanionTheory_EisTube_continuous_lin
import Theorems.Thm_GlobalTheory_CompanionTheory_EisTube_norm_lin_le
import Theorems.Thm_GlobalTheory_CompanionTheory_EisTube_hasFDerivAt_ker
import Theorems.Thm_GlobalTheory_CompanionTheory_EisTube_mul_exp_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Topology
universe u
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.EisTube
namespace GlobalTheory.CompanionTheory.EisTube
theorem _root_.solution (ι : Type) [Fintype ι] (P : Type u) [TopologicalSpace P]
    [FirstCountableTopology P] (h : P → ℝ) (hh : ∀ p, 0 ≤ h p)
    (hloc : ∀ p, ∃ U ∈ nhds p, BddAbove (h '' U))
    (ψ : P → (ι → ℝ) → ℂ) (hm : ∀ p, MeasureTheory.AEStronglyMeasurable (ψ p))
    (hc : ∀ t, Continuous (fun p => ψ p t))
    (hv : ∀ v : ι → ℝ, ∃ C : ℝ, ∀ p t,
      ‖ψ p t‖ ≤ C * h p * Real.exp (-(2 * Real.pi * ∑ i, v i * t i))) :
    (∀ p (z : ι → ℂ), MeasureTheory.Integrable
        (fun t : ι → ℝ => ψ p t * Complex.exp (2 * (Real.pi : ℂ) * ∑ i, z i * t i))) ∧
    (∀ p, Differentiable ℂ (fun z : ι → ℂ =>
        ∫ t : ι → ℝ, ψ p t * Complex.exp (2 * (Real.pi : ℂ) * ∑ i, z i * t i))) ∧
    Continuous (fun q : (ι → ℂ) × P =>
        ∫ t : ι → ℝ, ψ q.2 t * Complex.exp (2 * (Real.pi : ℂ) * ∑ i, q.1 i * t i)) ∧
    (∀ K : Set (ι → ℂ), IsCompact K → ∃ C : ℝ, ∀ z ∈ K, ∀ p,
        ‖∫ t : ι → ℝ, ψ p t * Complex.exp (2 * (Real.pi : ℂ) * ∑ i, z i * t i)‖ ≤ C * h p) := by
  have h2pi : (0 : ℝ) < 2 * Real.pi := by positivity
  have hG : Integrable (fun t : ι → ℝ => Real.exp (-(2 * Real.pi * ∑ i, |t i|))) :=
    integrable_exp_neg_sum_abs h2pi
  have hmeas : ∀ p (z : ι → ℂ), AEStronglyMeasurable (fun t => ψ p t * ker z t) := fun p z =>
    (hm p).mul (continuous_ker_right z).aestronglyMeasurable
  have hI : ∀ p (z : ι → ℂ), Integrable (fun t => ψ p t * ker z t) := by
    intro p z
    obtain ⟨C, hC0, hC⟩ := uniform_bound hh hv ((∑ j, |(z j).re|) + 1 + 1)
    have hz : ∀ i, |(z i).re| ≤ (∑ j, |(z j).re|) + 1 := fun i =>
      re_le_of_dist (by simp) i
    exact Integrable.mono' (hG.const_mul (C * h p)) (hmeas p z)
      (Filter.Eventually.of_forall fun t => dom_bound hh hC0 hC hz p t)
  refine ⟨hI, ?_, ?_, ?_⟩
  · intro p z₀
    change DifferentiableAt ℂ (fun z : ι → ℂ => ∫ t : ι → ℝ, ψ p t * ker z t) z₀
    obtain ⟨C, hC0, hC⟩ := uniform_bound hh hv ((∑ j, |(z₀ j).re|) + 1 + 1)
    have hb : ∀ t : ι → ℝ, ∀ z ∈ Metric.ball z₀ 1,
        ‖(ψ p t * ker z t) • lin t‖ ≤ C * h p * (2 * Real.pi) * Real.exp (-(1 * ∑ i, |t i|)) := by
      intro t z hz
      have hS : 0 ≤ ∑ i, |t i| := Finset.sum_nonneg fun _ _ => abs_nonneg _
      have hCh : 0 ≤ C * h p := mul_nonneg hC0 (hh p)
      rw [norm_smul, one_mul]
      calc ‖ψ p t * ker z t‖ * ‖lin t‖
          ≤ (C * h p * Real.exp (-(2 * Real.pi * ∑ i, |t i|))) * (2 * Real.pi * ∑ i, |t i|) :=
            mul_le_mul (dom_bound hh hC0 hC (re_le_of_dist hz) p t) (norm_lin_le t) (norm_nonneg _)
              (mul_nonneg hCh (Real.exp_pos _).le)
        _ = C * h p * (2 * Real.pi) *
              ((∑ i, |t i|) * Real.exp (-(2 * Real.pi * ∑ i, |t i|))) := by ring
        _ ≤ C * h p * (2 * Real.pi) * Real.exp (-∑ i, |t i|) :=
            mul_le_mul_of_nonneg_left (mul_exp_le hS) (mul_nonneg hCh h2pi.le)
    have key := hasFDerivAt_integral_of_dominated_of_fderiv_le (𝕜 := ℂ) (μ := volume)
      (F := fun (z : ι → ℂ) (t : ι → ℝ) => ψ p t * ker z t)
      (F' := fun (z : ι → ℂ) (t : ι → ℝ) => (ψ p t * ker z t) • lin t) (x₀ := z₀)
      (s := Metric.ball z₀ 1)
      (bound := fun t => C * h p * (2 * Real.pi) * Real.exp (-(1 * ∑ i, |t i|)))
      (Metric.ball_mem_nhds _ one_pos) (Filter.Eventually.of_forall fun z => hmeas p z) (hI p z₀)
      ((hmeas p z₀).smul continuous_lin.aestronglyMeasurable)
      (Filter.Eventually.of_forall hb)
      ((integrable_exp_neg_sum_abs one_pos).const_mul _)
      (Filter.Eventually.of_forall fun t z _ => hasFDerivAt_ker (ψ p t) t z)
    exact key.differentiableAt
  · change Continuous (fun q : (ι → ℂ) × P => ∫ t : ι → ℝ, ψ q.2 t * ker q.1 t)
    rw [continuous_iff_continuousAt]
    rintro ⟨z₀, p₀⟩
    obtain ⟨U, hU, M, hM⟩ := hloc p₀
    obtain ⟨C, hC0, hC⟩ := uniform_bound hh hv ((∑ j, |(z₀ j).re|) + 1 + 1)
    have hev : ∀ᶠ q : (ι → ℂ) × P in 𝓝 (z₀, p₀), dist q.1 z₀ < 1 ∧ q.2 ∈ U :=
      ((continuous_fst.tendsto (z₀, p₀)).eventually (Metric.ball_mem_nhds z₀ one_pos)).and
        ((continuous_snd.tendsto (z₀, p₀)).eventually hU)
    refine continuousAt_of_dominated
      (bound := fun t => C * M * Real.exp (-(2 * Real.pi * ∑ i, |t i|)))
      (Filter.Eventually.of_forall fun q => hmeas q.2 q.1)
      (hev.mono fun q hq => Filter.Eventually.of_forall fun t => ?_)
      (hG.const_mul (C * M)) (Filter.Eventually.of_forall fun t => ?_)
    · exact (dom_bound hh hC0 hC (re_le_of_dist hq.1) q.2 t).trans
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (hM ⟨_, hq.2, rfl⟩) hC0) (Real.exp_pos _).le)
    · exact (((hc t).comp continuous_snd).mul
        ((continuous_ker_left t).comp continuous_fst)).continuousAt
  · intro K hK
    obtain ⟨R, hR⟩ := hK.isBounded.exists_norm_le
    have hz : ∀ z ∈ K, ∀ i, |(z i).re| ≤ R := fun z hzK i =>
      (Complex.abs_re_le_norm _).trans ((norm_le_pi_norm z i).trans (hR z hzK))
    obtain ⟨C, hC0, hC⟩ := uniform_bound hh hv (R + 1)
    refine ⟨C * ∫ t : ι → ℝ, Real.exp (-(2 * Real.pi * ∑ i, |t i|)), fun z hzK p => ?_⟩
    have key := norm_integral_le_of_norm_le (hG.const_mul (C * h p))
      (Filter.Eventually.of_forall fun t => dom_bound hh hC0 hC (hz z hzK) p t)
    rw [integral_const_mul] at key
    calc ‖∫ t : ι → ℝ, ψ p t * Complex.exp (2 * (Real.pi : ℂ) * ∑ i, z i * t i)‖
        ≤ C * h p * ∫ t : ι → ℝ, Real.exp (-(2 * Real.pi * ∑ i, |t i|)) := key
      _ = (C * ∫ t : ι → ℝ, Real.exp (-(2 * Real.pi * ∑ i, |t i|))) * h p := by ring
end GlobalTheory.CompanionTheory.EisTube
