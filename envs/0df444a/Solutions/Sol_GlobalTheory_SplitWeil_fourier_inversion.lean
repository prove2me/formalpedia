-- Prove2me | solution 1 for GlobalTheory.SplitWeil.fourier_inversion
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:09:43.346675+00:00
-- url     : https://prove2.me/submissions/8ef179fa-43bc-48a3-8bf6-aea9b7da929c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MatrixMeasurableSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Theorems.Thm_GlobalTheory_SplitWeil_secondCountable
import Theorems.Thm_GlobalTheory_SplitWeil_t2Space
import Theorems.Thm_GlobalTheory_SplitWeil_nabs_mul
import Theorems.Thm_GlobalTheory_SplitWeil_isOpen_cball
import Theorems.Thm_GlobalTheory_SplitWeil_isCompact_cball
import Theorems.Thm_GlobalTheory_SplitWeil_measureReal_cball
import Theorems.Thm_GlobalTheory_SplitWeil_HasConductor_continuous
import Theorems.Thm_GlobalTheory_SplitWeil_exists_cball_invariant
import Theorems.Thm_GlobalTheory_SplitWeil_fourier_eq_zero
import Theorems.Thm_GlobalTheory_SplitWeil_fourier_indicator

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
open scoped NNReal ENNReal Pointwise Topology
noncomputable section
open GlobalTheory GlobalTheory.SplitWeil
variable (k : Type*) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {k}
variable {ψ : AddChar k Circle} {c : kˣ}
variable [MeasurableSpace k] [BorelSpace k] (ν : Measure k) [ν.IsAddHaarMeasure]
namespace GlobalTheory.SplitWeil
theorem _root_.solution (h : HasConductor ψ c) {f : k → ℂ} (hf : f ∈ SB k) :
    ∫ y, (∫ x, f x * (ψ (x * y) : ℂ) ∂ν) ∂ν =
      ((ν.real (𝒪[k] : Set k) ^ 2 * nabs k c : ℝ) : ℂ) * f 0 := by
  haveI := secondCountable k
  haveI := t2Space k
  obtain ⟨s, hs⟩ := exists_cball_invariant hf
  set e : k → ℂ := (cball (c * s⁻¹)).indicator (fun _ => (1 : ℂ)) with he
  have h1 : ∀ y, ∫ x, f x * (ψ (x * y) : ℂ) ∂ν = ∫ x, f x * (e y * (ψ (y * x) : ℂ)) ∂ν := by
    intro y
    by_cases hy : y ∈ cball (c * s⁻¹)
    · simp [he, Set.indicator_of_mem hy, mul_comm y]
    · simp [he, Set.indicator_of_notMem hy, fourier_eq_zero ν h hs hy]
  have hei : Integrable e ν :=
    (integrable_indicator_iff (isOpen_cball _).measurableSet).mpr
      (integrableOn_const (isCompact_cball _).measure_lt_top.ne)
  have hfi : Integrable f ν := hf.1.continuous.integrable_of_hasCompactSupport hf.2
  have hint : Integrable (Function.uncurry fun y x => f x * (e y * (ψ (y * x) : ℂ))) (ν.prod ν) := by
    have h2 := (hei.mul_prod hfi).mul_bdd (c := 1) (g := fun q : k × k => (ψ (q.1 * q.2) : ℂ))
      (Continuous.aestronglyMeasurable
        (continuous_subtype_val.comp (h.continuous.comp (by fun_prop))))
      (Filter.Eventually.of_forall fun q => (Circle.norm_coe _).le)
    refine h2.congr (Filter.Eventually.of_forall fun q => ?_)
    simp only [Function.uncurry]
    ring
  simp only [h1]
  rw [integral_integral_swap hint]
  simp only [integral_const_mul, he, fourier_indicator ν h s]
  have h3 : ∀ x, f x * (cball s).indicator (fun _ => (ν.real (cball (c * s⁻¹)) : ℂ)) x =
      (cball s).indicator (fun _ => (ν.real (cball (c * s⁻¹)) : ℂ) * f 0) x := by
    intro x
    by_cases hx : x ∈ cball s
    · have := hs x hx 0
      rw [zero_add] at this
      rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx, this, mul_comm]
    · simp [Set.indicator_of_notMem hx]
  simp only [h3]
  rw [integral_indicator_const _ (isOpen_cball _).measurableSet, measureReal_cball, measureReal_cball,
    Complex.real_smul, ← mul_assoc, ← Complex.ofReal_mul]
  congr 2
  have h4 : nabs k c = nabs k s * nabs k (c * s⁻¹) := by
    rw [← nabs_mul, mul_comm, inv_mul_cancel_right]
  rw [h4]; ring
end GlobalTheory.SplitWeil
