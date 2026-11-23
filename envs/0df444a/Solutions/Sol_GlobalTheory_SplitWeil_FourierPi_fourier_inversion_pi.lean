-- Prove2me | solution 1 for GlobalTheory.SplitWeil.FourierPi.fourier_inversion_pi
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:04:50.965241+00:00
-- url     : https://prove2.me/submissions/cfa2634c-d1ef-408e-b532-126852ca7d20

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_AddCharConductorAndHaarIntegersExist
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_FourierTransformInversionLocalFieldPi
import Theorems.Thm_GlobalTheory_SplitWeil_FourierPi_isOpen_box
import Theorems.Thm_GlobalTheory_SplitWeil_FourierPi_isCompact_box
import Theorems.Thm_GlobalTheory_SplitWeil_FourierPi_exists_box_invariant
import Theorems.Thm_GlobalTheory_SplitWeil_FourierPi_continuous_dot
import Theorems.Thm_GlobalTheory_SplitWeil_FourierPi_fourier_eq_zero_pi
import Theorems.Thm_GlobalTheory_SplitWeil_FourierPi_fourier_indicator_pi
import Theorems.Thm_GlobalTheory_SplitWeil_HasConductor_continuous
import Theorems.Thm_GlobalTheory_SplitWeil_secondCountable
import Theorems.Thm_GlobalTheory_SplitWeil_t2Space


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
open scoped Topology
noncomputable section
open GlobalTheory GlobalTheory.SplitWeil GlobalTheory.SplitWeil.FourierPi
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {n : Type*} [Fintype n] [DecidableEq n]
variable {ψ : AddChar k Circle} {c : kˣ}
variable [MeasurableSpace k] [BorelSpace k]
namespace GlobalTheory.SplitWeil.FourierPi
theorem _root_.solution (μ : Measure (n → k)) [μ.IsAddHaarMeasure] (h : HasConductor ψ c)
    {f : (n → k) → ℂ} (hf : f ∈ SB (n → k)) :
    ∃ s : kˣ, ∫ y, (∫ x, f x * (ψ (x ⬝ᵥ y) : ℂ) ∂μ) ∂μ =
      ((μ.real (box n s) * μ.real (box n (c * s⁻¹)) : ℝ) : ℂ) * f 0 := by
  haveI := secondCountable k
  haveI := t2Space k
  obtain ⟨s, hs⟩ := exists_box_invariant hf
  refine ⟨s, ?_⟩
  set e : (n → k) → ℂ := (box n (c * s⁻¹)).indicator (fun _ => (1 : ℂ)) with he
  have h1 : ∀ y, ∫ x, f x * (ψ (x ⬝ᵥ y) : ℂ) ∂μ = ∫ x, f x * (e y * (ψ (y ⬝ᵥ x) : ℂ)) ∂μ := by
    intro y
    by_cases hy : y ∈ box n (c * s⁻¹)
    · simp [he, Set.indicator_of_mem hy, dotProduct_comm y]
    · simp [he, Set.indicator_of_notMem hy, fourier_eq_zero_pi μ h hs hy]
  have hei : Integrable e μ :=
    (integrable_indicator_iff (isOpen_box _).measurableSet).mpr
      (integrableOn_const (isCompact_box _).measure_lt_top.ne)
  have hfi : Integrable f μ := hf.1.continuous.integrable_of_hasCompactSupport hf.2
  have hint : Integrable (Function.uncurry fun y x => f x * (e y * (ψ (y ⬝ᵥ x) : ℂ))) (μ.prod μ) := by
    have h2 := (hei.mul_prod hfi).mul_bdd (c := 1) (g := fun q : (n → k) × (n → k) => (ψ (q.1 ⬝ᵥ q.2) : ℂ))
      (Continuous.aestronglyMeasurable
        (continuous_subtype_val.comp (h.continuous.comp continuous_dot)))
      (Filter.Eventually.of_forall fun q => (Circle.norm_coe _).le)
    refine h2.congr (Filter.Eventually.of_forall fun q => ?_)
    simp only [Function.uncurry]
    ring
  simp only [h1]
  rw [integral_integral_swap hint]
  simp only [integral_const_mul, he, fourier_indicator_pi μ h s]
  have h3 : ∀ x, f x * (box n s).indicator (fun _ => (μ.real (box n (c * s⁻¹)) : ℂ)) x =
      (box n s).indicator (fun _ => (μ.real (box n (c * s⁻¹)) : ℂ) * f 0) x := by
    intro x
    by_cases hx : x ∈ box n s
    · have := hs x hx 0
      rw [zero_add] at this
      rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx, this, mul_comm]
    · simp [Set.indicator_of_notMem hx]
  simp only [h3]
  rw [integral_indicator_const _ (isOpen_box _).measurableSet, Complex.real_smul, ← mul_assoc,
    ← Complex.ofReal_mul]
end GlobalTheory.SplitWeil.FourierPi
