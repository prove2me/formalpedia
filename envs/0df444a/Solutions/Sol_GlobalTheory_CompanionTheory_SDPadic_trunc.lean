-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SDPadic.trunc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T13:09:41.606124+00:00
-- url     : https://prove2.me/submissions/ea5f8875-0fe0-4307-8814-4b2b2fbe6886

import Mathlib
import Definitions.Def_Formalism_UnipotentAdelicQuotients_SWXSDefs
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsSelfDualOfDualSubgroups
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_HermitianForms_IndicatorInSchrodingerSpan
import Theorems.Thm_GlobalTheory_JR_AbsInv_integral_eq_zero_of_translate


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory HeckeCharacterZeroLocus.SiegelWeilU Filter Topology
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SDPadic
variable {V : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]
  [MeasurableSpace V] [BorelSpace V] [T2Space V] [LocallyCompactSpace V] [SecondCountableTopology V]
namespace GlobalTheory.CompanionTheory.SDPadic
theorem _root_.solution (μ : Measure V) [μ.IsAddHaarMeasure] (B : V → V → ℂ)
    (hB : Continuous (fun p : V × V => B p.1 p.2)) (hs : ∀ x y, B x y = B y x)
    (ha : ∀ x x' y, B (x + x') y = B x y * B x' y) (M N : AddSubgroup V)
    (hMo : IsOpen (M : Set V)) (hNo : IsOpen (N : Set V)) (hNc : IsCompact (N : Set V))
    (hM : ∀ x, x ∈ M ↔ ∀ y ∈ N, B x y = 1)
    (f : V → ℂ) (hf : Continuous f) (hfc : HasCompactSupport f) (z : V) :
    ∫ y in (N : Set V), (∫ x, f x * B x y ∂μ) * B y z ∂μ
      = ∫ u in (M : Set V), (μ.real N : ℂ) * f (u - z) ∂μ := by
  classical
  have ha' : ∀ w y y', B w (y + y') = B w y * B w y' := fun w y y' => by rw [hs, ha, hs y, hs y']
  set χ : V → ℂ := (N : Set V).indicator (fun _ => 1) with hχ
  have hχc : Continuous χ := (IsClopen.continuous_indicator ⟨hNc.isClosed, hNo⟩ continuous_const)
  have h1 : ∀ y, (N : Set V).indicator (fun y => (∫ x, f x * B x y ∂μ) * B y z) y
      = ∫ x, f x * (χ y * B (x + z) y) ∂μ := by
    intro y
    by_cases hy : y ∈ N
    · rw [Set.indicator_of_mem (by exact hy)]
      simp only [hχ, ← integral_mul_const]
      congr 1; ext x
      rw [Set.indicator_of_mem (by exact hy), ha, hs y]; ring
    · simp [hχ, hy]
  have h2 : ∀ x, ∫ y, f x * (χ y * B (x + z) y) ∂μ =
      (M : Set V).indicator (fun u => (μ.real N : ℂ) * f (u - z)) (x + z) := by
    intro x
    by_cases hx : x + z ∈ M
    · rw [Set.indicator_of_mem (by exact hx), integral_const_mul]
      have e1 : (fun y => χ y * B (x + z) y) = χ := by
        ext y
        by_cases hy : y ∈ N
        · rw [(hM _).1 hx y hy, mul_one]
        · simp [hχ, hy]
      rw [e1, hχ, integral_indicator_const _ hNo.measurableSet]
      simp [mul_comm]
    · rw [Set.indicator_of_notMem (by exact hx)]
      have hx' := hx
      rw [hM] at hx'
      push Not at hx'
      obtain ⟨n, hn, hn1⟩ := hx'
      refine GlobalTheory.JR.AbsInv.integral_eq_zero_of_translate μ _ n _ hn1 fun y => ?_
      have : χ (y + n) = χ y := by
        by_cases hy : y ∈ N
        · simp [hχ, hy, N.add_mem hy hn]
        · have : y + n ∉ N := fun h => hy (by simpa using N.sub_mem h hn)
          simp [hχ, hy, this]
      rw [this, ha']; ring
  have hsw : ∫ y, ∫ x, f x * (χ y * B (x + z) y) ∂μ ∂μ = ∫ x, ∫ y, f x * (χ y * B (x + z) y) ∂μ ∂μ := by
    refine integral_integral_swap (Continuous.integrable_of_hasCompactSupport ?_ ?_)
    · have : Continuous fun p : V × V => B (p.2 + z) p.1 :=
        hB.comp (f := fun p : V × V => (p.2 + z, p.1)) (by fun_prop)
      exact (hf.comp continuous_snd).mul ((hχc.comp continuous_fst).mul this)
    · refine HasCompactSupport.intro (hNc.prod hfc) ?_
      rintro ⟨y, x⟩ h
      simp only [Set.mem_prod, not_and_or] at h
      rcases h with h | h
      · simp [Function.uncurry, hχ, Set.indicator_of_notMem h]
      · simp [Function.uncurry, image_eq_zero_of_notMem_tsupport h]
  rw [← integral_indicator hNo.measurableSet, ← integral_indicator hMo.measurableSet]
  simp_rw [h1]
  rw [hsw]
  simp_rw [h2]
  exact integral_add_right_eq_self (μ := μ) ((M : Set V).indicator (fun u => (μ.real N : ℂ) * f (u - z))) z
end GlobalTheory.CompanionTheory.SDPadic
