-- Prove2me | solution 1 for GlobalTheory.contDensityOn_eq_fibre_mass
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:46:57.141403+00:00
-- url     : https://prove2.me/submissions/9c7bf7f5-14e1-4a65-8f00-313660534d6c

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_GenusMassVolumes
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ContDensityOnEqFibreMass
import Theorems.Thm_GlobalTheory_eq_zero_of_setIntegral_compact_eq_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : ∀ (K V : Type) [NormedField K] [ProperSpace K] [MeasurableSpace K] [BorelSpace K] [TopologicalSpace V] [T2Space V] [MeasurableSpace V] [BorelSpace V] (μ : Measure V) (ν : Measure K) [ν.IsAddHaarMeasure] (q : V → K), Continuous q → ∀ (fib : K → Measure V), IsFibreFamily μ q id Set.univ ν {t | t ≠ 0} fib → ∀ (L : Set V), IsCompact L → IsOpen L → ∀ g : K → ℂ, IsContDensityOn μ q id ν {t | t ≠ 0} (L.indicator 1) g → ∀ t : K, t ≠ 0 → g t = (((fib t L).toReal : ℝ) : ℂ) := by
  intro K V _ _ _ _ _ _ _ _ μ ν _ q hq fib hfib L hLc hLo g hg t ht
  obtain ⟨hf1, hf2, hf3⟩ := hfib
  obtain ⟨hgc, hgS⟩ := hg
  have hLm : MeasurableSet L := hLo.measurableSet
  have hBo : IsOpen {t : K | t ≠ 0} := isOpen_ne
  have hφc : Continuous (L.indicator (1 : V → ℝ)) :=
    IsClopen.continuous_indicator ⟨hLc.isClosed, hLo⟩ continuous_const
  have hφs : HasCompactSupport (L.indicator (1 : V → ℝ)) :=
    HasCompactSupport.intro hLc (fun x hx => Set.indicator_of_notMem hx _)
  obtain ⟨hint, hcont⟩ := hf3 _ hφc hφs (Set.subset_univ _)
  have hm_eq : (fun b => ∫ v, L.indicator (1 : V → ℝ) v ∂(fib b)) = fun b => (fib b L).toReal := by
    funext b; rw [integral_indicator_one hLm]; rfl
  have hmc : ContinuousOn (fun b => (fib b L).toReal) {t : K | t ≠ 0} := by
    rw [← hm_eq]; exact hcont
  have hfin : ∀ b ∈ {t : K | t ≠ 0}, fib b L < ⊤ := by
    intro b hb
    have hi := hint b hb
    rw [integrable_indicator_iff hLm] at hi
    exact ((integrableOn_const_iff (C := (1 : ℝ))).1 hi).resolve_left (by simp)
  have hmcC : ContinuousOn (fun b => (((fib b L).toReal : ℝ) : ℂ)) {t : K | t ≠ 0} :=
    Complex.continuous_ofReal.comp_continuousOn hmc
  have key : ∀ S : Set K, IsCompact S → S ⊆ {t : K | t ≠ 0} →
      ∫ b in S, (g b - (((fib b L).toReal : ℝ) : ℂ)) ∂ν = 0 := by
    intro S hS hSB
    have hSm : MeasurableSet S := hS.measurableSet
    rw [integral_sub ((hgc.mono hSB).integrableOn_compact hS)
      ((hmcC.mono hSB).integrableOn_compact hS), sub_eq_zero, ← hgS S hS hSB, Set.image_id]
    have hind : L.indicator (1 : V → ℂ) = L.indicator (fun _ => (1 : ℂ)) := rfl
    rw [hind, integral_indicator_const _ hLm, integral_complex_ofReal, Complex.real_smul, mul_one]
    congr 1
    have haem : AEMeasurable (fun b => fib b L) (ν.restrict S) :=
      ((hmc.mono hSB).aemeasurable hSm).ennreal_ofReal.congr
        ((ae_restrict_mem hSm).mono fun b hb => ENNReal.ofReal_toReal (hfin b (hSB hb)).ne)
    rw [integral_toReal haem ((ae_restrict_mem hSm).mono fun b hb => hfin b (hSB hb)),
      measureReal_def, Measure.restrict_apply hLm]
    congr 1
    have hTm : MeasurableSet (L ∩ q ⁻¹' S) := hLm.inter (hq.measurable hSm)
    have h2 := hf2 ((L ∩ q ⁻¹' S).indicator 1) (measurable_one.indicator hTm)
    rw [Measure.restrict_univ, lintegral_indicator_one hTm] at h2
    rw [h2, ← lintegral_indicator hSm]
    refine lintegral_congr fun b => ?_
    rw [lintegral_indicator_one hTm]
    by_cases hb : b ∈ S
    · rw [Set.indicator_of_mem hb]
      refine measure_inter_conull (measure_mono_null (Set.compl_subset_compl.2 ?_) (hf1 b))
      intro v hv
      simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff, id] at hv
      simp only [Set.mem_preimage, hv.1, hb]
    · rw [Set.indicator_of_notMem hb]
      refine measure_mono_null (fun v hv => ?_) (hf1 b)
      simp only [Set.mem_compl_iff, Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff,
        id, Set.mem_univ, and_true]
      intro hqv
      exact hb (hqv ▸ hv.2)
  exact sub_eq_zero.1 (eq_zero_of_setIntegral_compact_eq_zero ν hBo (hgc.sub hmcC) key
    (show t ∈ {t : K | t ≠ 0} from ht))
end GlobalTheory
