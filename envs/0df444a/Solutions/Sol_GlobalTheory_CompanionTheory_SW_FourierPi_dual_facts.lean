-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.FourierPi.dual_facts
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T13:15:12.355806+00:00
-- url     : https://prove2.me/submissions/fb6a6ca3-ec0b-4df8-aed6-2b59fd694b4b

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_HarrisTaylorCardKilledByIdealEqAbsNormPow
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_FourierPi_integral_subgroup_eq_zero
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_FourierPi_integral_subgroup_eq_real

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.FourierPi
variable {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
  [LocallyCompactSpace R] [SecondCountableTopology R] [T2Space R] [MeasurableSpace R] [BorelSpace R]
  {ψ : R → ℂ}
namespace GlobalTheory.CompanionTheory.SW.FourierPi
theorem _root_.solution (hc : Continuous ψ) (ha : ∀ x y, ψ (x + y) = ψ x * ψ y) (hn : ∀ x, ‖ψ x‖ = 1)
    (lam : Measure R) (hsd : SelfDual lam (fun s t => ψ (s * t))) (L : AddSubgroup R)
    (hLc : IsCompact (L : Set R)) (hLo : IsOpen (L : Set R))
    (hP : IsCompact (ann ha hn L : Set R)) :
    lam.real (L : Set R) * lam.real (ann ha hn L : Set R) = 1 ∧
      (∀ z, z ∈ ann ha hn (ann ha hn L) → z ∈ L) ∧ IsOpen (ann ha hn L : Set R) := by
  classical
  haveI := hsd.1
  set P := ann ha hn L with hPdef
  have hLm : MeasurableSet (L : Set R) := hLo.measurableSet
  have hPm : MeasurableSet (P : Set R) := hP.isClosed.measurableSet
  set Φ : R → ℂ := (L : Set R).indicator 1 with hΦ
  have hcl : IsClopen (L : Set R) := ⟨AddSubgroup.isClosed_of_isOpen _ hLo, hLo⟩
  have Φc : Continuous Φ :=
    continuous_indicator (by simp [hcl.frontier_eq]) continuous_one.continuousOn
  have Φs : HasCompactSupport Φ := by
    refine HasCompactSupport.intro hLc fun x hx => ?_
    simp [hΦ, hx]
  have hat : ∀ y, ∫ x, Φ x * ψ (x * y) ∂lam = (P : Set R).indicator (fun _ => (lam.real (L : Set R) : ℂ)) y := by
    intro y
    have e : (fun x => Φ x * ψ (x * y)) = (L : Set R).indicator fun x => ψ (x * y) := by
      funext x
      by_cases hx : x ∈ (L : Set R) <;> simp [hΦ, hx]
    rw [e, integral_indicator hLm]
    by_cases hy : y ∈ P
    · rw [Set.indicator_of_mem (SetLike.mem_coe.2 hy)]
      exact integral_subgroup_eq_real lam _ hLm y hy
    · rw [Set.indicator_of_notMem (show y ∉ (P : Set R) from hy)]
      have : ∃ a ∈ L, ψ (a * y) ≠ 1 := by
        by_contra hcon
        push_neg at hcon
        exact hy hcon
      obtain ⟨a, haL, hne⟩ := this
      exact integral_subgroup_eq_zero lam L hLm ha y a haL hne
  have hint : Integrable (fun y => ∫ x, Φ x * ψ (x * y) ∂lam) lam := by
    simp only [hat]
    exact (integrable_indicator_iff hPm).2 (integrableOn_const hP.measure_lt_top.ne)
  have inv := hsd.2 Φ Φc Φs hint
  have inv' : ∀ z, (lam.real (L : Set R) : ℂ) * ∫ y in (P : Set R), ψ (y * z) ∂lam = Φ (-z) := by
    intro z
    rw [← inv z, ← integral_const_mul, ← integral_indicator hPm]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    by_cases hy : y ∈ (P : Set R) <;> simp [hat, hy]
  have hone : (lam.real (L : Set R) : ℂ) * (lam.real (P : Set R) : ℂ) = 1 := by
    have h0 := inv' 0
    rw [integral_subgroup_eq_real lam _ hPm 0 (by simp [psi_zero ha hn])] at h0
    rw [h0]
    simp [hΦ, L.zero_mem]
  have hone' : lam.real (L : Set R) * lam.real (P : Set R) = 1 := by exact_mod_cast hone
  refine ⟨hone', ?_, ?_⟩
  · intro z hz
    have h1 := inv' z
    rw [integral_subgroup_eq_real lam _ hPm z (fun x hx => hz x hx), hone] at h1
    by_contra hzL
    have : -z ∉ (L : Set R) := fun h => hzL (by simpa using L.neg_mem h)
    simp [hΦ, this] at h1
  · have hpos : lam (P : Set R) ≠ 0 := by
      intro h0
      have : lam.real (P : Set R) = 0 := by simp [Measure.real, h0]
      simp [this] at hone'
    have hn0 := MeasureTheory.Measure.sub_mem_nhds_zero_of_addHaar_pos lam (P : Set R) hPm (pos_iff_ne_zero.2 hpos)
    refine AddSubgroup.isOpen_of_mem_nhds P (g := 0) ?_
    refine Filter.mem_of_superset hn0 ?_
    rintro _ ⟨a, ha', b, hb', rfl⟩
    exact P.sub_mem ha' hb'
end GlobalTheory.CompanionTheory.SW.FourierPi
