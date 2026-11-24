-- Prove2me | solution 1 for GlobalTheory.JR.selfDual_iff_lattice_volume_and_plancherel
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:13:10.103609+00:00
-- url     : https://prove2.me/submissions/c62a443e-043e-4464-8c87-55b6e5104c5a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_SelfDualMeasureExistsUniqueFourierInversionStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnramifiedStandardAddCharConductorPropertiesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_SelfDualIffLatticeVolumeAndPlancherel
import Theorems.Thm_GlobalTheory_JR_SelfDualLat_isLC_indicator_one
import Theorems.Thm_GlobalTheory_JR_SelfDualLat_topo
import Theorems.Thm_GlobalTheory_JR_SelfDualLat_orth
import Theorems.Thm_GlobalTheory_JR_SelfDualLat_planch
import Theorems.Thm_GlobalTheory_T_selfDual_measure_exists_unique_fourier_inversion


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
open GlobalTheory.JR.SelfDualLat
namespace GlobalTheory.JR
theorem _root_.solution : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (ψ : AddChar F ℂ), IsStdChar ψ → ∀ (V : Type) [AddCommGroup V] [Module F V] [Module.Finite F V] [TopologicalSpace V] [IsModuleTopology F V] [MeasurableSpace V] [BorelSpace V] (β : LinearMap.BilinForm F V), β.IsSymm → β.Nondegenerate → ∀ μ : Measure V, μ.IsAddHaarMeasure → (∀ M : AddSubgroup V, IsOpen (M : Set V) → IsCompact (M : Set V) → (SelfDual μ (fun x y => ψ (β x y)) ↔ μ M * μ {y | ∀ x ∈ M, ψ (β x y) = 1} = 1) ∧ ∀ y, ∫ x in (M : Set V), ψ (β x y) ∂μ = Set.indicator {y | ∀ x ∈ M, ψ (β x y) = 1} (fun _ => ((μ M).toReal : ℂ)) y) ∧ (SelfDual μ (fun x y => ψ (β x y)) → ∀ f, IsTest f → ∫ y, ‖fourB μ (fun x y => ψ (β x y)) f y‖ ^ 2 ∂μ = ∫ x, ‖f x‖ ^ 2 ∂μ) := by
  intro F E _ _ _ _ _ ψ hψ V _ _ _ _ _ _ _ β hβs hβn μ hμ
  obtain ⟨hLC, hSC, hT2, hTG⟩ := topo F E V
  haveI := hLC; haveI := hSC; haveI := hT2; haveI := hTG
  have hI := GlobalTheory.T.selfDual_measure_exists_unique_fourier_inversion F E ψ hψ V β hβs hβn
  have fwd : ∀ ν : Measure V, SelfDual ν (fun x y => ψ (β x y)) → ∀ M : AddSubgroup V, IsOpen (M : Set V) →
      IsCompact (M : Set V) → ν M * ν {y | ∀ x ∈ M, ψ (β x y) = 1} = 1 := by
    intro ν hν M hMo hMc
    haveI := hν.1
    set P : Set V := {y | ∀ x ∈ M, ψ (β x y) = 1} with hP
    set g : V → ℂ := (M : Set V).indicator (fun _ => 1) with hg
    have hMcl : IsClosed (M : Set V) := AddSubgroup.isClosed_of_isOpen M hMo
    have hgt : IsTest g := ⟨isLC_indicator_one _ ⟨hMcl, hMo⟩,
      HasCompactSupport.intro hMc (fun x hx => Set.indicator_of_notMem hx _)⟩
    have h1 : ∀ x, fourB ν (fun x y => ψ (β x y)) g x = P.indicator (fun _ => ((ν M).toReal : ℂ)) x := by
      intro x
      rw [← orth F E ψ hψ V β ν hν.1 M hMo hMc x]
      unfold fourB
      rw [← integral_indicator hMo.measurableSet]
      congr 1; ext t
      by_cases ht : t ∈ (M : Set V) <;> simp [hg, ht]
    have hc : ((ν M).toReal : ℂ) ≠ 0 := by
      have h0 : ν M ≠ 0 := (hMo.measure_pos ν ⟨0, M.zero_mem⟩).ne'
      have ht : ν M ≠ ⊤ := hMc.measure_lt_top.ne
      exact_mod_cast (ENNReal.toReal_pos h0 ht).ne'
    have hft := hI.2 ν hν.1 g hgt
    have hPm : MeasurableSet P := by
      have : P = (fourB ν (fun x y => ψ (β x y)) g) ⁻¹' {((ν M).toReal : ℂ)} := by
        ext y
        show y ∈ P ↔ fourB ν (fun x y => ψ (β x y)) g y = ((ν M).toReal : ℂ)
        rw [h1]
        by_cases hy : y ∈ P
        · simp [Set.indicator_of_mem hy, hy]
        · rw [Set.indicator_of_notMem hy]; exact ⟨fun h => absurd h hy, fun h => absurd h.symm hc⟩
      rw [this]; exact (hft.1.isOpen_fiber _).measurableSet
    have h2 := hν.2 g hgt 0
    rw [neg_zero, show g 0 = 1 by simp [hg, M.zero_mem]] at h2
    have h3 : fourB ν (fun x y => ψ (β x y)) (fourB ν (fun x y => ψ (β x y)) g) 0 =
        (ν P).toReal * (ν M).toReal := by
      show ∫ x, fourB ν (fun x y => ψ (β x y)) g x * ψ (β x 0) ∂ν = _
      simp_rw [h1, map_zero, AddChar.map_zero_eq_one, mul_one]
      rw [integral_indicator_const _ hPm]
      simp [Measure.real]
    rw [h3] at h2
    rw [← ENNReal.toReal_eq_one_iff, ENNReal.toReal_mul]
    have h4 : (((ν M).toReal * (ν P).toReal : ℝ) : ℂ) = 1 := by push_cast; linear_combination h2
    exact_mod_cast h4
  refine ⟨fun M hMo hMc => ⟨⟨fun hsd => fwd μ hsd M hMo hMc, fun h => ?_⟩, orth F E ψ hψ V β μ hμ M hMo hMc⟩,
    fun hsd f hf => planch F E ψ hψ V β hβs hβn μ hsd f hf⟩
  obtain ⟨⟨μ0, hμ0, -⟩, -⟩ := hI
  haveI := hμ0.1
  have hsc : μ = Measure.addHaarScalarFactor μ μ0 • μ0 := Measure.isAddLeftInvariant_eq_smul μ μ0
  set c := Measure.addHaarScalarFactor μ μ0 with hcdef
  have h0 := fwd μ0 hμ0 M hMo hMc
  rw [hsc] at h
  simp only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at h
  have hcc : ((c * c : NNReal) : ENNReal) = 1 := by
    calc ((c * c : NNReal) : ENNReal) = (c : ENNReal) * c * (μ0 M * μ0 {y | ∀ x ∈ M, ψ (β x y) = 1}) := by
          rw [h0, mul_one, ENNReal.coe_mul]
      _ = (c : ENNReal) * μ0 M * ((c : ENNReal) * μ0 {y | ∀ x ∈ M, ψ (β x y) = 1}) := by ring
      _ = 1 := h
  have hcc' : (c : ℝ) * c = 1 := by exact_mod_cast (ENNReal.coe_eq_one.1 hcc)
  have hc1 : c = 1 := by
    have : (c : ℝ) = 1 := by nlinarith [c.2]
    exact_mod_cast this
  have : μ = μ0 := by rw [hsc, hc1, one_smul]
  rw [this]; exact hμ0
end GlobalTheory.JR
