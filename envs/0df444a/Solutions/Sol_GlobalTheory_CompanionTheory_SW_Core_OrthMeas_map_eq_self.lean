-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.Core.OrthMeas.map_eq_self
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T13:30:46.213532+00:00
-- url     : https://prove2.me/submissions/913ab811-cfcd-4f3a-a84b-0de621c38566

import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_CountData
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_WeilOrthogonalGroupInvariance
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_Core_OrthMeas_perp_image

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.Core GlobalTheory.CompanionTheory.SW.Core.OrthMeas
namespace GlobalTheory.CompanionTheory.SW.Core.OrthMeas
theorem _root_.solution {V : Type} [AddCommGroup V] [TopologicalSpace V] [MeasurableSpace V]
    (χ : V → V → ℂ) (μ : Measure V) (hD : NADual V χ μ) (e : V ≃+ V) (he : Continuous e)
    (hes : Continuous e.symm) (hχ : ∀ x y, χ (e x) (e y) = χ x y) :
    Measure.map e μ = μ := by
  obtain ⟨hTG, hT2, hLC, hSC, hBS, hHaar, -, hEx, -, -, -, -, hPerp⟩ := hD
  haveI := hTG
  haveI := hT2
  haveI := hLC
  haveI := hSC
  haveI := hBS
  haveI := hHaar
  haveI : (μ.map e).IsAddHaarMeasure := e.isAddHaarMeasure_map μ he hes
  obtain ⟨c, hc⟩ : ∃ c : ℝ≥0, μ.map e = c • μ :=
    ⟨_, Measure.isAddLeftInvariant_eq_smul (μ.map e) μ⟩
  let t : V ≃ₜ V := { toEquiv := e.toEquiv, continuous_toFun := he, continuous_invFun := hes }
  have key : ∀ A : Set V, IsOpen A → μ A = c * μ (e '' A) := by
    intro A hA
    have hm : MeasurableSet (e '' A) := (t.isOpenMap A hA).measurableSet
    have h1 : (μ.map e) (e '' A) = (c • μ) (e '' A) := by rw [hc]
    rw [Measure.map_apply he.measurable hm, Set.preimage_image_eq _ e.injective,
      Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at h1
    exact h1
  obtain ⟨L, hLc, hLo, -⟩ := hEx 0
  have hset : ((L.map e.toAddMonoidHom : AddSubgroup V) : Set V) = e '' (L : Set V) := by
    ext x; simp
  have hL'c : IsCompact ((L.map e.toAddMonoidHom : AddSubgroup V) : Set V) := by
    rw [hset]; exact hLc.image he
  have hL'o : IsOpen ((L.map e.toAddMonoidHom : AddSubgroup V) : Set V) := by
    rw [hset]; exact t.isOpenMap _ hLo
  obtain ⟨-, hPo, -, hP⟩ := hPerp L hLc hLo
  obtain ⟨-, -, -, hP'⟩ := hPerp _ hL'c hL'o
  rw [hset, show perp χ (e '' (L : Set V)) = e '' perp χ (L : Set V) from
    perp_image χ e.toEquiv hχ _] at hP'
  have hcc : ((c : ℝ≥0∞)) * c = 1 := by
    rw [key _ hLo, key _ hPo] at hP
    calc ((c : ℝ≥0∞)) * c = (c : ℝ≥0∞) * c * (μ (e '' (L : Set V)) * μ (e '' perp χ (L : Set V))) := by
          rw [hP', mul_one]
      _ = 1 := by rw [← hP]; ring
  have hc1 : c = 1 := by
    have h2 : c * c = 1 := by exact_mod_cast hcc
    have h3 : c ^ 2 = 1 := by rw [sq]; exact h2
    exact (pow_eq_one_iff.1 h3).resolve_right two_ne_zero
  rw [hc, hc1, one_smul]
end GlobalTheory.CompanionTheory.SW.Core.OrthMeas
