-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.QLHaarAdd.eq_addHaar
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T13:14:06.252369+00:00
-- url     : https://prove2.me/submissions/04f4ebdd-ee9d-4e23-9fe5-f3e582235fe4

import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_InstBorelGL
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_LocalFieldTopologyNormBallsStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_MatrixAdditiveHaarNormalized
import Theorems.Thm_GlobalTheory_CompanionTheory_QLHaarAdd_finite_on_compacts

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix GlobalTheory.CompanionTheory.QL
open scoped ComplexConjugate ValuativeRel
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.QLHaarAdd
namespace GlobalTheory.CompanionTheory.QLHaarAdd
theorem _root_.solution {G : Type} [AddGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (K₀ : TopologicalSpace.PositiveCompacts G) (hKo : IsOpen (K₀ : Set G)) (h0 : (0 : G) ∈ (K₀ : Set G))
    (dx : Measure G) [dx.IsAddLeftInvariant] (h1 : dx (K₀ : Set G) = 1) :
    dx = Measure.addHaarMeasure K₀ := by
  haveI := finite_on_compacts hKo h0 dx h1
  obtain ⟨c, h⟩ : ∃ c : NNReal, dx = c • Measure.addHaarMeasure K₀ :=
    ⟨_, Measure.isAddLeftInvariant_eq_smul dx (Measure.addHaarMeasure K₀)⟩
  have h2 : (c • Measure.addHaarMeasure K₀) (K₀ : Set G) = 1 := by rw [← h]; exact h1
  have hc : c = 1 := by
    rw [Measure.smul_apply, Measure.addHaarMeasure_self, ENNReal.smul_def, smul_eq_mul, mul_one] at h2
    exact_mod_cast h2
  rw [hc, one_smul] at h
  exact h
end GlobalTheory.CompanionTheory.QLHaarAdd
