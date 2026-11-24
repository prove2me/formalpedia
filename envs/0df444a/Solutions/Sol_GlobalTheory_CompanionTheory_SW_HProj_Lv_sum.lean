-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.HProj.Lv_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T13:22:37.847961+00:00
-- url     : https://prove2.me/submissions/d4059686-09da-4b43-b733-b587d22c00a3

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_AdelicTupleProjectionsStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_AdelicUnitaryGroupProjections
import Theorems.Thm_GroundTheory_Global_residueFieldEquiv_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Global.residueFieldEquiv_mk



set_option autoImplicit false
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.HProj
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {d : ℕ}
namespace GlobalTheory.CompanionTheory.SW.HProj
theorem _root_.solution (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) {ι : Type} (s : Finset ι)
    (f : ι → Fv F v ⊗[F] E) (hf : ∀ i ∈ s, f i ∈ Lv b v) : ∑ i ∈ s, f i ∈ Lv b v := by
  intro k
  simp only [map_sum, Finsupp.coe_finset_sum, Finset.sum_apply]
  exact sum_mem fun i hi => hf i hi k
end GlobalTheory.CompanionTheory.SW.HProj
