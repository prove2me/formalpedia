-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.PureH.consTup_mem_latV
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T13:30:47.331105+00:00
-- url     : https://prove2.me/submissions/ea01a932-dade-4a5a-a99d-b590e10136f8

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_BlockOneDetHermitianGram
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_AdelicUnitaryGroupProjections
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_LatticeStableAlmostEverywhere
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_AdelicUnitaryFiniteSetDecomposition
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PureH
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
namespace GlobalTheory.CompanionTheory.SW.PureH
theorem _root_.solution {d : ℕ} (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) {M n : ℕ}
    (h0 : ∀ X₀ : Fin 0 → Fin M → Fv F v ⊗[F] E, consTup X₀ ∈ latV b v)
    (X : Fin n → Fin M → Fv F v ⊗[F] E) : consTup X ∈ latV b v ↔ X ∈ latV b v := by
  constructor
  · intro h a i k
    simpa [consTup] using h a.succ i.succ k
  · intro h a i k
    induction a using Fin.cases with
    | zero => simpa [consTup] using h0 (fun a => a.elim0) 0 i k
    | succ a =>
      induction i using Fin.cases with
      | zero => simp [consTup, zero_mem]
      | succ i => simpa [consTup] using h a i k
end GlobalTheory.CompanionTheory.SW.PureH
