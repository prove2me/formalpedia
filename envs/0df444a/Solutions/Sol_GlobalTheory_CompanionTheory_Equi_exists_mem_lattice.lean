-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Equi.exists_mem_lattice
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:28:55.050505+00:00
-- url     : https://prove2.me/submissions/f1311b24-b23f-4bec-80ea-bcd8b9cef41a

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CosetOff
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_InfiniteAdeleHaarMapEqScaledVolume
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ArchimedeanFundamentalDomainIntegers

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter GlobalTheory.CompanionTheory.Equi
open scoped Classical
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Equi
open GlobalTheory.CompanionTheory.SW.RealCoord
variable (F : Type) [Field F] [NumberField F] [IsTotallyReal F]
namespace GlobalTheory.CompanionTheory.Equi
theorem _root_.solution {x : mixedEmbedding.mixedSpace F}
    (hx : x ∈ Submodule.span ℤ (Set.range (mixedEmbedding.latticeBasis F))) :
    ∃ a : 𝓞 F, mixedEmbedding F (a : F) = x := by
  rw [mixedEmbedding.mem_span_latticeBasis F] at hx
  obtain ⟨a, rfl⟩ := hx
  exact ⟨a, rfl⟩
end GlobalTheory.CompanionTheory.Equi
