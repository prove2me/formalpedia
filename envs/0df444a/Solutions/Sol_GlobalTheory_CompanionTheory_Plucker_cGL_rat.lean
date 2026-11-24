-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Plucker.cGL_rat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:18:09.139842+00:00
-- url     : https://prove2.me/submissions/3f6ab591-a102-44b6-95d7-529f40f14772

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_ConvGrOf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_MulConjTransposeEqOneOfOrthonormal
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ConvergenceGroupOfBlockDet
import Theorems.Thm_GlobalTheory_CompanionTheory_Plucker_cmp_map
import Theorems.Thm_GlobalTheory_CompanionTheory_Plucker_cGL_coe
import Theorems.Thm_GlobalTheory_CompanionTheory_Plucker_map_coe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Plucker
open PositivityTheory.RgEis
variable {E R : Type} [Field E] [CommRing R] {ι : Type} [Fintype ι] [DecidableEq ι] {m : Type} [Fintype m] [DecidableEq m]
namespace GlobalTheory.CompanionTheory.Plucker
theorem _root_.solution (A : Ad E R) {γ : GL ι R} (hγ : γ ∈ A.ratGL ι) : cGL m γ ∈ A.ratGL (Sub ι m) := by
  obtain ⟨δ, rfl⟩ := hγ
  refine ⟨cGL m δ, Units.ext ?_⟩
  rw [map_coe, cGL_coe, cGL_coe, map_coe, cmp_map]
end GlobalTheory.CompanionTheory.Plucker
