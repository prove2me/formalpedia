-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Plucker.cGL_k
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:19:07.44342+00:00
-- url     : https://prove2.me/submissions/66b3317b-3fda-48cc-a8c0-ae06644cdc89

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_ConvGrOf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_MulConjTransposeEqOneOfOrthonormal
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ConvergenceGroupOfBlockDet
import Theorems.Thm_GlobalTheory_CompanionTheory_Plucker_cmp_map
import Theorems.Thm_GlobalTheory_CompanionTheory_Plucker_cmp_conjTranspose
import Theorems.Thm_GlobalTheory_CompanionTheory_Plucker_cmp_mem
import Theorems.Thm_GlobalTheory_CompanionTheory_Plucker_cGL_coe
import Theorems.Thm_GlobalTheory_CompanionTheory_Plucker_cGL_inv_coe
import Theorems.Thm_GlobalTheory_CompanionTheory_Plucker_mem_kGL

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
theorem _root_.solution (A : Ad E R) {k : GL ι R} (hk : k ∈ A.kGL ι) : cGL m k ∈ A.kGL (Sub ι m) := by
  rw [mem_kGL] at hk ⊢
  refine ⟨fun r c => ⟨cmp_mem A.O _ (fun a b => (hk.1 a b).1) r c, ?_⟩, fun w => ?_⟩
  · rw [cGL_inv_coe]
    exact cmp_mem A.O _ (fun a b => (hk.1 a b).2) r c
  · have hU := hk.2 w
    rw [Matrix.mem_unitaryGroup_iff'] at hU ⊢
    rw [cGL_coe, ← cmp_map, star_eq_conjTranspose, ← cmp_conjTranspose, ← cmp_mul, ← star_eq_conjTranspose, hU, cmp_one]
end GlobalTheory.CompanionTheory.Plucker
