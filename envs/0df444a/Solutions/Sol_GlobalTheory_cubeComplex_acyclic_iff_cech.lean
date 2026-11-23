-- Prove2me | solution 1 for GlobalTheory.cubeComplex_acyclic_iff_cech
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:08:11.322834+00:00
-- url     : https://prove2.me/submissions/e75b8ab7-cf48-4137-bcec-5032ef56e6ca

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsIsoTermComparisonRestrictScalars
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_CubeComplexAcyclicIffQuasiIsoCechAug
import Theorems.Thm_GlobalTheory_isIso_cechAugHomology_iff
import Theorems.Thm_GlobalTheory_cechComplex_exactAt_succ_iff_cube


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits HomologicalComplex
universe v u
open GlobalTheory
variable {ι : Type} [LinearOrder ι] {R : Type u} [Ring R]
namespace GlobalTheory
theorem _root_.solution (A : Cube.{v} ι R) :
    (cubeComplex A).Acyclic ↔
      IsIso (cechAugHomology A) ∧ ∀ p, IsZero ((cechComplex A).homology (p + 1)) := by
  simp only [isIso_cechAugHomology_iff, ← exactAt_iff_isZero_homology,
    cechComplex_exactAt_succ_iff_cube]
  refine ⟨fun h => ⟨⟨h _, h _⟩, fun _ => h _⟩, fun h p => ?_⟩
  match p with
  | 0 => exact h.1.1
  | 1 => exact h.1.2
  | p + 2 => exact h.2 p
end GlobalTheory
