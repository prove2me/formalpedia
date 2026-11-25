-- Prove2me | solution 1 for GlobalTheory.cubeComplex_exactAt_succ_iff_faces
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T02:46:10.821515+00:00
-- url     : https://prove2.me/submissions/3cfa162b-b129-45e2-851f-1c42b12a447f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsIsoTermComparisonRestrictScalars
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_CubeComplexAcyclicIffQuasiIsoCechAug
import Theorems.Thm_P2M_GlobalTheory_mono_cubeFaceSequence___iff_45ee17f4c004
import Theorems.Thm_P2M_GlobalTheory_epi_cubeFaceSequence___iff_dcaa57b52eff

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
variable {ι κ : Type} [LinearOrder ι] [LinearOrder κ] {R : Type u} [Ring R]
  {e : κ ↪o ι} {i : ι} (he : Set.range e = {i}ᶜ)
include he
namespace GlobalTheory
theorem _root_.solution (A : Cube.{v} ι R) (p : ℕ) :
    (cubeComplex A).ExactAt (p + 1) ↔
      Epi (homologyMap (cubeComplexMap (Cube.faceMap e i A)) p) ∧
        Mono (homologyMap (cubeComplexMap (Cube.faceMap e i A)) (p + 1)) := by
  have hS := cubeFaceSequence_shortExact he A
  rw [← mono_cubeFaceSequence_δ_iff he, ← epi_cubeFaceSequence_δ_iff he,
    exactAt_iff_isZero_homology, (hS.homology_exact₃ (p + 1) (p + 1 + 1) rfl).mono_g_iff,
    (hS.homology_exact₁ p (p + 1) rfl).epi_f_iff]
  exact (hS.homology_exact₂ (p + 1)).isZero_X₂_iff
end GlobalTheory
