-- Prove2me | solution 1 for GlobalTheory.LatOrbGL.matLat_le_of_entries
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T18:37:36.374109+00:00
-- url     : https://prove2.me/submissions/4c24bb9e-d3fb-4e90-bfb9-298271940287

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemMatLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemGLintIffMatrixImageStandardLatticeEq
import Theorems.Thm_GlobalTheory_LatOrbGL_mem_range_iff
import Theorems.Thm_GlobalTheory_LatOrb_mem_matLat
import Theorems.Thm_GlobalTheory_LatOrb_mem_stdLat


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial Matrix GlobalTheory.LatOrb
open GlobalTheory GlobalTheory.LatOrbGL
variable {K : Type} [Field K] (V : ValuationSubring K)
namespace GlobalTheory.LatOrbGL
theorem _root_.solution {n : ℕ} (g : Matrix (Fin n) (Fin n) K) (hg : ∀ i j, g i j ∈ V) :
    matLat V g (stdLat V n) ≤ stdLat V n := by
  intro v hv
  rw [mem_matLat] at hv
  obtain ⟨u, hu, rfl⟩ := hv
  rw [mem_stdLat] at hu ⊢
  intro i
  have hu' := fun j => (mem_range_iff V _).1 (hu j)
  apply (mem_range_iff V _).2
  simp only [Matrix.mulVec, dotProduct]
  exact V.toSubring.sum_mem fun j _ => V.toSubring.mul_mem (hg i j) (hu' j)
end GlobalTheory.LatOrbGL
