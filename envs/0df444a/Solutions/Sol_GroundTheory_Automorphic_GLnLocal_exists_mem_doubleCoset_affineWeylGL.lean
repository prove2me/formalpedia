-- Prove2me | solution 1 for GroundTheory.Automorphic.GLnLocal.exists_mem_doubleCoset_affineWeylGL
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:13:43.617513+00:00
-- url     : https://prove2.me/submissions/8580f91b-7055-43c6-b576-26bdf5e48add

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GLnLocal
import Definitions.Def_GroundTheory_AutomorphicForms_GLnLattice
import Definitions.Def_GroundTheory_AutomorphicForms_FiniteBruhat
import Definitions.Def_GroundTheory_AutomorphicForms_AffineBruhat
import Theorems.Thm_GroundTheory_Automorphic_GLnLocal_exists_rowsReducedOn_univ
import Theorems.Thm_GroundTheory_Automorphic_GLnLocal_exists_eq_mul_affineWeylGL_of_rowsReducedOn

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Automorphic
open Matrix DoubleCoset ValuativeRel
open GroundTheory.Automorphic.GLnLocal
variable (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  (n : ℕ)
local notation "ϖ" => ((uniformizer F : 𝒪[F]) : F)
namespace GroundTheory.Automorphic.GLnLocal
theorem _root_.solution (g : GL (Fin n) F) :
    ∃ w : ExtendedAffineWeyl n,
      g ∈ doubleCoset (affineWeylGL F n w) (iwahori F n) (iwahori F n) := by
  obtain ⟨x, hx, y, hy, hred⟩ := exists_rowsReducedOn_univ F n g
  obtain ⟨w, t, ht, hgt⟩ := exists_eq_mul_affineWeylGL_of_rowsReducedOn F n _ hred
  refine ⟨w, mem_doubleCoset.mpr ⟨x⁻¹ * t, (iwahori F n).mul_mem ((iwahori F n).inv_mem hx) ht,
    y⁻¹, (iwahori F n).inv_mem hy, ?_⟩⟩
  rw [mul_assoc x⁻¹ t, ← hgt]
  group
end GroundTheory.Automorphic.GLnLocal
