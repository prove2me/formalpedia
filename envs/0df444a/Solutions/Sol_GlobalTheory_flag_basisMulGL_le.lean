-- Prove2me | solution 1 for GlobalTheory.flag_basisMulGL_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:57:38.320391+00:00
-- url     : https://prove2.me/submissions/c4ffdc40-2d68-4b09-959a-0cf27f3f963e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_ExistsIsAdaptedOfIsLocalRing
import Theorems.Thm_GlobalTheory_mem_upperTriangularGL

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module TensorProduct
open GlobalTheory
noncomputable section
variable (ι R : Type*) [CommRing R] [Fintype ι] [LinearOrder ι]
variable {ι R}
variable {M : Type*} [AddCommGroup M] [Module R M] {n : ℕ}
namespace GlobalTheory
theorem _root_.solution (b : Basis (Fin n) R M) {g : GL (Fin n) R}
    (hg : g ∈ upperTriangularGL (Fin n) R) (k : Fin (n + 1)) :
    (basisMulGL b g).flag k ≤ b.flag k := by
  rw [Basis.flag_le_iff]
  intro j hj
  rw [mem_basis_flag_iff]
  intro i hi
  have : j < i := Fin.castSucc_lt_castSucc_iff.mp (hj.trans_le hi)
  rw [← Basis.toMatrix_apply, toMatrix_basisMulGL, mem_upperTriangularGL.mp hg i j this]
end GlobalTheory
