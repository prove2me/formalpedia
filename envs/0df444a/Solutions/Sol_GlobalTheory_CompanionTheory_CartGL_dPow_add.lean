-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.CartGL.dPow_add
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:56:51.070804+00:00
-- url     : https://prove2.me/submissions/5b222259-f23a-49b6-a815-cb7e095818cb

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_InhabitedFinite
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_EntryMulSubOne
import Theorems.Thm_GlobalTheory_CompanionTheory_CartGL_dPow_val

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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.CartGL
variable {L : Type} [NontriviallyNormedField L] [IsUltrametricDist L] {n : ℕ}
namespace GlobalTheory.CompanionTheory.CartGL
theorem _root_.solution (p : Lˣ) (a b : Fin n → ℤ) : (dPow p (a + b) : GL (Fin n) L) = dPow p a * dPow p b := by
  apply Units.ext
  rw [Units.val_mul, dPow_val, dPow_val, dPow_val, diagonal_mul_diagonal]
  congr 1
  funext i
  rw [Pi.add_apply, _root_.zpow_add, Units.val_mul]
end GlobalTheory.CompanionTheory.CartGL
