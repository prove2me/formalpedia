-- Prove2me | solution 1 for GroundTheory.Automorphic.Iwasawa.torusPow_neg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T13:26:35.508282+00:00
-- url     : https://prove2.me/submissions/ff227a92-e584-42a9-8622-57d4dae905d6

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GLnLattice
import Definitions.Def_GroundTheory_AutomorphicForms_Iwasawa
import Theorems.Thm_GroundTheory_Automorphic_GLnLocal_quotientEquivLattice_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.GLnLocal.quotientEquivLattice_mk



set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Automorphic
open ValuativeRel Matrix Filter
open scoped Pointwise
open GroundTheory.Automorphic.Iwasawa
open GLnLocal
variable (F : Type*) [Field F] (n : ℕ)
variable [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
namespace GroundTheory.Automorphic.Iwasawa
theorem _root_.solution (l : Fin n → ℤ) : torusPow F n (-l) = (torusPow F n l)⁻¹ := by
  rw [torusPow, torusPow, ← map_inv]
  congr 1
  funext i
  simp [_root_.zpow_neg]
end GroundTheory.Automorphic.Iwasawa
