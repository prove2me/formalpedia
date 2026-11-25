-- Prove2me | solution 1 for GroundTheory.Automorphic.GodementJacquet.detPow_eq_qs_zpow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:23:42.68639+00:00
-- url     : https://prove2.me/submissions/f2440f11-5e9c-4aea-98ac-8fce91baaee4

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_AdmissibleFiniteLength
import Definitions.Def_GroundTheory_LocalFields_LocalFourierHaar
import Definitions.Def_GroundTheory_LocalFields_LocalFourierChar
import Definitions.Def_GroundTheory_LocalFields_LocalZetaEpsilon
import Definitions.Def_GroundTheory_LocalFields_ExistsUnitFiltrationUnitsLeRangeNormUnits
import Definitions.Def_GroundTheory_AutomorphicForms_GL2_GJZetaDefs
import Theorems.Thm_GroundTheory_LocalField_modulus_cpow_eq_qcpow
import Theorems.Thm_GroundTheory_LocalField_qcpow_zpow


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
open GroundTheory.Automorphic.GodementJacquet
open Matrix GLnLocal ValuativeRel Topology Filter
variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ}
namespace GroundTheory.Automorphic.GodementJacquet
theorem _root_.solution (g : GL (Fin n) F) (s : ℂ) : detPow g s = qs F s ^ ordDet g := by
  have hd : (g : Matrix (Fin n) (Fin n) F).det ≠ 0 := (Matrix.GeneralLinearGroup.det g).ne_zero
  rw [detPow, absDet, qs, ordDet, LocalField.modulus_cpow_eq_qcpow hd, LocalField.qcpow_zpow]
  congr 1
  ring
end GroundTheory.Automorphic.GodementJacquet
