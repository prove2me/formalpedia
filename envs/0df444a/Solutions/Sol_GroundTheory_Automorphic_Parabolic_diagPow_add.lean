-- Prove2me | solution 1 for GroundTheory.Automorphic.Parabolic.diagPow_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:42:42.420317+00:00
-- url     : https://prove2.me/submissions/ea4d949e-f2fd-47f4-99ac-fda7266917d1

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_LeviCartan
import Definitions.Def_GroundTheory_AutomorphicForms_SmoothRepSchur
import Definitions.Def_GroundTheory_AutomorphicForms_MeasuresModulus
import Definitions.Def_GroundTheory_AutomorphicForms_CuspidalAdmissible
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_uniformizer_ne_zero


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
open GroundTheory.Automorphic.Parabolic
open Matrix Iwasawa GLnLocal ValuativeRel Topology Filter Set
variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ} {α : Type*} [LinearOrder α] {β : Fin n → α}
open Cartan
namespace GroundTheory.Automorphic.Parabolic
theorem _root_.solution (μ ν : Fin n → ℤ) : diagPow F n (μ + ν) = diagPow F n μ * diagPow F n ν := by
  apply Units.ext
  rw [Units.val_mul, coe_diagPow, coe_diagPow, coe_diagPow, diagonal_mul_diagonal]
  congr 1
  funext i
  rw [Pi.add_apply, zpow_add₀ (Cartan.uniformizer_ne_zero F)]
end GroundTheory.Automorphic.Parabolic
