-- Prove2me | solution 1 for GroundTheory.Automorphic.Parabolic.diagPow_conj_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:00:23.731951+00:00
-- url     : https://prove2.me/submissions/6e110385-faed-47fc-8af8-cea9cb610c7e

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_LeviCartan
import Definitions.Def_GroundTheory_AutomorphicForms_SmoothRepSchur
import Definitions.Def_GroundTheory_AutomorphicForms_MeasuresModulus
import Definitions.Def_GroundTheory_AutomorphicForms_CuspidalAdmissible
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_diagPow_neg
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
theorem _root_.solution (μ : Fin n → ℤ) (g : GL (Fin n) F) (i j : Fin n) :
    (diagPow F n μ * g * (diagPow F n μ)⁻¹ : GL (Fin n) F) i j =
      (uniformizer F : F) ^ (μ i - μ j) * g i j := by
  rw [← diagPow_neg]
  rw [Units.val_mul, Units.val_mul, coe_diagPow, coe_diagPow, mul_diagonal, diagonal_mul,
    Pi.neg_apply,
    zpow_sub₀ (Cartan.uniformizer_ne_zero F), _root_.zpow_neg, div_eq_mul_inv]
  ring
end GroundTheory.Automorphic.Parabolic
