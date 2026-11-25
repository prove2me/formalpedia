-- Prove2me | solution 1 for GlobalTheory.ThLoc.cm1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T18:25:38.805144+00:00
-- url     : https://prove2.me/submissions/54ee7ffa-d70e-4524-a141-205509f07d31

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_CMGoodModels_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_ExistsFieldCmCurvesUnitDiscriminant
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ExistsGoodReductionAlgebraicWeierstrassModel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_JInvNormLeOne
import Theorems.Thm_GlobalTheory_isIntegral_modularJ_of_mul_mem
import Theorems.Thm_P2M_GlobalTheory_g__cube_div_eq_modularJ_a1bc96193403


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CMCurves
open GlobalTheory GlobalTheory.ThLoc
namespace GlobalTheory.ThLoc
theorem _root_.solution : Formalism.L2.Th1.CM.JInvariantIntegrality := by
  intro d L _ hd hL
  obtain ⟨a, τ, ha, h⟩ := exists_lattice_eq_mul_tau L
  rw [Formalism.L2.Th1.CM.jInv, g₂_cube_div_eq_modularJ ha h]
  refine isIntegral_modularJ_of_mul_mem (α := Formalism.L2.Th1.CM.omegaK d) (fun m hm => ?_) fun x hx ↦ ?_
  · have := congrArg Complex.im hm
    have h0 : (0:ℝ) < Real.sqrt d := Real.sqrt_pos.mpr (by exact_mod_cast (by omega : 0 < d))
    simp [Formalism.L2.Th1.CM.omegaK] at this
    omega
  · have key : ∀ y : ℂ, y ∈ Submodule.span ℤ {(τ : ℂ), 1} ↔ a * y ∈ L.lattice := fun y ↦ by
      rw [h, Submodule.mem_span_pair]
      simp [mul_right_inj' ha]
    rw [key] at hx ⊢
    simpa [mul_left_comm] using hL _ hx
end GlobalTheory.ThLoc
