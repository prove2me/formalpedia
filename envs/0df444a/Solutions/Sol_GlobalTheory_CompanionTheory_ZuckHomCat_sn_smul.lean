-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.ZuckHomCat.sn_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T06:14:13.880529+00:00
-- url     : https://prove2.me/submissions/371ba88c-490f-453e-8690-f7becd6e7b70

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_SmoothCyc
import Definitions.Def_CompanionTheory_AutomorphicTheory_ZuckermanCommutation_ZuckermanFunctors_IsSimpleFam
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_HomCategory
import Theorems.Thm_CompanionTheory_D_Upq_Sm_dsW_smul
import Theorems.Thm_CompanionTheory_D_Upq_Sm_ex_mem_of_lie
import Theorems.Thm_P2M_CompanionTheory_D_Upq_Sm_dsigW_eq__320e841fce93


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CompanionTheory.Zuck BranchingSupport Matrix Finset
open scoped InnerProductSpace Kronecker
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.ZuckHomCat
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData CompanionTheory.D.Upq.Sm
variable {k r : ℕ}
namespace GlobalTheory.CompanionTheory.ZuckHomCat
theorem _root_.solution (X : Obj k r) {W : List (Mx k r)} (hW : LieWd k r W) (a : ℂ) (x : M X) :
    sn X W (a • x) = ‖a‖ * sn X W x := by
  unfold sn
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  simp only [dsigW_eq', Pi.smul_apply, Submodule.coe_smul]
  rw [dsW_smul X.2.repOn (x c).2 a (fun Y hY t => ex_mem_of_lie (hW Y hY) t)]
  exact norm_smul _ _
end GlobalTheory.CompanionTheory.ZuckHomCat
