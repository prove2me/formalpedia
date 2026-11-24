-- Prove2me | solution 1 for GlobalTheory.isLattice_of_fg_dualSubmodule
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:04:48.980821+00:00
-- url     : https://prove2.me/submissions/d550c16e-21a4-4bd3-a25e-b40312bfc21c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FiniteAndNcardSetOfSubmoduleLeRelIndexEqLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_RelIndexDualSubmoduleInfOfSelfDual
import Theorems.Thm_GlobalTheory_eq_zero_of_forall_rat_smul_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module
open GlobalTheory
variable {V : Type*} [AddCommGroup V] [Module ℚ V]
variable [FiniteDimensional ℚ V]
namespace GlobalTheory
theorem _root_.solution (B : LinearMap.BilinForm ℚ V) (hB : B.Nondegenerate)
    (L : Submodule ℤ V) (hL : L.FG) (hd : (B.dualSubmodule L).FG) : L.IsLattice ℚ := by
  refine ⟨hL, ?_⟩
  by_contra hne
  obtain ⟨φ, hφ, hle⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.2 hne)
  have h0 : (B.toDual hB).symm φ = 0 := by
    refine eq_zero_of_forall_rat_smul_mem _ hd fun q y hy => ?_
    have h1 : B ((B.toDual hB).symm φ) y = 0 := by
      rw [LinearMap.BilinForm.apply_toDual_symm_apply]
      exact hle (Submodule.subset_span hy)
    rw [map_smul, LinearMap.smul_apply, h1, smul_zero]
    exact zero_mem _
  exact hφ (by simpa using h0)
end GlobalTheory
