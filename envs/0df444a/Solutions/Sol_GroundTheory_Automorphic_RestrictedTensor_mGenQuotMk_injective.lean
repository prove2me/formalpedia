-- Prove2me | solution 1 for GroundTheory.Automorphic.RestrictedTensor.mGenQuotMk_injective
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:24:57.05515+00:00
-- url     : https://prove2.me/submissions/ee120250-fcae-4dc7-ac09-e8c40b427026

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_Operators
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_GenWindow
import Theorems.Thm_GroundTheory_Automorphic_RestrictedTensor_IsWinProj_apply_of_mem

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
open GroundTheory.Automorphic.RestrictedTensor
open Module Set
variable {M : Type*} [Monoid M] {V W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
  [Module ℂ W]
variable (ρ : Representation ℂ M V)
variable (e : End ℂ V) (N : Submodule ℂ V)
variable {ρ e N}
namespace GroundTheory.Automorphic.RestrictedTensor
theorem _root_.solution (he : IsWinProj ρ e) (hNe : N ≤ LinearMap.range e) :
    Function.Injective (mGenQuotMk ρ e N) := by
  rw [← LinearMap.ker_eq_bot, eq_bot_iff]
  intro n hn
  rw [LinearMap.mem_ker, mGenQuotMk, LinearMap.comp_apply, Submodule.mkQ_apply,
    Submodule.Quotient.mk_eq_zero] at hn
  have := hn 1
  rw [map_one, Module.End.one_apply] at this
  simp only [Submodule.coe_inclusion] at this
  rw [Submodule.mem_bot]
  exact Subtype.ext ((he.apply_of_mem (hNe n.2)).symm.trans this)
end GroundTheory.Automorphic.RestrictedTensor
