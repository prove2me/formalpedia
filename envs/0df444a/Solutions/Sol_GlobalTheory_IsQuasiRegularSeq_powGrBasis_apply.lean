-- Prove2me | solution 1 for GlobalTheory.IsQuasiRegularSeq.powGrBasis_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:58:48.799976+00:00
-- url     : https://prove2.me/submissions/cc693f33-d502-4714-b5d7-6f5eea399b6e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsQuasiRegularSeqSelfIffLocalizationMaximal
import Theorems.Thm_GlobalTheory_monoToPowGr_single

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open GlobalTheory
variable {R : Type*} [CommRing R] {ι : Type*} [Finite ι]
namespace GlobalTheory
namespace IsQuasiRegularSeq
theorem _root_.solution {f : ι → R} (h : IsQuasiRegularSeq R f) (a : ℕ)
    (α : MonoDeg ι a) : h.powGrBasis a α = powGr.mk _ R a
      ⟨monoVal f α.1, by simpa using monoVal_mem_pow f α⟩ := by
  classical
  have h1 : (LinearEquiv.piCongrRight fun _ : MonoDeg ι a =>
      quotSMulTopEquivQuot (Ideal.span (Set.range f))).symm (Pi.single α 1) =
      Pi.single α (Submodule.Quotient.mk 1) := by
    rw [LinearEquiv.symm_apply_eq]
    funext β
    rw [LinearEquiv.piCongrRight_apply]
    by_cases hβ : β = α
    · subst hβ
      rw [Pi.single_eq_same, Pi.single_eq_same]
      rfl
    · rw [Pi.single_eq_of_ne hβ, Pi.single_eq_of_ne hβ, map_zero]
  rw [IsQuasiRegularSeq.powGrBasis, Module.Basis.coe_ofEquivFun]
  beta_reduce
  rw [LinearEquiv.trans_symm, LinearEquiv.trans_apply, LinearEquiv.symm_symm, h1,
    IsQuasiRegularSeq.powGrEquiv_apply, monoToPowGr_single, powGr.mulElem_mk]
  congr 2
  exact mul_one _
end IsQuasiRegularSeq
end GlobalTheory
