-- Prove2me | solution 1 for GlobalTheory.SW.HaarLevel.perSub_eq_range
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:21:10.080566+00:00
-- url     : https://prove2.me/submissions/a0dc0fd4-147c-4c3b-8085-7401726807ee

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IMemSiegel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_FinsumQuotientOfLe
import Theorems.Thm_GlobalTheory_SW_HaarLevel_intM_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex GlobalTheory.SW
open scoped ComplexConjugate Real
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.HaarLevel
noncomputable section
open NumberField
variable {K : Type} [Field K] [NumberField K] {κ ι : Type} [Fintype κ] [Fintype ι]
omit [NumberField K] [Fintype κ] [Fintype ι]
namespace GlobalTheory.SW.HaarLevel
theorem _root_.solution (R : ℕ) :
    perSub K κ ι R = ((incl K κ ι).comp (nsmulAddMonoidHom R)).range := by
  have : {x | ∃ y : Matrix κ ι K, IntM y ∧ x = (R : K) • y} =
      (((incl K κ ι).comp (nsmulAddMonoidHom R)).range : Set (Matrix κ ι K)) := by
    ext z
    simp only [Set.mem_setOf_eq, SetLike.mem_coe, AddMonoidHom.mem_range, AddMonoidHom.comp_apply,
      nsmulAddMonoidHom_apply, map_nsmul, intM_iff, Nat.cast_smul_eq_nsmul]
    constructor
    · rintro ⟨_, ⟨y, rfl⟩, rfl⟩; exact ⟨y, rfl⟩
    · rintro ⟨y, rfl⟩; exact ⟨_, ⟨y, rfl⟩, rfl⟩
  rw [perSub, this, AddSubgroup.closure_eq]
end GlobalTheory.SW.HaarLevel
