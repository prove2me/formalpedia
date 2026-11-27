-- Prove2me | solution 1 for GlobalTheory.card_selfDual_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:35:52.940016+00:00
-- url     : https://prove2.me/submissions/45538760-f1f4-41bb-831a-6e03db024555

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FiniteAndNcardSetOfSubmoduleLeRelIndexEqLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_RelIndexDualSubmoduleInfOfSelfDual
import Theorems.Thm_GlobalTheory_dualSubmodule_le_dualSubmodule_of_le
import Theorems.Thm_GlobalTheory_isLattice_of_fg_dualSubmodule
import Theorems.Thm_GlobalTheory_finrank_eq_of_isLattice
import Theorems.Thm_GlobalTheory_isLattice_dualSubmodule
import Theorems.Thm_GlobalTheory_relIndex_ne_zero_of_isLattice
import Theorems.Thm_GlobalTheory_relIndex_dualSubmodule_inf_of_selfDual
import Theorems.Thm_GlobalTheory_encard_biUnion_le_mul
import Theorems.Thm_GlobalTheory_encard_setOf_submodule_le_relIndex_eq_le


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
namespace GlobalTheory
theorem _root_.solution {V : Type*} [AddCommGroup V] [Module ℚ V] [FiniteDimensional ℚ V] (B : LinearMap.BilinForm ℚ V) (hB : B.Nondegenerate) (hr : B.IsRefl)
    (hlr : ∀ x y, B x y = B y x ∨ B x y = - B y x) (L : Submodule ℤ V) (hL : L.FG) (hLd : B.dualSubmodule L = L) (m : ℕ) (hm : 1 ≤ m) :
    {L' : Submodule ℤ V | L'.FG ∧ B.dualSubmodule L' = L' ∧ L'.toAddSubgroup.relIndex L.toAddSubgroup = m}.Finite ∧
    {L' : Submodule ℤ V | L'.FG ∧ B.dualSubmodule L' = L' ∧ L'.toAddSubgroup.relIndex L.toAddSubgroup = m}.ncard ≤ m ^ (2 * Module.finrank ℚ V) ∧
    ∀ L' : Submodule ℤ V, L'.FG → B.dualSubmodule L' = L' → L'.toAddSubgroup.relIndex L.toAddSubgroup ≠ 0 ∧ (L'.toAddSubgroup.relIndex L.toAddSubgroup = 1 → L' = L) := by
  have hm0 : m ≠ 0 := by omega
  haveI : L.IsLattice ℚ := isLattice_of_fg_dualSubmodule B hB L hL (hLd.symm ▸ hL)
  have hinf : ∀ L' : Submodule ℤ V, (L ⊓ L').toAddSubgroup.relIndex L.toAddSubgroup =
      L'.toAddSubgroup.relIndex L.toAddSubgroup := fun L' =>
    AddSubgroup.inf_relIndex_left L.toAddSubgroup L'.toAddSubgroup
  have hsub : {L' : Submodule ℤ V | L'.FG ∧ B.dualSubmodule L' = L' ∧
      L'.toAddSubgroup.relIndex L.toAddSubgroup = m} ⊆
      ⋃ M ∈ {M : Submodule ℤ V | M.IsLattice ℚ ∧ M ≤ L ∧
        M.toAddSubgroup.relIndex L.toAddSubgroup = m},
        {H | H ≤ B.dualSubmodule M ∧
          H.toAddSubgroup.relIndex (B.dualSubmodule M).toAddSubgroup = m} := by
    rintro L' ⟨h1, h2, h3⟩
    haveI : L'.IsLattice ℚ := isLattice_of_fg_dualSubmodule B hB L' h1 (h2.symm ▸ h1)
    refine Set.mem_biUnion (x := L ⊓ L') ⟨inferInstance, inf_le_left, (hinf L').trans h3⟩ ⟨?_, ?_⟩
    · exact h2.ge.trans (dualSubmodule_le_dualSubmodule_of_le B inf_le_right)
    · rw [relIndex_dualSubmodule_inf_of_selfDual B hB hLd h2, hinf, h3]
  have hcard : {L' : Submodule ℤ V | L'.FG ∧ B.dualSubmodule L' = L' ∧
      L'.toAddSubgroup.relIndex L.toAddSubgroup = m}.encard ≤
      ((m ^ (2 * finrank ℚ V) : ℕ) : ℕ∞) := by
    rw [two_mul, pow_add]
    refine (Set.encard_le_encard hsub).trans (encard_biUnion_le_mul _ _ _ _ ?_ ?_)
    · rw [← finrank_eq_of_isLattice L]
      exact (Set.encard_le_encard fun M hM => hM.2).trans
        (encard_setOf_submodule_le_relIndex_eq_le L hm0)
    · intro M hM
      haveI := hM.1
      haveI := isLattice_dualSubmodule B hB M
      rw [← finrank_eq_of_isLattice (B.dualSubmodule M)]
      exact encard_setOf_submodule_le_relIndex_eq_le _ hm0
  have hf := Set.finite_of_encard_le_coe hcard
  refine ⟨hf, ?_, fun L' h1 h2 => ⟨?_, fun h3 => ?_⟩⟩
  · rw [← hf.cast_ncard_eq] at hcard
    exact_mod_cast hcard
  · haveI : L'.IsLattice ℚ := isLattice_of_fg_dualSubmodule B hB L' h1 (h2.symm ▸ h1)
    rw [← hinf]
    exact relIndex_ne_zero_of_isLattice inf_le_left
  · have h4 : L ≤ L' := AddSubgroup.relIndex_eq_one.1 h3
    refine le_antisymm ?_ h4
    have := dualSubmodule_le_dualSubmodule_of_le B h4
    rwa [hLd, h2] at this
end GlobalTheory
