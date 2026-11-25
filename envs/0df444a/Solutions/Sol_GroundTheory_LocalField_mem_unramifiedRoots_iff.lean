-- Prove2me | solution 1 for GroundTheory.LocalField.mem_unramifiedRoots_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:45:29.899418+00:00
-- url     : https://prove2.me/submissions/13649d66-e492-4f17-a189-717351cb2a9d

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_Interface
import Definitions.Def_GroundTheory_LocalFields_FiniteExtension
import Definitions.Def_GroundTheory_LocalFields_Uniqueness
import Definitions.Def_GroundTheory_LocalFields_Integers
import Definitions.Def_GroundTheory_LocalFields_UnitsPowers
import Definitions.Def_GroundTheory_LocalFields_UnramifiedRootsOfUnity
import Definitions.Def_GroundTheory_LocalFields_UnramifiedGalois
import Definitions.Def_GroundTheory_LocalFields_UnramifiedExistence
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_ProfiniteInteger
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_ExistsEqNsmulOfProjEqZero
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_Frobenius
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_Valuation
import Definitions.Def_GroundTheory_LocalFields_MaximalUnramified
import Theorems.Thm_GroundTheory_LocalField_Abstract_cosetConj_mk
import Theorems.Thm_GroundTheory_LocalField_galoisEquivResidue_apply
import Theorems.Thm_GroundTheory_LocalField_natCast_card_pow_sub_one_ne_zero
import Theorems.Thm_GroundTheory_LocalField_residueAlgEquiv_residue
import Theorems.Thm_GroundTheory_LocalField_unitsEquivResidueProd_fst
import Theorems.Thm_GroundTheory_LocalField_unitsEquivResidueProd_symm_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
attribute [local simp] GroundTheory.LocalField.Abstract.cosetConj_mk
attribute [local simp] GroundTheory.LocalField.galoisEquivResidue_apply
attribute [local simp] GroundTheory.LocalField.residueAlgEquiv_residue
attribute [local simp] GroundTheory.LocalField.unitsEquivResidueProd_fst
attribute [local simp] GroundTheory.LocalField.unitsEquivResidueProd_symm_apply



set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.LocalField
open ValuativeRel IntermediateField GroundTheory.LocalField.Abstract GroundTheory.LocalField.Abstract.ProfiniteInteger
variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {Ω : Type*} [Field Ω] [Algebra K Ω]
omit [Algebra K Ω]
namespace GroundTheory.LocalField
theorem _root_.solution {ξ : Ω} :
    ξ ∈ unramifiedRoots K Ω ↔ ∃ m : ℕ, (m : 𝓀[K]) ≠ 0 ∧ ξ ^ m = 1 := by
  constructor
  · rintro ⟨n, hn, hξ⟩
    exact ⟨_, natCast_card_pow_sub_one_ne_zero hn, hξ⟩
  · rintro ⟨m, hm, hξ⟩
    have hm0 : m ≠ 0 := by rintro rfl; simp at hm
    have := Fintype.ofFinite 𝓀[K]
    obtain ⟨p, hp⟩ := CharP.exists 𝓀[K]
    obtain ⟨k, hprime, hcard⟩ := FiniteField.card 𝓀[K] p
    have hpm : ¬ p ∣ m := fun h ↦ hm ((CharP.cast_eq_zero_iff 𝓀[K] p m).2 h)
    have hcop : Nat.Coprime (Nat.card 𝓀[K]) m := by
      rw [Nat.card_eq_fintype_card, hcard]
      exact Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hprime).2 hpm)
    have hdvd : m ∣ Nat.card 𝓀[K] ^ m.totient - 1 :=
      (Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ Nat.card_pos)).1 (Nat.ModEq.pow_totient hcop).symm
    refine ⟨m.totient, (Nat.totient_pos.2 (Nat.pos_of_ne_zero hm0)).ne', ?_⟩
    obtain ⟨c, hc⟩ := hdvd
    rw [hc, pow_mul, hξ, one_pow]
end GroundTheory.LocalField
