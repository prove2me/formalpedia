-- Prove2me | solution 1 for GroundTheory.ProfCoh.exists_card_quotient_eq_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:51:08.640369+00:00
-- url     : https://prove2.me/submissions/c58f6bfd-fcb8-414c-b565-2cc04ca309f5

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_LocalEulerCharacteristic_UnitsLattice
import Definitions.Def_GroundTheory_LocalFields_NormalLattice
import Definitions.Def_GroundTheory_ProfiniteCohomology_LocalEulerCharacteristic_ModNEquivOfSurjectiveApplyModNRep
import Theorems.Thm_GroundTheory_LocalField_coe_smul_integerUnits
import Theorems.Thm_GroundTheory_LocalField_residueAlgEquiv_residue
import Theorems.Thm_GroundTheory_LocalField_unitsEquivResidueProd_fst
import Theorems.Thm_GroundTheory_LocalField_unitsEquivResidueProd_symm_apply
import Theorems.Thm_GroundTheory_ProfCoh_coe_torsNRep_apply
import Theorems.Thm_GroundTheory_ProfCoh_modNRep_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.LocalField.coe_smul_integerUnits
attribute [local simp] GroundTheory.LocalField.residueAlgEquiv_residue
attribute [local simp] GroundTheory.LocalField.unitsEquivResidueProd_fst
attribute [local simp] GroundTheory.LocalField.unitsEquivResidueProd_symm_apply
attribute [local simp] GroundTheory.ProfCoh.coe_torsNRep_apply
attribute [local simp] GroundTheory.ProfCoh.modNRep_mk



set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.ProfCoh
universe u
open GroundTheory.LocalField ValuativeRel IsLocalRing
variable {E : Type*} [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  {p : ℕ}
variable [Fact p.Prime]
namespace GroundTheory.ProfCoh
theorem _root_.solution (hp0 : (p : E) ≠ 0) :
    ∃ n, Nat.card (𝒪[E] ⧸ Ideal.span {(p : 𝒪[E])}) = p ^ n := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[E]
  have hp' : (p : 𝒪[E]) ≠ 0 := fun h ↦ hp0 (by simpa using congrArg Subtype.val h)
  obtain ⟨m, ε, hm⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hp' hπ
  have hfin : Finite (𝒪[E] ⧸ Ideal.span {(p : 𝒪[E])}) := by
    refine IsLocalRing.finite_quotient_iff.mpr ⟨m, fun x hx ↦ ?_⟩
    obtain ⟨a, rfl⟩ := (mem_maximalIdeal_pow_iff hπ).mp hx
    rw [Ideal.mem_span_singleton', hm]
    exact ⟨((ε⁻¹ : 𝒪[E]ˣ) : 𝒪[E]) * a, by
      have := ε.inv_mul
      linear_combination (π ^ m * a) * this⟩
  have hfin' : Finite (ModN 𝒪[E] p) := Finite.of_equiv _ modNIntegerEquiv.symm.toEquiv
  have := Fintype.ofFinite (ModN 𝒪[E] p)
  refine ⟨Module.finrank (ZMod p) (ModN 𝒪[E] p), ?_⟩
  rw [← Nat.card_congr modNIntegerEquiv.toEquiv, Nat.card_eq_fintype_card,
    Module.card_eq_pow_finrank (K := ZMod p), ZMod.card]
end GroundTheory.ProfCoh
