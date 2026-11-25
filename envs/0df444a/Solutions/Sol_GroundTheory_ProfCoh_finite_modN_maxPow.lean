-- Prove2me | solution 1 for GroundTheory.ProfCoh.finite_modN_maxPow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:24:04.798286+00:00
-- url     : https://prove2.me/submissions/10823f62-3cd5-40c6-8018-d04b4654e4f6

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_LocalEulerCharacteristic_UnitsLattice
import Definitions.Def_GroundTheory_LocalFields_NormalLattice
import Definitions.Def_GroundTheory_ProfiniteCohomology_LocalEulerCharacteristic_ModNEquivOfSurjectiveApplyModNRep
import Theorems.Thm_GroundTheory_LocalField_coe_smul_integerUnits
import Theorems.Thm_GroundTheory_LocalField_residueAlgEquiv_residue
import Theorems.Thm_GroundTheory_LocalField_unitsEquivResidueProd_fst
import Theorems.Thm_GroundTheory_LocalField_unitsEquivResidueProd_symm_apply
import Theorems.Thm_GroundTheory_ProfCoh_coe_torsNRep_apply
import Theorems.Thm_GroundTheory_ProfCoh_mem_maximalIdeal_pow_add_iff
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
variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {ϖ : 𝒪[F]} (hϖ : Irreducible ϖ) {p e : ℕ} {ε : 𝒪[F]ˣ} (hpe : (p : 𝒪[F]) = ϖ ^ e * ε)
include hϖ hpe
namespace GroundTheory.ProfCoh
theorem _root_.solution (k : ℕ) : Finite (ModN (maxPow F k) p) := by
  have hfin : Finite (𝒪[F] ⧸ 𝓂[F] ^ (k + e)) :=
    IsLocalRing.finite_quotient_iff.mpr ⟨k + e, le_rfl⟩
  let φ : maxPow F k →+ 𝒪[F] ⧸ 𝓂[F] ^ (k + e) :=
    (Ideal.Quotient.mk (𝓂[F] ^ (k + e))).toAddMonoidHom.comp (maxPow F k).subtype
  have hφ : ∀ a : maxPow F k, φ a = 0 ↔ a ∈ LinearMap.range (LinearMap.lsmul ℤ (maxPow F k) p) := by
    intro a
    rw [mem_range_lsmul_iff]
    change Ideal.Quotient.mk _ (a : 𝒪[F]) = 0 ↔ _
    rw [Ideal.Quotient.eq_zero_iff_mem, mem_maximalIdeal_pow_add_iff hϖ hpe]
    constructor
    · rintro ⟨y, hy, h⟩
      exact ⟨⟨y, hy⟩, Subtype.ext (by simp [h])⟩
    · rintro ⟨y, rfl⟩
      exact ⟨y, y.2, by simp⟩
  let L := (LinearMap.range (LinearMap.lsmul ℤ (maxPow F k) p)).liftQ φ.toIntLinearMap
    fun a ha ↦ LinearMap.mem_ker.mpr ((hφ a).mpr ha)
  refine Finite.of_injective L ?_
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  exact (Submodule.Quotient.mk_eq_zero _).mpr ((hφ a).mp hx)
end GroundTheory.ProfCoh
