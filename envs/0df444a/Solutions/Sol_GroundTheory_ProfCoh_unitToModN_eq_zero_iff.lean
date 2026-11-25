-- Prove2me | solution 1 for GroundTheory.ProfCoh.unitToModN_eq_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T01:29:42.035266+00:00
-- url     : https://prove2.me/submissions/e7dd0aaf-8a03-4aa2-addd-8f5cd0a59967

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_LocalEulerCharacteristic_UnitsPower
import Definitions.Def_GroundTheory_LocalFields_UnitsGalois
import Definitions.Def_GroundTheory_LocalFields_ExistsUnitFiltrationUnitsLeAndRangePowLe
import Definitions.Def_GroundTheory_ProfiniteCohomology_LocalEulerCharacteristic_Additive
import Definitions.Def_GroundTheory_ProfiniteCohomology_LocalEulerCharacteristic_UnitsLattice
import Theorems.Thm_GroundTheory_ProfCoh_mem_maximalIdeal_pow_add_iff
import Theorems.Thm_GroundTheory_ProfCoh_unitToModN_apply
import Theorems.Thm_GroundTheory_LocalField_coe_smul_integerUnits
import Theorems.Thm_GroundTheory_LocalField_residueAlgEquiv_residue
import Theorems.Thm_GroundTheory_LocalField_unitsEquivResidueProd_fst
import Theorems.Thm_GroundTheory_LocalField_unitsEquivResidueProd_symm_apply
import Theorems.Thm_GroundTheory_ProfCoh_coe_torsNRep_apply
import Theorems.Thm_GroundTheory_ProfCoh_exists_pow_eq_of_mem_unitFiltration
import Theorems.Thm_GroundTheory_ProfCoh_modNRep_mk
import Theorems.Thm_GroundTheory_ProfCoh_pow_mem_unitFiltration
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
open GroundTheory.LocalField ValuativeRel IsLocalRing
variable (E F : Type*) [Field E] [ValuativeRel E] [TopologicalSpace E]
  [IsNonarchimedeanLocalField E]
  [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [Algebra E F] [ValuativeExtension E F] [FiniteDimensional E F]
attribute [local instance] integerAction
attribute [local instance] unitFiltrationAction maxPowAction
variable {E F}
variable {ϖ : 𝒪[F]} (hϖ : Irreducible ϖ) {p : ℕ} {e : ℕ} {ε : 𝒪[F]ˣ}
  (hpe : (p : 𝒪[F]) = ϖ ^ e * ε)
include hϖ hpe
namespace GroundTheory.ProfCoh
theorem _root_.solution (hp : p.Prime) {k : ℕ} (hk : e + 1 ≤ k)
    (u : Additive (unitFiltration F k)) :
    unitToModN hϖ hpe (Nat.le_of_succ_le hk) u = 0 ↔
      u ∈ LinearMap.range (LinearMap.lsmul ℤ (Additive (unitFiltration F k)) p) := by
  rw [unitToModN_apply, Submodule.Quotient.mk_eq_zero, mem_range_lsmul_iff, mem_range_lsmul_iff]
  constructor
  · rintro ⟨y, hy⟩
    have hy' : ((u.toMul : 𝒪[F]ˣ) : 𝒪[F]) - 1 = p * (y : 𝒪[F]) := by
      have := congrArg Subtype.val hy
      simpa [nsmul_eq_mul] using this.symm
    have h1 : (u.toMul : 𝒪[F]ˣ) ∈ unitFiltration F (k + e) :=
      (mem_maximalIdeal_pow_add_iff hϖ hpe).mpr ⟨y, y.2, hy'⟩
    obtain ⟨v, hv, hvp⟩ := exists_pow_eq_of_mem_unitFiltration hϖ hp hpe hk h1
    refine ⟨Additive.ofMul ⟨v, hv⟩, ?_⟩
    apply Additive.toMul.injective
    ext
    simp [hvp]
  · rintro ⟨v, rfl⟩
    have h1 : ((v.toMul : 𝒪[F]ˣ)) ^ p ∈ unitFiltration F (k + e) :=
      pow_mem_unitFiltration hϖ hp hpe hk v.toMul.2
    obtain ⟨y, hy, hyp⟩ := (mem_maximalIdeal_pow_add_iff hϖ hpe).mp h1
    refine ⟨⟨y, hy⟩, Subtype.ext ?_⟩
    simp only [AddSubgroup.coe_nsmul, nsmul_eq_mul, toMul_nsmul, SubmonoidClass.coe_pow,
      Units.val_pow_eq_pow_val] at hyp ⊢
    exact hyp.symm
end GroundTheory.ProfCoh
