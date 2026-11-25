-- Prove2me | solution 1 for GroundTheory.LocalField.finite_quotient_range_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:13:30.065229+00:00
-- url     : https://prove2.me/submissions/1eeae844-7354-4f6e-adbe-c13ea6c589ca

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_UnitsBasic
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ExistsRootOfAdicComplete
import Definitions.Def_GroundTheory_LocalFields_UnitsPowers
import Theorems.Thm_GroundTheory_LocalField_unitsEquivResidueProd_fst
import Theorems.Thm_GroundTheory_LocalField_unitsEquivResidueProd_symm_apply
import Theorems.Thm_GroundTheory_LocalField_exists_unitFiltration_le_range_pow
import Theorems.Thm_GroundTheory_LocalField_unitsEquivIntProd_symm_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
attribute [local simp] GroundTheory.LocalField.unitsEquivResidueProd_fst
attribute [local simp] GroundTheory.LocalField.unitsEquivResidueProd_symm_apply

set_option autoImplicit false
open GroundTheory GroundTheory.LocalField
open ValuativeRel IsLocalRing Polynomial
open scoped WithZero
variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable {K}
namespace GroundTheory.LocalField
theorem _root_.solution {m : ℕ} (hm : (m : K) ≠ 0) :
    Finite (Kˣ ⧸ (powMonoidHom m : Kˣ →* Kˣ).range) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
  obtain ⟨N, hN⟩ := exists_unitFiltration_le_range_pow hm
  have hm0 : m ≠ 0 := by rintro rfl; simp at hm
  set H := (powMonoidHom m : Kˣ →* Kˣ).range
  set ψ : 𝒪[K]ˣ →* Kˣ ⧸ H := (QuotientGroup.mk' H).comp (unitsIncl K)
  have hle : unitFiltration K N ≤ ψ.ker := by
    intro w hw
    obtain ⟨x, rfl⟩ := hN hw
    rw [MonoidHom.mem_ker]
    simp only [ψ, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact ⟨unitsIncl K x, by simp⟩
  set ψ' := QuotientGroup.lift _ ψ hle
  set π := uniformizerUnit hϖ
  let g : Fin m × (𝒪[K]ˣ ⧸ unitFiltration K N) → Kˣ ⧸ H :=
    fun p ↦ (QuotientGroup.mk π : Kˣ ⧸ H) ^ (p.1 : ℕ) * ψ' p.2
  refine Finite.of_surjective g ?_
  intro y
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
  set p := unitsEquivIntProd hϖ x
  have hx : x = unitsOfIntProd hϖ p := by
    rw [← unitsEquivIntProd_symm_apply, MulEquiv.symm_apply_apply]
  set n := Multiplicative.toAdd p.1
  have hmpos : (0 : ℤ) < m := by exact_mod_cast Nat.pos_of_ne_zero hm0
  set r := n % (m : ℤ)
  set q := n / (m : ℤ)
  have hr0 : 0 ≤ r := Int.emod_nonneg _ hmpos.ne'
  have hrm : r < m := Int.emod_lt_of_pos _ hmpos
  have hnrq : n = r + m * q := by have := Int.mul_ediv_add_emod n m; linarith
  refine ⟨(⟨r.toNat, by omega⟩, QuotientGroup.mk p.2), ?_⟩
  have hπ : π ^ n = π ^ r.toNat * (π ^ q) ^ m := by
    rw [← zpow_natCast, ← zpow_natCast (π ^ q) m, ← zpow_mul, ← zpow_add, Int.toNat_of_nonneg hr0,
      hnrq, mul_comm]
  have hxπ : x = π ^ n * unitsIncl K p.2 := by
    rw [hx]
    rfl
  simp only [g, ψ', QuotientGroup.lift_mk, ψ, MonoidHom.comp_apply, QuotientGroup.mk'_apply]
  rw [hxπ, hπ, ← QuotientGroup.mk_pow, ← QuotientGroup.mk_mul, QuotientGroup.eq]
  refine ⟨π ^ q, ?_⟩
  rw [powMonoidHom_apply, mul_right_comm (π ^ r.toNat), inv_mul_cancel_left]
end GroundTheory.LocalField
