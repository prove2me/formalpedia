-- Prove2me | solution 1 for GroundTheory.LocalField.exists_pow_smul_mem_normalLattice
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:19:00.53747+00:00
-- url     : https://prove2.me/submissions/3c8129ce-6855-4c66-92a8-fb6153f81fc5

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_Interface
import Definitions.Def_GroundTheory_LocalFields_UnitsBasic
import Definitions.Def_GroundTheory_LocalFields_NormalLattice
import Theorems.Thm_GroundTheory_LocalField_integer_smul_eq
import Theorems.Thm_GroundTheory_LocalField_mem_normalLattice_iff
import Theorems.Thm_GroundTheory_LocalField_exists_pow_mul_mem_integer

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.LocalField
open ValuativeRel Finset
variable {K L : Type*} [Field K] [ValuativeRel K] [Field L] [Algebra K L]
variable [FiniteDimensional K L]
variable [TopologicalSpace K] [IsNonarchimedeanLocalField K] [ValuativeRel L]
  [ValuativeExtension K L]
variable (π : 𝒪[K]) (θ : L)
variable [IsGalois K L]
omit [ValuativeRel L] [ValuativeExtension K L]
namespace GroundTheory.LocalField
theorem _root_.solution (hπ : Irreducible π)
    (hθ : LinearIndependent K fun σ : Gal(L/K) => σ θ) (y : L) :
    ∃ n, ∀ m ≥ n, π ^ m • y ∈ normalLattice π θ 0 := by
  let b : Module.Basis Gal(L/K) K L := basisOfLinearIndependentOfCardEqFinrank hθ
    (Fintype.card_eq_nat_card.trans (IsGalois.card_aut_eq_finrank K L))
  have hb : ∀ σ, b σ = σ θ := fun σ => by
    simp [b, coe_basisOfLinearIndependentOfCardEqFinrank]
  choose n hn using fun σ => exists_pow_mul_mem_integer π hπ (b.repr y σ)
  refine ⟨univ.sup n, fun m hm => (mem_normalLattice_iff π θ).mpr
    ⟨fun σ => ⟨_, hn σ m ((le_sup (mem_univ σ)).trans hm)⟩, ?_⟩⟩
  conv_rhs => rw [← b.sum_repr y]
  rw [pow_zero, one_smul, smul_sum]
  refine sum_congr rfl fun σ _ => ?_
  rw [hb, integer_smul_eq, integer_smul_eq, Algebra.smul_def, ← mul_assoc, ← map_mul]
  simp
end GroundTheory.LocalField
