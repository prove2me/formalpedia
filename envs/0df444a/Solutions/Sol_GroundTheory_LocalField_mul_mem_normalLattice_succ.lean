-- Prove2me | solution 1 for GroundTheory.LocalField.mul_mem_normalLattice_succ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:25:42.856398+00:00
-- url     : https://prove2.me/submissions/e3cbdd2e-9146-4cc8-8701-279cb08803ff

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_Interface
import Definitions.Def_GroundTheory_LocalFields_UnitsBasic
import Definitions.Def_GroundTheory_LocalFields_NormalLattice
import Theorems.Thm_GroundTheory_LocalField_normalLattice_antitone
import Theorems.Thm_GroundTheory_LocalField_mul_mem_normalLattice

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
variable (π : 𝒪[K]) (θ : L)
namespace GroundTheory.LocalField
theorem _root_.solution {r : ℕ}
    (hr : ∀ σ τ : Gal(L/K), π ^ r • (σ θ * τ θ) ∈ normalLattice π θ 0) {s t : ℕ} (hs : r < s)
    {x y : L} (hx : x ∈ normalLattice π θ s) (hy : y ∈ normalLattice π θ t) :
    x * y ∈ normalLattice π θ (t + 1) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt hs
  have h := mul_mem_normalLattice π θ hr (a := d + 1) (b := t)
    (by rwa [show d + 1 + r = r + d + 1 by omega]) hy
  exact normalLattice_antitone π θ (show t + 1 ≤ d + 1 + t by omega) h
end GroundTheory.LocalField
