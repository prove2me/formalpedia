-- Prove2me | solution 1 for GroundTheory.LocalField.exists_pow_mul_mem_integer_of_lt_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:59:56.622217+00:00
-- url     : https://prove2.me/submissions/31213334-fd31-4a23-99dc-d8a8eb5d8993

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_Interface
import Definitions.Def_GroundTheory_LocalFields_UnitsBasic
import Definitions.Def_GroundTheory_LocalFields_NormalLattice

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
omit [ValuativeRel L] [ValuativeExtension K L] [FiniteDimensional K L]
namespace GroundTheory.LocalField
theorem _root_.solution {F : Type*} [Field F] [ValuativeRel F]
    [TopologicalSpace F] [IsNonarchimedeanLocalField F] {t : F}
    (ht : valuation F t < 1) (a : F) : ∃ n, ∀ m ≥ n, t ^ m * a ∈ 𝒪[F] := by
  have ht1 : t ∈ 𝒪[F] := (Valuation.mem_integer_iff _ _).mpr ht.le
  have key : ∃ n, t ^ n * a ∈ 𝒪[F] := by
    by_cases ha : a = 0
    · exact ⟨0, by simp [ha]⟩
    have hva : valuation F a ≠ 0 := by simpa using ha
    obtain ⟨n, hn⟩ := exists_pow_lt₀ ht (Units.mk0 (valuation F a)⁻¹ (inv_ne_zero hva))
    refine ⟨n, (Valuation.mem_integer_iff _ _).mpr (le_of_lt ?_)⟩
    calc valuation F (t ^ n * a) = valuation F t ^ n * valuation F a := by simp
      _ < (valuation F a)⁻¹ * valuation F a :=
          mul_lt_mul_of_pos_right (by simpa using hn) (zero_lt_iff.mpr hva)
      _ = 1 := inv_mul_cancel₀ hva
  obtain ⟨n, hn⟩ := key
  refine ⟨n, fun m hm => ?_⟩
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hm
  rw [pow_add, mul_comm (t ^ n), mul_assoc]
  exact mul_mem (pow_mem ht1 d) hn
end GroundTheory.LocalField
