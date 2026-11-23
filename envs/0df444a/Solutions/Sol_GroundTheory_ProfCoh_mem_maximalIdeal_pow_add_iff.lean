-- Prove2me | solution 1 for GroundTheory.ProfCoh.mem_maximalIdeal_pow_add_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:13:18.430036+00:00
-- url     : https://prove2.me/submissions/2839b610-204d-4efb-aebc-2853776d6795

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_LocalEulerCharacteristic_UnitsPower
import Definitions.Def_GroundTheory_LocalFields_UnitsGalois
import Definitions.Def_GroundTheory_LocalFields_ExistsUnitFiltrationUnitsLeAndRangePowLe
import Definitions.Def_GroundTheory_ProfiniteCohomology_LocalEulerCharacteristic_Additive
import Definitions.Def_GroundTheory_ProfiniteCohomology_LocalEulerCharacteristic_UnitsLattice

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
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
theorem _root_.solution {k : ℕ} {x : 𝒪[F]} :
    x ∈ 𝓂[F] ^ (k + e) ↔ ∃ y ∈ 𝓂[F] ^ k, x = p * y := by
  constructor
  · intro h
    obtain ⟨a, rfl⟩ := (mem_maximalIdeal_pow_iff hϖ).mp h
    refine ⟨ϖ ^ k * a * ((ε⁻¹ : 𝒪[F]ˣ) : 𝒪[F]), ?_, ?_⟩
    · rw [mem_maximalIdeal_pow_iff hϖ, mul_assoc]
      exact dvd_mul_right _ _
    · rw [hpe]
      have := ε.mul_inv
      linear_combination (-(ϖ ^ (k + e)) * a) * this
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨b, rfl⟩ := (mem_maximalIdeal_pow_iff hϖ).mp hy
    rw [mem_maximalIdeal_pow_iff hϖ, hpe]
    exact ⟨ε * b, by ring⟩
end GroundTheory.ProfCoh
