-- Prove2me | solution 1 for GroundTheory.ProfCoh.exists_maxPow_le_normalSub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:37:13.233813+00:00
-- url     : https://prove2.me/submissions/54d3ebd0-6cf6-48e3-81fe-120e1a24767a

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_LocalEulerCharacteristic_UnitsLattice
import Definitions.Def_GroundTheory_LocalFields_NormalLattice
import Definitions.Def_GroundTheory_ProfiniteCohomology_LocalEulerCharacteristic_ModNEquivOfSurjectiveApplyModNRep
import Theorems.Thm_GroundTheory_ProfCoh_valuation_le_of_mem_maxPow
import Theorems.Thm_GroundTheory_LocalField_exists_pow_lt
import Theorems.Thm_GroundTheory_LocalField_isOpen_normalLattice
import Theorems.Thm_GroundTheory_ProfCoh_normalLattice_zero_eq
import Theorems.Thm_P2M_UpperTheory_Reformulated_B_AdicCompleteRootExistence_exists_root_of_dvd__8130b8fccf10


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
universe u
open GroundTheory.LocalField ValuativeRel IsLocalRing
variable {E F : Type u} [Field E] [ValuativeRel E] [TopologicalSpace E]
  [IsNonarchimedeanLocalField E]
  [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [Algebra E F] [ValuativeExtension E F] [FiniteDimensional E F]
variable {l : ℕ} [NeZero l] (d : AdditiveFunction.{u} l (F ≃ₐ[E] F))
attribute [local instance] integerAction unitFiltrationAction
attribute [local instance] maxPowAction normalSubAction
namespace GroundTheory.ProfCoh
theorem _root_.solution [IsGalois E F] {θ : F}
    (hθ : LinearIndependent E fun σ : F ≃ₐ[E] F ↦ σ θ) :
    ∃ j, ∀ k ≥ j, maxPow F k ≤ normalSub E θ := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[E]
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[F]
  have hopen := isOpen_normalLattice π θ hπ hθ 0
  rw [normalLattice_zero_eq] at hopen
  obtain ⟨γ, hγ⟩ := (IsValuativeTopology.mem_nhds_zero_iff _).mp
    (hopen.mem_nhds (Submodule.zero_mem _))
  obtain ⟨j, -, hj⟩ := exists_pow_lt hϖ γ.ne_zero
  refine ⟨j, fun k hk x hx ↦ mem_normalSub.mpr (hγ ?_)⟩
  have h1 : valuation F (ϖ : F) ≤ 1 := ϖ.2
  calc valuation F (x : F) ≤ valuation F (ϖ : F) ^ k := valuation_le_of_mem_maxPow hϖ hx
    _ ≤ valuation F (ϖ : F) ^ j := pow_le_pow_right_of_le_one' h1 hk
    _ < γ := hj
end GroundTheory.ProfCoh
