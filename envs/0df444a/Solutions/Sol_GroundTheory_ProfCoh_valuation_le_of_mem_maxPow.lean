-- Prove2me | solution 1 for GroundTheory.ProfCoh.valuation_le_of_mem_maxPow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:25:42.814295+00:00
-- url     : https://prove2.me/submissions/a0c51b7a-42ee-40e8-a596-ba57e1cc809b

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_LocalEulerCharacteristic_UnitsLattice
import Definitions.Def_GroundTheory_LocalFields_NormalLattice
import Definitions.Def_GroundTheory_ProfiniteCohomology_LocalEulerCharacteristic_ModNEquivOfSurjectiveApplyModNRep
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
omit [FiniteDimensional E F]
namespace GroundTheory.ProfCoh
theorem _root_.solution {ϖ : 𝒪[F]} (hϖ : Irreducible ϖ) {k : ℕ} {x : 𝒪[F]}
    (hx : x ∈ 𝓂[F] ^ k) : valuation F (x : F) ≤ valuation F (ϖ : F) ^ k := by
  obtain ⟨a, rfl⟩ := (mem_maximalIdeal_pow_iff hϖ).mp hx
  rw [Subring.coe_mul, map_mul, SubmonoidClass.coe_pow, map_pow]
  exact mul_le_of_le_one_right' a.2
end GroundTheory.ProfCoh
