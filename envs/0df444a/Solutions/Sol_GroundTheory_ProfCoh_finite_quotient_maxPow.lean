-- Prove2me | solution 1 for GroundTheory.ProfCoh.finite_quotient_maxPow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:24:43.514748+00:00
-- url     : https://prove2.me/submissions/215eee41-21e9-44d3-b31f-de841fb96361

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
omit [TopologicalSpace E] [IsNonarchimedeanLocalField E] [ValuativeExtension E F]
  [FiniteDimensional E F]
namespace GroundTheory.ProfCoh
theorem _root_.solution {θ : F} {k : ℕ} (hle : maxPow F k ≤ normalSub E θ) :
    Finite (normalSub E θ ⧸ (AddSubgroup.inclusion hle).range) := by
  have hr : (AddSubgroup.inclusion hle).range = (maxPow F k).addSubgroupOf (normalSub E θ) := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact y.2
    · intro hx
      exact ⟨⟨x, hx⟩, rfl⟩
  have hfin : Finite (𝒪[F] ⧸ maxPow F k) :=
    IsLocalRing.finite_quotient_iff.mpr ⟨k, le_rfl⟩
  have hidx : (maxPow F k).index ≠ 0 := AddSubgroup.index_ne_zero_of_finite
  have hrel : (maxPow F k).relIndex (normalSub E θ) ≠ 0 :=
    fun h ↦ hidx (Nat.eq_zero_of_zero_dvd (h ▸ AddSubgroup.relIndex_dvd_index_of_le hle))
  rw [hr]
  have : ((maxPow F k).addSubgroupOf (normalSub E θ)).FiniteIndex := ⟨hrel⟩
  infer_instance
end GroundTheory.ProfCoh
