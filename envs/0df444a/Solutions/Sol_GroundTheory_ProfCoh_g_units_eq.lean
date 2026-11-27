-- Prove2me | solution 1 for GroundTheory.ProfCoh.g_units_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:49:37.051354+00:00
-- url     : https://prove2.me/submissions/3521fe3b-32d0-47bb-9178-924eeca89117

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_LocalEulerCharacteristic_UnitsLattice
import Definitions.Def_GroundTheory_LocalFields_NormalLattice
import Definitions.Def_GroundTheory_ProfiniteCohomology_LocalEulerCharacteristic_ModNEquivOfSurjectiveApplyModNRep
import Theorems.Thm_GroundTheory_ProfCoh_g_units_eq_one_add
import Theorems.Thm_GroundTheory_ProfCoh_g_integerUnits_eq
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
  [Algebra E F] [ValuativeExtension E F] [FiniteDimensional E F] [IsGalois E F]
  {l : ℕ} [Fact l.Prime] (d : AdditiveFunction.{u} l (F ≃ₐ[E] F))
attribute [local instance] integerAction unitFiltrationAction maxPowAction normalSubAction
namespace GroundTheory.ProfCoh
theorem _root_.solution (hl : (l : E) ≠ 0) {n : ℕ}
    (hn : Nat.card (𝒪[E] ⧸ Ideal.span {(l : 𝒪[E])}) = l ^ n) :
    d.g (Additive Fˣ) = d.one + n * d.toFun (MonoidAlgebra (ZMod l) (F ≃ₐ[E] F))
      (Representation.leftRegular (ZMod l) (F ≃ₐ[E] F)) := by
  have hlF : (l : F) ≠ 0 := by
    rw [← map_natCast (algebraMap E F)]
    exact (map_ne_zero _).mpr hl
  obtain ⟨hfin, hg⟩ := g_integerUnits_eq d hlF hn
  rw [g_units_eq_one_add d, hg]
end GroundTheory.ProfCoh
