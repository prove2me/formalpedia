-- Prove2me | solution 1 for GroundTheory.ProfCoh.unitToModN_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:12:43.104666+00:00
-- url     : https://prove2.me/submissions/d7a47506-e149-4802-a3c4-4979fb8870e9

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
omit hϖ hpe
variable (ϖ)
namespace GroundTheory.ProfCoh
theorem _root_.solution (hϖ : Irreducible ϖ) (hpe : (p : 𝒪[F]) = ϖ ^ e * ε) {k : ℕ} (hk : e ≤ k)
    (u : Additive (unitFiltration F k)) :
    unitToModN hϖ hpe hk u =
      Submodule.Quotient.mk ⟨((u.toMul : 𝒪[F]ˣ) : 𝒪[F]) - 1, sub_one_mem_maxPow u.toMul⟩ :=
  rfl
end GroundTheory.ProfCoh
