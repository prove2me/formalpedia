-- Prove2me | solution 1 for GroundTheory.ProfCoh.unitToModN_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:37:08.930796+00:00
-- url     : https://prove2.me/submissions/50533f3a-4ea5-410a-8631-050439573b95

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_LocalEulerCharacteristic_UnitsPower
import Definitions.Def_GroundTheory_LocalFields_UnitsGalois
import Definitions.Def_GroundTheory_LocalFields_ExistsUnitFiltrationUnitsLeAndRangePowLe
import Definitions.Def_GroundTheory_ProfiniteCohomology_LocalEulerCharacteristic_Additive
import Definitions.Def_GroundTheory_ProfiniteCohomology_LocalEulerCharacteristic_UnitsLattice
import Theorems.Thm_GroundTheory_ProfCoh_coe_maxPow_smul
import Theorems.Thm_GroundTheory_ProfCoh_unitToModN_apply
import Theorems.Thm_GroundTheory_ProfCoh_modNRep_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.ProfCoh.modNRep_mk



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
theorem _root_.solution (hϖ : Irreducible ϖ) (hpe : (p : 𝒪[F]) = ϖ ^ e * ε) {k : ℕ}
    (hk : e ≤ k) (σ : F ≃ₐ[E] F) (u : Additive (unitFiltration F k)) :
    unitToModN hϖ hpe hk (σ • u) =
      modNRep (F ≃ₐ[E] F) (maxPow F k) p σ (unitToModN hϖ hpe hk u) := by
  rw [unitToModN_apply, unitToModN_apply, modNRep_mk]
  congr 1
  ext
  rw [coe_maxPow_smul, smul_sub, smul_one]
  rfl
end GroundTheory.ProfCoh
