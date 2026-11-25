-- Prove2me | solution 1 for GroundTheory.ProfCoh.unitsIncl_toAdditive_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:25:41.186523+00:00
-- url     : https://prove2.me/submissions/0d7e9db6-3f9a-4f74-a0ed-4a0c531c1d39

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_LocalEulerCharacteristic_UnitsLattice
import Definitions.Def_GroundTheory_LocalFields_NormalLattice
import Definitions.Def_GroundTheory_ProfiniteCohomology_LocalEulerCharacteristic_ModNEquivOfSurjectiveApplyModNRep
import Theorems.Thm_GroundTheory_LocalField_unitsIncl_smul


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
namespace GroundTheory.ProfCoh
theorem _root_.solution (σ : F ≃ₐ[E] F) (a : Additive 𝒪[F]ˣ) :
    (unitsIncl F).toAdditive (σ • a) = σ • (unitsIncl F).toAdditive a :=
  congrArg Additive.ofMul (unitsIncl_smul σ a.toMul)
end GroundTheory.ProfCoh
