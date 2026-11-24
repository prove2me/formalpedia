-- Prove2me | solution 1 for GlobalTheory.AdLat.UnitRoot.exists_incl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:54:11.829483+00:00
-- url     : https://prove2.me/submissions/3fe7fc7c-8d4c-44d6-b8c4-b23813bf74b3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_Hat1
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_AdelicCompletionFractionalIdealProperties
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsIntegralUnitRootNormOneAdele

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.AdLat
open scoped TensorProduct Topology Matrix
open GlobalTheory GlobalTheory.AdLat GlobalTheory.AdLat.UnitRoot
variable (F : Type) [Field F] [NumberField F]
namespace GlobalTheory.AdLat.UnitRoot
theorem _root_.solution {a : FiniteAdeleRing (𝓞 F) F} (ha : ∀ v, a v ∈ v.adicCompletionIntegers F) :
    ∃ b, incl F b = a := ⟨fun v => ⟨a v, ha v⟩, rfl⟩
end GlobalTheory.AdLat.UnitRoot
