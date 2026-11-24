-- Prove2me | solution 1 for GlobalTheory.AdelicMatLat.isLattice_lat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T15:25:58.301897+00:00
-- url     : https://prove2.me/submissions/9bd7f551-7a55-4932-9b37-a29f62f685ad

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FiniteAdeleStrongApproximationModNat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsLatticeAdelicMatrixIntegralTranslate
import Theorems.Thm_GlobalTheory_AdelicMatLat_span_lat
import Theorems.Thm_GlobalTheory_AdelicMatLat_fg_lat

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped Matrix
open NumberField IsDedekindDomain
open GlobalTheory GlobalTheory.AdelicMatLat
variable (E : Type) [Field E] [NumberField E]
variable {E} {n : ℕ}
namespace GlobalTheory.AdelicMatLat
theorem _root_.solution (β : GL (Fin n) (FiniteAdeleRing (𝓞 E) E)) :
    Submodule.IsLattice E (lat β.1) := ⟨fg_lat β, span_lat β.1⟩
end GlobalTheory.AdelicMatLat
