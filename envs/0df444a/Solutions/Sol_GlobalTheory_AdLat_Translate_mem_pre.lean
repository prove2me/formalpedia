-- Prove2me | solution 1 for GlobalTheory.AdLat.Translate.mem_pre
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T14:15:35.80172+00:00
-- url     : https://prove2.me/submissions/45fe4ad6-c02e-4100-9f75-5656ae0bbc64

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_Hat1
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_AdelicCompletionRationalPointsAndApproximation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsLatticeRationalVectorsInAdelicTranslate

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.AdLat
open scoped TensorProduct Matrix nonZeroDivisors
open GlobalTheory GlobalTheory.AdLat GlobalTheory.AdLat.Translate
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ}
namespace GlobalTheory.AdLat.Translate
theorem _root_.solution {M : Matrix (Fin n) (Fin n) (RA F E)} {L : Submodule (𝓞 E) (Fin n → E)} {v : Fin n → E} :
    v ∈ pre M L ↔ M.mulVec (fv F v) ∈ hat F (L : Set (Fin n → E)) := Iff.rfl
end GlobalTheory.AdLat.Translate
