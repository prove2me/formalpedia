-- Prove2me | solution 1 for GlobalTheory.AdLat.Translate.fv_mem_hat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T14:07:53.210516+00:00
-- url     : https://prove2.me/submissions/1de10080-1017-4d3d-85a8-b429d1694a3d

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
theorem _root_.solution {S : Set (Fin n → E)} {x : Fin n → E} (hx : x ∈ S) : fv F x ∈ hat F S :=
  AddSubgroup.subset_closure ⟨1, fun v => one_mem _, x, hx, rfl⟩
end GlobalTheory.AdLat.Translate
