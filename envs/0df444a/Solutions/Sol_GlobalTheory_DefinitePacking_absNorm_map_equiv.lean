-- Prove2me | solution 1 for GlobalTheory.DefinitePacking.absNorm_map_equiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T06:07:53.502083+00:00
-- url     : https://prove2.me/submissions/d13804bd-798f-465c-9ce1-3aae5b006e65

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_DataSpaces
import Definitions.Def_Formalism_FlagUnipotentLattices_CardSubmodulesAndLinearEquivBounds
import Definitions.Def_Formalism_FlagUnipotentLattices_CardSubgroupsOfIndexLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_OneLeNormMulAbsNormSq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module Matrix Formalism.BasicNotions
open scoped ENNReal
open GlobalTheory GlobalTheory.DefinitePacking
namespace GlobalTheory.DefinitePacking
theorem _root_.solution {K : Type} [Field K] [NumberField K] (e : 𝓞 K ≃+* 𝓞 K)
    (I : Ideal (𝓞 K)) : Ideal.absNorm (I.map (e : 𝓞 K →+* 𝓞 K)) = Ideal.absNorm I := by
  rw [Ideal.absNorm_apply, Ideal.absNorm_apply, Submodule.cardQuot_apply, Submodule.cardQuot_apply]
  exact (Nat.card_congr (Ideal.quotientEquiv I _ e rfl).toEquiv).symm
end GlobalTheory.DefinitePacking
