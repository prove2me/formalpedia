-- Prove2me | solution 1 for GlobalTheory.NormOneSplit.finite_hom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T03:34:32.564072+00:00
-- url     : https://prove2.me/submissions/f4e3a966-882e-4df1-afa9-89d44feee473

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_DataSpaces
import Definitions.Def_Formalism_FlagUnipotentLattices_CardSubmodulesAndLinearEquivBounds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsForallHomEq

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
open GlobalTheory GlobalTheory.NormOneSplit
open NumberField Module Matrix
open scoped ENNReal
namespace GlobalTheory.NormOneSplit
namespace _root_.GlobalTheory.NormOneSplit
theorem _root_.solution {E : Type} [Field E] [NumberField E] {T : ℕ}
    (hT : T.Prime) :
    Finite (𝓞 E →+* ZMod T) := by
  haveI : NeZero T := ⟨hT.ne_zero⟩
  let b := Module.Free.chooseBasis ℤ (𝓞 E)
  refine Finite.of_injective (fun φ : 𝓞 E →+* ZMod T => fun i => φ (b i)) ?_
  intro φ ψ h
  have key : φ.toIntAlgHom.toLinearMap = ψ.toIntAlgHom.toLinearMap :=
    b.ext (fun i => congrFun h i)
  ext x
  exact LinearMap.congr_fun key x
end _root_.GlobalTheory.NormOneSplit
end GlobalTheory.NormOneSplit
