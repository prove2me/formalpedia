-- Prove2me | solution 1 for GlobalTheory.CNorm.pTor_range_of_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T13:32:19.387229+00:00
-- url     : https://prove2.me/submissions/0c4c433b-14c9-466b-ae11-b843ca60e976

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_MemPowSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_PowIndexTorsionKerRangeMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_SubgroupPowRelIndexTopOfGroupFg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_CardQuotSpanAlgebraMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IsAdicCompleteSpanAlgebraMapOfFreeFinite
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IsAdicCompleteAndCardQuotientAdicCompletionInteg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_NormCoeffMinpolyLeOneOfNormLeOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_SubgroupPowRelIndexUnitsOfIsAdicCompleteStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsGlobalUniformizerResidueRepresentatives
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_PIdxUnitsFiniteExtensionAdicCompletion

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct
open GlobalTheory GlobalTheory.CNorm
namespace GlobalTheory.CNorm
theorem _root_.solution (p : ℕ) {A B : Type} [CommGroup A] [CommGroup B] (j : A →* B)
    (hj : Function.Injective j) : pTor p j.range = pTor p (⊤ : Subgroup A) := by
  unfold pTor
  symm
  refine Nat.card_congr (Equiv.ofBijective
    (fun x => ⟨j x.1, ⟨x.1, rfl⟩, by rw [← map_pow, x.2.2, map_one]⟩) ⟨?_, ?_⟩)
  · intro x y h
    exact Subtype.ext (hj (congrArg Subtype.val h))
  · rintro ⟨_, ⟨a, rfl⟩, h⟩
    exact ⟨⟨a, trivial, hj (by rw [map_pow, h, map_one])⟩, rfl⟩
end GlobalTheory.CNorm
