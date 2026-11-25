-- Prove2me | solution 1 for GlobalTheory.TateFree.comp_ofId_bijective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:55:20.921839+00:00
-- url     : https://prove2.me/submissions/1697eb93-3777-4098-8fb2-4bb1a2498972

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ToSpanSingletonConstGenInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsCounitEqOneMulEqZeroOfIsNilpotent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsUniqueAlgEquivOfCompatibleQuotient
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ConvEqOneOfForallPairing
import Theorems.Thm_GlobalTheory_IsBicharacter_map


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open TensorProduct Coalgebra Bialgebra WithConv Module
open GlobalTheory
open GlobalTheory.TateFree
variable (O C A : Type) [CommRing O] [Field C] [Algebra O C] [IsIntegrallyClosedIn O C]
  [CommRing A]
namespace GlobalTheory.TateFree
theorem _root_.solution [Algebra O A] [Module.Finite O A] :
    Function.Bijective fun x : A →ₐ[O] O => (Algebra.ofId O C).comp x := by
  have hi : Function.Injective (Algebra.ofId O C) := IsIntegralClosure.algebraMap_injective O O C
  refine ⟨fun x y h => AlgHom.ext fun a => hi (DFunLike.congr_fun h a), fun y => ?_⟩
  have hm : ∀ a, y a ∈ (Algebra.ofId O C).range := fun a =>
    IsIntegrallyClosedIn.isIntegral_iff.1 ((Algebra.IsIntegral.isIntegral a).map y)
  let e := AlgEquiv.ofInjective _ hi
  exact ⟨(e.symm : (Algebra.ofId O C).range →ₐ[O] O).comp (y.codRestrict _ hm),
    AlgHom.ext fun a => congrArg Subtype.val (e.apply_symm_apply ⟨y a, hm a⟩)⟩
end GlobalTheory.TateFree
