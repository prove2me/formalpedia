-- Prove2me | solution 1 for GlobalTheory.HomExt.finite_preimage_of_finite_lifts
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:51:02.55819+00:00
-- url     : https://prove2.me/submissions/1129e2a3-8a0f-48c1-882b-74fcab352c44

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_FlatImageOfOverFractionFieldOfValuationRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsOpenOfMemIrreducibleComponentsOfFinite
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_BijectiveAlgebraMapIntegralClosureOfBirational
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_IsIsoStalkMapOfFlatOfSurjectiveOnStalks
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_LocallyQuasiFiniteOfFiniteGeometricPoints
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_IsIsoOfDensePartOfIsIntegral
import Theorems.Thm_GlobalTheory_finite_of_finite_sections


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace
open GlobalTheory GlobalTheory.HomExt
namespace GlobalTheory.HomExt
theorem _root_.solution {X Y : Scheme.{0}} (f : X ⟶ Y) [LocallyOfFiniteType f]
    {Ω : Type} [Field Ω] [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ Y)
    (h : Finite {x : Spec (.of Ω) ⟶ X // x ≫ f = y}) : (f ⁻¹' Set.range y).Finite := by
  have hP : Finite ↥(pullback f y) := by
    refine finite_of_finite_sections (pullback.snd f y) ?_
    refine Finite.of_injective (β := {x : Spec (.of Ω) ⟶ X // x ≫ f = y})
      (fun x ↦ ⟨x.1 ≫ pullback.fst f y, by
        rw [Category.assoc, pullback.condition, ← Category.assoc, x.2, Category.id_comp]⟩) ?_
    intro a b hab
    apply Subtype.ext
    apply pullback.hom_ext
    · exact congrArg Subtype.val hab
    · rw [a.2, b.2]
  rw [← Scheme.Pullback.range_fst]
  exact Set.finite_range _
end GlobalTheory.HomExt
