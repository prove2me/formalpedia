-- Prove2me | solution 1 for GlobalTheory.exists_comp_comp_eq_of_field
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T07:54:58.656805+00:00
-- url     : https://prove2.me/submissions/3294c489-f9af-463a-8ec5-2600bb28f01a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_CubeTotalComplexAcyclicOfSlicesInductionOnCard
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_RangeRestrictCompSubtypeOfOrthogonalOfNe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits HomologicalComplex TensorProduct
universe v u
open GlobalTheory
variable {ι : Type} [LinearOrder ι] {K : Type u} [Field K]
open GlobalTheory.Cube
namespace GlobalTheory
theorem _root_.solution {V W : Type*} [AddCommGroup V] [Module K V] [AddCommGroup W]
    [Module K W] (f : V →ₗ[K] W) : ∃ g : W →ₗ[K] V, ∀ x, f (g (f x)) = f x := by
  obtain ⟨s, hs⟩ := f.rangeRestrict.exists_rightInverse_of_surjective f.range_rangeRestrict
  obtain ⟨g, hg⟩ := s.exists_extend
  refine ⟨g, fun x => ?_⟩
  have h1 : g (f x) = s (f.rangeRestrict x) := congr($hg (f.rangeRestrict x))
  rw [h1]
  exact congrArg Subtype.val congr($hs (f.rangeRestrict x))
end GlobalTheory
