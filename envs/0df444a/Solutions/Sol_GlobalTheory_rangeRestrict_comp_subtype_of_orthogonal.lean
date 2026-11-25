-- Prove2me | solution 1 for GlobalTheory.rangeRestrict_comp_subtype_of_orthogonal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T07:44:25.266274+00:00
-- url     : https://prove2.me/submissions/aee0353e-3250-438b-8cd6-335c109110b9

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
variable {K : Type u} [CommRing K] {V V' : Type*} [AddCommGroup V] [Module K V]
  [AddCommGroup V'] [Module K V']
namespace GlobalTheory
theorem _root_.solution {f : ℕ → Module.End K V}
    (hf : ∀ p q, f p * f q = if p = q then f p else 0) (p : ℕ) :
    (f p).rangeRestrict ∘ₗ (LinearMap.range (f p)).subtype = LinearMap.id := by
  refine LinearMap.ext ?_
  rintro ⟨_, x, rfl⟩
  have := hf p p
  rw [if_pos rfl] at this
  exact Subtype.ext congr($this x)
end GlobalTheory
